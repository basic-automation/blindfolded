/-
  BlindPRF/Unforgeability.lean — the "signature" in the design: forging is the CDH problem.

  The value party A obtains is `σ = prf H k m = k • H m`, a signature (MAC tag) on `m` under
  party B's key `k`.  The classical claim is: with the hash `H` modelled as a random oracle,
  nobody who has seen signatures on other messages can produce the signature on a fresh message,
  under the Computational Diffie–Hellman (CDH) assumption.

  HONESTY POINT FIRST.  Unforgeability cannot be proved outright: it implies that a computational
  problem is hard.  CDH is an ASSUMPTION; it is neither proved nor postulated (no axiom, no
  hypothesis) anywhere in this file.  What is proved is the REDUCTION, as an exact equality
  between two explicitly defined experiments (probability distributions on `Bool`):

      forgeExp F g m* Adv  =  cdhExp F g (cdhSolver F g m* Adv)            (`forge_eq_cdh`)

  i.e. whatever a forger `Adv` achieves in the forgery experiment, the explicitly written CDH
  solver built from it achieves, with exactly the same probability, against CDH.  Section E
  proves that an unbounded forger wins with certainty, so the statement "every forger wins with
  small probability" is FALSE in this model (Lean functions are not computationally bounded) and
  is never stated.

  The forgery experiment `forgeExp F g m* Adv` (selective target, known messages):

  * the target message `m*` is FIXED IN ADVANCE (it is a parameter of the experiment);
  * a key `k : F` and a table of exponents `h : M → F` are sampled uniformly; the hash function is
    the eagerly sampled random oracle `H m = h m • g` on the FINITE message space `M`;
  * the forger is handed `ForgerInput G M`: the public key `k • g`, the WHOLE hash table `H`
    (group elements, not their discrete logarithms) and the signatures `k • H m` on ALL messages
    `m ≠ m*` (a dummy `0` at `m*`);
  * it outputs ONE group element and wins if that is `prf H k m* = k • H m*`.

  The CDH experiment `cdhExp F g S`: sample `a, b : F` uniformly, give the solver `(a • g, b • g)`,
  it wins if it outputs `(a * b) • g`.

  Contents.

  * 0. General facts about uniform sampling (overwriting one coordinate of a uniform function
       with a fresh uniform value; probability of an event as a ratio of cardinalities).
  * A. Definitions: `ForgerInput`, `roHash`, `knownSigs`, `forgeExp`, `cdhExp`, `cdhSolver`, and
       the auxiliary adversaries/experiments used in the later sections.
  * B. Sanity of the definitions: the oracle is a uniformly random function when `g` generates
       the group; everything party A sees in an honest protocol run on a message other than the
       target is computable from the forger's input.
  * C. `forge_eq_cdh` (forger ⟹ CDH solver, exact) and the converse `cdh_eq_forge`
       (CDH solver ⟹ forger, exact).
  * D. The honest-but-curious party A: the experiment `hbcExp`, in which A first runs `n` honest
       protocol sessions on messages other than the target and sees its complete views, IS a
       forgery experiment (`hbc_eq_forge`) and hence a CDH experiment (`hbc_eq_cdh`).
  * E. S1: an unbounded forger (`dlogForger`, takes a discrete logarithm) wins with certainty.
  * F. S2: the experiment is not trivially winnable: a forger that outputs a constant wins with
       probability exactly `(|F| - 1) / |F|²` (constant `≠ 0`, `g` a generator) or
       `(2|F| - 1) / |F|²` (constant `0`, `g ≠ 0`); in particular at most `2 / |F|` and strictly
       less than `1`.  (These are statements about the constant forgers only.)
  * G. S3: teeth: if the forger is additionally handed the oracle EXPONENT `h m*` of the target,
       one scalar multiplication wins with certainty (`forgeExpLeaky_leakForger`).  So it matters
       that `ForgerInput` contains group elements only.
  * H. Non-vacuity: a model of all hypotheses (`F = G = ZMod p`, `g = 1`) — in which, by the way,
       CDH is easy and an efficient forger wins with certainty: hardness is a property of the
       concrete group and can never follow from the algebraic setting alone.

  What is NOT claimed or modelled:

  * CDH (or any other hardness assumption) is not proved and not assumed.  No theorem here says
    that any winning probability is small for all adversaries.
  * The forger is PASSIVE: it sees signatures on messages, but it cannot make B evaluate group
    elements of its choice.  This covers an honest-but-curious party A (section D), not a party A
    that deviates from the protocol.  Against a deviating A, who may submit arbitrary group
    elements to B, unforgeability is the ONE-MORE Diffie–Hellman assumption ("one-more
    unforgeability": after `n` interactions, no `n + 1` valid signatures).  That notion is NOT
    proved, NOT reduced to anything, and not even defined in this file.
  * The target is SELECTIVE (fixed before the key and the oracle are sampled).  The adaptive
    notion, where the forger chooses the target after seeing its input, is not treated here.
  * The forger has no verification oracle: it outputs a single candidate and is never told
    whether a candidate is valid.  Verification needs the key (`verifyWithKey`); a forger that
    may ask the key holder to verify candidates is not covered (that is a gap-type assumption).
    The pairing setting of `PublicVerify.lean`, where everybody can verify, is not formalised
    here either.
  * The random oracle is an eagerly sampled table `m ↦ h m • g` on a finite message space; no
    statement is made about any concrete hash function, nor about lazily sampled oracles on
    infinite domains.
  * Lean has no cost model here.  "The reduction is efficient" (`cdhSolver` samples one table of
    exponents, performs at most two scalar multiplications per message and calls the forger
    once) is a claim to be checked by reading the definition `cdhSolver`, whose input type
    `G × G` visibly contains neither the key nor a discrete logarithm.  The equality
    `forge_eq_cdh` itself holds for arbitrary (also inefficient) forgers.

  Everything lives in the namespace `BlindPRF.Unforgeability`.
-/
import BlindPRF.Correctness
import BlindPRF.Prob

namespace BlindPRF

namespace Unforgeability

open scoped ENNReal

universe u v w x

/-! ## 0. General facts about uniform sampling (not specific to the protocol) -/

section General

variable {α : Type u} {ι : Type w} {γ : Type x}

/-- Overwriting one coordinate of a function: `(b, h) ↦ (h[i ↦ b], h i)` is a bijection (the
second component remembers the overwritten value). -/
def updateEquiv (α : Type u) {ι : Type w} [DecidableEq ι] (i : ι) :
    α × (ι → α) ≃ (ι → α) × α where
  toFun p := (Function.update p.2 i p.1, p.2 i)
  invFun q := (q.1 i, Function.update q.1 i q.2)
  left_inv p := by
    rcases p with ⟨b, h⟩
    simp
  right_inv q := by
    rcases q with ⟨h, c⟩
    simp

/-- Overwriting one coordinate of a uniformly random function with a fresh uniform value gives a
uniformly random function. -/
theorem unif_map_update [Fintype α] [Nonempty α] [Fintype ι] [DecidableEq ι] (i : ι) :
    (unif (α × (ι → α))).map (fun p => Function.update p.2 i p.1) = unif (ι → α) :=
  unif_map_of_equiv_prod (updateEquiv α i) _ (fun _ => rfl)

/-- The same fact for an experiment that continues: sampling `b` and `h` and continuing with
`h[i ↦ b]` is the same as sampling `h` and continuing with `h`.  ("Programming" one entry of a
uniformly random table with an independent uniform value is invisible.) -/
theorem unif_bind_update [Fintype α] [Nonempty α] [Fintype ι] [DecidableEq ι] (i : ι)
    (f : (ι → α) → PMF γ) :
    ((unif α).bind fun b => (unif (ι → α)).bind fun h => f (Function.update h i b)) =
      (unif (ι → α)).bind f := by
  rw [← unif_prod_bind (fun p : α × (ι → α) => f (Function.update p.2 i p.1)),
    ← unif_map_update i, PMF.bind_map]
  rfl

/-- An experiment that reads only one entry of a uniformly random table sees a uniform value. -/
theorem unif_bind_eval [Fintype α] [Nonempty α] [Fintype ι] [DecidableEq ι] (i : ι)
    (f : α → PMF γ) :
    ((unif (ι → α)).bind fun h => f (h i)) = (unif α).bind f := by
  refine (unif_bind_update i _).symm.trans ?_
  refine congrArg _ (funext fun b => ?_)
  simp only [Function.update_self]
  exact PMF.bind_const _ _

/-- The probability of an event under the uniform distribution is the number of favourable
outcomes divided by the number of outcomes. -/
theorem unif_map_decide_true [Fintype α] [Nonempty α] (p : α → Prop) [DecidablePred p] :
    ((unif α).map fun a => decide (p a)) true =
      (Fintype.card {a // p a} : ℝ≥0∞) / (Fintype.card α : ℝ≥0∞) := by
  rw [PMF.map_apply, tsum_fintype, Fintype.card_subtype, div_eq_mul_inv, ← nsmul_eq_mul,
    ← Finset.sum_const, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : p a <;> simp [h]

end General

variable {F : Type u} {G : Type v} {M : Type w}

/-! ## A. The experiments, the reduction, and the auxiliary adversaries -/

/-- What the forger is handed, as a triple of group-valued data:

1. the public key `k • g`,
2. the whole hash table `m ↦ H m` (group elements — NOT their discrete logarithms),
3. the table of signatures on every message except the target (a dummy `0` at the target).

There is no scalar in this type: the forger receives neither the key nor any oracle exponent. -/
abbrev ForgerInput (G : Type v) (M : Type w) : Type (max v w) := G × (M → G) × (M → G)

section Defs

variable [Field F] [AddCommGroup G] [Module F G]

/-- The eagerly sampled random oracle: the hash table determined by a table `h` of exponents,
`H m = h m • g`.  (For uniform `h` and a generator `g` this is a uniformly random function
`M → G`, see `roHash_uniform`.) -/
def roHash (g : G) (h : M → F) : M → G := fun m => h m • g

/-- The signatures the forger gets to see: the true signature `prf H k m = k • H m` on every
message `m` other than the target `mstar`, and the dummy value `0` at the target. -/
def knownSigs [DecidableEq M] (H : M → G) (k : F) (mstar : M) : M → G :=
  fun m => if m = mstar then 0 else prf H k m

/-- The forger obtained from a CDH solver `S` (used for the converse reduction `cdh_eq_forge`):
run the solver on the public key and the hash of the target; ignore everything else. -/
def forgerOfSolver (mstar : M) (S : G × G → PMF G) : ForgerInput G M → PMF G :=
  fun x => S (x.1, x.2.1 mstar)

/-- The forger for the LEAKY experiment `forgeExpLeaky`: given the oracle exponent `e = h mstar`
of the target and the public key `pk`, output `e • pk`.  One scalar multiplication. -/
noncomputable def leakForger : F × ForgerInput G M → PMF G :=
  fun x => PMF.pure (x.1 • x.2.1)

variable (F)

/-- An UNBOUNDED forger: take a discrete logarithm `c` of the public key (any scalar with
`c • g = pk`, obtained by classical choice — there is no algorithm here) and output `c • H mstar`.
It exists as a Lean function, which is why unforgeability cannot be a theorem about all
functions. -/
noncomputable def dlogForger (g : G) (mstar : M) : ForgerInput G M → PMF G :=
  fun x => PMF.pure ((Classical.epsilon fun c : F => c • g = x.1) • x.2.1 mstar)

variable [Fintype F] [DecidableEq G] [Fintype M] [DecidableEq M]

/-- **The forgery experiment** (selective target, known messages, random oracle).

The target message `mstar` is fixed in advance.  Sample a key `k : F` and a table of oracle
exponents `h : M → F` uniformly; let `H = roHash g h` be the hash table.  Hand the forger the
public key `k • g`, the whole table `H` and the signatures on all messages other than `mstar`.
The result is `true` iff the forger outputs the signature `prf H k mstar` on the target, i.e. iff
`verifyWithKey H k mstar σ` holds for its output `σ`. -/
noncomputable def forgeExp (g : G) (mstar : M) (Adv : ForgerInput G M → PMF G) : PMF Bool :=
  (unif F).bind fun k => (unif (M → F)).bind fun h =>
    (Adv (k • g, roHash g h, knownSigs (roHash g h) k mstar)).map
      fun σ => decide (σ = prf (roHash g h) k mstar)

/-- **The CDH experiment** over the group generated by `g`: sample `a, b : F` uniformly, hand the
solver the pair `(a • g, b • g)`; the result is `true` iff it outputs `(a * b) • g`. -/
noncomputable def cdhExp (g : G) (S : G × G → PMF G) : PMF Bool :=
  (unif (F × F)).bind fun ab =>
    (S (ab.1 • g, ab.2 • g)).map fun Z => decide (Z = (ab.1 * ab.2) • g)

/-- **The reduction**: the CDH solver built from a forger `Adv`.  Input: `AB = (A, B)`, to be
thought of as `(a • g, b • g)`.  Sample a table of exponents `h : M → F` and run the forger on

* public key `A` (so the unknown key is `a`),
* hash table `m ↦ h m • g` for `m ≠ mstar`, with `B` PLANTED as the hash of the target,
* signatures `m ↦ h m • A` for `m ≠ mstar` (correct, since `a • (h m • g) = h m • (a • g)`).

The forger's output is the solver's output.  The inputs are group elements only; the forger is
used as a black box, once; the work besides is two scalar multiplications per message other
than the target.  That this is "efficient" is by inspection, not a theorem.  (The sampled value
`h mstar` is not used.) -/
noncomputable def cdhSolver (g : G) (mstar : M) (Adv : ForgerInput G M → PMF G) :
    G × G → PMF G := fun AB =>
  (unif (M → F)).bind fun h =>
    Adv (AB.1, (fun m => if m = mstar then AB.2 else h m • g),
      (fun m => if m = mstar then 0 else h m • AB.1))

/-- **The leaky forgery experiment** (used only to show that the real experiment has teeth):
exactly `forgeExp`, except that the forger is additionally handed the oracle EXPONENT `h mstar`
of the target, i.e. the discrete logarithm of `H mstar`. -/
noncomputable def forgeExpLeaky (g : G) (mstar : M) (Adv : F × ForgerInput G M → PMF G) :
    PMF Bool :=
  (unif F).bind fun k => (unif (M → F)).bind fun h =>
    (Adv (h mstar, k • g, roHash g h, knownSigs (roHash g h) k mstar)).map
      fun σ => decide (σ = prf (roHash g h) k mstar)

/-- **The honest-but-curious experiment.**  Party A follows the protocol: it runs `n` honest
sessions with B on the messages `ms 0, …, ms (n-1)` (fixed in advance; repetitions allowed) with
independent uniform nonzero blinding coins `r i`.  Afterwards the adversary `AdvA` is handed the
public key, the whole hash table and A's COMPLETE view `viewA` of every session (message, coin and
B's reply), and outputs a candidate signature on the target `mstar`.  The result is `true` iff
the candidate is `prf H k mstar`. -/
noncomputable def hbcExp [DecidableEq F] (g : G) (mstar : M) {n : ℕ} (ms : Fin n → M)
    (AdvA : G × (M → G) × (Fin n → M × Fˣ × G) → PMF G) : PMF Bool :=
  (unif F).bind fun k => (unif (M → F)).bind fun h =>
    (unif (Fin n → Fˣ)).bind fun r : Fin n → Fˣ =>
      (AdvA (k • g, roHash g h, fun i => viewA (roHash g h) k (ms i) (r i))).map
        fun σ => decide (σ = prf (roHash g h) k mstar)

/-- The forger that simulates the honest-but-curious party A: it samples the blinding coins
itself and computes each session's view from the signature table it was handed (B's reply in
session `i` is `r i • (signature on ms i)`). -/
noncomputable def forgerOfHbc [DecidableEq F] {n : ℕ} (ms : Fin n → M)
    (AdvA : G × (M → G) × (Fin n → M × Fˣ × G) → PMF G) : ForgerInput G M → PMF G :=
  fun x => (unif (Fin n → Fˣ)).bind fun r : Fin n → Fˣ =>
    AdvA (x.1, x.2.1, fun i => (ms i, r i, ((r i : Fˣ) : F) • x.2.2 (ms i)))

end Defs

/-! ## B. Sanity of the definitions -/

section Sanity

variable [Field F] [AddCommGroup G] [Module F G]

/-- The oracle's value at `m` is the `h m`-th multiple of the base point. -/
@[simp]
theorem roHash_apply (g : G) (h : M → F) (m : M) : roHash g h m = h m • g := rfl

/-- At the target the forger sees only the dummy value. -/
@[simp]
theorem knownSigs_self [DecidableEq M] (H : M → G) (k : F) (mstar : M) :
    knownSigs H k mstar mstar = 0 := by
  simp [knownSigs]

/-- Away from the target the forger sees the true signature. -/
theorem knownSigs_of_ne [DecidableEq M] (H : M → G) (k : F) {m mstar : M} (hm : m ≠ mstar) :
    knownSigs H k mstar m = prf H k m := by
  simp [knownSigs, hm]

/-- The output of every honest protocol run on a message other than the target is an entry of
the table the forger is handed. -/
theorem run_eq_knownSigs [DecidableEq M] (H : M → G) (k : F) {m mstar : M} (hm : m ≠ mstar)
    (r : Fˣ) : run H k m r = knownSigs H k mstar m := by
  rw [correctness, knownSigs_of_ne H k hm]

/-- **The forger's input covers an honest-but-curious party A.**  Everything A sees in an honest
protocol session on a message `m` other than the target — its message, its blinding coin `r` and
B's reply — is computed from `m`, `r` and the entry `knownSigs H k mstar m` of the forger's
input: B's reply is `r • (k • H m)`.

This says nothing about a party A that deviates from the protocol (sends B something other than
`r • H m`): B's reply to an arbitrary group element is NOT a function of the forger's input. -/
theorem viewA_eq_of_knownSigs [DecidableEq M] (H : M → G) (k : F) {m mstar : M}
    (hm : m ≠ mstar) (r : Fˣ) :
    viewA H k m r = (m, r, (r : F) • knownSigs H k mstar m) := by
  rw [knownSigs_of_ne H k hm]
  simp only [viewA, evaluate, blind, prf]
  rw [smul_comm]

/-- Discrete logarithms with respect to a nonzero element are unique. -/
theorem smul_left_injective_of_ne_zero {g : G} (hg0 : g ≠ 0) :
    Function.Injective fun c : F => c • g := by
  intro c c' h
  have h0 : (c - c') • g = 0 := by
    rw [sub_smul]
    exact sub_eq_zero.mpr h
  rcases smul_eq_zero.mp h0 with h1 | h1
  · exact sub_eq_zero.mp h1
  · exact absurd h1 hg0

/-- **The oracle is a uniformly random function.**  If `g` generates the group, the hash table
`roHash g h` for uniform exponents `h` is uniformly distributed over ALL functions `M → G`.
(This justifies calling `roHash` a random oracle; it says nothing about any concrete hash
function.) -/
theorem roHash_uniform [Fintype F] [Fintype G] [Fintype M] [DecidableEq M] {g : G}
    (hg : IsGenerator F g) : (unif (M → F)).map (roHash g) = unif (M → G) :=
  unif_map_equiv (Equiv.piCongrRight fun _ : M => hg.equiv)

/-- The leaky experiment with a forger that ignores the leak is the forgery experiment. -/
theorem forgeExpLeaky_ignore [Fintype F] [DecidableEq G] [Fintype M] [DecidableEq M] (g : G)
    (mstar : M) (Adv : ForgerInput G M → PMF G) :
    forgeExpLeaky F g mstar (fun x => Adv x.2) = forgeExp F g mstar Adv :=
  rfl

end Sanity

/-! ## C. The reduction: forging = solving CDH -/

section Reduction

variable [Field F] [Fintype F] [AddCommGroup G] [Module F G] [DecidableEq G]
  [Fintype M] [DecidableEq M]

/-- **Forging is solving CDH (exact reduction).**  For every group element `g`, every target
message `mstar` and EVERY forger `Adv` (any function, randomised or not), the forgery experiment
with `Adv` and the CDH experiment with the explicit solver `cdhSolver F g mstar Adv` are the
SAME distribution on `Bool`.  In particular the forger's winning probability equals the solver's
success probability (`forge_winProb_eq_cdh`); there is no loss.

Meaning: a forger who sees the public key, the entire random-oracle table and the signatures on
all messages other than a target fixed in advance — in particular an honest-but-curious party A
after any number of protocol runs on other messages (made precise in `hbc_eq_cdh`) — and then
produces the signature on the target, yields, by the visible construction `cdhSolver`, a solver
for the Computational Diffie–Hellman problem in the group generated by `g`.

What this does NOT claim:

* It does not say that forging is hard, nor that any probability is small.  CDH is an
  assumption, not proved and not assumed here; and an unbounded forger wins with certainty
  (`exists_forger_wins`).
* The forger is PASSIVE (known-message attack): it cannot have B evaluate group elements of its
  choice.  Against a party A that deviates from the protocol the relevant notion is one-more
  unforgeability, which rests on the one-more Diffie–Hellman assumption and is neither proved
  nor reduced here.
* The target `mstar` is selective (fixed before key and oracle are sampled), and the random
  oracle is an eagerly sampled table on a finite message space.
* Efficiency of `cdhSolver` (one call to `Adv`, two scalar multiplications per message, no
  access to any exponent of the CDH instance) is by inspection of its definition; Lean has no
  cost model here. -/
theorem forge_eq_cdh (g : G) (mstar : M) (Adv : ForgerInput G M → PMF G) :
    forgeExp F g mstar Adv = cdhExp F g (cdhSolver F g mstar Adv) := by
  unfold forgeExp cdhExp cdhSolver
  rw [unif_prod_bind]
  refine congrArg _ (funext fun a => ?_)
  -- the oracle exponent of the target plays the role of the CDH exponent `b`
  refine (unif_bind_update mstar _).symm.trans ?_
  refine congrArg _ (funext fun b => ?_)
  rw [PMF.map_bind]
  refine congrArg _ (funext fun h => ?_)
  have e1 : roHash g (Function.update h mstar b) =
      fun m => if m = mstar then b • g else h m • g := by
    funext m
    by_cases hm : m = mstar
    · subst hm
      simp [roHash]
    · simp [roHash, hm]
  have e2 : knownSigs (roHash g (Function.update h mstar b)) a mstar =
      fun m => if m = mstar then 0 else h m • a • g := by
    funext m
    by_cases hm : m = mstar
    · simp [knownSigs, hm]
    · simp only [knownSigs, prf, roHash, hm, ↓reduceIte, ne_eq, not_false_eq_true,
        Function.update_of_ne]
      exact smul_comm _ _ _
  have e3 : prf (roHash g (Function.update h mstar b)) a mstar = (a * b) • g := by
    simp [prf, roHash, mul_smul]
  rw [e2, e3, e1]

/-- The forger's winning probability IS the success probability of the explicit CDH solver.
(Same caveats as `forge_eq_cdh`: this is a reduction, not a hardness statement.) -/
theorem forge_winProb_eq_cdh (g : G) (mstar : M) (Adv : ForgerInput G M → PMF G) :
    forgeExp F g mstar Adv true = cdhExp F g (cdhSolver F g mstar Adv) true := by
  rw [forge_eq_cdh]

/-- **Converse reduction: a CDH solver forges.**  For every CDH solver `S`, the forger
`forgerOfSolver mstar S` (run `S` on the public key and the hash of the target) wins the forgery
experiment with exactly the success probability of `S`.

Together with `forge_eq_cdh`: in this model, forging a signature on a fixed target is neither
easier nor harder than CDH in the group generated by `g`.  Like `forge_eq_cdh` this is an
equality of experiments and says nothing about whether either probability is small. -/
theorem cdh_eq_forge (g : G) (mstar : M) (S : G × G → PMF G) :
    cdhExp F g S = forgeExp F g mstar (forgerOfSolver mstar S) := by
  unfold cdhExp forgeExp forgerOfSolver
  rw [unif_prod_bind]
  refine congrArg _ (funext fun a => ?_)
  refine (unif_bind_eval mstar
    (fun b => (S (a • g, b • g)).map fun Z => decide (Z = (a * b) • g))).symm.trans ?_
  refine congrArg _ (funext fun h => ?_)
  show (S (a • g, h mstar • g)).map (fun Z => decide (Z = (a * h mstar) • g)) =
    (S (a • g, h mstar • g)).map (fun σ => decide (σ = a • h mstar • g))
  rw [mul_smul]

end Reduction

/-! ## D. The honest-but-curious party A is a passive forger -/

section HonestButCurious

variable [Field F] [Fintype F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
  [Fintype M] [DecidableEq M]

/-- **An honest-but-curious A is a passive forger (exact).**  If none of the messages A runs the
protocol on is the target, the honest-but-curious experiment with adversary `AdvA` is the SAME
distribution as the forgery experiment with the explicit forger `forgerOfHbc F ms AdvA`, which
recomputes A's views from the signature table.

Meaning: running the blind protocol honestly, any number of times, on messages other than the
target gives A nothing beyond the signatures on those messages — its complete views (including
its own blinding coins and B's replies) are simulated from them.

What this does NOT claim: nothing about an A that deviates from the protocol (e.g. sends B a
group element that is not `r • H m`; that is the one-more Diffie–Hellman setting, not treated);
the session messages are fixed in advance rather than chosen adaptively; and it is an equality
of experiments, not a statement that any probability is small. -/
theorem hbc_eq_forge (g : G) (mstar : M) {n : ℕ} (ms : Fin n → M) (hms : ∀ i, ms i ≠ mstar)
    (AdvA : G × (M → G) × (Fin n → M × Fˣ × G) → PMF G) :
    hbcExp F g mstar ms AdvA = forgeExp F g mstar (forgerOfHbc F ms AdvA) := by
  unfold hbcExp forgeExp forgerOfHbc
  refine congrArg _ (funext fun k => congrArg _ (funext fun h => ?_))
  rw [PMF.map_bind]
  refine congrArg _ (funext fun r => ?_)
  have hview : (fun i => viewA (roHash g h) k (ms i) (r i)) =
      fun i => (ms i, r i, ((r i : Fˣ) : F) • knownSigs (roHash g h) k mstar (ms i)) :=
    funext fun i => viewA_eq_of_knownSigs (roHash g h) k (hms i) (r i)
  rw [hview]

/-- **Forging after honest protocol runs is solving CDH (exact reduction).**  The success
probability of an honest-but-curious party A — who ran `n` honest sessions on messages other than
the target and then tries to produce the signature on the target — is exactly the success
probability of the explicit CDH solver `cdhSolver F g mstar (forgerOfHbc F ms AdvA)`.

Same caveats as `forge_eq_cdh` and `hbc_eq_forge`: a reduction only (CDH is an assumption and is
not proved or assumed); A is honest-but-curious, the one-more Diffie–Hellman setting of a
deviating A is not covered; selective target; eagerly sampled random oracle on a finite message
space; efficiency of the solver is by inspection. -/
theorem hbc_eq_cdh (g : G) (mstar : M) {n : ℕ} (ms : Fin n → M) (hms : ∀ i, ms i ≠ mstar)
    (AdvA : G × (M → G) × (Fin n → M × Fˣ × G) → PMF G) :
    hbcExp F g mstar ms AdvA =
      cdhExp F g (cdhSolver F g mstar (forgerOfHbc F ms AdvA)) := by
  rw [hbc_eq_forge g mstar ms hms, forge_eq_cdh]

end HonestButCurious

/-! ## E. S1 — an unbounded forger wins: the property can only be computational -/

section Unbounded

variable [Field F] [Fintype F] [AddCommGroup G] [Module F G] [DecidableEq G]
  [Fintype M] [DecidableEq M]

/-- The discrete-logarithm forger wins the forgery experiment with certainty, for every `g`
(generator or not) and every target.  It is not an algorithm: it "computes" a discrete logarithm
of the public key by classical choice. -/
theorem forgeExp_dlogForger (g : G) (mstar : M) :
    forgeExp F g mstar (dlogForger F g mstar) = PMF.pure true := by
  have key : ∀ (k : F) (h : M → F),
      (dlogForger F g mstar (k • g, roHash g h, knownSigs (roHash g h) k mstar)).map
        (fun σ => decide (σ = prf (roHash g h) k mstar)) = PMF.pure true := by
    intro k h
    have hc : (Classical.epsilon fun c : F => c • g = k • g) • g = k • g :=
      Classical.epsilon_spec (p := fun c : F => c • g = k • g) ⟨k, rfl⟩
    have hσ : (Classical.epsilon fun c : F => c • g = k • g) • roHash g h mstar =
        prf (roHash g h) k mstar := by
      simp only [roHash, prf]
      rw [smul_comm, hc, smul_comm]
    show (PMF.pure _).map _ = _
    rw [PMF.pure_map]
    exact congrArg PMF.pure (decide_eq_true hσ)
  simp only [forgeExp, key, PMF.bind_const]

/-- **S1. Unforgeability against unbounded forgers is false.**  There is a forger (a Lean
function) that wins the forgery experiment with probability `1`.  Hence `forge_eq_cdh` can only
be about computational hardness, and a theorem "for all forgers the winning probability is
small" would be false; none is stated.  No generator hypothesis is needed.

This does NOT say that an efficient forger exists: the witness `dlogForger` takes a discrete
logarithm by classical choice.  Whether a feasible forger exists is exactly the CDH question. -/
theorem exists_forger_wins (g : G) (mstar : M) :
    ∃ Adv : ForgerInput G M → PMF G, forgeExp F g mstar Adv = PMF.pure true :=
  ⟨dlogForger F g mstar, forgeExp_dlogForger g mstar⟩

/-- Consequently CDH is solved with certainty by an unbounded solver (the image of the
discrete-log forger under the reduction): CDH hardness, too, is computational only. -/
theorem exists_cdhSolver_wins (g : G) :
    ∃ S : G × G → PMF G, cdhExp F g S = PMF.pure true :=
  ⟨cdhSolver F g () (dlogForger F g ()), by
    rw [← forge_eq_cdh (M := Unit), forgeExp_dlogForger]⟩

end Unbounded

/-! ## F. S2 — the experiment is not trivially winnable -/

section Counting

variable [Field F] [Fintype F] [DecidableEq F]

/-- A nonzero scalar `c` has exactly `|F| - 1` factorisations `c = a * b`. -/
theorem card_mul_eq_of_ne_zero {c : F} (hc : c ≠ 0) :
    Fintype.card {ab : F × F // ab.1 * ab.2 = c} = Fintype.card F - 1 := by
  rw [← Fintype.card_units]
  refine (Fintype.card_congr ?_).symm
  exact
    { toFun := fun u => ⟨((u : F), (u : F)⁻¹ * c), mul_inv_cancel_left₀ u.ne_zero c⟩
      invFun := fun ab =>
        Units.mk0 ab.1.1 (fun h0 => hc (by rw [← ab.2, h0, zero_mul]))
      left_inv := fun u => Units.ext rfl
      right_inv := by
        rintro ⟨⟨a, b⟩, hab⟩
        subst hab
        have ha : a ≠ 0 := left_ne_zero_of_mul hc
        exact Subtype.ext (Prod.ext rfl (inv_mul_cancel_left₀ ha b)) }

/-- Zero has exactly `2|F| - 1` factorisations `0 = a * b`. -/
theorem card_mul_eq_zero :
    Fintype.card {ab : F × F // ab.1 * ab.2 = 0} = 2 * Fintype.card F - 1 := by
  have e : F ⊕ Fˣ ≃ {ab : F × F // ab.1 * ab.2 = 0} :=
    Equiv.ofBijective
      (Sum.elim (fun b => ⟨(0, b), zero_mul b⟩) (fun u => ⟨((u : F), 0), mul_zero _⟩))
      ⟨by
        rintro (b | u) (b' | u') h
        · exact congrArg Sum.inl (congrArg (fun z : {ab : F × F // ab.1 * ab.2 = 0} => z.1.2) h)
        · exact absurd (congrArg (fun z : {ab : F × F // ab.1 * ab.2 = 0} => z.1.1) h).symm
            u'.ne_zero
        · exact absurd (congrArg (fun z : {ab : F × F // ab.1 * ab.2 = 0} => z.1.1) h) u.ne_zero
        · exact congrArg Sum.inr
            (Units.ext (congrArg (fun z : {ab : F × F // ab.1 * ab.2 = 0} => z.1.1) h)),
       by
        rintro ⟨⟨a, b⟩, hab⟩
        by_cases ha : a = 0
        · subst ha
          exact ⟨Sum.inl b, rfl⟩
        · have hb : b = 0 := (mul_eq_zero.mp hab).resolve_left ha
          subst hb
          exact ⟨Sum.inr (Units.mk0 a ha), rfl⟩⟩
  rw [← Fintype.card_congr e, Fintype.card_sum, Fintype.card_units]
  have hpos : 0 < Fintype.card F := Fintype.card_pos
  omega

end Counting

section Constant

variable [Field F] [Fintype F] [AddCommGroup G] [Module F G] [DecidableEq G]
  [Fintype M] [DecidableEq M]

/-- The forgery experiment for a forger that ignores its input and outputs the constant `σ₀`:
it wins iff `σ₀ = (a * b) • g` for two independent uniform scalars (the key and the oracle
exponent of the target). -/
theorem forgeExp_const (g : G) (mstar : M) (σ₀ : G) :
    forgeExp F g mstar (fun _ => PMF.pure σ₀) =
      (unif (F × F)).map fun ab => decide (σ₀ = (ab.1 * ab.2) • g) := by
  rw [← PMF.bind_pure_comp, unif_prod_bind]
  unfold forgeExp
  refine congrArg _ (funext fun a => ?_)
  refine Eq.trans ?_ (unif_bind_eval mstar
    (fun b => PMF.pure (decide (σ₀ = (a * b) • g))))
  refine congrArg _ (funext fun h => ?_)
  show (PMF.pure σ₀).map (fun σ => decide (σ = a • h mstar • g)) =
    PMF.pure (decide (σ₀ = (a * h mstar) • g))
  rw [PMF.pure_map, mul_smul]

/-- The winning probability of the constant forger as a ratio of cardinalities. -/
theorem forgeExp_const_apply_true (g : G) (mstar : M) (σ₀ : G) :
    forgeExp F g mstar (fun _ => PMF.pure σ₀) true =
      (Fintype.card {ab : F × F // σ₀ = (ab.1 * ab.2) • g} : ℝ≥0∞) /
        (Fintype.card F : ℝ≥0∞) ^ 2 := by
  rw [forgeExp_const, unif_map_decide_true, Fintype.card_prod, Nat.cast_mul, sq]

/-- **S2, exact value, nonzero constant in the span of `g`.**  If `g ≠ 0` and `c ≠ 0`, the
forger that always outputs `c • g` wins with probability exactly `(|F| - 1) / |F|²` (it wins iff
key times oracle exponent of the target equals `c`).  One trivial forger; no bound for others. -/
theorem forgeExp_const_smul {g : G} (hg0 : g ≠ 0) (mstar : M) {c : F} (hc : c ≠ 0) :
    forgeExp F g mstar (fun _ => PMF.pure (c • g)) true =
      ((Fintype.card F - 1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ^ 2 := by
  classical
  rw [forgeExp_const_apply_true, ← card_mul_eq_of_ne_zero hc]
  congr 2
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun ab => by
    rw [(smul_left_injective_of_ne_zero hg0).eq_iff, eq_comm])

/-- **S2, exact value, nonzero constant.**  If `g` generates the group, a forger that ignores
its input and always outputs a fixed element `σ₀ ≠ 0` wins the forgery experiment with
probability exactly `(|F| - 1) / |F|²` (NOT `1 / |F|`: the product of the key and the oracle
exponent is not uniform, it is `0` too often).  This is a statement about ONE trivial forger; it
is not a bound for other forgers. -/
theorem forgeExp_const_of_ne_zero {g : G} (hg : IsGenerator F g) (mstar : M) {σ₀ : G}
    (hσ : σ₀ ≠ 0) :
    forgeExp F g mstar (fun _ => PMF.pure σ₀) true =
      ((Fintype.card F - 1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ^ 2 := by
  obtain ⟨c, rfl⟩ := hg.spans σ₀
  have hc : c ≠ 0 := by
    rintro rfl
    exact hσ (zero_smul F g)
  exact forgeExp_const_smul hg.ne_zero mstar hc

/-- **S2, exact value, constant zero.**  If `g ≠ 0`, the forger that always outputs `0` wins
with probability exactly `(2|F| - 1) / |F|²` (it wins iff the key or the oracle exponent of the
target is `0`).  One trivial forger; no bound for others. -/
theorem forgeExp_const_zero {g : G} (hg0 : g ≠ 0) (mstar : M) :
    forgeExp F g mstar (fun _ => PMF.pure 0) true =
      ((2 * Fintype.card F - 1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ^ 2 := by
  classical
  rw [forgeExp_const_apply_true, ← card_mul_eq_zero (F := F)]
  congr 2
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun ab => by
    rw [eq_comm, smul_eq_zero, or_iff_left hg0])

/-- **S2, uniform bound for constant forgers.**  If `g ≠ 0`, a forger that ignores its input and
outputs any fixed group element `σ₀` (zero, nonzero, or not even a multiple of `g`) wins with
probability at most `2 / |F|`.  This bounds the constant forgers only; it is NOT a bound for
forgers that use their input (no such bound can hold for all functions, see
`exists_forger_wins`). -/
theorem forgeExp_const_le {g : G} (hg0 : g ≠ 0) (mstar : M) (σ₀ : G) :
    forgeExp F g mstar (fun _ => PMF.pure σ₀) true ≤ 2 / (Fintype.card F : ℝ≥0∞) := by
  have hq0 : (Fintype.card F : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hqt : (Fintype.card F : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  -- it suffices to bound the number of favourable pairs `(key, exponent)` by `2|F|`
  have key : ∀ n : ℕ, n ≤ 2 * Fintype.card F →
      (n : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ^ 2 ≤ 2 / (Fintype.card F : ℝ≥0∞) := by
    intro n hn
    refine ENNReal.div_le_of_le_mul ?_
    rw [sq, ← mul_assoc, ENNReal.div_mul_cancel hq0 hqt]
    exact_mod_cast hn
  by_cases hspan : ∃ c : F, c • g = σ₀
  · obtain ⟨c, rfl⟩ := hspan
    by_cases hc : c = 0
    · subst hc
      rw [zero_smul, forgeExp_const_zero hg0]
      exact key _ (by omega)
    · rw [forgeExp_const_smul hg0 mstar hc]
      exact key _ (by omega)
  · rw [forgeExp_const_apply_true]
    have hempty : IsEmpty {ab : F × F // σ₀ = (ab.1 * ab.2) • g} :=
      ⟨fun ab => hspan ⟨_, ab.2.symm⟩⟩
    rw [Fintype.card_eq_zero]
    simp

/-- **S2. The experiment is not trivially winnable.**  If `g ≠ 0`, a forger that ignores its
input and outputs any fixed group element wins with probability strictly less than `1`.  (For
`g = 0` the whole group generated by `g` is trivial and the constant `0` wins, see
`forgeExp_const_zero_gen`.)  This is about constant forgers only. -/
theorem forgeExp_const_lt_one {g : G} (hg0 : g ≠ 0) (mstar : M) (σ₀ : G) :
    forgeExp F g mstar (fun _ => PMF.pure σ₀) true < 1 := by
  rw [forgeExp_const, unif_map_decide_true]
  have hlt : Fintype.card {ab : F × F // σ₀ = (ab.1 * ab.2) • g} < Fintype.card (F × F) := by
    by_cases hσ : σ₀ = 0
    · refine Fintype.card_subtype_lt (x := ((1 : F), (1 : F))) ?_
      simpa [hσ] using hg0.symm
    · refine Fintype.card_subtype_lt (x := ((0 : F), (0 : F))) ?_
      simpa using hσ
  refine (ENNReal.div_lt_iff (Or.inl ?_) (Or.inl (ENNReal.natCast_ne_top _))).mpr ?_
  · exact_mod_cast Fintype.card_ne_zero
  · rw [one_mul]
    exact_mod_cast hlt

/-- In particular the constant forger's experiment is not the "always wins" distribution. -/
theorem forgeExp_const_ne_pure_true {g : G} (hg0 : g ≠ 0) (mstar : M) (σ₀ : G) :
    forgeExp F g mstar (fun _ => PMF.pure σ₀) ≠ PMF.pure true := by
  intro h
  have hlt := forgeExp_const_lt_one (F := F) hg0 mstar σ₀
  rw [h, PMF.pure_apply_self] at hlt
  exact lt_irrefl _ hlt

/-- The hypothesis `g ≠ 0` in `forgeExp_const_lt_one` is necessary: over the trivial base point
every signature is `0` and the constant forger `0` always wins. -/
theorem forgeExp_const_zero_gen (mstar : M) :
    forgeExp F (0 : G) mstar (fun _ => PMF.pure 0) = PMF.pure true := by
  rw [forgeExp_const]
  simp only [smul_zero, decide_true]
  exact PMF.map_const _ _

end Constant

/-! ## G. S3 — teeth: leaking the oracle exponent of the target breaks the scheme -/

section Leaky

variable [Field F] [Fintype F] [AddCommGroup G] [Module F G] [DecidableEq G]
  [Fintype M] [DecidableEq M]

/-- **S3. With the oracle exponent of the target, forging is trivial.**  In the leaky experiment,
where the forger is additionally handed `h mstar` (the discrete logarithm of `H mstar`), the
explicit forger `leakForger`, which outputs `h mstar • pk` (one scalar multiplication), wins with
certainty.

Meaning: the forgery experiment genuinely distinguishes a hash function with KNOWN discrete
logarithms (e.g. `H m = h(m) • g` for a public `h` — insecure) from a proper hash-to-group; it
matters that `ForgerInput` contains the hash table as group elements only.  This is also exactly
the trapdoor the reduction `cdhSolver` uses for the messages other than the target.

It does not claim anything about the non-leaky experiment `forgeExp`. -/
theorem forgeExpLeaky_leakForger (g : G) (mstar : M) :
    forgeExpLeaky F g mstar leakForger = PMF.pure true := by
  have key : ∀ (k : F) (h : M → F),
      (leakForger (h mstar, k • g, roHash g h, knownSigs (roHash g h) k mstar)).map
        (fun σ => decide (σ = prf (roHash g h) k mstar)) = PMF.pure true := by
    intro k h
    have hσ : h mstar • k • g = prf (roHash g h) k mstar := by
      simp only [roHash, prf]
      rw [smul_comm]
    show (PMF.pure _).map _ = _
    rw [PMF.pure_map]
    exact congrArg PMF.pure (decide_eq_true hσ)
  simp only [forgeExpLeaky, key, PMF.bind_const]

/-- There is a forger that wins the leaky experiment with certainty (namely `leakForger`). -/
theorem exists_leaky_forger_wins (g : G) (mstar : M) :
    ∃ Adv : F × ForgerInput G M → PMF G, forgeExpLeaky F g mstar Adv = PMF.pure true :=
  ⟨leakForger, forgeExpLeaky_leakForger g mstar⟩

end Leaky

/-! ## H. Non-vacuity: a model of all hypotheses -/

section NonVacuity

variable (p : ℕ) [Fact p.Prime]

/-- A model of the algebraic setting: `F = G = ZMod p` with generator `g = 1`.  All typeclass
hypotheses used in this file hold in it, so no theorem above is vacuous.  (This model is NOT a
secure group: see `forgeExp_zmod_mulForger`.) -/
theorem isGenerator_zmod_one : IsGenerator (ZMod p) (1 : ZMod p) :=
  ⟨one_ne_zero, fun x => ⟨x, by simp⟩⟩

/-- The reduction, instantiated in the model (two messages, target `true`). -/
example (Adv : ForgerInput (ZMod p) Bool → PMF (ZMod p)) :
    forgeExp (ZMod p) (1 : ZMod p) true Adv =
      cdhExp (ZMod p) (1 : ZMod p) (cdhSolver (ZMod p) (1 : ZMod p) true Adv) :=
  forge_eq_cdh _ _ _

/-- The exact value of S2, instantiated in the model. -/
example (σ₀ : ZMod p) (hσ : σ₀ ≠ 0) :
    forgeExp (ZMod p) (1 : ZMod p) true (fun _ : ForgerInput (ZMod p) Bool => PMF.pure σ₀) true =
      ((Fintype.card (ZMod p) - 1 : ℕ) : ℝ≥0∞) / (Fintype.card (ZMod p) : ℝ≥0∞) ^ 2 :=
  forgeExp_const_of_ne_zero (isGenerator_zmod_one p) true hσ

/-- **Hardness is a property of the concrete group, not of the algebraic setting.**  In the model
`F = G = ZMod p`, `g = 1` (the additive group of the field, where "scalar multiplication" is
field multiplication and CDH is easy), the EFFICIENT forger `σ = pk * H mstar` wins the forgery
experiment with certainty.  So no theorem valid for all `F`-modules `G` can assert that forging
is hard; only reductions such as `forge_eq_cdh` are available at this level of generality. -/
theorem forgeExp_zmod_mulForger [Fintype M] [DecidableEq M] (mstar : M) :
    forgeExp (ZMod p) (1 : ZMod p) mstar
      (fun x : ForgerInput (ZMod p) M => PMF.pure (x.1 * x.2.1 mstar)) = PMF.pure true := by
  have key : ∀ (k : ZMod p) (h : M → ZMod p),
      (PMF.pure ((k • (1 : ZMod p)) * roHash (1 : ZMod p) h mstar)).map
        (fun σ => decide (σ = prf (roHash (1 : ZMod p) h) k mstar)) = PMF.pure true := by
    intro k h
    rw [PMF.pure_map]
    refine congrArg PMF.pure (decide_eq_true ?_)
    simp [prf, roHash]
  simp only [forgeExp, key, PMF.bind_const]

end NonVacuity

end Unforgeability

end BlindPRF
