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
       the auxiliary adversaries/experiments used in the later sections.  The deterministic parts
       of the reductions and simulators are separate, named definitions (`cdhSolverInput`,
       `solverInput`, `hbcSimInput`, `wireSim`, `leakCore`) so that they can be audited on their
       own: `#print axioms` reports no `Classical.choice` for any of them (a check that can be
       enforced by listing them under the choice-free audit of `Audit.lean`).  The randomised
       wrappers only add uniform sampling; they depend on `Classical.choice` through Mathlib's
       `PMF`, so the audit has to be applied to the cores.  The unbounded adversaries
       `dlogForger` and `dlogForgerOfLeaky` DO use classical choice, on purpose.
  * B. Sanity of the definitions: the oracle is a uniformly random function when `g` generates
       the group, and `forgeExp` then IS the experiment with a hash function drawn uniformly from
       all functions `M → G` (`forgeExp_eq_unifRO`); everything party A sees in an honest
       protocol run on a message other than the target is computable from the forger's input.
  * C. `forge_eq_cdh` (forger ⟹ CDH solver, exact) and the converse `cdh_eq_forge`
       (CDH solver ⟹ forger, exact).
  * D. Passive adversaries are forgers.  (1) The honest-but-curious party A: the experiment
       `hbcExp`, in which A first runs `n` honest protocol sessions on messages other than the
       target and sees its complete views, IS a forgery experiment (`hbc_eq_forge`) and hence a
       CDH experiment (`hbc_eq_cdh`); the restriction to messages other than the target is
       necessary (`hbcExp_target_wins`).  (2) The wire eavesdropper: the experiment
       `eavesdropExp`, in which the adversary additionally sees the wire transcripts `(a, b)` of
       honest sessions of OTHER parties on arbitrary messages — the target included — IS a
       forgery experiment (`eavesdrop_eq_forge`, `eavesdrop_eq_cdh`).  (3) Both at once:
       `passiveExp`, `passive_eq_forge`, `passive_eq_cdh`.
  * E. S1: an unbounded forger (`dlogForger`, takes a discrete logarithm) wins with certainty.
  * F. S2: the experiment is not trivially winnable: a forger that outputs a constant wins with
       probability exactly `(|F| - 1) / |F|²` (constant `≠ 0`, `g` a generator) or
       `(2|F| - 1) / |F|²` (constant `0`, `g ≠ 0`); in particular at most `2 / |F|` and strictly
       less than `1`.  The forgers that copy one entry of their input (the public key, the hash
       of the target, the dummy, a known signature) win, for `g ≠ 0`, with probability exactly
       `(2|F| - 1) / |F|²`.  (These are statements about these particular forgers only.)
  * G. S3: if the forger is additionally handed the oracle EXPONENT `h m*` of the target, one
       scalar multiplication — no classical choice — wins with certainty
       (`forgeExpLeaky_leakForger`).  Formally the leak adds nothing: every leaky forger is
       matched by a non-leaky one (`exists_forger_of_leaky`; for `g ≠ 0` it takes a discrete
       logarithm).  So the difference between `forgeExp` and `forgeExpLeaky` is COMPUTATIONAL
       ONLY and is not a theorem of this file; what the file shows is which forger needs
       classical choice.
  * H. Non-vacuity: a model of all hypotheses (`F = G = ZMod p`, `g = 1`) — in which, by the way,
       CDH is easy and an efficient forger wins with certainty: hardness is a property of the
       concrete group and can never follow from the algebraic setting alone.

  What is NOT claimed or modelled:

  * CDH (or any other hardness assumption) is not proved and not assumed.  No theorem here says
    that any winning probability is small for all adversaries.
  * The adversary is PASSIVE, in exactly this sense.  It sees (i) the signatures on all messages
    other than the target, (ii) hence the complete views of its own honest sessions on such
    messages (section D.1), (iii) the wire transcripts of honest sessions of other parties on
    any message, target included, whose blinding coins stay secret (sections D.2, D.3).  It can NOT
    make B evaluate group elements of its choice, it can NOT modify messages on the wire, and it
    does NOT learn the blinding coin or the output of a session on the target (if it does, it
    simply holds the signature: `hbcExp_target_wins`).  So an honest-but-curious party A and a
    wire eavesdropper are covered; a party A that deviates from the protocol and an active
    network attacker are not.  Against a deviating A, who may submit arbitrary group elements to
    B, unforgeability is the ONE-MORE Diffie–Hellman assumption ("one-more unforgeability":
    after `n` interactions, no `n + 1` valid signatures).  That notion is NOT proved, NOT
    reduced to anything, and not even defined in this file.
  * The target is SELECTIVE (fixed before the key and the oracle are sampled), and so are the
    messages of the observed sessions.  The adaptive notions, where the forger chooses the
    target or the session messages after seeing data, are not treated here.
  * The forger has no verification oracle: it outputs a single candidate and is never told
    whether a candidate is valid.  Verification needs the key (`verifyWithKey`); a forger that
    may ask the key holder to verify candidates is not covered (that is a gap-type assumption).
    The pairing setting of `PublicVerify.lean`, where everybody can verify, is not formalised
    here either.
  * The random oracle is an eagerly sampled table `m ↦ h m • g` on a finite message space; no
    statement is made about any concrete hash function, nor about lazily sampled oracles on
    infinite domains.
  * Lean has no cost model here.  "The reduction is efficient" is a claim to be checked by
    reading the definitions `cdhSolver` and `cdhSolverInput`: the solver samples one table of
    `|M|` exponents, performs `2 (|M| - 1)` scalar multiplications and calls the forger once,
    and its input type `G × G` visibly contains neither the key nor a discrete logarithm.  Note
    the consequence: the solver's work, like the forger's input (`2 |M| + 1` group elements), is
    LINEAR IN THE SIZE OF THE MESSAGE SPACE, not in the number of signatures an attacker
    actually saw.  The reduction is therefore efficient only relative to a message space of
    feasible size (equivalently: read `M` as the set of messages that are ever hashed); for
    `M` = all bit strings of some length it has no polynomial-time reading.  The equality
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

/-- An experiment that reads two different entries of a uniformly random table sees two
independent uniform values. -/
theorem unif_bind_eval₂ [Fintype α] [Nonempty α] [Fintype ι] [DecidableEq ι] {i j : ι}
    (hij : i ≠ j) (f : α → α → PMF γ) :
    ((unif (ι → α)).bind fun h => f (h i) (h j)) =
      (unif α).bind fun a => (unif α).bind fun b => f a b := by
  refine (unif_bind_update i _).symm.trans ?_
  refine congrArg _ (funext fun a => ?_)
  simp only [Function.update_self, Function.update_of_ne hij.symm]
  exact unif_bind_eval j (f a)

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

/-- The CDH instance that the converse reduction reads off the forger's input: the public key
and the hash of the target.  (The deterministic core of `forgerOfSolver`: two projections.) -/
def solverInput (mstar : M) (x : ForgerInput G M) : G × G := (x.1, x.2.1 mstar)

/-- The forger obtained from a CDH solver `S` (used for the converse reduction `cdh_eq_forge`):
run the solver on the public key and the hash of the target; ignore everything else. -/
def forgerOfSolver (mstar : M) (S : G × G → PMF G) : ForgerInput G M → PMF G :=
  fun x => S (solverInput mstar x)

/-- The output of the forger for the LEAKY experiment: the leaked exponent `e` times the public
key `pk`.  (The deterministic core of `leakForger`: one scalar multiplication, no classical
choice.) -/
def leakCore (x : F × ForgerInput G M) : G := x.1 • x.2.1

/-- The forger for the LEAKY experiment `forgeExpLeaky`: given the oracle exponent `e = h mstar`
of the target and the public key `pk`, output `e • pk`.  One scalar multiplication. -/
noncomputable def leakForger : F × ForgerInput G M → PMF G :=
  fun x => PMF.pure (leakCore x)

/-- **The deterministic core of the reduction**: the forger's input that the CDH solver prepares
from a CDH instance `AB = (A, B)` (to be thought of as `(a • g, b • g)`) and a table of exponents
`h : M → F` of its own choosing:

* public key `A` (so the unknown key is `a`),
* hash table `m ↦ h m • g` for `m ≠ mstar`, with `B` PLANTED as the hash of the target,
* signatures `m ↦ h m • A` for `m ≠ mstar` (correct, since `a • (h m • g) = h m • (a • g)`), and
  the dummy `0` at the target.

Its arguments are group elements and the solver's own exponents; neither `a`, `b` nor any
discrete logarithm is available to it, and its definition uses no classical choice.  The work is
`2 (|M| - 1)` scalar multiplications; the entry `h mstar` is not used. -/
def cdhSolverInput [DecidableEq M] (g : G) (mstar : M) (AB : G × G) (h : M → F) :
    ForgerInput G M :=
  (AB.1, (fun m => if m = mstar then AB.2 else h m • g),
    (fun m => if m = mstar then 0 else h m • AB.1))

/-- The deterministic core of `forgerOfHbc`: the input of an honest-but-curious adversary,
recomputed from the forger's input `x` and blinding coins `r`.  The view of session `i` is the
message `ms i`, the coin `r i` and B's reply `r i • (signature on ms i)`, read off the signature
table.  One scalar multiplication per session, no classical choice. -/
def hbcSimInput {n : ℕ} (ms : Fin n → M) (x : ForgerInput G M) (r : Fin n → Fˣ) :
    G × (M → G) × (Fin n → M × Fˣ × G) :=
  (x.1, x.2.1, fun i => (ms i, r i, ((r i : Fˣ) : F) • x.2.2 (ms i)))

/-- What a wire eavesdropper sees of one honest session on message `m` with blinding coin `r`:
A's message `a = r • H m` and B's reply `b = k • a`.  (Neither `m` nor `r` nor A's output.) -/
def wire (H : M → G) (k : F) (m : M) (r : Fˣ) : G × G :=
  (blind H m r, evaluate k (blind H m r))

/-- The simulated wire transcript of an honest session on `m`, computed from the forger's input
`x = (pk, H, _)`, the base point and ONE fresh nonzero scalar `u`: if `H m = 0` the transcript is
`(0, 0)`, otherwise it is `(u • g, u • pk)`.  Two scalar multiplications and one zero test, no
classical choice; the signature table is not used. -/
def wireSim [DecidableEq G] (g : G) (x : ForgerInput G M) (m : M) (u : Fˣ) : G × G :=
  if x.2.1 m = 0 then (0, 0) else ((u : F) • g, (u : F) • x.1)

/-- The UNBOUNDED non-leaky forger that emulates a leaky forger `Adv`: recover the oracle exponent
of the target as a discrete logarithm of `H mstar` (any scalar `c` with `c • g = H mstar`,
obtained by classical choice — there is no algorithm here) and run `Adv` with it. -/
noncomputable def dlogForgerOfLeaky (g : G) (mstar : M) (Adv : F × ForgerInput G M → PMF G) :
    ForgerInput G M → PMF G :=
  fun x => Adv (Classical.epsilon fun c : F => c • g = x.2.1 mstar, x)

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
`verifyWithKey H k mstar σ` holds for its output `σ`.

When `g` generates the group this is the same experiment as `forgeExpUnifRO`, where `H` is drawn
uniformly from all functions `M → G` (`forgeExp_eq_unifRO`). -/
noncomputable def forgeExp (g : G) (mstar : M) (Adv : ForgerInput G M → PMF G) : PMF Bool :=
  (unif F).bind fun k => (unif (M → F)).bind fun h =>
    (Adv (k • g, roHash g h, knownSigs (roHash g h) k mstar)).map
      fun σ => decide (σ = prf (roHash g h) k mstar)

/-- The forgery experiment in its canonical random-oracle form (finite group): exactly `forgeExp`,
except that the hash function `H` is drawn uniformly from ALL functions `M → G` instead of being
built from a table of exponents.  Used only in `forgeExp_eq_unifRO`. -/
noncomputable def forgeExpUnifRO [Fintype G] (g : G) (mstar : M)
    (Adv : ForgerInput G M → PMF G) : PMF Bool :=
  (unif F).bind fun k => (unif (M → G)).bind fun H =>
    (Adv (k • g, H, knownSigs H k mstar)).map fun σ => decide (σ = prf H k mstar)

/-- **The CDH experiment** over the group generated by `g`: sample `a, b : F` uniformly, hand the
solver the pair `(a • g, b • g)`; the result is `true` iff it outputs `(a * b) • g`. -/
noncomputable def cdhExp (g : G) (S : G × G → PMF G) : PMF Bool :=
  (unif (F × F)).bind fun ab =>
    (S (ab.1 • g, ab.2 • g)).map fun Z => decide (Z = (ab.1 * ab.2) • g)

/-- **The reduction**: the CDH solver built from a forger `Adv`.  Input: `AB = (A, B)`, to be
thought of as `(a • g, b • g)`.  Sample a table of exponents `h : M → F` and run the forger on
the input `cdhSolverInput g mstar AB h`, i.e. on

* public key `A` (so the unknown key is `a`),
* hash table `m ↦ h m • g` for `m ≠ mstar`, with `B` PLANTED as the hash of the target,
* signatures `m ↦ h m • A` for `m ≠ mstar` (correct, since `a • (h m • g) = h m • (a • g)`).

The forger's output is the solver's output.  The inputs are group elements only; the forger is
used as a black box, once; the work besides is sampling `|M|` exponents and `2 (|M| - 1)` scalar
multiplications — linear in the size of the message space `M`, so "efficient" only when `M` is
of feasible size.  That reading is by inspection of this definition and of `cdhSolverInput`, not
a theorem: Lean has no cost model here.  (The sampled value `h mstar` is not used.)  The unfolded
form is `cdhSolver_apply`. -/
noncomputable def cdhSolver (g : G) (mstar : M) (Adv : ForgerInput G M → PMF G) :
    G × G → PMF G := fun AB =>
  (unif (M → F)).bind fun h => Adv (cdhSolverInput g mstar AB h)

/-- **The leaky forgery experiment** (a comparison experiment for section G):
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
session `i` is `r i • (signature on ms i)`); the computation is `hbcSimInput`. -/
noncomputable def forgerOfHbc [DecidableEq F] {n : ℕ} (ms : Fin n → M)
    (AdvA : G × (M → G) × (Fin n → M × Fˣ × G) → PMF G) : ForgerInput G M → PMF G :=
  fun x => (unif (Fin n → Fˣ)).bind fun r : Fin n → Fˣ => AdvA (hbcSimInput ms x r)

/-- **The eavesdropper experiment.**  Exactly `forgeExp` (the adversary gets the public key, the
whole hash table and the signatures on all messages other than the target), except that the
adversary ADDITIONALLY sees the wire transcripts `wire H k (ms i) (r i) = (r i • H (ms i),
k • r i • H (ms i))` of `n` honest protocol sessions run by other parties on the messages
`ms 0, …, ms (n-1)`.  These messages are fixed in advance, repetitions are allowed, and they MAY
INCLUDE THE TARGET.  The blinding coins `r i` are independent, uniform, nonzero and are NOT given
to the adversary.  The result is `true` iff the adversary outputs `prf H k mstar`. -/
noncomputable def eavesdropExp [DecidableEq F] (g : G) (mstar : M) {n : ℕ} (ms : Fin n → M)
    (Adv : ForgerInput G M × (Fin n → G × G) → PMF G) : PMF Bool :=
  (unif F).bind fun k => (unif (M → F)).bind fun h =>
    (unif (Fin n → Fˣ)).bind fun r : Fin n → Fˣ =>
      (Adv ((k • g, roHash g h, knownSigs (roHash g h) k mstar),
        fun i => wire (roHash g h) k (ms i) (r i))).map
        fun σ => decide (σ = prf (roHash g h) k mstar)

/-- The forger that simulates the eavesdropper: it samples one fresh nonzero scalar per observed
session and computes a transcript with `wireSim` (from the base point, the public key and one
zero test on the hash table). -/
noncomputable def forgerOfEavesdropper [DecidableEq F] (g : G) {n : ℕ} (ms : Fin n → M)
    (Adv : ForgerInput G M × (Fin n → G × G) → PMF G) : ForgerInput G M → PMF G :=
  fun x => (unif (Fin n → Fˣ)).bind fun u : Fin n → Fˣ =>
    Adv (x, fun i => wireSim g x (ms i) (u i))

/-- **The passive experiment** (an honest-but-curious party A that also taps the wire).  The
adversary is handed the public key, the whole hash table, party A's COMPLETE views of `n` honest
sessions of its own on the messages `ms i` (message, coin and B's reply, as in `hbcExp`), and the
wire transcripts of `n'` honest sessions of OTHER parties on the messages `ms' j` (as in
`eavesdropExp`; the coins of those sessions are not given to it).  All coins are independent,
uniform and nonzero; all session messages are fixed in advance.  The result is `true` iff the
adversary outputs `prf H k mstar`. -/
noncomputable def passiveExp [DecidableEq F] (g : G) (mstar : M) {n n' : ℕ} (ms : Fin n → M)
    (ms' : Fin n' → M)
    (Adv : (G × (M → G) × (Fin n → M × Fˣ × G)) × (Fin n' → G × G) → PMF G) : PMF Bool :=
  (unif F).bind fun k => (unif (M → F)).bind fun h =>
    (unif (Fin n → Fˣ)).bind fun r : Fin n → Fˣ =>
      (unif (Fin n' → Fˣ)).bind fun r' : Fin n' → Fˣ =>
        (Adv ((k • g, roHash g h, fun i => viewA (roHash g h) k (ms i) (r i)),
          fun j => wire (roHash g h) k (ms' j) (r' j))).map
          fun σ => decide (σ = prf (roHash g h) k mstar)

/-- The forger that simulates the passive adversary: it samples the coins of its own sessions
and one fresh nonzero scalar per observed session, and computes the views with `hbcSimInput` and
the wire transcripts with `wireSim`. -/
noncomputable def forgerOfPassive [DecidableEq F] (g : G) {n n' : ℕ} (ms : Fin n → M)
    (ms' : Fin n' → M)
    (Adv : (G × (M → G) × (Fin n → M × Fˣ × G)) × (Fin n' → G × G) → PMF G) :
    ForgerInput G M → PMF G :=
  fun x => (unif (Fin n → Fˣ)).bind fun r : Fin n → Fˣ =>
    (unif (Fin n' → Fˣ)).bind fun u : Fin n' → Fˣ =>
      Adv (hbcSimInput ms x r, fun j => wireSim g x (ms' j) (u j))

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

/-- The reduction, written out: `cdhSolver` is literally "sample a table of exponents, run the
forger on (`A`, hash table with `B` planted at the target, signatures `h m • A`)". -/
theorem cdhSolver_apply [Fintype F] [Fintype M] [DecidableEq M] (g : G) (mstar : M)
    (Adv : ForgerInput G M → PMF G) (AB : G × G) :
    cdhSolver F g mstar Adv AB =
      (unif (M → F)).bind fun h =>
        Adv (AB.1, (fun m => if m = mstar then AB.2 else h m • g),
          (fun m => if m = mstar then 0 else h m • AB.1)) :=
  rfl

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
`r • H m`): B's reply to an arbitrary group element is not obtained from the forger's input by
the simulation used here.  (For `g ≠ 0` that reply IS determined by the public key, see
`exists_evaluate_of_publicKey`; but computing it from the public key is a Diffie–Hellman
problem, and an adversary that obtains such replies from B is in the one-more Diffie–Hellman
setting, which is not treated in this file.) -/
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
This is the law of the hash table alone; the statement about the whole experiment (table jointly
with key, signatures and winning condition) is `forgeExp_eq_unifRO`.  It says nothing about any
concrete hash function. -/
theorem roHash_uniform [Fintype F] [Fintype G] [Fintype M] [DecidableEq M] {g : G}
    (hg : IsGenerator F g) : (unif (M → F)).map (roHash g) = unif (M → G) :=
  unif_map_equiv (Equiv.piCongrRight fun _ : M => hg.equiv)

/-- **The forgery experiment in random-oracle form.**  If `g` generates the (finite) group, the
forgery experiment `forgeExp` — whose hash table is built from uniform exponents — is the SAME
distribution as `forgeExpUnifRO`, in which the hash function is drawn uniformly from all
functions `M → G`, for every target and every forger.  So `forgeExp` is the usual random-oracle
experiment, with the oracle sampled eagerly.

What this does NOT claim: anything about a concrete hash function, about lazily sampled oracles
or infinite message spaces; and it is an equality of experiments, not a bound on any
probability. -/
theorem forgeExp_eq_unifRO [Fintype F] [Fintype G] [DecidableEq G] [Fintype M] [DecidableEq M]
    {g : G} (hg : IsGenerator F g) (mstar : M) (Adv : ForgerInput G M → PMF G) :
    forgeExp F g mstar Adv = forgeExpUnifRO F g mstar Adv := by
  unfold forgeExp forgeExpUnifRO
  refine congrArg _ (funext fun k => ?_)
  rw [← roHash_uniform hg, PMF.bind_map]
  rfl

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
after any number of protocol runs on other messages (made precise in `hbc_eq_cdh`), or a wire
eavesdropper (`eavesdrop_eq_cdh`) — and then produces the signature on the target, yields, by the
visible construction `cdhSolver`, a solver for the Computational Diffie–Hellman problem in the
group generated by `g`.

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
* Efficiency of `cdhSolver` (one call to `Adv`, `|M|` sampled exponents, `2 (|M| - 1)` scalar
  multiplications, no access to any exponent of the CDH instance) is by inspection of its
  definition; Lean has no cost model here.  The solver's work, like the forger's input, is
  linear in `|M|`: the reduction is efficient only relative to a message space of feasible size
  (equivalently: `M` is the set of messages ever hashed). -/
theorem forge_eq_cdh (g : G) (mstar : M) (Adv : ForgerInput G M → PMF G) :
    forgeExp F g mstar Adv = cdhExp F g (cdhSolver F g mstar Adv) := by
  unfold forgeExp cdhExp cdhSolver cdhSolverInput
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

Together with `forge_eq_cdh`: as equalities of experiments, every forger for a fixed target is
turned into a CDH solver for the group generated by `g` with the same success probability, and
vice versa.  Like `forge_eq_cdh` this says nothing about whether either probability is small.
"Neither easier nor harder than CDH" in the computational sense additionally needs both
transformations to be cheap: `forgerOfSolver` is two projections, but `cdhSolver` does work
linear in `|M|` (see `forge_eq_cdh`), so that reading holds only for a message space of
feasible size, and it is by inspection, not a theorem. -/
theorem cdh_eq_forge (g : G) (mstar : M) (S : G × G → PMF G) :
    cdhExp F g S = forgeExp F g mstar (forgerOfSolver mstar S) := by
  unfold cdhExp forgeExp forgerOfSolver solverInput
  rw [unif_prod_bind]
  refine congrArg _ (funext fun a => ?_)
  refine (unif_bind_eval mstar
    (fun b => (S (a • g, b • g)).map fun Z => decide (Z = (a * b) • g))).symm.trans ?_
  refine congrArg _ (funext fun h => ?_)
  show (S (a • g, h mstar • g)).map (fun Z => decide (Z = (a * h mstar) • g)) =
    (S (a • g, h mstar • g)).map (fun σ => decide (σ = a • h mstar • g))
  rw [mul_smul]

end Reduction

/-! ## D. Passive adversaries are forgers -/

/-! ### D.1 The honest-but-curious party A -/

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
of experiments, not a statement that any probability is small.  The hypothesis `hms` cannot be
dropped: see `hbcExp_target_wins`. -/
theorem hbc_eq_forge (g : G) (mstar : M) {n : ℕ} (ms : Fin n → M) (hms : ∀ i, ms i ≠ mstar)
    (AdvA : G × (M → G) × (Fin n → M × Fˣ × G) → PMF G) :
    hbcExp F g mstar ms AdvA = forgeExp F g mstar (forgerOfHbc F ms AdvA) := by
  unfold hbcExp forgeExp forgerOfHbc hbcSimInput
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
space; efficiency of the solver is by inspection and its work is linear in `|M|`. -/
theorem hbc_eq_cdh (g : G) (mstar : M) {n : ℕ} (ms : Fin n → M) (hms : ∀ i, ms i ≠ mstar)
    (AdvA : G × (M → G) × (Fin n → M × Fˣ × G) → PMF G) :
    hbcExp F g mstar ms AdvA =
      cdhExp F g (cdhSolver F g mstar (forgerOfHbc F ms AdvA)) := by
  rw [hbc_eq_forge g mstar ms hms, forge_eq_cdh]

/-- **The restriction to non-target sessions is necessary.**  An honest party A that DID run the
protocol on the target simply unblinds B's reply and holds the signature: in `hbcExp` with the
single session message `mstar`, the adversary "unblind the reply with my coin" wins with
certainty.  So the hypothesis `hms` of `hbc_eq_forge` is not a convenience, and `hbcExp` is
faithful to the protocol (this is its correctness).  This is no attack: the signature on the
target was issued to A. -/
theorem hbcExp_target_wins (g : G) (mstar : M) :
    hbcExp F g mstar (fun _ : Fin 1 => mstar)
      (fun x => PMF.pure (unblind (x.2.2 0).2.1 (x.2.2 0).2.2)) = PMF.pure true := by
  have key : ∀ (k : F) (h : M → F) (r : Fin 1 → Fˣ),
      (PMF.pure (unblind (r 0) (evaluate k (blind (roHash g h) mstar (r 0))))).map
        (fun σ => decide (σ = prf (roHash g h) k mstar)) = PMF.pure true := by
    intro k h r
    rw [PMF.pure_map]
    exact congrArg PMF.pure (decide_eq_true (unblind_evaluate_blind _ _ _ _))
  simp only [hbcExp, viewA, key, PMF.bind_const]

end HonestButCurious

/-! ### D.2 The wire eavesdropper -/

section WireSim

variable [Field F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- **One eavesdropped session is simulated from public data.**  For every key, every table of
oracle exponents and every message `m` there is a bijection `τ` of the nonzero scalars such that
the real wire transcript with blinding coin `r` is the simulated transcript `wireSim` with the
scalar `τ r`.  (If `H m = 0` both are `(0, 0)`; otherwise `τ r = r * h m`, and the transcript is
`(u • g, u • pk)` with `u = τ r`.)  Since `τ` is a bijection, a uniform coin gives a uniform
simulation scalar.  The third component `S` of the forger's input is not used. -/
theorem exists_wire_equiv (g : G) (k : F) (h : M → F) (S : M → G) (m : M) :
    ∃ τ : Fˣ ≃ Fˣ, ∀ r : Fˣ,
      wireSim g (k • g, roHash g h, S) m (τ r) = wire (roHash g h) k m r := by
  by_cases hH : h m • g = 0
  · refine ⟨Equiv.refl _, fun r => ?_⟩
    simp [wireSim, wire, blind, evaluate, roHash, hH]
  · have hm : h m ≠ 0 := fun h0 => hH (by rw [h0, zero_smul])
    refine ⟨Equiv.mulRight (Units.mk0 (h m) hm), fun r => ?_⟩
    simp only [wireSim, wire, blind, evaluate, roHash, hH, ite_false, Equiv.coe_mulRight,
      Units.val_mul, Units.val_mk0, mul_smul]
    rw [smul_comm k, smul_comm k]

end WireSim

section Eavesdropper

variable [Field F] [Fintype F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
  [Fintype M] [DecidableEq M]

/-- **A wire eavesdropper is a passive forger (exact).**  The eavesdropper experiment — the
adversary sees the public key, the hash table, the signatures on all messages other than the
target AND the wire transcripts `(a, b) = (r • H m, k • r • H m)` of `n` honest sessions of
other parties on arbitrary messages, THE TARGET INCLUDED — is the SAME distribution as the
forgery experiment with the explicit forger `forgerOfEavesdropper F g ms Adv`, which simulates
every transcript from the base point and the public key.  No hypothesis on `g` or on `ms`.

Meaning: watching honest sessions on the wire adds nothing to what the forger already holds,
not even sessions on the target message: because the blinding coin is uniform and stays secret,
a transcript is just `(u • g, u • pk)` for a fresh uniform nonzero `u` (or `(0, 0)` if
`H m = 0`), which the forger produces itself.
The adversary here is handed the forger's whole input (the signatures on ALL messages other than
the target); the variant in which it instead holds the views of its own honest sessions is
`passive_eq_forge`.

What this does NOT claim: the observed sessions are HONEST (uniform nonzero coin that the
adversary never learns, B answers honestly) and their messages are fixed in advance; an
adversary that learns the coin or the output of a session on the target holds the signature
(`hbcExp_target_wins`); an adversary that modifies or injects messages (active network attacker,
deviating party A — the one-more Diffie–Hellman setting) is not covered; and this is an equality
of experiments, not a statement that any probability is small. -/
theorem eavesdrop_eq_forge (g : G) (mstar : M) {n : ℕ} (ms : Fin n → M)
    (Adv : ForgerInput G M × (Fin n → G × G) → PMF G) :
    eavesdropExp F g mstar ms Adv = forgeExp F g mstar (forgerOfEavesdropper F g ms Adv) := by
  unfold eavesdropExp forgeExp forgerOfEavesdropper
  refine congrArg _ (funext fun k => congrArg _ (funext fun h => ?_))
  rw [PMF.map_bind]
  choose τ hτ using fun m : M => exists_wire_equiv g k h (knownSigs (roHash g h) k mstar) m
  refine unif_bind_eq_of_equiv (Equiv.piCongrRight fun i : Fin n => τ (ms i)) _ _ fun r => ?_
  have hwire : (fun i => wireSim g (k • g, roHash g h, knownSigs (roHash g h) k mstar) (ms i)
      ((Equiv.piCongrRight fun i : Fin n => τ (ms i)) r i)) =
      fun i => wire (roHash g h) k (ms i) (r i) :=
    funext fun i => hτ (ms i) (r i)
  simp only [hwire]

/-- **Forging while eavesdropping is solving CDH (exact reduction).**  The success probability
of an adversary that knows the signatures on all messages other than the target and has watched
`n` honest sessions on the wire (on any messages, the target included) is exactly the success
probability of the explicit CDH solver `cdhSolver F g mstar (forgerOfEavesdropper F g ms Adv)`.

Same caveats as `forge_eq_cdh` and `eavesdrop_eq_forge`: a reduction only (CDH is an assumption
and is not proved or assumed); the adversary is passive — honest sessions, secret coins, no
tampering; selective target and session messages; eagerly sampled random oracle on a finite
message space; efficiency of the solver is by inspection and its work is linear in `|M| + n`. -/
theorem eavesdrop_eq_cdh (g : G) (mstar : M) {n : ℕ} (ms : Fin n → M)
    (Adv : ForgerInput G M × (Fin n → G × G) → PMF G) :
    eavesdropExp F g mstar ms Adv =
      cdhExp F g (cdhSolver F g mstar (forgerOfEavesdropper F g ms Adv)) := by
  rw [eavesdrop_eq_forge, forge_eq_cdh]

/-! ### D.3 Both at once: an honest-but-curious A that also taps the wire -/

/-- **A passive adversary is a forger (exact).**  If none of the messages of A's OWN sessions is
the target, the passive experiment — the adversary sees the public key, the hash table, A's
complete views of `n` honest sessions of its own, and the wire transcripts of `n'` honest
sessions of other parties on arbitrary messages, the target included — is the SAME distribution
as the forgery experiment with the explicit forger `forgerOfPassive F g ms ms' Adv`.

Meaning: `hbc_eq_forge` and `eavesdrop_eq_forge` hold jointly; everything a party sees that
follows the protocol and listens to everybody else's sessions is simulated from the public key,
the hash table and the signatures on the messages it ran the protocol on.

What this does NOT claim: the same limits as `hbc_eq_forge` and `eavesdrop_eq_forge`.  The
adversary is passive: all sessions are honest, the coins of the observed sessions stay secret,
nothing is modified or injected, and all session messages are fixed in advance.  A party A that
deviates from the protocol is the one-more Diffie–Hellman setting and is not covered.  `hms`
restricts A's own sessions only (`hbcExp_target_wins` shows it is needed); the observed sessions
`ms'` are unrestricted.  It is an equality of experiments, not a bound on any probability. -/
theorem passive_eq_forge (g : G) (mstar : M) {n n' : ℕ} (ms : Fin n → M)
    (hms : ∀ i, ms i ≠ mstar) (ms' : Fin n' → M)
    (Adv : (G × (M → G) × (Fin n → M × Fˣ × G)) × (Fin n' → G × G) → PMF G) :
    passiveExp F g mstar ms ms' Adv =
      forgeExp F g mstar (forgerOfPassive F g ms ms' Adv) := by
  unfold passiveExp forgeExp forgerOfPassive hbcSimInput
  refine congrArg _ (funext fun k => congrArg _ (funext fun h => ?_))
  rw [PMF.map_bind]
  refine congrArg _ (funext fun r => ?_)
  rw [PMF.map_bind]
  have hview : (fun i => viewA (roHash g h) k (ms i) (r i)) =
      fun i => (ms i, r i, ((r i : Fˣ) : F) • knownSigs (roHash g h) k mstar (ms i)) :=
    funext fun i => viewA_eq_of_knownSigs (roHash g h) k (hms i) (r i)
  rw [hview]
  choose τ hτ using fun m : M => exists_wire_equiv g k h (knownSigs (roHash g h) k mstar) m
  refine unif_bind_eq_of_equiv (Equiv.piCongrRight fun j : Fin n' => τ (ms' j)) _ _ fun r' => ?_
  have hwire : (fun j => wireSim g (k • g, roHash g h, knownSigs (roHash g h) k mstar) (ms' j)
      ((Equiv.piCongrRight fun j : Fin n' => τ (ms' j)) r' j)) =
      fun j => wire (roHash g h) k (ms' j) (r' j) :=
    funext fun j => hτ (ms' j) (r' j)
  simp only [hwire]

/-- **Forging as a passive adversary is solving CDH (exact reduction).**  The success
probability of a passive adversary — an honest-but-curious party A after `n` honest sessions on
messages other than the target, who has also watched `n'` honest sessions of other parties on
the wire (on any messages, the target included) — is exactly the success probability of the
explicit CDH solver `cdhSolver F g mstar (forgerOfPassive F g ms ms' Adv)`.

Same caveats as `forge_eq_cdh` and `passive_eq_forge`: a reduction only (CDH is an assumption
and is not proved or assumed); passive adversary only, the one-more Diffie–Hellman setting of a
deviating A and active network attackers are not covered; selective target and session messages;
eagerly sampled random oracle on a finite message space; efficiency of the solver is by
inspection and its work is linear in `|M| + n + n'`. -/
theorem passive_eq_cdh (g : G) (mstar : M) {n n' : ℕ} (ms : Fin n → M)
    (hms : ∀ i, ms i ≠ mstar) (ms' : Fin n' → M)
    (Adv : (G × (M → G) × (Fin n → M × Fˣ × G)) × (Fin n' → G × G) → PMF G) :
    passiveExp F g mstar ms ms' Adv =
      cdhExp F g (cdhSolver F g mstar (forgerOfPassive F g ms ms' Adv)) := by
  rw [passive_eq_forge g mstar ms hms, forge_eq_cdh]

end Eavesdropper

/-! ## E. S1 — an unbounded forger wins: the property can only be computational -/

section PublicKeyDetermines

variable [Field F] [AddCommGroup G] [Module F G]

/-- **B's replies are determined by the public key (information-theoretically).**  If `g ≠ 0`
there is a function `f` that maps the public key `k • g` and any group element `a` to B's reply
`evaluate k a = k • a`.  The witness takes a discrete logarithm of the public key by classical
choice: it is NOT an algorithm.

Meaning: "B's reply to an arbitrary group element is not a function of public data" would be
false; a party that cannot query B is kept from these replies only by the cost of computing
this function (for `a` a multiple of `g`: the CDH problem).  Nothing here says that it is
hard. -/
theorem exists_evaluate_of_publicKey {g : G} (hg0 : g ≠ 0) :
    ∃ f : G → G → G, ∀ (k : F) (a : G), f (k • g) a = evaluate k a := by
  refine ⟨fun pk a => (Classical.epsilon fun c : F => c • g = pk) • a, fun k a => ?_⟩
  have hc : (Classical.epsilon fun c : F => c • g = k • g) • g = k • g :=
    Classical.epsilon_spec (p := fun c : F => c • g = k • g) ⟨k, rfl⟩
  have hk : (Classical.epsilon fun c : F => c • g = k • g) = k :=
    smul_left_injective_of_ne_zero hg0 hc
  simp only [evaluate]
  rw [hk]

end PublicKeyDetermines

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

section Numbers

variable [Field F] [Fintype F]

/-- The number `(2|F| - 1) / |F|²` (the winning probability of the constant-`0` forger and of
the copying forgers below) is at most `2 / |F|`. -/
theorem two_mul_card_sub_one_div_sq_le :
    ((2 * Fintype.card F - 1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ^ 2 ≤
      2 / (Fintype.card F : ℝ≥0∞) := by
  have hq0 : (Fintype.card F : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hqt : (Fintype.card F : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  refine ENNReal.div_le_of_le_mul ?_
  rw [sq, ← mul_assoc, ENNReal.div_mul_cancel hq0 hqt]
  have h : 2 * Fintype.card F - 1 ≤ 2 * Fintype.card F := Nat.sub_le _ _
  exact_mod_cast h

/-- The number `(2|F| - 1) / |F|²` is strictly less than `1` (a field has at least two
elements). -/
theorem two_mul_card_sub_one_div_sq_lt_one :
    ((2 * Fintype.card F - 1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ^ 2 < 1 := by
  have h2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have hlt : 2 * Fintype.card F - 1 < Fintype.card F * Fintype.card F := by
    have := Nat.mul_le_mul_right (Fintype.card F) h2
    omega
  refine (ENNReal.div_lt_iff (Or.inl ?_) (Or.inl ?_)).mpr ?_
  · exact pow_ne_zero _ (by exact_mod_cast Fintype.card_ne_zero)
  · exact ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
  · rw [one_mul, sq]
    exact_mod_cast hlt

end Numbers

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
probability at most `2 / |F|`.  (For `|F| = 2` this bound is `1` and says nothing; the exact
values and `forgeExp_const_lt_one` cover that case.)  This bounds the constant forgers only; it
is NOT a bound for forgers that use their input (no such bound can hold for all functions, see
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

/-! ### Forgers that copy an entry of their input

The constant forgers above ignore their input.  The next cheapest strategies copy one entry of
it.  Each of them wins with probability exactly `(2|F| - 1) / |F|²`, the value of the
constant-`0` forger, hence at most `2 / |F|` and strictly less than `1`
(`two_mul_card_sub_one_div_sq_le`, `two_mul_card_sub_one_div_sq_lt_one`).  As before, these are
statements about particular forgers; they bound nothing else. -/

section Copying

variable [Field F] [Fintype F] [AddCommGroup G] [Module F G] [DecidableEq G]
  [Fintype M] [DecidableEq M]

/-- The forgery experiment for a deterministic forger that looks only at the public key and at
the hash of the target (and computes any function `s` of them): it wins iff
`s (a • g, b • g) = (a * b) • g` for two independent uniform scalars — literally a CDH experiment
with the deterministic solver `s`. -/
theorem forgeExp_pkHash (g : G) (mstar : M) (s : G × G → G) :
    forgeExp F g mstar (fun x => PMF.pure (s (solverInput mstar x))) =
      (unif (F × F)).map fun ab => decide (s (ab.1 • g, ab.2 • g) = (ab.1 * ab.2) • g) := by
  refine (cdh_eq_forge (F := F) g mstar (fun AB => PMF.pure (s AB))).symm.trans ?_
  unfold cdhExp
  simp only [PMF.pure_map]
  exact PMF.bind_pure_comp _ _

/-- The winning probability of such a forger as a ratio of cardinalities. -/
theorem forgeExp_pkHash_apply_true (g : G) (mstar : M) (s : G × G → G) :
    forgeExp F g mstar (fun x => PMF.pure (s (solverInput mstar x))) true =
      (Fintype.card {ab : F × F // s (ab.1 • g, ab.2 • g) = (ab.1 * ab.2) • g} : ℝ≥0∞) /
        (Fintype.card F : ℝ≥0∞) ^ 2 := by
  rw [forgeExp_pkHash, unif_map_decide_true, Fintype.card_prod, Nat.cast_mul, sq]

/-- **S2, the forger that outputs the public key.**  If `g ≠ 0` it wins with probability exactly
`(2|F| - 1) / |F|²` (it wins iff the key is `0` or the oracle exponent of the target is `1`).
One particular forger; no bound for others. -/
theorem forgeExp_copy_pk {g : G} (hg0 : g ≠ 0) (mstar : M) :
    forgeExp F g mstar (fun x => PMF.pure x.1) true =
      ((2 * Fintype.card F - 1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ^ 2 := by
  classical
  refine (forgeExp_pkHash_apply_true (F := F) g mstar Prod.fst).trans ?_
  rw [← card_mul_eq_zero (F := F)]
  congr 2
  exact Fintype.card_congr
    (Equiv.subtypeEquiv (Equiv.prodCongr (Equiv.refl F) (Equiv.subLeft 1)) fun ab => by
      show ab.1 • g = (ab.1 * ab.2) • g ↔ ab.1 * (1 - ab.2) = 0
      rw [(smul_left_injective_of_ne_zero hg0).eq_iff, mul_sub, mul_one, sub_eq_zero])

/-- **S2, the forger that outputs the hash of the target.**  If `g ≠ 0` it wins with probability
exactly `(2|F| - 1) / |F|²` (it wins iff the key is `1` or the oracle exponent of the target is
`0`).  One particular forger; no bound for others. -/
theorem forgeExp_copy_hash {g : G} (hg0 : g ≠ 0) (mstar : M) :
    forgeExp F g mstar (fun x => PMF.pure (x.2.1 mstar)) true =
      ((2 * Fintype.card F - 1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ^ 2 := by
  classical
  refine (forgeExp_pkHash_apply_true (F := F) g mstar Prod.snd).trans ?_
  rw [← card_mul_eq_zero (F := F)]
  congr 2
  exact Fintype.card_congr
    (Equiv.subtypeEquiv (Equiv.prodCongr (Equiv.subLeft 1) (Equiv.refl F)) fun ab => by
      show ab.2 • g = (ab.1 * ab.2) • g ↔ (1 - ab.1) * ab.2 = 0
      rw [(smul_left_injective_of_ne_zero hg0).eq_iff, sub_mul, one_mul, sub_eq_zero])

/-- The forger that reads the signature table AT THE TARGET finds only the dummy: it is the
constant-`0` forger.  (Had the table not been masked at the target, this forger would win with
certainty; the dummy is what makes the experiment meaningful.) -/
theorem forgeExp_copy_dummy (g : G) (mstar : M) :
    forgeExp F g mstar (fun x => PMF.pure (x.2.2 mstar)) =
      forgeExp F g mstar (fun _ => PMF.pure 0) := by
  unfold forgeExp
  simp only [knownSigs_self]

/-- **S2, the forger that outputs a known signature.**  If `g ≠ 0` and `m ≠ mstar`, the forger
that outputs the signature on `m` it was handed wins with probability exactly
`(2|F| - 1) / |F|²` (it wins iff the key is `0` or the two messages have the same hash).  So a
signature on one message is not a signature on another, except by this accident.  One particular
forger; no bound for others. -/
theorem forgeExp_copy_sig {g : G} (hg0 : g ≠ 0) {m mstar : M} (hm : m ≠ mstar) :
    forgeExp F g mstar (fun x => PMF.pure (x.2.2 m)) true =
      ((2 * Fintype.card F - 1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ^ 2 := by
  classical
  have key : forgeExp F g mstar (fun x => PMF.pure (x.2.2 m)) =
      (unif (F × F)).map fun ab => decide (ab.1 * ab.2 = 0) := by
    rw [← PMF.bind_pure_comp, unif_prod_bind]
    unfold forgeExp
    refine congrArg _ (funext fun k => ?_)
    -- only the entries `h m` and `h mstar` of the table of exponents matter
    have step : ∀ h : M → F,
        (PMF.pure (knownSigs (roHash g h) k mstar m)).map
          (fun σ => decide (σ = prf (roHash g h) k mstar)) =
        PMF.pure (decide (k * (h m - h mstar) = 0)) := by
      intro h
      rw [PMF.pure_map, knownSigs_of_ne _ _ hm]
      refine congrArg PMF.pure ?_
      simp only [prf, roHash, smul_smul]
      rw [decide_eq_decide, (smul_left_injective_of_ne_zero hg0).eq_iff, mul_sub, sub_eq_zero]
    simp only [step]
    rw [unif_bind_eval₂ hm (fun c d => PMF.pure (decide (k * (c - d) = 0)))]
    -- for fixed `c`, the difference `c - d` is uniform; then `c` is not used any more
    refine Eq.trans (congrArg _ (funext fun c =>
      unif_bind_eq_of_equiv (Equiv.subLeft c) _
        (fun b => PMF.pure (decide (k * b = 0))) (fun _ => rfl))) ?_
    exact PMF.bind_const _ _
  rw [key, unif_map_decide_true, Fintype.card_prod, Nat.cast_mul, sq,
    ← card_mul_eq_zero (F := F)]

end Copying

/-! ## G. S3 — the leaky experiment: one scalar multiplication with the leak, CDH without -/

section Leaky

variable [Field F] [Fintype F] [AddCommGroup G] [Module F G] [DecidableEq G]
  [Fintype M] [DecidableEq M]

/-- **S3. With the oracle exponent of the target, forging is one scalar multiplication.**  In
the leaky experiment, where the forger is additionally handed `h mstar` (the discrete logarithm
of `H mstar`), the explicit forger `leakForger`, which outputs `h mstar • pk`, wins with
certainty.  Its core `leakCore` is one scalar multiplication and uses no classical choice.

Meaning, and its limits.  A hash function with KNOWN discrete logarithms (e.g. `H m = h(m) • g`
for a public `h`) is insecure: forging is then trivial.  This is also exactly the trapdoor the
reduction `cdhSolver` uses for the messages other than the target.  But this theorem does NOT
separate the two experiments formally.  Adversaries here are arbitrary functions, and for them
the leak adds nothing: every leaky forger is matched by a non-leaky forger with exactly the same
experiment (`exists_forger_of_leaky`; for `g ≠ 0` it recovers the exponent as a discrete
logarithm), and without any leak `dlogForger` already wins with certainty.  The difference
between `forgeExp` and `forgeExpLeaky` is therefore computational only: with the leak the winning
forger is a choice-free one-liner, without it winning is exactly CDH (`forge_eq_cdh`), which is
an assumption.  That it "matters that `ForgerInput` contains group elements only" is true in
that efficiency reading alone, by inspection; no theorem here says so. -/
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

/-- If `g ≠ 0`, the unbounded forger `dlogForgerOfLeaky g mstar Adv` — recover the oracle
exponent of the target as a discrete logarithm of `H mstar`, then run the leaky forger `Adv` —
has exactly the experiment of `Adv` in the leaky game.  The witness is NOT an algorithm. -/
theorem forgeExp_dlogForgerOfLeaky {g : G} (hg0 : g ≠ 0) (mstar : M)
    (Adv : F × ForgerInput G M → PMF G) :
    forgeExp F g mstar (dlogForgerOfLeaky g mstar Adv) = forgeExpLeaky F g mstar Adv := by
  unfold forgeExp forgeExpLeaky dlogForgerOfLeaky
  refine congrArg _ (funext fun k => congrArg _ (funext fun h => ?_))
  have hc : (Classical.epsilon fun c : F => c • g = h mstar • g) • g = h mstar • g :=
    Classical.epsilon_spec (p := fun c : F => c • g = h mstar • g) ⟨h mstar, rfl⟩
  have he : (Classical.epsilon fun c : F => c • g = h mstar • g) = h mstar :=
    smul_left_injective_of_ne_zero hg0 hc
  show (Adv ((Classical.epsilon fun c : F => c • g = h mstar • g), _)).map _ = _
  rw [he]

/-- **The leak adds nothing against unbounded forgers.**  For every `g`, every target and every
leaky forger `Adv` there is a non-leaky forger whose forgery experiment is the SAME distribution
as the leaky experiment of `Adv`.  (For `g ≠ 0` the witness takes a discrete logarithm of
`H mstar`; for `g = 0` the leaked exponent is independent of everything else and the witness
samples it itself.)

Meaning: in this model, where adversaries are arbitrary functions, `forgeExp` and `forgeExpLeaky`
can NOT be told apart by what forgers achieve (`forgeExpLeaky_achievable_iff`).  The teeth of S3
are computational: the leaky winner `leakForger` is choice-free, the witness here is not an
algorithm.  Nothing here says that an EFFICIENT non-leaky forger exists; that is the CDH
question. -/
theorem exists_forger_of_leaky (g : G) (mstar : M) (Adv : F × ForgerInput G M → PMF G) :
    ∃ Adv' : ForgerInput G M → PMF G,
      forgeExp F g mstar Adv' = forgeExpLeaky F g mstar Adv := by
  by_cases hg0 : g = 0
  · subst hg0
    refine ⟨fun x => (unif F).bind fun e => Adv (e, x), ?_⟩
    unfold forgeExp forgeExpLeaky
    refine congrArg _ (funext fun k => ?_)
    -- over the trivial base point the tables do not depend on the exponents
    have hH : ∀ h : M → F, roHash (0 : G) h = fun _ => 0 := fun h =>
      funext fun m => smul_zero _
    simp only [hH]
    rw [PMF.bind_const, PMF.map_bind]
    exact (unif_bind_eval mstar (fun e =>
      (Adv (e, k • (0 : G), (fun _ => 0), knownSigs (fun _ => (0 : G)) k mstar)).map
        fun σ => decide (σ = prf (fun _ => (0 : G)) k mstar))).symm
  · exact ⟨dlogForgerOfLeaky g mstar Adv, forgeExp_dlogForgerOfLeaky hg0 mstar Adv⟩

/-- The outcome distributions achievable in the leaky experiment are exactly those achievable in
the forgery experiment: as far as arbitrary (unbounded) forgers are concerned the two experiments
are the same.  See `exists_forger_of_leaky` for what this does and does not mean. -/
theorem forgeExpLeaky_achievable_iff (g : G) (mstar : M) (d : PMF Bool) :
    (∃ Adv : F × ForgerInput G M → PMF G, forgeExpLeaky F g mstar Adv = d) ↔
      ∃ Adv : ForgerInput G M → PMF G, forgeExp F g mstar Adv = d := by
  constructor
  · rintro ⟨Adv, rfl⟩
    exact exists_forger_of_leaky g mstar Adv
  · rintro ⟨Adv, rfl⟩
    exact ⟨fun x => Adv x.2, forgeExpLeaky_ignore g mstar Adv⟩

end Leaky

/-! ## H. Non-vacuity: a model of all hypotheses -/

section NonVacuity

variable (p : ℕ) [Fact p.Prime]

/-- A model of the algebraic setting: `F = G = ZMod p` with generator `g = 1`.  All typeclass
hypotheses used in this file hold in it; the examples below instantiate the main theorems in it
(including the ones with a hypothesis on the session messages).  (This model is NOT a secure
group: see `forgeExp_zmod_mulForger`.) -/
theorem isGenerator_zmod_one : IsGenerator (ZMod p) (1 : ZMod p) :=
  ⟨one_ne_zero, fun x => ⟨x, by simp⟩⟩

/-- The reduction, instantiated in the model (two messages, target `true`). -/
example (Adv : ForgerInput (ZMod p) Bool → PMF (ZMod p)) :
    forgeExp (ZMod p) (1 : ZMod p) true Adv =
      cdhExp (ZMod p) (1 : ZMod p) (cdhSolver (ZMod p) (1 : ZMod p) true Adv) :=
  forge_eq_cdh _ _ _

/-- The random-oracle form of the experiment, instantiated in the model. -/
example (Adv : ForgerInput (ZMod p) Bool → PMF (ZMod p)) :
    forgeExp (ZMod p) (1 : ZMod p) true Adv = forgeExpUnifRO (ZMod p) (1 : ZMod p) true Adv :=
  forgeExp_eq_unifRO (isGenerator_zmod_one p) _ _

/-- The honest-but-curious reduction, instantiated in the model: three messages, target `0`,
two sessions on the messages `1` and `2`.  The hypothesis on the session messages is
satisfiable. -/
example (AdvA : ZMod p × (Fin 3 → ZMod p) × (Fin 2 → Fin 3 × (ZMod p)ˣ × ZMod p) →
    PMF (ZMod p)) :
    hbcExp (ZMod p) (1 : ZMod p) (0 : Fin 3) ![1, 2] AdvA =
      cdhExp (ZMod p) (1 : ZMod p)
        (cdhSolver (ZMod p) (1 : ZMod p) (0 : Fin 3) (forgerOfHbc (ZMod p) ![1, 2] AdvA)) :=
  hbc_eq_cdh _ _ _ (by decide) _

/-- The eavesdropper reduction, instantiated in the model: three messages, target `0`, two
observed sessions, one of them ON THE TARGET. -/
example (Adv : ForgerInput (ZMod p) (Fin 3) × (Fin 2 → ZMod p × ZMod p) → PMF (ZMod p)) :
    eavesdropExp (ZMod p) (1 : ZMod p) (0 : Fin 3) ![0, 1] Adv =
      cdhExp (ZMod p) (1 : ZMod p)
        (cdhSolver (ZMod p) (1 : ZMod p) (0 : Fin 3)
          (forgerOfEavesdropper (ZMod p) (1 : ZMod p) ![0, 1] Adv)) :=
  eavesdrop_eq_cdh _ _ _ _

/-- The passive reduction, instantiated in the model: three messages, target `0`, own sessions
on the messages `1` and `2`, one observed session on the target. -/
example (Adv : (ZMod p × (Fin 3 → ZMod p) × (Fin 2 → Fin 3 × (ZMod p)ˣ × ZMod p)) ×
    (Fin 1 → ZMod p × ZMod p) → PMF (ZMod p)) :
    passiveExp (ZMod p) (1 : ZMod p) (0 : Fin 3) ![1, 2] ![0] Adv =
      cdhExp (ZMod p) (1 : ZMod p)
        (cdhSolver (ZMod p) (1 : ZMod p) (0 : Fin 3)
          (forgerOfPassive (ZMod p) (1 : ZMod p) ![1, 2] ![0] Adv)) :=
  passive_eq_cdh _ _ _ (by decide) _ _

/-- The exact value of S2, instantiated in the model. -/
example (σ₀ : ZMod p) (hσ : σ₀ ≠ 0) :
    forgeExp (ZMod p) (1 : ZMod p) true (fun _ : ForgerInput (ZMod p) Bool => PMF.pure σ₀) true =
      ((Fintype.card (ZMod p) - 1 : ℕ) : ℝ≥0∞) / (Fintype.card (ZMod p) : ℝ≥0∞) ^ 2 :=
  forgeExp_const_of_ne_zero (isGenerator_zmod_one p) true hσ

/-- A copying forger, instantiated in the model: echoing the signature on `false` as a forgery
on `true`. -/
example :
    forgeExp (ZMod p) (1 : ZMod p) true
        (fun x : ForgerInput (ZMod p) Bool => PMF.pure (x.2.2 false)) true =
      ((2 * Fintype.card (ZMod p) - 1 : ℕ) : ℝ≥0∞) / (Fintype.card (ZMod p) : ℝ≥0∞) ^ 2 :=
  forgeExp_copy_sig one_ne_zero (by decide)

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
