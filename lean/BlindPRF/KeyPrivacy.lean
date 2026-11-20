/-
  BlindPRF/KeyPrivacy.lean — what party A learns about party B's key `k`.

  HONESTY POINT FIRST.  Party A is *supposed* to receive the signature `σ = k • H m`.  In a group
  of prime order that single value already determines `k` information-theoretically (as soon as
  `H m ≠ 0`).  So "A learns nothing about `k`" is FALSE as an information-theoretic statement, for
  this protocol and for every other protocol that computes the same function.  It is not claimed
  anywhere in this file; section C proves the opposite.

  What is proved instead:

  * A. Simulation (any module, no generator hypothesis).  Everything A sees in a session is
       reproduced, as an equality of values, by an explicit simulator that is handed the signature
       `σ` and nothing else: the protocol transcript gives A nothing beyond its legitimate output.
  * B. A dishonest A that sends an arbitrary group element still gets exactly one value
       `k • a`, i.e. one signature scaled by a scalar that depends on A's query only, not on the
       key.  (Security against such an A is the one-more Diffie–Hellman assumption, which is NOT
       proved here.  The type `G` models *validated* elements of the prime-order group; a B that
       does not check group membership is outside this model.)  The one class of deviating A that
       IS reduced to the public key is in F: queries whose exponents in base `g` are chosen by
       A (`keyGoalKE_eq_pkGoal`, and the `send` nodes of `keyGoalOracle_eq_pkGoal`); queries
       involving the public key or B's earlier replies are not.
  * C. Negative results: the signature, hence A's view, determines the key; a key extractor
       exists as a function; no correct protocol for this function can hide the key perfectly.
  * D. The programmed random oracle `H m = h m • g` with uniform exponents `h` IS a uniformly
       random hash function into a group with generator `g`.  Also: a uniformly random table
       restricted to distinct query points is a uniformly random table on those points.
  * E. All of A's sessions, together with the public key `k • g` and even the oracle exponents,
       are reproduced from the public key alone by an explicit simulator.
  * F. The reduction.  For ANY goal about the key (any function of the key and of the adversary's
       output: exact recovery, one bit of the key, ...) the experiment in which an
       honest-but-curious A runs any number of sessions is EQUAL, as a distribution, to the
       experiment in which an explicit solver built from the adversary is given the public key
       `k • g` and nothing else (`keyGoal_eq_pkGoal`).  Exact key recovery is the special case
       "discrete logarithm" (`keyRecovery_eq_dlog`).  Variants, all Lean theorems:
       messages depending on the public key, the oracle exponents and the coins (built in);
       messages depending on the replies of earlier sessions (`keyGoalInteractive_eq_pkGoal`);
       an independent random tape shared by message selection and adversary
       (`keyGoal_mixture_eq_pkGoal`); the genuine random-oracle experiment, no exponents shown
       (`keyGoalRO_eq_pkGoal`, `keyGoalROInteractive_eq_pkGoal`, `keyRecoveryRO_eq_dlog`); the
       oracle visible only at query points declared in advance, with a solver that samples one
       exponent per declared point (`keyGoalQueried_eq_pkGoal`); a deviating A whose queries
       have known exponents (`keyGoalKE_eq_pkGoal`); and, in a different adversary model, an A
       given as a strategy tree with ADAPTIVE access to the oracle and to B, against a solver
       that samples the oracle LAZILY, one exponent per point actually touched
       (`keyGoalOracle_eq_pkGoal`; with hash values instead of exponents
       `keyGoalOracleRO_eq_pkGoal`, `keyRecoveryOracleRO_eq_dlog`).
  * G. Sanity checks: the experiments are not degenerate (an unbounded solver wins with
       certainty, a guess independent of the public key wins with probability exactly `1/|F|`),
       and a strawman protocol that leaks `k` is separated from the real one by two theorems
       (`leaky_not_simulable`, `keyRecovery_zero_lt_leaky`) whose limits are stated there.

  MODELLING LIMITS OF SECTION F (read these before quoting it).

  * The random oracle is ONE FINITE TABLE (`[Fintype M]`), sampled up front.  In the experiments
    whose adversary is a function of a view (`keyGoalExp`, `keyRecoveryExp`, their `RO`,
    `Interactive` and `KE` variants) the table is handed to the adversary in full and the solvers
    `pkSolver` / `dlogSolver` / `pkSolverKE` sample that whole table: `|M|` scalars.  Read
    literally those solvers are efficient only when the table is small; for a realistic message
    space (say 256-bit strings) they are exponential.  The remedy is lazy sampling (one scalar
    per oracle query).  It is formalised in two forms: statically (`keyGoalQueried_eq_pkGoal`: the
    points at which the oracle is ever looked at are fixed in advance) and adaptively
    (`keyGoalOracle_eq_pkGoal`: the adversary is a strategy tree that queries the oracle and B
    one step at a time; the solver `lazySolver` samples an exponent only when a new point is
    touched, and is defined even for an infinite message space).  The adaptive form restricts
    the adversary to a deterministic decision tree plus an independent random tape; its
    continuations are arbitrary functions.
  * "Proportional to the number of queries" is nowhere a theorem.  It is what one reads off
    `Strategy.runLazy`.  The cache there is a function `M → Option F`; an implementation would
    use a finite map.
  * Goals are about the key only: functions of the key and of the adversary's output.  Where the
    adversary is handed the oracle exponents it can sign every message from the public key
    (`prf_progHash`), so forgery-type goals are meaningless there.  They are out of scope of this
    file in every experiment, including those that show hash values only.
  * A is honest-but-curious: it sends blinded hashes.  The only deviation covered is a query
    `x • g` whose exponent `x` A chose itself (`keyGoalKE_eq_pkGoal`; `send` nodes in
    `keyGoalOracle_eq_pkGoal`).  A query built from the public key or from earlier replies makes
    B a static Diffie–Hellman oracle; nothing is proved about that regime (see B).
  * The mere existence of a solver is not the content of the reduction: with arbitrary functions
    as solvers even the leaky strawman "reduces to discrete log"
    (`keyRecoveryGame_leaky_eq_dlog_unbounded`).  The content is the explicit form of the solver.

  No hardness assumption (discrete log, DDH, one-more-DH) is proved or assumed anywhere.  Lean has
  no cost model: "the simulator / the solver is efficient" is a claim to be checked by reading
  the definitions `simReply`, `viewsSim`, `viewsKESim`, `pkSolver`, `pkSolverKE`, `dlogSolver`,
  `Strategy.runLazy`, `lazySolver`; the docstrings of `pkSolver` and `Strategy.runLazy` list what
  they do.  None of them takes `k` or a discrete logarithm as input.  The solvers call the
  message-selection rule, the adversary and the strategy's continuations as black boxes, so they
  are only as efficient as those are.

  Everything lives in the namespace `BlindPRF.KeyPrivacy`.
-/
import BlindPRF.Correctness
import BlindPRF.Prob

namespace BlindPRF

namespace KeyPrivacy

open scoped ENNReal

variable {F G M : Type*} [Field F] [AddCommGroup G] [Module F G]

/-! ## A. Simulation: the transcript gives A nothing beyond the signature -/

section Simulation

/-- The simulator's version of B's reply: given A's own coin `r` and the signature `σ` (A's
legitimate output), compute `r • σ`.  One scalar multiplication; the key is not an input. -/
def simReply (r : Fˣ) (σ : G) : G := (r : F) • σ

/-- The simulator for A's whole view of one session.  Inputs: A's message, A's coin and the
signature `σ`.  The key `k` is not an input and no discrete logarithm is taken. -/
def simViewA (m : M) (r : Fˣ) (σ : G) : M × Fˣ × G := (m, r, simReply r σ)

/-- B's reply to an honest query is the signature re-blinded with A's own coin.

Meaning: the one message A receives is a function of things A is entitled to (its coin `r` and
its output `σ = prf H k m`).  This is an equality of group elements, valid in every module; it
says nothing about how hard it is to get `k` out of `σ` (see section C: it is information-
theoretically possible). -/
theorem reply_eq_simReply (H : M → G) (k : F) (m : M) (r : Fˣ) :
    evaluate k (blind H m r) = simReply r (prf H k m) := by
  simp only [evaluate, blind, simReply, prf]
  exact smul_comm _ _ _

/-- **Simulation of A's view (one session).**  For every hash function, key, message and coin,
A's real view equals the output of the explicit simulator `simViewA` run on the signature.

What this means: the protocol leaks to an honest-but-curious A *nothing beyond the signature
itself*.  The content of the theorem is that `simViewA` is an explicit term that uses one scalar
multiplication and has no access to `k`; Lean has no cost model, so "the simulator is efficient"
is established by inspecting the definition, not by a theorem.

What this does NOT mean: it does not say that A learns nothing about `k`.  The signature itself
determines `k` (`prf_injective_key`, `exists_key_extractor`). -/
theorem viewA_eq_simViewA (H : M → G) (k : F) (m : M) (r : Fˣ) :
    viewA H k m r = simViewA m r (prf H k m) := by
  simp only [viewA, simViewA, reply_eq_simReply]

/-- The view depends on the key only through the signature: two keys that sign `m` identically
give A identical views.  (When `H m ≠ 0` two such keys are in fact equal, by `prf_injective_key`,
so read on its own this corollary is informative only when `H m = 0`.  Its role is to be the
"nothing beyond σ" half of `viewA_eq_iff_prf_eq`.) -/
theorem viewA_eq_of_prf_eq {H : M → G} {k k' : F} {m : M} (r : Fˣ)
    (h : prf H k m = prf H k' m) : viewA H k m r = viewA H k' m r := by
  rw [viewA_eq_simViewA, viewA_eq_simViewA, h]

/-- A's view carries *exactly* the signature: views under two keys coincide if and only if the
signatures coincide.  So the view is neither more nor less informative about the key than the
legitimate output. -/
theorem viewA_eq_iff_prf_eq (H : M → G) (k k' : F) (m : M) (r : Fˣ) :
    viewA H k m r = viewA H k' m r ↔ prf H k m = prf H k' m := by
  refine ⟨fun h => ?_, viewA_eq_of_prf_eq r⟩
  have h2 := congrArg (fun v : M × Fˣ × G => unblind r v.2.2) h
  simpa only [viewA, unblind_evaluate_blind] using h2

/-- Simulation against a randomized adversary, for an arbitrary distribution of A's coin:
whatever a (possibly randomized, computationally unbounded) procedure `Adv` computes from the
real view, it computes with the same distribution from the simulated view. -/
theorem adv_viewA_eq_adv_simViewA_of_coins {β : Type*} (coins : PMF Fˣ) (H : M → G) (k : F)
    (m : M) (Adv : M × Fˣ × G → PMF β) :
    (coins.bind fun r => Adv (viewA H k m r)) =
      coins.bind fun r => Adv (simViewA m r (prf H k m)) := by
  simp only [viewA_eq_simViewA]

/-- **Simulation against a randomized adversary (uniform coin).**  The output distribution of
any adversary run on A's real view (coin `r` uniform among the nonzero scalars) equals its output
distribution on the simulated view, which is computed from the signature alone.

The simulator is the explicit term `simViewA`; it uses one scalar multiplication and no knowledge
of `k`.  "Efficient" is by inspection of that definition (Lean has no cost model).  This does NOT
say the adversary cannot compute `k`: it says that anything it computes from a protocol run it
could have computed from the signature. -/
theorem adv_viewA_eq_adv_simViewA {β : Type*} [Fintype F] [DecidableEq F] (H : M → G) (k : F)
    (m : M) (Adv : M × Fˣ × G → PMF β) :
    ((unif Fˣ).bind fun r => Adv (viewA H k m r)) =
      (unif Fˣ).bind fun r => Adv (simViewA m r (prf H k m)) :=
  adv_viewA_eq_adv_simViewA_of_coins _ H k m Adv

/-- The distribution of A's real view equals the distribution of the simulated view. -/
theorem viewA_dist_eq_simViewA_dist [Fintype F] [DecidableEq F] (H : M → G) (k : F) (m : M) :
    (unif Fˣ).map (viewA H k m) = (unif Fˣ).map fun r => simViewA m r (prf H k m) := by
  congr 1
  funext r
  exact viewA_eq_simViewA H k m r

/-- Many sessions with an arbitrary hash function: the family of A's views is the family of
simulated views, each computed from the corresponding signature. -/
theorem viewsA_eq_simViewsA {ι : Type*} (H : M → G) (k : F) (ms : ι → M) (rs : ι → Fˣ) :
    (fun i => viewA H k (ms i) (rs i)) = fun i => simViewA (ms i) (rs i) (prf H k (ms i)) :=
  funext fun i => viewA_eq_simViewA H k (ms i) (rs i)

end Simulation

/-! ## B. A dishonest A: one query is one scaled signature -/

section Malicious

/-- If A deviates and sends `c • H m'` for a scalar `c` and message `m'` of its choice, B's reply
is the signature on `m'` scaled by `c`.  Valid in every module. -/
theorem evaluate_smul_hash (H : M → G) (k c : F) (m : M) :
    evaluate k (c • H m) = c • prf H k m := by
  simp only [evaluate, prf]
  exact smul_comm _ _ _

/-- **A malicious query is one scaled signature, with a scalar that does not depend on the key.**
In a prime-order group with generator `g`, if `H m ≠ 0` then *every* group element `a` that a
dishonest A might send is `c • H m` for some scalar `c`, and for EVERY key `k` B's reply is then
`c • prf H k m`.  The scalar is determined by A's query alone (it is unique:
`malicious_query_scalar_unique`).

Meaning: each interaction gives A exactly one evaluation of the map `P ↦ k • P` at a point of A's
choosing, which for a computationally unbounded party is the same information as one signature
scaled by a scalar fixed by the query.

What this does NOT claim.  The scalar `c` is only shown to exist; a real attacker who picks `a`
cleverly need not know it.  Security against such an A (it cannot produce more valid signatures
than it made queries) is the *one-more Diffie–Hellman* assumption.  Moreover an oracle for
`P ↦ k • P` (a "static Diffie–Hellman oracle") is known to weaken the discrete logarithm problem
quantitatively (Brown–Gallant, Cheon).  None of that is proved, assumed or quantified here.

Modelling caveat.  The type `G` models *validated* elements of the prime-order group: the
hypothesis `IsGenerator F g` says every element B can receive is a multiple of `g`.  An
implementation in which B does not check group membership (cofactor groups, invalid-curve points,
small-subgroup elements) is outside this model, and the generator hypothesis cannot be dropped:
see the two-dimensional counterexample at the end of the file. -/
theorem malicious_query_scalar_indep_of_key {g : G} (hg : IsGenerator F g) (H : M → G) {m : M}
    (hm : H m ≠ 0) :
    ∀ a : G, ∃ c : F, a = c • H m ∧ ∀ k : F, evaluate k a = c • prf H k m := by
  intro a
  obtain ⟨c, rfl⟩ := (hg.of_ne_zero hm).spans a
  exact ⟨c, rfl, fun k => evaluate_smul_hash H k c m⟩

/-- **A malicious query is one (scaled) signature.**  The form with the key fixed first; it is a
consequence of the stronger `malicious_query_scalar_indep_of_key`, where the scalar is shown not
to depend on the key.  In a prime-order group with generator `g`, if `H m ≠ 0` then every group
element `a` that a dishonest A might send is `c • H m` for some scalar `c`, and B's reply is
`c • prf H k m`.

The same non-claims apply: `c` is only shown to exist; security against such an A is the one-more
Diffie–Hellman assumption; a static Diffie–Hellman oracle weakens the discrete logarithm problem
quantitatively (Brown–Gallant, Cheon); none of that is proved or assumed here.  `G` models
validated group elements only (see `malicious_query_scalar_indep_of_key`). -/
theorem malicious_query_is_one_signature {g : G} (hg : IsGenerator F g) (H : M → G) (k : F)
    {m : M} (hm : H m ≠ 0) :
    ∀ a : G, ∃ c : F, a = c • H m ∧ evaluate k a = c • prf H k m := by
  intro a
  obtain ⟨c, hc, hk⟩ := malicious_query_scalar_indep_of_key hg H hm a
  exact ⟨c, hc, hk k⟩

/-- The scalar in `malicious_query_is_one_signature` is unique. -/
theorem malicious_query_scalar_unique {g : G} (hg : IsGenerator F g) (H : M → G) {m : M}
    (hm : H m ≠ 0) (a : G) : ∃! c : F, a = c • H m := by
  obtain ⟨c, rfl⟩ := (hg.of_ne_zero hm).spans a
  exact ⟨c, rfl, fun c' hc' => ((hg.of_ne_zero hm).smul_injective hc').symm⟩

end Malicious

/-! ## C. Negative results: perfect key hiding is impossible -/

section Negative

/-- **The signature determines the key.**  If `H m ≠ 0`, distinct keys give distinct signatures
on `m`.  (Holds in every module over a field; no generator hypothesis is needed.)

This is a LIMITATION, stated on purpose: perfect (information-theoretic) key hiding against A is
impossible, because A's legitimate output already pins down `k`.  Key hiding can only be
computational. -/
theorem prf_injective_key (H : M → G) {m : M} (hm : H m ≠ 0) :
    Function.Injective fun k : F => prf H k m := by
  intro k k' h
  have h0 : (k - k') • H m = 0 := by
    rw [sub_smul]
    exact sub_eq_zero.mpr h
  rcases smul_eq_zero.mp h0 with h1 | h1
  · exact sub_eq_zero.mp h1
  · exact absurd h1 hm

/-- **A key extractor exists.**  If `H m ≠ 0` there is a function recovering the key from a
single signature on `m`.

This is a LIMITATION: an unbounded A learns `k` from one honest session.  The function `ext` is
obtained non-constructively; computing it is a discrete-logarithm computation (see
`key_eq_dlog_div`), and nothing here says that it is easy or hard. -/
theorem exists_key_extractor (H : M → G) {m : M} (hm : H m ≠ 0) :
    ∃ ext : G → F, ∀ k, ext (prf H k m) = k :=
  (prf_injective_key H hm).hasLeftInverse

/-- In a prime-order group the extractor is a quotient of two discrete logarithms:
`k = log_g σ / log_g (H m)`. -/
theorem key_eq_dlog_div {g : G} (hg : IsGenerator F g) (H : M → G) {m : M} (hm : H m ≠ 0)
    (k : F) : hg.equiv.symm (prf H k m) / hg.equiv.symm (H m) = k := by
  have hx : hg.equiv.symm (H m) ≠ 0 := by
    intro h0
    apply hm
    rw [← hg.smul_equiv_symm (H m), h0, zero_smul]
  have hσ : hg.equiv.symm (prf H k m) = k * hg.equiv.symm (H m) := by
    apply hg.smul_injective
    simp only [prf]
    rw [hg.smul_equiv_symm, mul_smul, hg.smul_equiv_symm]
  rw [hσ, mul_div_assoc, div_self hx, mul_one]

/-- A's view of a single honest session determines the key (if `H m ≠ 0`): for every fixed coin,
views under distinct keys are distinct. -/
theorem viewA_injective_key (H : M → G) {m : M} (hm : H m ≠ 0) (r : Fˣ) :
    Function.Injective fun k : F => viewA H k m r := by
  intro k k' h
  exact prf_injective_key H hm ((viewA_eq_iff_prf_eq H k k' m r).mp h)

/-- **Views under different keys never coincide.**  If `H m ≠ 0` and `k ≠ k'`, then no view A can
have with key `k` (whatever the coin) equals a view it can have with key `k'` (whatever the
coin).  The distribution-level form is `viewA_supports_disjoint`: the opposite of "A's view is
independent of the key". -/
theorem viewA_ne_of_key_ne (H : M → G) {m : M} (hm : H m ≠ 0) {k k' : F} (hk : k ≠ k')
    (r r' : Fˣ) : viewA H k m r ≠ viewA H k' m r' := by
  intro h
  have hr : r = r' := congrArg (fun v : M × Fˣ × G => v.2.1) h
  subst hr
  exact hk (viewA_injective_key H hm r h)

/-- **The view distributions under two different keys have disjoint supports**, whatever the
distributions of A's coin in the two worlds.  So the two distributions are perfectly
distinguishable (statistical distance 1, although that number is not computed here): A's view is
as far from "independent of the key" as it can be.  A LIMITATION, stated on purpose. -/
theorem viewA_supports_disjoint_of_coins (coins coins' : PMF Fˣ) (H : M → G) {m : M}
    (hm : H m ≠ 0) {k k' : F} (hk : k ≠ k') :
    Disjoint (coins.map (viewA H k m)).support (coins'.map (viewA H k' m)).support := by
  rw [Set.disjoint_left]
  intro v hv hv'
  rw [PMF.support_map] at hv hv'
  obtain ⟨r, -, rfl⟩ := hv
  obtain ⟨r', -, h⟩ := hv'
  exact viewA_ne_of_key_ne H hm hk r r' h.symm

/-- `viewA_supports_disjoint_of_coins` for the protocol's own coin distribution (uniform on the
nonzero scalars). -/
theorem viewA_supports_disjoint [Fintype F] [DecidableEq F] (H : M → G) {m : M} (hm : H m ≠ 0)
    {k k' : F} (hk : k ≠ k') :
    Disjoint ((unif Fˣ).map (viewA H k m)).support ((unif Fˣ).map (viewA H k' m)).support :=
  viewA_supports_disjoint_of_coins _ _ H hm hk

/-- **No correct protocol hides the key perfectly.**  Take *any* two-party protocol, described
abstractly by A's view `view k ω` (as a function of the key and of all the randomness `ω` in the
execution) and A's output function `out`.  If the protocol is correct, i.e. A always outputs
`prf H k m`, and `H m ≠ 0`, then A's view determines the key.

So the impossibility of information-theoretic key hiding is a property of the *function*
`(k, m) ↦ k • H m` being computed, not a defect of this particular protocol. -/
theorem no_protocol_hides_key_perfectly {Ω V : Type*} (H : M → G) {m : M} (hm : H m ≠ 0)
    (view : F → Ω → V) (out : V → G) (hcorrect : ∀ k ω, out (view k ω) = prf H k m) :
    ∃ ext : V → F, ∀ k ω, ext (view k ω) = k := by
  obtain ⟨ext, hext⟩ := exists_key_extractor (F := F) H hm
  refine ⟨fun v => ext (out v), fun k ω => ?_⟩
  show ext (out (view k ω)) = k
  rw [hcorrect, hext]

/-- The previous theorem applies to the protocol of this development: there is a function that
recovers the key from A's view of one honest session (if `H m ≠ 0`), whatever the coin. -/
theorem exists_key_extractor_from_view (H : M → G) {m : M} (hm : H m ≠ 0) :
    ∃ ext : M × Fˣ × G → F, ∀ (k : F) (r : Fˣ), ext (viewA H k m r) = k :=
  no_protocol_hides_key_perfectly H hm (fun k r => viewA H k m r)
    (fun v => unblind v.2.1 v.2.2) fun k r => unblind_evaluate_blind H k m r

end Negative

/-! ## D. The programmed random oracle -/

section Programmed

/-- The programmed hash function: the hash of `m` is `h m • g`, where the table of exponents
`h : M → F` is known to whoever programs the oracle (the reduction), not to the parties. -/
def progHash (g : G) (h : M → F) : M → G := fun m => h m • g

@[simp]
theorem progHash_apply (g : G) (h : M → F) (m : M) : progHash g h m = h m • g := rfl

/-- With a programmed hash, the signature is computable from the public key `k • g` and the
exponent `h m`, without the key.  This is the algebraic fact behind the simulation in section E.

It is also the reason why section F is about goals concerning the key only: whoever knows the
exponents can sign every message from the public key, so "forgery" is trivial there. -/
theorem prf_progHash (g : G) (h : M → F) (k : F) (m : M) :
    prf (progHash g h) k m = h m • (k • g) := by
  simp only [prf, progHash]
  exact smul_comm _ _ _

/-- B's reply to an honest query under a programmed hash, computed from the public key. -/
theorem evaluate_blind_progHash (g : G) (k : F) (h : M → F) (m : M) (r : Fˣ) :
    evaluate k (blind (progHash g h) m r) = ((r : F) * h m) • (k • g) := by
  simp only [evaluate, blind, progHash, smul_smul]
  rw [mul_comm]

/-- **The programmed oracle is a true random oracle.**  If `g` generates the group, then sampling
the exponent table `h : M → F` uniformly and setting `H m = h m • g` gives exactly the uniform
distribution on hash functions `M → G`.

So an experiment in the programmed model has the same distribution as the experiment with a
uniformly random hash function; programming loses nothing.  (This is a statement about
distributions only; that the map `h ↦ progHash g h` is hard to invert is the discrete logarithm
assumption and is not claimed.  The oracle is one finite table: `M` is a finite type.) -/
theorem progHash_uniform [Fintype M] [DecidableEq M] [Fintype F] [Fintype G] {g : G}
    (hg : IsGenerator F g) : (unif (M → F)).map (progHash g) = unif (M → G) :=
  unif_map_equiv (Equiv.piCongrRight fun _ : M => hg.equiv)

end Programmed

/-! ### Restricting a uniform table to distinct points -/

section Restriction

/-- **Lazy sampling, static form.**  A uniformly random table `M → α`, looked at only at the
pairwise distinct points `qs : κ → M`, is a uniformly random table `κ → α`.

So an experiment that touches the oracle only at points fixed in advance may sample one value per
point instead of the whole table.  This does NOT cover points chosen adaptively (as a function of
earlier oracle answers); for those see `unif_bind_update` and `keyGoalOracle_eq_pkGoal`. -/
theorem unif_comp_injective {X κ α : Type*} [Fintype X] [DecidableEq X] [Fintype κ]
    [DecidableEq κ] [Fintype α] [Nonempty α] {qs : κ → X} (hqs : Function.Injective qs) :
    (unif (X → α)).map (fun h : X → α => h ∘ qs) = unif (κ → α) := by
  classical
  let e : (X → α) ≃ (κ → α) × ({x : X // x ∉ Set.range qs} → α) :=
    (Equiv.piEquivPiSubtypeProd (fun x => x ∈ Set.range qs) (fun _ => α)).trans
      (Equiv.prodCongr (Equiv.arrowCongr (Equiv.ofInjective qs hqs).symm (Equiv.refl α))
        (Equiv.refl _))
  exact unif_map_of_equiv_prod e _ fun h => by
    funext i
    simp [e]

end Restriction

/-! ## E. Simulating all of A's sessions from the public key alone -/

section Sessions

variable {ι : Type*}

/-- A's total view of a family of sessions indexed by `ι`, in the programmed model:
`(public key, oracle exponents, messages, coins, replies)`.  Note that the oracle exponents are
*more* than a real A sees (a real A sees only the hash values `h m • g`). -/
abbrev View (F G M ι : Type*) [Monoid F] : Type _ :=
  G × (M → F) × (ι → M) × (ι → Fˣ) × (ι → G)

/-- The real total view: B has key `k`, the hash is programmed with exponents `h`, A (honestly)
blinds message `ms i` with coin `rs i` in session `i`. -/
def viewsReal (g : G) (k : F) (h : M → F) (ms : ι → M) (rs : ι → Fˣ) : View F G M ι :=
  (k • g, h, ms, rs, fun i => evaluate k (blind (progHash g h) (ms i) (rs i)))

/-- The simulated total view, computed from the *public key* `pk` instead of the key: the reply
in session `i` is `(rs i * h (ms i)) • pk`.  One field multiplication and one scalar
multiplication per session; neither `k` nor any discrete logarithm is an input. -/
def viewsSim (pk : G) (h : M → F) (ms : ι → M) (rs : ι → Fˣ) : View F G M ι :=
  (pk, h, ms, rs, fun i => ((rs i : F) * h (ms i)) • pk)

/-- **Simulation of all sessions from the public key.**  Pointwise (for all values of the key,
the oracle exponents, the messages and the coins, with no probability involved) A's real total
view equals the simulated one computed from the public key `k • g`.

Holds in every module, for any index type of sessions.  It covers an A that blinds honestly; it
says nothing about an A that sends other group elements (section B). -/
theorem viewsReal_eq_viewsSim (g : G) (k : F) (h : M → F) (ms : ι → M) (rs : ι → Fˣ) :
    viewsReal g k h ms rs = viewsSim (k • g) h ms rs := by
  simp only [viewsReal, viewsSim, evaluate_blind_progHash]

/-- The multi-session simulator is the one-session simulator `simReply` of section A, fed with
the signature `h (ms i) • pk` that it computes from the public key (cf. `prf_progHash`). -/
theorem viewsSim_reply_eq_simReply (pk : G) (h : M → F) (ms : ι → M) (rs : ι → Fˣ) (i : ι) :
    (viewsSim pk h ms rs).2.2.2.2 i = simReply (rs i) (h (ms i) • pk) :=
  mul_smul _ _ _

/-! ### Views with a plain hash table (used for the genuine random-oracle experiment) -/

/-- A's total view when the hash function is an arbitrary table `H : M → G` (no exponents):
`(public key, hash table, messages, coins, replies)`.  Handing the adversary the whole table is
at least as generous as oracle access. -/
abbrev ViewRO (F G M ι : Type*) [Monoid F] : Type _ :=
  G × (M → G) × (ι → M) × (ι → Fˣ) × (ι → G)

/-- The real total view with hash table `H`. -/
def viewsRO (g : G) (k : F) (H : M → G) (ms : ι → M) (rs : ι → Fˣ) : ViewRO F G M ι :=
  (k • g, H, ms, rs, fun i => evaluate k (blind H (ms i) (rs i)))

/-- Forget the exponents: turn a programmed-model view into a view with a plain hash table. -/
def forgetExponents (g : G) (v : View F G M ι) : ViewRO F G M ι :=
  (v.1, progHash g v.2.1, v.2.2)

/-- With a programmed hash table, the plain view is the programmed view with the exponents
forgotten. -/
theorem viewsRO_progHash (g : G) (k : F) (h : M → F) (ms : ι → M) (rs : ι → Fˣ) :
    viewsRO g k (progHash g h) ms rs = forgetExponents g (viewsReal g k h ms rs) := rfl

/-! ### Queries with known exponents (views of a deviating A; the experiment is in section F) -/

/-- B's reply to the query `x • g`, computed from the public key. -/
theorem evaluate_smul_gen (g : G) (k x : F) : evaluate k (x • g) = x • (k • g) :=
  smul_comm _ _ _

/-- An honest query under a programmed hash is a multiple of the generator with exponent
`r * h m`. -/
theorem blind_progHash (g : G) (h : M → F) (m : M) (r : Fˣ) :
    blind (progHash g h) m r = ((r : F) * h m) • g := by
  simp only [blind, progHash, smul_smul]

/-- Every linear combination of the generator and of programmed hash values is a multiple of the
generator with an exponent computed from the coefficients and the oracle exponents.  So an A that
sends unblinded hashes, multiples of hashes (including `0`), sums of hashes or multiples of `g`
sends "queries with known exponents" in the sense of `viewsKE`. -/
theorem smul_add_sum_smul_progHash {J : Type*} (g : G) (h : M → F) (s : Finset J) (x₀ : F)
    (c : J → F) (ms : J → M) :
    x₀ • g + ∑ j ∈ s, c j • progHash g h (ms j) = (x₀ + ∑ j ∈ s, c j * h (ms j)) • g := by
  simp only [progHash, add_smul, Finset.sum_smul, mul_smul]

/-- Total view of a (possibly dishonest) A that, in session `i`, sends the group element
`xs i • g`: `(public key, oracle exponents, query exponents, replies)`. -/
abbrev ViewKE (F G M ι : Type*) : Type _ :=
  G × (M → F) × (ι → F) × (ι → G)

/-- The real total view of an A whose query in session `i` is `xs i • g`. -/
def viewsKE (g : G) (k : F) (h : M → F) (xs : ι → F) : ViewKE F G M ι :=
  (k • g, h, xs, fun i => evaluate k (xs i • g))

/-- The simulated view for known-exponent queries, from the public key: the reply to `x • g` is
`x • pk`.  One scalar multiplication per session; the key is not an input. -/
def viewsKESim (pk : G) (h : M → F) (xs : ι → F) : ViewKE F G M ι :=
  (pk, h, xs, fun i => xs i • pk)

/-- Pointwise simulation for known-exponent queries. -/
theorem viewsKE_eq_viewsKESim (g : G) (k : F) (h : M → F) (xs : ι → F) :
    viewsKE g k h xs = viewsKESim (k • g) h xs := by
  simp only [viewsKE, viewsKESim, evaluate_smul_gen]

/-- The honest sessions are the special case of known-exponent queries with exponents
`rs i * h (ms i)`: the replies coincide. -/
theorem viewsReal_replies_eq_viewsKE (g : G) (k : F) (h : M → F) (ms : ι → M) (rs : ι → Fˣ) :
    (viewsReal g k h ms rs).2.2.2.2 = (viewsKE g k h fun i => (rs i : F) * h (ms i)).2.2.2 := by
  funext i
  simp only [viewsReal, viewsKE, blind_progHash]

/-! ### A strawman protocol that leaks the key (used only in the sanity checks of section G) -/

/-- STRAWMAN (a deliberately bad protocol, for comparison only): B replies with `k • a` *and*
the key itself. -/
def leakyEvaluate (k : F) (a : G) : G × F := (evaluate k a, k)

/-- The strawman is still functionally correct: A can unblind the first component of the reply
and obtain the signature. -/
theorem unblind_leakyEvaluate (H : M → G) (k : F) (m : M) (r : Fˣ) :
    unblind r (leakyEvaluate k (blind H m r)).1 = prf H k m :=
  unblind_evaluate_blind H k m r

/-- The type of A's total view in the strawman protocol: as `View`, with replies in `G × F`. -/
abbrev ViewLeaky (F G M ι : Type*) [Monoid F] : Type _ :=
  G × (M → F) × (ι → M) × (ι → Fˣ) × (ι → G × F)

/-- A's total view in the strawman protocol. -/
def viewsLeaky (g : G) (k : F) (h : M → F) (ms : ι → M) (rs : ι → Fˣ) : ViewLeaky F G M ι :=
  (k • g, h, ms, rs, fun i => leakyEvaluate k (blind (progHash g h) (ms i) (rs i)))

end Sessions

/-! ### Sequential sessions: the list of replies seen so far -/

section History

variable {Msg Coin Rep : Type*} {n : ℕ}

/-- The replies of the first `j` sessions when A runs `n` sessions one after the other and picks
the message of each session with the rule `next`, applied to the list of replies received so
far.  `reply m r` is what B answers to the honest query for message `m` blinded with coin `r`.
(For `j ≥ n` the list stops growing.) -/
def replyHistory (reply : Msg → Coin → Rep) (next : List Rep → Msg) (rs : Fin n → Coin) :
    ℕ → List Rep
  | 0 => []
  | j + 1 => replyHistory reply next rs j ++
      (if hj : j < n then [reply (next (replyHistory reply next rs j)) (rs ⟨j, hj⟩)] else [])

/-- The messages A ends up using in the `n` sequential sessions: the message of session `i` is
`next` applied to the replies of sessions `0, …, i - 1`. -/
def interactiveMsgs (reply : Msg → Coin → Rep) (next : List Rep → Msg) (rs : Fin n → Coin) :
    Fin n → Msg :=
  fun i => next (replyHistory reply next rs i)

/-- Sanity check of the definition: after session `i` the history is the previous history
followed by B's reply to the message of session `i`. -/
theorem replyHistory_succ (reply : Msg → Coin → Rep) (next : List Rep → Msg) (rs : Fin n → Coin)
    (i : Fin n) :
    replyHistory reply next rs (i + 1) =
      replyHistory reply next rs i ++ [reply (interactiveMsgs reply next rs i) (rs i)] := by
  rw [replyHistory, dite_eq_left i.isLt]
  rfl

/-- Sanity check of the definition: before session `i` exactly `i` replies have been seen. -/
theorem replyHistory_length (reply : Msg → Coin → Rep) (next : List Rep → Msg)
    (rs : Fin n → Coin) (j : ℕ) : (replyHistory reply next rs j).length = min j n := by
  induction j with
  | zero => simp [replyHistory]
  | succ j ih =>
    rw [replyHistory, List.length_append, ih]
    split_ifs with hj
    · simp only [List.length_cons, List.length_nil]
      omega
    · simp only [List.length_nil]
      omega

end History

/-! ## F. The reduction: what A computes about the key, a solver computes from the public key -/

section Reduction

variable {ι β γ : Type*} [Fintype F] [DecidableEq F] [Fintype M] [DecidableEq M]
  [Fintype ι] [DecidableEq ι]

/-! ### The general statement: an arbitrary goal about the key -/

/-- The key-goal experiment against an honest-but-curious A, in the programmed random-oracle
model.  A uniformly random key `k`, a uniformly random table of oracle exponents `h` and uniform
nonzero coins `rs` are sampled; A runs one honest session per index `i : ι` on the messages
`choose (k • g) h rs` (chosen as a function of the public key, the oracle exponents and the
coins); the adversary sees the total view and outputs some `out : β`.  The result of the
experiment is `goal k out`: any function of the key and of the adversary's output.

Examples: `β = F`, `goal k k' = decide (k' = k)` is exact key recovery (`keyRecoveryExp`);
`β = Bool`, `goal k b = decide (b = bit k)` is "predict one bit of the key"; `goal = Prod.mk`
records the joint distribution of the key and the output. -/
noncomputable def keyGoalExp (g : G) (choose : G → (M → F) → (ι → Fˣ) → ι → M)
    (Adv : View F G M ι → PMF β) (goal : F → β → γ) : PMF γ :=
  (unif F).bind fun k => (unif (M → F)).bind fun h => (unif (ι → Fˣ)).bind fun rs =>
    (Adv (viewsReal g k h (choose (k • g) h rs) rs)).map (goal k)

/-- The same goal played from the public key alone: a uniformly random scalar `k` is sampled,
the solver `S` is given `k • g` and nothing else, and the result is `goal k out`. -/
noncomputable def pkGoalExp (g : G) (S : G → PMF β) (goal : F → β → γ) : PMF γ :=
  (unif F).bind fun k => (S (k • g)).map (goal k)

/-- The explicit solver built from an adversary.  On input `pk` it never sees `k`.  Inventory of
what it does (read off this definition; Lean has no cost model, so this is not a theorem):

* samples the oracle exponent table `h : M → F`, i.e. `|M|` scalars — the WHOLE table;
* samples `|ι|` nonzero coins;
* evaluates the message-selection rule `choose` once;
* builds the simulated view `viewsSim pk …`: `|ι|` field multiplications and `|ι|` scalar
  multiplications;
* runs the adversary once.

Because of the first item the solver is efficient, as written, only when the table `M` is small.
With lazy sampling the table costs one scalar per oracle query.  That is formalised for query
points fixed in advance (`keyGoalQueried_eq_pkGoal`, where the role of `M` is played by the set of
declared query points) and, for an adversary given as a strategy tree with adaptive oracle
access, by the different solver `lazySolver` (`keyGoalOracle_eq_pkGoal`).  For THIS solver, whose
adversary is an arbitrary function of the whole table, no lazy version exists. -/
noncomputable def pkSolver (choose : G → (M → F) → (ι → Fˣ) → ι → M)
    (Adv : View F G M ι → PMF β) : G → PMF β := fun pk =>
  (unif (M → F)).bind fun h => (unif (ι → Fˣ)).bind fun rs =>
    Adv (viewsSim pk h (choose pk h rs) rs)

/-- **Whatever A computes about the key from its sessions, a solver computes from the public key
alone, with exactly the same distribution.**  For every adversary `Adv`, every message-selection
rule `choose` and every goal `goal : F → β → γ`, the key-goal experiment equals the experiment in
which the explicit solver `pkSolver choose Adv` is given only `k • g`.

Taking `goal k k' = decide (k' = k)` gives exact key recovery = discrete logarithm
(`keyRecovery_eq_dlog`).  Taking a goal such as "guess one bit of `k`" shows that partial
information about the key is covered as well: whatever an adversary achieves about the key with
A's sessions, the wrapper `pkSolver` achieves with the public key alone (at the cost listed in
the docstring of `pkSolver`).  Taking `goal = Prod.mk` gives equality of the joint distributions
of (key, output) (`key_output_joint_eq`).

Scope: an honest-but-curious A (it blinds as prescribed), any finite number of sessions, messages
chosen as a function of the public key, the oracle exponents and the coins; the adversary is even
handed the oracle exponents and may be randomized and unbounded.  The equality holds in every
module (no generator hypothesis is needed for it).

What this does NOT claim.
* No hardness: it does not prove or assume that anything about `k` is hard to compute from
  `k • g`.  Under a generator hypothesis an unbounded solver computes `k` itself
  (`dlogExp_unbounded_solver`).
* No efficiency theorem: the cost of the solver is the inventory in the docstring of `pkSolver`;
  it includes sampling the whole oracle table.  (The reduction whose solver samples the oracle
  lazily is `keyGoalOracle_eq_pkGoal`.)
* Goals are functions of the key and the output only.  Forgery-type goals are out of scope: here
  the adversary is handed the exponents `h` and can sign every message from the public key
  (`prf_progHash`).
* It does not cover an A that sends non-blinded group elements (see
  `malicious_query_scalar_indep_of_key` and the remarks there; the one class of deviations that
  is covered, queries with known exponents, is `keyGoalKE_eq_pkGoal`). -/
theorem keyGoal_eq_pkGoal (g : G) (choose : G → (M → F) → (ι → Fˣ) → ι → M)
    (Adv : View F G M ι → PMF β) (goal : F → β → γ) :
    keyGoalExp g choose Adv goal = pkGoalExp g (pkSolver choose Adv) goal := by
  simp only [keyGoalExp, pkGoalExp, pkSolver, viewsReal_eq_viewsSim, PMF.map_bind]

/-- The joint distribution of (key, adversary's output) in A's sessions equals the joint
distribution of (key, solver's output) when the solver sees only the public key.  This is
`keyGoal_eq_pkGoal` for the goal that records everything; every other goal is a function of this
pair. -/
theorem key_output_joint_eq (g : G) (choose : G → (M → F) → (ι → Fˣ) → ι → M)
    (Adv : View F G M ι → PMF β) :
    keyGoalExp g choose Adv (fun k out => (k, out)) =
      pkGoalExp g (pkSolver choose Adv) fun k out => (k, out) :=
  keyGoal_eq_pkGoal g choose Adv _

/-- The converse (trivial) direction: an algorithm working from the public key is an adversary
with the same result distribution, because the public key is part of the view.  Together with
`keyGoal_eq_pkGoal`: in this model, for every goal about the key, A's sessions and the bare
public key give the same achievable distributions, up to the explicit wrappers `pkSolver` and
`fun v => S v.1` (whose cost is read off their definitions; no complexity statement is
formalised). -/
theorem pkGoal_eq_keyGoal (g : G) (choose : G → (M → F) → (ι → Fˣ) → ι → M) (S : G → PMF β)
    (goal : F → β → γ) :
    pkGoalExp g S goal = keyGoalExp g choose (fun v => S v.1) goal := by
  simp only [keyGoalExp, pkGoalExp, viewsReal, PMF.bind_const]

/-- **Randomized message selection, shared state.**  Let `ρ` be any distribution of a random
tape `ω`, independent of the key, the oracle and the coins, on which both the message-selection
rule and the adversary may depend.  The mixture of the key-goal experiments equals the
public-key experiment for the solver that samples `ω` itself.  (Same scope and non-claims as
`keyGoal_eq_pkGoal`.) -/
theorem keyGoal_mixture_eq_pkGoal {Ω : Type*} (ρ : PMF Ω) (g : G)
    (choose : Ω → G → (M → F) → (ι → Fˣ) → ι → M) (Adv : Ω → View F G M ι → PMF β)
    (goal : F → β → γ) :
    (ρ.bind fun ω => keyGoalExp g (choose ω) (Adv ω) goal) =
      pkGoalExp g (fun pk => ρ.bind fun ω => pkSolver (choose ω) (Adv ω) pk) goal := by
  simp only [keyGoal_eq_pkGoal, pkGoalExp, PMF.map_bind]
  exact PMF.bind_comm _ _ _

/-! ### Exact key recovery is the discrete-logarithm experiment -/

/-- The key-recovery experiment against an honest-but-curious A, in the programmed random-oracle
model.  A uniformly random key `k`, a uniformly random table of oracle exponents `h` and uniform
nonzero coins `rs` are sampled; A runs one honest session per index `i : ι` on the messages
`choose h` (chosen as a function of the oracle); the adversary sees the total view and outputs a
guess for the key.  The result is `true` iff the guess is the key. -/
noncomputable def keyRecoveryExp (g : G) (choose : (M → F) → ι → M)
    (Adv : View F G M ι → PMF F) : PMF Bool :=
  (unif F).bind fun k => (unif (M → F)).bind fun h => (unif (ι → Fˣ)).bind fun rs =>
    (Adv (viewsReal g k h (choose h) rs)).map fun k' => decide (k' = k)

/-- The discrete-logarithm experiment in base `g`: a uniformly random scalar `k` is sampled, the
solver `S` is given `k • g` and outputs a guess.  The result is `true` iff the guess is `k`. -/
noncomputable def dlogExp (g : G) (S : G → PMF F) : PMF Bool :=
  (unif F).bind fun k => (S (k • g)).map fun k' => decide (k' = k)

/-- The explicit discrete-logarithm solver built from a key-recovery adversary.  On input
`pk`, it samples the oracle exponents and the coins itself, builds the simulated view
`viewsSim pk …` and runs the adversary once on it.  It never sees `k`.

Inventory (read off the definition; no cost model): the WHOLE oracle exponent table (`|M|`
scalars), `|ι|` nonzero coins, `|ι|` field multiplications, `|ι|` scalar multiplications, one
evaluation of `choose`, one run of `Adv`.  It is `pkSolver` for a rule that ignores the public
key and the coins (`dlogSolver_eq_pkSolver`). -/
noncomputable def dlogSolver (choose : (M → F) → ι → M) (Adv : View F G M ι → PMF F) :
    G → PMF F := fun pk =>
  (unif (M → F)).bind fun h => (unif (ι → Fˣ)).bind fun rs => Adv (viewsSim pk h (choose h) rs)

/-- The key-recovery experiment is the key-goal experiment for the goal "the output is the
key" and a selection rule that ignores the public key and the coins. -/
theorem keyRecoveryExp_eq_keyGoalExp (g : G) (choose : (M → F) → ι → M)
    (Adv : View F G M ι → PMF F) :
    keyRecoveryExp g choose Adv =
      keyGoalExp g (fun _ h _ => choose h) Adv fun k k' => decide (k' = k) := rfl

/-- The discrete-logarithm experiment is the public-key experiment for the goal "the output is
the scalar". -/
theorem dlogExp_eq_pkGoalExp (g : G) (S : G → PMF F) :
    dlogExp g S = pkGoalExp g S fun k k' => decide (k' = k) := rfl

/-- `dlogSolver` is `pkSolver` for a selection rule that ignores the public key and the coins. -/
theorem dlogSolver_eq_pkSolver (choose : (M → F) → ι → M) (Adv : View F G M ι → PMF F) :
    dlogSolver choose Adv = pkSolver (fun _ h _ => choose h) Adv := rfl

/-- **Key recovery reduces to discrete logarithm, exactly.**  For every adversary `Adv`, the
key-recovery experiment has the same distribution as the discrete-logarithm experiment played by
the explicit solver `dlogSolver choose Adv`.  In particular the two winning probabilities (the
mass at `true`) are equal: an adversary that recovers B's key from A's side of the protocol with
probability `ε` yields a discrete-logarithm solver with probability exactly `ε`.

What the solver costs (by inspection of `dlogSolver`; Lean has no cost model): one run of the
adversary, `|ι|` coins, `|ι|` field multiplications, `|ι|` scalar multiplications, AND sampling
the whole oracle exponent table, `|M|` scalars.  So the reduction as literally stated is
efficient only for a small table `M`.  For a large message space one needs lazy sampling of the
oracle (one scalar per oracle query).  That is a different experiment and a different solver:
`keyGoalQueried_eq_pkGoal` (query points fixed in advance) and `keyRecoveryOracle_eq_dlog` /
`keyRecoveryOracleRO_eq_dlog` (adversary given as a strategy tree with adaptive oracle access).

Scope: an honest-but-curious A (it blinds as prescribed), any finite number of sessions, messages
chosen as a function of the random oracle; the adversary is even handed the oracle exponents and
the public key `k • g`, and may be randomized and unbounded.  The equality holds in every module
(no generator hypothesis is needed for it).  This is the special case of `keyGoal_eq_pkGoal` for
the weakest goal, total key recovery; partial information about the key is covered by that more
general theorem.

What this does NOT claim: it does not prove that discrete logarithms are hard, and it does not
assume it.  It does not cover an A that sends non-blinded group elements (see
`malicious_query_is_one_signature` and the remarks there).  The experiment as stated lets the
adversary see the exponents `h`; the link to the experiment with a genuinely uniform hash
function is `keyRecoveryRO_eq_dlog`. -/
theorem keyRecovery_eq_dlog (g : G) (choose : (M → F) → ι → M) (Adv : View F G M ι → PMF F) :
    keyRecoveryExp g choose Adv = dlogExp g (dlogSolver choose Adv) :=
  keyGoal_eq_pkGoal g (fun _ h _ => choose h) Adv _

/-- The winning probabilities in `keyRecovery_eq_dlog` are equal. -/
theorem keyRecovery_win_eq_dlog_win (g : G) (choose : (M → F) → ι → M)
    (Adv : View F G M ι → PMF F) :
    keyRecoveryExp g choose Adv true = dlogExp g (dlogSolver choose Adv) true := by
  rw [keyRecovery_eq_dlog]

/-- The converse (trivial) direction: a discrete-logarithm solver is a key-recovery adversary
with the same success distribution, because the public key is part of the view.  Together with
`keyRecovery_eq_dlog`: in this model the two problems have the same success probabilities, up to
the explicit wrappers `dlogSolver` and `fun v => S v.1` (whose cost is read off their
definitions; no complexity statement is formalised). -/
theorem dlog_eq_keyRecovery (g : G) (choose : (M → F) → ι → M) (S : G → PMF F) :
    dlogExp g S = keyRecoveryExp g choose fun v => S v.1 :=
  pkGoal_eq_keyGoal g (fun _ h _ => choose h) S _

/-! ### Messages that depend on the public key and on the coins -/

/-- Key-recovery experiment in which the messages may depend on the public key, the oracle
exponents and all the coins. -/
noncomputable def keyRecoveryExpAdaptive (g : G) (choose : G → (M → F) → (ι → Fˣ) → ι → M)
    (Adv : View F G M ι → PMF F) : PMF Bool :=
  (unif F).bind fun k => (unif (M → F)).bind fun h => (unif (ι → Fˣ)).bind fun rs =>
    (Adv (viewsReal g k h (choose (k • g) h rs) rs)).map fun k' => decide (k' = k)

/-- The solver for `keyRecoveryExpAdaptive`: as `dlogSolver`, computing the messages from the
public key, the exponents and the coins it sampled itself.  It is `pkSolver` with output type
`F`; the inventory in the docstring of `pkSolver` applies. -/
noncomputable def dlogSolverAdaptive (choose : G → (M → F) → (ι → Fˣ) → ι → M)
    (Adv : View F G M ι → PMF F) : G → PMF F := fun pk =>
  (unif (M → F)).bind fun h => (unif (ι → Fˣ)).bind fun rs =>
    Adv (viewsSim pk h (choose pk h rs) rs)

/-- **The reduction with messages depending on the public key and the coins.**  Same statement as
`keyRecovery_eq_dlog`, for a deterministic message-selection rule that may look at the public
key, the oracle exponents and all of A's coins.  It is `keyGoal_eq_pkGoal` for the goal "the
output is the key".

A rule that picks the message of session `i` after seeing the replies of earlier sessions is
covered by `keyGoalInteractive_eq_pkGoal` (a Lean theorem, for sequential sessions), and a
randomized rule by `keyGoal_mixture_eq_pkGoal`.  The same scope restrictions as in
`keyRecovery_eq_dlog` apply (honest blinding only; the solver samples the whole oracle table; no
hardness is proved or assumed). -/
theorem keyRecoveryAdaptive_eq_dlog (g : G) (choose : G → (M → F) → (ι → Fˣ) → ι → M)
    (Adv : View F G M ι → PMF F) :
    keyRecoveryExpAdaptive g choose Adv = dlogExp g (dlogSolverAdaptive choose Adv) :=
  keyGoal_eq_pkGoal g choose Adv _

/-- The basic experiment is the adaptive one for a rule that ignores the key and the coins. -/
theorem keyRecoveryExp_eq_adaptive (g : G) (choose : (M → F) → ι → M)
    (Adv : View F G M ι → PMF F) :
    keyRecoveryExp g choose Adv = keyRecoveryExpAdaptive g (fun _ h _ => choose h) Adv := rfl

/-! ### Messages that depend on the replies of earlier sessions -/

/-- The key-goal experiment with `n` *sequential* sessions and reply-dependent message selection:
the message of session `i` is `next (k • g) h rs` applied to the list of B's replies in sessions
`0, …, i - 1` (see `replyHistory`, `interactiveMsgs`).  The rule may also look at the public key,
the oracle exponents and all the coins.  Sessions are numbered in the order in which A sends its
queries; a schedule in which some earlier replies have not yet arrived is the special case of a
rule that ignores them. -/
noncomputable def keyGoalExpInteractive {n : ℕ} (g : G)
    (next : G → (M → F) → (Fin n → Fˣ) → List G → M) (Adv : View F G M (Fin n) → PMF β)
    (goal : F → β → γ) : PMF γ :=
  (unif F).bind fun k => (unif (M → F)).bind fun h => (unif (Fin n → Fˣ)).bind fun rs =>
    (Adv (viewsReal g k h
      (interactiveMsgs (fun m r => evaluate k (blind (progHash g h) m r)) (next (k • g) h rs) rs)
      rs)).map (goal k)

/-- The message-selection rule that the solver uses to replay a reply-dependent rule `next`: it
computes the replies of earlier sessions from the public key (`(r * h m) • pk`) instead of
receiving them from B. -/
def simInteractiveChoose {n : ℕ} (next : G → (M → F) → (Fin n → Fˣ) → List G → M) :
    G → (M → F) → (Fin n → Fˣ) → Fin n → M :=
  fun pk h rs => interactiveMsgs (fun m (r : Fˣ) => ((r : F) * h m) • pk) (next pk h rs) rs

omit [Fintype F] [DecidableEq F] [Fintype M] [DecidableEq M] in
/-- In a real execution, the messages produced by a reply-dependent rule are the messages the
solver computes from the public key.  Pointwise, no probability. -/
theorem interactiveMsgs_real_eq_sim {n : ℕ} (g : G) (k : F) (h : M → F)
    (next : G → (M → F) → (Fin n → Fˣ) → List G → M) (rs : Fin n → Fˣ) :
    interactiveMsgs (fun m r => evaluate k (blind (progHash g h) m r)) (next (k • g) h rs) rs =
      simInteractiveChoose next (k • g) h rs := by
  simp only [simInteractiveChoose, evaluate_blind_progHash]

/-- The interactive experiment is an instance of the non-interactive one: reply-dependent message
selection is selection as a function of the public key, the exponents and the coins. -/
theorem keyGoalExpInteractive_eq_keyGoalExp {n : ℕ} (g : G)
    (next : G → (M → F) → (Fin n → Fˣ) → List G → M) (Adv : View F G M (Fin n) → PMF β)
    (goal : F → β → γ) :
    keyGoalExpInteractive g next Adv goal =
      keyGoalExp g (simInteractiveChoose next) Adv goal := by
  simp only [keyGoalExpInteractive, keyGoalExp, interactiveMsgs_real_eq_sim]

/-- **The reduction with reply-dependent (interactive) message selection.**  If A runs `n`
sessions one after the other and chooses each message after seeing B's replies in the earlier
sessions, then, for every goal about the key, the experiment still equals the public-key
experiment played by the explicit solver `pkSolver (simInteractiveChoose next) Adv`, which
replays A's choices by computing the earlier replies from the public key.

Scope and non-claims are those of `keyGoal_eq_pkGoal` (honest blinding; goals about the key only;
the solver samples the whole oracle table; no hardness is proved or assumed).  The selection rule
is deterministic; combine with `keyGoal_mixture_eq_pkGoal` for a randomized one. -/
theorem keyGoalInteractive_eq_pkGoal {n : ℕ} (g : G)
    (next : G → (M → F) → (Fin n → Fˣ) → List G → M) (Adv : View F G M (Fin n) → PMF β)
    (goal : F → β → γ) :
    keyGoalExpInteractive g next Adv goal =
      pkGoalExp g (pkSolver (simInteractiveChoose next) Adv) goal := by
  rw [keyGoalExpInteractive_eq_keyGoalExp, keyGoal_eq_pkGoal]

/-! ### The oracle seen only at declared query points (static lazy sampling) -/

/-- The key-goal experiment in which the big oracle table `h : M → F` is sampled in full, but is
only ever *looked at* at the pairwise distinct points `qs : κ → M` declared in advance.  A's
session messages are among these points (`qs (choose … i)`; repetitions are allowed) and the
adversary sees the exponents at these points only: its view is
`(public key, exponents at the query points, indices of the messages, coins, replies)`. -/
noncomputable def keyGoalExpQueried {κ : Type*} (g : G) (qs : κ → M)
    (choose : G → (κ → F) → (ι → Fˣ) → ι → κ) (Adv : View F G κ ι → PMF β)
    (goal : F → β → γ) : PMF γ :=
  (unif F).bind fun k => (unif (M → F)).bind fun h => (unif (ι → Fˣ)).bind fun rs =>
    (Adv (k • g, h ∘ qs, choose (k • g) (h ∘ qs) rs, rs, fun i =>
      evaluate k (blind (progHash g h) (qs (choose (k • g) (h ∘ qs) rs i)) (rs i)))).map (goal k)

/-- With distinct declared query points, the experiment over the big table `M` is the key-goal
experiment whose oracle table is indexed by the query points themselves. -/
theorem keyGoalExpQueried_eq_keyGoalExp {κ : Type*} [Fintype κ] [DecidableEq κ] (g : G)
    {qs : κ → M} (hqs : Function.Injective qs) (choose : G → (κ → F) → (ι → Fˣ) → ι → κ)
    (Adv : View F G κ ι → PMF β) (goal : F → β → γ) :
    keyGoalExpQueried g qs choose Adv goal = keyGoalExp g choose Adv goal := by
  unfold keyGoalExpQueried keyGoalExp
  rw [← unif_comp_injective (α := F) hqs]
  simp only [PMF.bind_map]
  rfl

/-- **The reduction with a solver that samples one exponent per declared oracle query.**  If the
oracle is looked at only at `|κ|` distinct points fixed in advance, then for every goal about the
key the experiment (with a full random table over an arbitrarily large finite `M`) equals the
public-key experiment played by `pkSolver choose Adv` *over the index type `κ`*: that solver
samples `|κ|` exponents and `|ι|` coins, does `|ι|` field multiplications and `|ι|` scalar
multiplications and runs the adversary once.  Its work does not depend on `|M|`.

What this does NOT cover: an adversary that chooses its oracle queries adaptively, or that looks
at the oracle outside the declared points.  Adaptive queries are the subject of
`keyGoalOracle_eq_pkGoal`, in a different adversary model (strategy trees).  The other non-claims
of `keyGoal_eq_pkGoal` apply (honest blinding; goals about the key only; no hardness proved or
assumed; "efficient" is by inspection). -/
theorem keyGoalQueried_eq_pkGoal {κ : Type*} [Fintype κ] [DecidableEq κ] (g : G)
    {qs : κ → M} (hqs : Function.Injective qs) (choose : G → (κ → F) → (ι → Fˣ) → ι → κ)
    (Adv : View F G κ ι → PMF β) (goal : F → β → γ) :
    keyGoalExpQueried g qs choose Adv goal = pkGoalExp g (pkSolver choose Adv) goal := by
  rw [keyGoalExpQueried_eq_keyGoalExp g hqs, keyGoal_eq_pkGoal]

/-! ### The genuine random-oracle experiment -/

/-- The key-goal experiment with a genuinely uniform hash function `H : M → G` (the random
oracle model with the whole table given to the adversary).  No exponents appear anywhere.  The
messages may depend on the public key, the hash table and the coins. -/
noncomputable def keyGoalExpRO [Fintype G] (g : G) (choose : G → (M → G) → (ι → Fˣ) → ι → M)
    (Adv : ViewRO F G M ι → PMF β) (goal : F → β → γ) : PMF γ :=
  (unif F).bind fun k => (unif (M → G)).bind fun H => (unif (ι → Fˣ)).bind fun rs =>
    (Adv (viewsRO g k H (choose (k • g) H rs) rs)).map (goal k)

/-- The random-oracle experiment equals the programmed experiment for the adversary that forgets
the exponents.  Uses `progHash_uniform`, hence needs `g` to be a generator. -/
theorem keyGoalRO_eq_programmed [Fintype G] {g : G} (hg : IsGenerator F g)
    (choose : G → (M → G) → (ι → Fˣ) → ι → M) (Adv : ViewRO F G M ι → PMF β)
    (goal : F → β → γ) :
    keyGoalExpRO g choose Adv goal =
      keyGoalExp g (fun pk h rs => choose pk (progHash g h) rs)
        (fun v => Adv (forgetExponents g v)) goal := by
  unfold keyGoalExpRO keyGoalExp
  rw [← progHash_uniform hg]
  simp only [PMF.bind_map]
  rfl

/-- **Any goal about the key, in the random-oracle model, reduces to the public key alone.**  Let
`g` generate the group.  For every adversary against the experiment with a uniformly random hash
function (no exponents shown to it) and every goal about the key, the experiment has the same
distribution as the public-key experiment played by an explicit solver: `pkSolver` wrapped around
`Adv`, which programs the oracle as `H m = h m • g` and never shows the exponents to `Adv`.

Scope and non-claims are those of `keyGoal_eq_pkGoal`: honest-but-curious A only; messages a
deterministic function of the public key, the hash table and the coins; goals are functions of
the key and the output only (in particular NOT forgery, which would be a goal about the hash
table as well); the adversary receives the whole finite table and the solver samples and
programs all of it (`|M|` scalars and `|M|` scalar multiplications; for a solver that programs
the oracle lazily see `keyGoalOracleRO_eq_pkGoal`); no hardness is proved or assumed; the random
oracle is an idealisation of the hash function. -/
theorem keyGoalRO_eq_pkGoal [Fintype G] {g : G} (hg : IsGenerator F g)
    (choose : G → (M → G) → (ι → Fˣ) → ι → M) (Adv : ViewRO F G M ι → PMF β)
    (goal : F → β → γ) :
    keyGoalExpRO g choose Adv goal =
      pkGoalExp g (pkSolver (fun pk h rs => choose pk (progHash g h) rs) fun v =>
        Adv (forgetExponents g v)) goal := by
  rw [keyGoalRO_eq_programmed hg, keyGoal_eq_pkGoal]

/-- The random-oracle key-goal experiment with `n` sequential sessions and reply-dependent
message selection (as `keyGoalExpInteractive`, with a genuinely uniform hash table and no
exponents). -/
noncomputable def keyGoalExpROInteractive [Fintype G] {n : ℕ} (g : G)
    (next : G → (M → G) → (Fin n → Fˣ) → List G → M) (Adv : ViewRO F G M (Fin n) → PMF β)
    (goal : F → β → γ) : PMF γ :=
  (unif F).bind fun k => (unif (M → G)).bind fun H => (unif (Fin n → Fˣ)).bind fun rs =>
    (Adv (viewsRO g k H
      (interactiveMsgs (fun m r => evaluate k (blind H m r)) (next (k • g) H rs) rs)
      rs)).map (goal k)

/-- **Random-oracle model, reply-dependent message selection.**  Let `g` generate the group.  The
random-oracle experiment in which A chooses each message after seeing the earlier replies equals,
for every goal about the key, the public-key experiment played by an explicit solver.  Scope and
non-claims: those of `keyGoalRO_eq_pkGoal` and `keyGoalInteractive_eq_pkGoal`. -/
theorem keyGoalROInteractive_eq_pkGoal [Fintype G] {n : ℕ} {g : G} (hg : IsGenerator F g)
    (next : G → (M → G) → (Fin n → Fˣ) → List G → M) (Adv : ViewRO F G M (Fin n) → PMF β)
    (goal : F → β → γ) :
    keyGoalExpROInteractive g next Adv goal =
      pkGoalExp g (pkSolver (simInteractiveChoose fun pk h rs => next pk (progHash g h) rs)
        fun v => Adv (forgetExponents g v)) goal := by
  rw [← keyGoalInteractive_eq_pkGoal]
  unfold keyGoalExpROInteractive keyGoalExpInteractive
  rw [← progHash_uniform hg]
  simp only [PMF.bind_map]
  rfl

/-- The key-recovery experiment with a genuinely uniform hash function `H : M → G` (the random
oracle model with the whole table given to the adversary).  No exponents appear anywhere. -/
noncomputable def keyRecoveryExpRO [Fintype G] (g : G) (choose : (M → G) → ι → M)
    (Adv : ViewRO F G M ι → PMF F) : PMF Bool :=
  (unif F).bind fun k => (unif (M → G)).bind fun H => (unif (ι → Fˣ)).bind fun rs =>
    (Adv (viewsRO g k H (choose H) rs)).map fun k' => decide (k' = k)

/-- The random-oracle key-recovery experiment is the random-oracle key-goal experiment for the
goal "the output is the key" and a selection rule that looks at the hash table only. -/
theorem keyRecoveryExpRO_eq_keyGoalExpRO [Fintype G] (g : G) (choose : (M → G) → ι → M)
    (Adv : ViewRO F G M ι → PMF F) :
    keyRecoveryExpRO g choose Adv =
      keyGoalExpRO g (fun _ H _ => choose H) Adv fun k k' => decide (k' = k) := rfl

/-- The random-oracle experiment equals the programmed experiment for the adversary that forgets
the exponents.  Uses `progHash_uniform`, hence needs `g` to be a generator. -/
theorem keyRecoveryRO_eq_programmed [Fintype G] {g : G} (hg : IsGenerator F g)
    (choose : (M → G) → ι → M) (Adv : ViewRO F G M ι → PMF F) :
    keyRecoveryExpRO g choose Adv =
      keyRecoveryExp g (fun h => choose (progHash g h)) fun v => Adv (forgetExponents g v) :=
  keyGoalRO_eq_programmed hg (fun _ H _ => choose H) Adv _

/-- **Key recovery in the random-oracle model reduces to discrete logarithm, exactly.**  Let `g`
generate the group.  For every adversary `Adv` against the experiment with a uniformly random hash
function, the experiment has the same distribution as the discrete-logarithm experiment played by
an explicit solver: the solver of `keyRecovery_eq_dlog` wrapped around `Adv`, which programs the
oracle as `H m = h m • g` and never shows the exponents to `Adv`.

Scope and non-claims are those of `keyRecovery_eq_dlog`: honest-but-curious A only, messages a
function of the hash table (for messages depending also on the public key and the coins use
`keyGoalRO_eq_pkGoal`), any finite number of sessions; the adversary receives the whole finite
hash table and the solver samples and programs all of it (`|M|` scalars and `|M|` scalar
multiplications: efficient, as written, only for a small table; the version with adaptive oracle
access and a lazily programming solver is `keyRecoveryOracleRO_eq_dlog`, in the strategy-tree
model); hardness of discrete logarithms is neither proved nor assumed; the random oracle is an
idealisation of the hash function. -/
theorem keyRecoveryRO_eq_dlog [Fintype G] {g : G} (hg : IsGenerator F g)
    (choose : (M → G) → ι → M) (Adv : ViewRO F G M ι → PMF F) :
    keyRecoveryExpRO g choose Adv =
      dlogExp g (dlogSolver (fun h => choose (progHash g h)) fun v =>
        Adv (forgetExponents g v)) := by
  rw [keyRecoveryRO_eq_programmed hg, keyRecovery_eq_dlog]

end Reduction

/-! ### A deviating A whose queries have known exponents: the reduction -/

section KnownExponent

variable {ι β γ Ω : Type*} [Fintype F] [Fintype M] [DecidableEq M]

/-- The key-goal experiment against a possibly DISHONEST A whose queries have known exponents: in
session `i` it sends `x_i • g`, where the exponents `query ω (k • g) h` are any function of a
random tape `ω` (distribution `ρ`, independent of the key and the oracle), the public key and
the oracle exponents.  The adversary shares the tape, sees the total view and outputs `out`; the
result is `goal k out`. -/
noncomputable def keyGoalExpKE (ρ : PMF Ω) (g : G) (query : Ω → G → (M → F) → ι → F)
    (Adv : Ω → ViewKE F G M ι → PMF β) (goal : F → β → γ) : PMF γ :=
  (unif F).bind fun k => (unif (M → F)).bind fun h => ρ.bind fun ω =>
    (Adv ω (viewsKE g k h (query ω (k • g) h))).map (goal k)

/-- The solver for `keyGoalExpKE`.  Inventory (by inspection; no cost model): the whole oracle
exponent table (`|M|` scalars), one tape, one evaluation of `query`, one scalar multiplication
per session, one run of the adversary.  It never sees `k`. -/
noncomputable def pkSolverKE (ρ : PMF Ω) (query : Ω → G → (M → F) → ι → F)
    (Adv : Ω → ViewKE F G M ι → PMF β) : G → PMF β := fun pk =>
  (unif (M → F)).bind fun h => ρ.bind fun ω => Adv ω (viewsKESim pk h (query ω pk h))

/-- **A deviating A whose queries have known exponents gains nothing beyond the public key.**
For every goal about the key, the experiment in which A sends arbitrary multiples `x_i • g` of
the generator (exponents chosen from its random tape, the public key and the oracle exponents)
equals the public-key experiment played by the explicit solver `pkSolverKE`.

This goes beyond honest blinding (which is the case `x_i = r_i * h (m_i)`,
`viewsReal_replies_eq_viewsKE`): it covers sending unblinded hashes, zero, multiples and sums of
hashes, multiples of `g` (`smul_add_sum_smul_progHash`), with exponents that may depend on the
public key as data.

What this does NOT cover, and this is the important boundary: a query whose exponent in base `g`
is not something A can compute, i.e. a query with a component along the PUBLIC KEY or along an
earlier reply (for instance `a = k • g` itself, whose reply is `k² • g`), or any other group
element of unknown discrete logarithm.  Formally such a query can be written in the present
form, with `query` taking the discrete logarithm of the public key, and the equality still
holds; but then `pkSolverKE`, which calls `query`, takes that discrete logarithm too and the
statement is empty as a reduction.  Such queries turn B into a static Diffie–Hellman oracle;
that regime (Brown–Gallant, Cheon; one-more Diffie–Hellman for unforgeability) is neither proved
nor assumed here, and a real dishonest A is not restricted to known-exponent queries.  Same
further non-claims as `keyGoal_eq_pkGoal`: goals about the key only; no hardness; the solver
samples the whole oracle table.  (Known-exponent queries chosen one at a time, each after seeing
B's earlier replies, against a lazily sampling solver: the `send` nodes of
`keyGoalOracle_eq_pkGoal`.) -/
theorem keyGoalKE_eq_pkGoal (ρ : PMF Ω) (g : G) (query : Ω → G → (M → F) → ι → F)
    (Adv : Ω → ViewKE F G M ι → PMF β) (goal : F → β → γ) :
    keyGoalExpKE ρ g query Adv goal = pkGoalExp g (pkSolverKE ρ query Adv) goal := by
  simp only [keyGoalExpKE, pkGoalExp, pkSolverKE, viewsKE_eq_viewsKESim, PMF.map_bind]

omit [Fintype F] [Fintype M] [DecidableEq M] in
/-- Reply-dependent choice of the exponents is of the form allowed in `keyGoalExpKE`: if A picks
the exponent of each query after seeing B's earlier replies (rule `next`), the exponents it ends
up using in a real execution are those computed by replaying the rule with replies `x • pk`
computed from the public key.  Pointwise, no probability; the statement about experiments is
`keyGoalOracle_eq_pkGoal` (`send` nodes). -/
theorem interactiveExponents_real_eq_sim {n : ℕ} (g : G) (k : F) (next : List G → F) :
    interactiveMsgs (fun x (_ : Unit) => evaluate k (x • g)) next (fun _ : Fin n => ()) =
      interactiveMsgs (fun x _ => x • (k • g)) next fun _ => () := by
  simp only [evaluate_smul_gen]

end KnownExponent

/-! ### Adaptive access to the oracle and to B: strategy trees and a lazily sampling solver -/

section LazySampling

universe uA uK uP uX uβ

/-- A deterministic strategy of party A (together with whatever adversary looks over its
shoulder) that accesses the oracle and B *adaptively*.  It is a decision tree with four kinds of
nodes:

* `done out`: stop and output `out`;
* `ask m cont`: ask the oracle at the point `m` and continue with its answer;
* `session m cont`: run one honest session on the message `m`.  The experiment samples the
  blinding coin; the continuation receives that coin and B's reply;
* `send x cont`: a DEVIATION from the protocol: send B the group element `x • g`, where the
  exponent `x` is chosen by the strategy, and continue with B's reply.

`A` is the type of oracle answers (exponents in the programmed model, group elements in the
random-oracle model), `K` the scalars, `P` the group, `X` the messages, `β` the outputs.  The
continuations are arbitrary functions: the strategy is computationally unbounded.  Every oracle
point, every message and every exponent may depend on everything seen so far.

What a strategy can NOT do: send B a group element that is not an honest blinded hash and whose
exponent in base `g` it has not chosen itself (for instance the public key, or an earlier reply
of B).  That is the static Diffie–Hellman regime of section B. -/
inductive Strategy (A : Type uA) (K : Type uK) (P : Type uP) (X : Type uX) (β : Type uβ)
    [Monoid K] : Type (max uA uK uP uX uβ)
  /-- Stop and output `out`. -/
  | done (out : β) : Strategy A K P X β
  /-- Ask the oracle at the point `m`; continue with its answer. -/
  | ask (m : X) (cont : A → Strategy A K P X β) : Strategy A K P X β
  /-- Run one honest session on the message `m`; continue with the coin and B's reply. -/
  | session (m : X) (cont : Kˣ → P → Strategy A K P X β) : Strategy A K P X β
  /-- Deviation: send B the multiple of the generator with exponent `x`; continue with B's
  reply. -/
  | send (x : K) (cont : P → Strategy A K P X β) : Strategy A K P X β

namespace Strategy

variable {A A' β : Type*}

/-- Run a strategy when the oracle answers `ans m` at the point `m`, B's reply in an honest
session on message `m` with coin `r` is `reply m r`, and B's reply to the deviating query with
exponent `x` is `raw x`.  The coin of each honest session is sampled uniformly among the nonzero
scalars, as the protocol prescribes. -/
noncomputable def run [Fintype F] [DecidableEq F] (ans : M → A) (reply : M → Fˣ → G)
    (raw : F → G) : Strategy A F G M β → PMF β
  | .done out => PMF.pure out
  | .ask m cont => (cont (ans m)).run ans reply raw
  | .session m cont => (unif Fˣ).bind fun r => (cont r (reply m r)).run ans reply raw
  | .send x cont => (cont (raw x)).run ans reply raw

/-- Run a strategy *from the public key* `pk`, sampling the oracle lazily.  `c` is the cache of
the exponents fixed so far.  Inventory, per node of the path that is actually taken (read off this
definition; Lean has no cost model):

* `ask m`: one cache lookup; if `m` is new, one fresh uniform exponent, stored in the cache;
* `session m`: one cache lookup and possibly one fresh exponent as above, one uniform nonzero
  coin, one field multiplication, one scalar multiplication of `pk`;
* `send x`: one scalar multiplication of `pk`.

Neither the key nor a discrete logarithm is an input, and nothing depends on the size of the
message space.  (The cache is modelled as a function `M → Option F` updated at one point; an
implementation would use a finite map.) -/
noncomputable def runLazy [Fintype F] [DecidableEq F] [DecidableEq M] (pk : G) :
    Strategy F F G M β → (M → Option F) → PMF β
  | .done out, _ => PMF.pure out
  | .ask m cont, c =>
    match c m with
    | some e => (cont e).runLazy pk c
    | none => (unif F).bind fun e => (cont e).runLazy pk (Function.update c m (some e))
  | .session m cont, c =>
    match c m with
    | some e => (unif Fˣ).bind fun r => (cont r (((r : F) * e) • pk)).runLazy pk c
    | none => (unif F).bind fun e => (unif Fˣ).bind fun r =>
        (cont r (((r : F) * e) • pk)).runLazy pk (Function.update c m (some e))
  | .send x cont, c => (cont (x • pk)).runLazy pk c

/-- Turn a strategy that expects oracle answers of type `A` into one that expects answers of type
`A'`, by translating each answer with `f`.  Used with `f e = e • g`: a strategy that sees hash
values becomes a strategy that is given exponents and only looks at the corresponding hash
values.  One application of `f` per oracle query. -/
def mapAns (f : A' → A) : Strategy A F G M β → Strategy A' F G M β
  | .done out => .done out
  | .ask m cont => .ask m fun a => (cont (f a)).mapAns f
  | .session m cont => .session m fun r b => (cont r b).mapAns f
  | .send x cont => .send x fun b => (cont b).mapAns f

omit [AddCommGroup G] [Module F G] in
/-- Running a translated strategy is running the original strategy against the translated
oracle. -/
theorem run_mapAns [Fintype F] [DecidableEq F] (f : A' → A) (ans : M → A') (reply : M → Fˣ → G)
    (raw : F → G) (s : Strategy A F G M β) :
    (s.mapAns f).run ans reply raw = s.run (f ∘ ans) reply raw := by
  induction s with
  | done out => rfl
  | ask m cont ih => simp only [mapAns, run, ih, Function.comp_apply]
  | session m cont ih => simp only [mapAns, run, ih]
  | send x cont ih => simp only [mapAns, run, ih]

/-- Sanity check of the `session` node: the strategy "run one session on `m` and output what you
saw" produces exactly the distribution of A's view `viewA` of an honest session. -/
theorem run_session_done [Fintype F] [DecidableEq F] (H : M → G) (k : F) (ans : M → A)
    (raw : F → G) (m : M) :
    (session m fun r b => done (m, r, b) : Strategy A F G M (M × Fˣ × G)).run ans
        (fun m r => evaluate k (blind H m r)) raw = (unif Fˣ).map (viewA H k m) :=
  rfl

/-- Sanity check of the cache: the lazily sampled oracle is consistent.  A strategy that asks the
same point twice gets the same answer twice. -/
theorem runLazy_ask_twice [Fintype F] [DecidableEq F] [DecidableEq M] (pk : G) (m : M) :
    (ask m fun e => ask m fun e' => done (decide (e = e')) : Strategy F F G M Bool).runLazy pk
        (fun _ => none) = PMF.pure true := by
  simp only [runLazy, Function.update_self, decide_true, PMF.bind_const]

/-- Sanity check of the cache across node kinds: the exponent that the lazy run uses to answer a
session on `m` is the one it later reveals when the strategy asks the oracle at `m`. -/
theorem runLazy_session_then_ask [Fintype F] [DecidableEq F] [DecidableEq M] [DecidableEq G]
    (pk : G) (m : M) :
    (session m fun r b => ask m fun e => done (decide (b = ((r : F) * e) • pk)) :
      Strategy F F G M Bool).runLazy pk (fun _ => none) = PMF.pure true := by
  simp only [runLazy, Function.update_self, decide_true, PMF.bind_const]

/-- Sanity check of the `send` node: run from the public key, the reply to the deviating query
with exponent `x` is `x • pk`. -/
theorem runLazy_send_done [Fintype F] [DecidableEq F] [DecidableEq M] (pk : G) (x : F)
    (c : M → Option F) : (send x done : Strategy F F G M G).runLazy pk c = PMF.pure (x • pk) :=
  rfl

end Strategy

/-- The oracle table `h` overridden by the entries fixed in the cache `c`. -/
def overlay (c : M → Option F) (h : M → F) : M → F := fun m => (c m).getD (h m)

omit [Field F] in
/-- At a point that the cache does not fix, the overlaid table is the underlying table. -/
theorem overlay_apply_of_none {c : M → Option F} {m : M} (hc : c m = none) (h : M → F) :
    overlay c h m = h m := by
  simp [overlay, hc]

omit [Field F] in
/-- At a point that the cache fixes, the overlaid table has the cached value. -/
theorem overlay_apply_of_some {c : M → Option F} {m : M} {e : F} (hc : c m = some e)
    (h : M → F) : overlay c h m = e := by
  simp [overlay, hc]

omit [Field F] in
/-- Fixing a new point in the cache is the same as writing the value into the underlying
table. -/
theorem overlay_update [DecidableEq M] {c : M → Option F} {m : M} (hc : c m = none) (e : F)
    (h : M → F) :
    overlay (Function.update c m (some e)) h = overlay c (Function.update h m e) := by
  funext m'
  by_cases hm : m' = m
  · subst hm
    simp [overlay, hc]
  · simp [overlay, hm]

variable {β γ Ω : Type*} [Fintype F] [DecidableEq F] [Fintype M] [DecidableEq M]

omit [DecidableEq F] in
/-- **Resampling one entry of a uniform table.**  Sampling a table uniformly and reading its entry
at `x` is the same as sampling the entry `a` separately and writing it into an independent uniform
table.  This is the step that makes lazy sampling correct for a point chosen adaptively. -/
theorem unif_bind_update {α : Type*} [Fintype α] [Nonempty α] (x : M)
    (Φ : α → (M → α) → PMF γ) :
    ((unif α).bind fun a => (unif (M → α)).bind fun h => Φ a (Function.update h x a)) =
      (unif (M → α)).bind fun h => Φ (h x) h := by
  let e : α × (M → α) ≃ (M → α) × α :=
    { toFun := fun p => (Function.update p.2 x p.1, p.2 x)
      invFun := fun q => (q.1 x, Function.update q.1 x q.2)
      left_inv := fun p => by simp
      right_inv := fun q => by simp }
  rw [← unif_prod_bind fun p : α × (M → α) => Φ p.1 (Function.update p.2 x p.1),
    unif_bind_eq_of_equiv e _ (fun q : (M → α) × α => Φ (q.1 x) q.1) (fun p => by simp [e]),
    unif_prod_bind]
  simp only [PMF.bind_const]

/-- **Lazy sampling is exact, for adaptively chosen oracle points.**  Run a strategy in the real
world (key `k`, a uniformly random table of exponents overridden by the cache `c`, B answering
honest queries with `k`), and average over the table: the result is the lazy run from the public
key `k • g` started with the cache `c`. -/
theorem Strategy.bind_run_overlay_eq_runLazy (g : G) (k : F) (s : Strategy F F G M β)
    (c : M → Option F) :
    ((unif (M → F)).bind fun h =>
        s.run (overlay c h) (fun m r => evaluate k (blind (progHash g (overlay c h)) m r))
          fun x => evaluate k (x • g)) =
      s.runLazy (k • g) c := by
  induction s generalizing c with
  | done out => simp only [Strategy.run, Strategy.runLazy, PMF.bind_const]
  | ask m cont ih =>
    simp only [Strategy.run, Strategy.runLazy]
    rcases hc : c m with _ | e
    · simp only [← ih, overlay_apply_of_none hc, overlay_update hc]
      exact (unif_bind_update m fun e h' => (cont e).run (overlay c h')
        (fun m r => evaluate k (blind (progHash g (overlay c h')) m r))
        fun x => evaluate k (x • g)).symm
    · simp only [overlay_apply_of_some hc, ih]
  | session m cont ih =>
    simp only [Strategy.run, Strategy.runLazy, evaluate_blind_progHash]
    rcases hc : c m with _ | e
    · simp only [← ih, overlay_apply_of_none hc, overlay_update hc, evaluate_blind_progHash]
      rw [← unif_bind_update m fun e h' => (unif Fˣ).bind fun r =>
        (cont r (((r : F) * e) • k • g)).run (overlay c h')
          (fun m r => ((r : F) * overlay c h' m) • k • g) fun x => evaluate k (x • g)]
      congr 1
      funext e
      exact PMF.bind_comm _ _ _
    · simp only [overlay_apply_of_some hc, ← ih, evaluate_blind_progHash]
      exact PMF.bind_comm _ _ _
  | send x cont ih => simp only [Strategy.run, Strategy.runLazy, ← ih, evaluate_smul_gen]

/-- The key-goal experiment against an A with ADAPTIVE access to the oracle and to B, in the
programmed model.  A uniformly random key `k` and a uniformly random table of oracle exponents
`h` (over the whole, arbitrarily large, finite message space) are sampled.  The strategy
`t (k • g)` is run: each `ask m` is answered with the exponent `h m` (more than the hash value
`h m • g`), each `session m` is an honest session with B on the message `m` with a fresh uniform
coin, each `send x` is answered by B with `k • (x • g)`.  The result is `goal k out`. -/
noncomputable def keyGoalExpOracle (g : G) (t : G → Strategy F F G M β) (goal : F → β → γ) :
    PMF γ :=
  (unif F).bind fun k => (unif (M → F)).bind fun h =>
    ((t (k • g)).run h (fun m r => evaluate k (blind (progHash g h) m r))
      fun x => evaluate k (x • g)).map (goal k)

/-- The explicit solver built from a strategy: on input `pk` it runs the strategy from the public
key with a lazily sampled oracle, starting with the empty cache.  It never sees `k`.  What it
does is the inventory in the docstring of `Strategy.runLazy`: per oracle point touched at most one
fresh exponent, per session one coin, one field multiplication and one scalar multiplication,
per deviating query one scalar multiplication.  Unlike `pkSolver` it is defined without any
finiteness assumption on the message space: it cannot be sampling an oracle table. -/
noncomputable def lazySolver (t : G → Strategy F F G M β) : G → PMF β := fun pk =>
  (t pk).runLazy pk fun _ => none

/-- **The reduction with adaptive access to the oracle and to B, and a lazily sampling solver.**
For every strategy tree `t` (messages, oracle points, deviating exponents and the number of
sessions all chosen adaptively, as a function of the public key and of everything seen so far)
and every goal about the key, the experiment over a full uniformly random oracle table equals the
public-key experiment played by the explicit solver `lazySolver t`.

Why this matters: unlike `pkSolver`, this solver does not sample the oracle table.  Its work is
proportional to the number of oracle queries, sessions and deviating queries that the strategy
itself makes and does not depend on the size `|M|` of the message space.  That is read off
`Strategy.runLazy`; Lean has no cost model, so it is not a theorem.  (Machine-checked proxy:
`lazySolver` type-checks for an infinite message space, see the end of the file.)  The equality
holds in every module.

Scope.  The strategy is deterministic and unbounded; for a randomized one see
`keyGoalOracle_mixture_eq_pkGoal`.  Honest sessions use a fresh uniform nonzero coin sampled by
the experiment and are atomic (query, then reply).  Since B is stateless this includes concurrent
schedules: a schedule in which a later query is sent before an earlier reply arrives is a
strategy whose later query does not depend on that reply.  The only deviation from the protocol
is `send x` (the group element `x • g` with `x` chosen by the strategy; since `ask` returns
exponents this includes unblinded hashes, hashes blinded with a coin of A's choice, sums of
hashes, and `0`).  The oracle returns exponents; the version with hash values is
`keyGoalOracleRO_eq_pkGoal`.

What this does NOT claim: no hardness of any problem about `k • g`; nothing about goals that
mention the oracle (forgery; the strategy may learn every exponent); nothing about an A that
sends B the public key, an earlier reply, or any other group element whose exponent it has not
chosen (the static Diffie–Hellman regime of section B); the solver is only as efficient as the
strategy's own continuations. -/
theorem keyGoalOracle_eq_pkGoal (g : G) (t : G → Strategy F F G M β) (goal : F → β → γ) :
    keyGoalExpOracle g t goal = pkGoalExp g (lazySolver t) goal := by
  unfold keyGoalExpOracle pkGoalExp lazySolver
  congr 1
  funext k
  rw [← Strategy.bind_run_overlay_eq_runLazy g k, PMF.map_bind]
  rfl

/-- Exact key recovery with adaptive access to the oracle and to B is the discrete-logarithm
experiment played by the lazily sampling solver.  (`keyGoalOracle_eq_pkGoal` for the goal "the
output is the key"; same scope and non-claims.) -/
theorem keyRecoveryOracle_eq_dlog (g : G) (t : G → Strategy F F G M F) :
    keyGoalExpOracle g t (fun k k' => decide (k' = k)) = dlogExp g (lazySolver t) :=
  keyGoalOracle_eq_pkGoal g t _

/-- The converse (trivial) direction: a function of the public key is a strategy, namely the one
that touches neither the oracle nor B.  So the strategy experiments are not easier than the
public-key experiments. -/
theorem pkGoal_eq_keyGoalOracle (g : G) (f : G → β) (goal : F → β → γ) :
    pkGoalExp g (fun pk => PMF.pure (f pk)) goal =
      keyGoalExpOracle (M := M) g (fun pk => Strategy.done (f pk)) goal := by
  simp only [keyGoalExpOracle, pkGoalExp, Strategy.run, PMF.bind_const]

/-- **Randomized strategies.**  If the strategy also depends on a random tape `ω` (distribution
`ρ`, independent of the key and the oracle), the mixture of the experiments equals the public-key
experiment for the solver that samples the tape itself and then runs lazily. -/
theorem keyGoalOracle_mixture_eq_pkGoal (ρ : PMF Ω) (g : G) (t : Ω → G → Strategy F F G M β)
    (goal : F → β → γ) :
    (ρ.bind fun ω => keyGoalExpOracle g (t ω) goal) =
      pkGoalExp g (fun pk => ρ.bind fun ω => lazySolver (t ω) pk) goal := by
  simp only [keyGoalOracle_eq_pkGoal, pkGoalExp, PMF.map_bind]
  exact PMF.bind_comm _ _ _

/-- The key-goal experiment with adaptive access to the oracle and to B in the genuine
random-oracle model: the hash function `H : M → G` is uniformly random, `ask m` is answered with
the hash value `H m` (no exponents anywhere), `session m` is an honest session with B, and
`send x` is answered by B with `k • (x • g)`. -/
noncomputable def keyGoalExpOracleRO [Fintype G] (g : G) (t : G → Strategy G F G M β)
    (goal : F → β → γ) : PMF γ :=
  (unif F).bind fun k => (unif (M → G)).bind fun H =>
    ((t (k • g)).run H (fun m r => evaluate k (blind H m r))
      fun x => evaluate k (x • g)).map (goal k)

/-- **Random-oracle model, adaptive access, lazily sampling solver.**  Let `g` generate the
group.  For every strategy tree that sees hash values only and every goal about the key, the
random-oracle experiment equals the public-key experiment played by `lazySolver` applied to the
translated strategy: the solver answers a hash query at a new point with `e • g` for a fresh
exponent `e` that it keeps to itself, and computes B's replies from the public key.

Per oracle point touched: at most one fresh exponent, and one scalar multiplication per hash
query; per session one coin, one field multiplication, one scalar multiplication; nothing depends
on `|M|` (by inspection of `Strategy.runLazy` and `Strategy.mapAns`; no cost model).

Scope and non-claims: those of `keyGoalOracle_eq_pkGoal`, with one further restriction.  In this
model a deviating query `send x` is a multiple of `g` only.  A deviating query built from a hash
value (say `c • H m` with `c` chosen by A) is not a node of such a strategy; it is expressible in
the exponent model (`ask m`, then `send (c * e)`), which `keyGoalOracle_eq_pkGoal` covers.  The
random oracle is an idealisation of the hash function. -/
theorem keyGoalOracleRO_eq_pkGoal [Fintype G] {g : G} (hg : IsGenerator F g)
    (t : G → Strategy G F G M β) (goal : F → β → γ) :
    keyGoalExpOracleRO g t goal =
      pkGoalExp g (lazySolver fun pk => (t pk).mapAns fun e : F => e • g) goal := by
  rw [← keyGoalOracle_eq_pkGoal]
  unfold keyGoalExpOracleRO keyGoalExpOracle
  rw [← progHash_uniform hg]
  simp only [PMF.bind_map, Strategy.run_mapAns]
  rfl

/-- Randomized strategies in the random-oracle model (as `keyGoalOracle_mixture_eq_pkGoal`). -/
theorem keyGoalOracleRO_mixture_eq_pkGoal [Fintype G] {g : G} (hg : IsGenerator F g) (ρ : PMF Ω)
    (t : Ω → G → Strategy G F G M β) (goal : F → β → γ) :
    (ρ.bind fun ω => keyGoalExpOracleRO g (t ω) goal) =
      pkGoalExp g (fun pk => ρ.bind fun ω =>
        lazySolver (fun pk => (t ω pk).mapAns fun e : F => e • g) pk) goal := by
  simp only [keyGoalOracleRO_eq_pkGoal hg, pkGoalExp, PMF.map_bind]
  exact PMF.bind_comm _ _ _

/-- **Key recovery with adaptive access, in the random-oracle model, reduces to discrete
logarithm with a lazily sampling solver.**  (`keyGoalOracleRO_eq_pkGoal` for the goal "the output
is the key"; same scope and non-claims.  This is the form of the reduction whose solver does work
proportional to the adversary's own number of queries, by inspection.) -/
theorem keyRecoveryOracleRO_eq_dlog [Fintype G] {g : G} (hg : IsGenerator F g)
    (t : G → Strategy G F G M F) :
    keyGoalExpOracleRO g t (fun k k' => decide (k' = k)) =
      dlogExp g (lazySolver fun pk => (t pk).mapAns fun e : F => e • g) :=
  keyGoalOracleRO_eq_pkGoal hg t _

end LazySampling

/-! ## G. Sanity checks: the experiments are not degenerate -/

section Sanity

variable {ι : Type*} [Fintype F] [DecidableEq F] [Fintype M] [DecidableEq M]
  [Fintype ι] [DecidableEq ι]

/-- **An unbounded solver wins the discrete-logarithm experiment with certainty.**  If `g`
generates the group, the (non-computable) discrete-logarithm function is a solver that always
wins.  So `keyRecovery_eq_dlog` cannot be read as "key recovery is impossible": it is a statement
relating two *computational* problems, and it is only meaningful for bounded adversaries. -/
theorem dlogExp_unbounded_solver {g : G} (hg : IsGenerator F g) :
    ∃ S : G → PMF F, dlogExp g S = PMF.pure true := by
  refine ⟨fun x => PMF.pure (hg.equiv.symm x), ?_⟩
  simp only [dlogExp, PMF.pure_map, hg.equiv_symm_smul, decide_true, PMF.bind_const]

omit [Fintype M] [DecidableEq M] in
/-- **A guess that does not depend on the public key wins with probability exactly `1/|F|`.**  A
(possibly randomized) solver that ignores its input wins the discrete-logarithm experiment with
probability `1/|F|`, whatever the distribution `X` of its guess: the experiment is not winnable
by a solver that does no work. -/
theorem dlogExp_indep_guess (g : G) (X : PMF F) :
    dlogExp g (fun _ => X) true = (Fintype.card F : ℝ≥0∞)⁻¹ := by
  have h : ∀ k : F, (X.map fun k' => decide (k' = k)) true = X k := by
    intro k
    rw [PMF.map_apply, tsum_eq_single k]
    · simp
    · intro k' hk'
      simp [hk']
  rw [dlogExp, PMF.bind_apply]
  simp only [unif_apply, h]
  rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]

omit [Fintype M] [DecidableEq M] in
/-- **A blind guess wins with probability exactly `1/|F|`.**  A solver that ignores its input and
outputs a fixed scalar wins the discrete-logarithm experiment with probability `1/|F|`. -/
theorem dlogExp_const_guess (g : G) (k₀ : F) :
    dlogExp g (fun _ => PMF.pure k₀) true = (Fintype.card F : ℝ≥0∞)⁻¹ :=
  dlogExp_indep_guess g (PMF.pure k₀)

/-- An unbounded adversary wins the key-recovery experiment with certainty (if `g` generates the
group): it takes the discrete logarithm of the public key.  Again: key hiding is computational. -/
theorem keyRecoveryExp_unbounded_adversary {g : G} (hg : IsGenerator F g)
    (choose : (M → F) → ι → M) :
    ∃ Adv : View F G M ι → PMF F, keyRecoveryExp g choose Adv = PMF.pure true := by
  obtain ⟨S, hS⟩ := dlogExp_unbounded_solver hg
  exact ⟨fun v => S v.1, by rw [← dlog_eq_keyRecovery, hS]⟩

/-- An adversary that ignores its view and guesses a fixed key wins the key-recovery experiment
with probability exactly `1/|F|`. -/
theorem keyRecoveryExp_const_guess (g : G) (choose : (M → F) → ι → M) (k₀ : F) :
    keyRecoveryExp g choose (fun _ : View F G M ι => PMF.pure k₀) true =
      (Fintype.card F : ℝ≥0∞)⁻¹ := by
  rw [← dlogExp_const_guess g k₀]
  exact congrFun (congrArg DFunLike.coe
    (dlog_eq_keyRecovery g choose fun _ => PMF.pure k₀).symm) true

/-- **With the degenerate base `g = 0`, no adversary does better than a blind guess.**  If the
"public key" is `k • 0 = 0` it carries no information, and then EVERY adversary, however
powerful, wins the key-recovery experiment of the real protocol with probability exactly
`1/|F|`: all the sessions together give it nothing.  (A statement about the degenerate base
only; with a generator an unbounded adversary wins, `keyRecoveryExp_unbounded_adversary`.) -/
theorem keyRecoveryExp_zero (choose : (M → F) → ι → M) (Adv : View F G M ι → PMF F) :
    keyRecoveryExp (0 : G) choose Adv true = (Fintype.card F : ℝ≥0∞)⁻¹ := by
  rw [keyRecovery_eq_dlog, ← dlogExp_indep_guess (0 : G) (dlogSolver choose Adv 0)]
  simp only [dlogExp, smul_zero]

/-- The strategy experiment of `keyGoalOracle_eq_pkGoal` is not unwinnable: if `g` generates the
group, an unbounded strategy (one whose continuation takes a discrete logarithm; it touches
neither the oracle nor B) wins exact key recovery with certainty.  So that theorem, too, is about
computational hardness only. -/
theorem keyRecoveryOracle_unbounded_strategy {g : G} (hg : IsGenerator F g) :
    ∃ t : G → Strategy F F G M F,
      keyGoalExpOracle g t (fun k k' => decide (k' = k)) = PMF.pure true := by
  refine ⟨fun pk => Strategy.done (hg.equiv.symm pk), ?_⟩
  rw [keyGoalOracle_eq_pkGoal]
  simp only [pkGoalExp, lazySolver, Strategy.runLazy, PMF.pure_map, hg.equiv_symm_smul,
    decide_true, PMF.bind_const]

/-- The strategy experiment is not trivially winnable either: a strategy that runs an honest
session and then outputs a fixed guess, without using what it saw, wins exact key recovery with
probability exactly `1/|F|`. -/
theorem keyRecoveryOracle_session_const_guess (g : G) (m : M) (k₀ : F) :
    keyGoalExpOracle g (fun _ => Strategy.session m fun _ _ => Strategy.done k₀)
      (fun k k' => decide (k' = k)) true = (Fintype.card F : ℝ≥0∞)⁻¹ := by
  rw [keyRecoveryOracle_eq_dlog]
  have h : (lazySolver fun _ : G => (Strategy.session m fun _ _ => Strategy.done k₀ :
      Strategy F F G M F)) = fun _ => PMF.pure k₀ := by
    funext pk
    simp only [lazySolver, Strategy.runLazy, PMF.bind_const]
  rw [h, dlogExp_const_guess]

/-! ### A strawman protocol that leaks the key, compared with the real one -/

/-- The key-recovery game for an arbitrary protocol, described by its total-view function.
`keyRecoveryExp` is the instance `view := viewsReal g` (`keyRecoveryExp_eq_game`). -/
noncomputable def keyRecoveryGame {V : Type*}
    (view : F → (M → F) → (ι → M) → (ι → Fˣ) → V) (choose : (M → F) → ι → M)
    (Adv : V → PMF F) : PMF Bool :=
  (unif F).bind fun k => (unif (M → F)).bind fun h => (unif (ι → Fˣ)).bind fun rs =>
    (Adv (view k h (choose h) rs)).map fun k' => decide (k' = k)

/-- The experiment of section F is the generic game played with the real protocol. -/
theorem keyRecoveryExp_eq_game (g : G) (choose : (M → F) → ι → M)
    (Adv : View F G M ι → PMF F) :
    keyRecoveryExp g choose Adv = keyRecoveryGame (viewsReal g) choose Adv := rfl

/-- **The leaky strawman loses the key-recovery game to an adversary that does no work.**
Against the strawman protocol in which B's reply also contains the key, the adversary that simply
reads the key off the reply of one session `i₀` wins the key-recovery game with certainty, in
every module, however large `F` is.

How this compares with the real protocol, and what is and is NOT a theorem.  In the *same* game
(`keyRecoveryExp_eq_game`) the analogous adversary that does no work wins against the real
protocol with probability `1/|F|` (`keyRecoveryExp_const_guess`), and any winning adversary is
turned into a discrete-logarithm solver by the explicit wrapper `dlogSolver`
(`keyRecovery_eq_dlog`).  But for a fixed generator `g` the difference between the two protocols
is NOT expressed by any theorem here, and cannot be without a cost model: an unbounded adversary
wins against the real protocol too (`keyRecoveryExp_unbounded_adversary`), and with an arbitrary
function as solver the leaky game also "equals a discrete-logarithm experiment"
(`keyRecoveryGame_leaky_eq_dlog_unbounded`).  For a fixed generator the distinction rests on
reading the terms: this adversary and `dlogSolver` take no discrete logarithm.  The two formal
separations that do hold are `leaky_not_simulable` and `keyRecovery_zero_lt_leaky`; both rely on
the base `g` being allowed to vary (down to the degenerate base `0`). -/
theorem keyRecoveryGame_leaky (g : G) (choose : (M → F) → ι → M) (i₀ : ι) :
    keyRecoveryGame (viewsLeaky g) choose (fun v => PMF.pure (v.2.2.2.2 i₀).2) =
      PMF.pure true := by
  simp only [keyRecoveryGame, viewsLeaky, leakyEvaluate, PMF.pure_map, decide_true,
    PMF.bind_const]

/-- **HONESTY CHECK: existence of a solver means nothing.**  If `g` generates the group and the
solver may be an arbitrary function, then even the leaky strawman's key-recovery game equals a
discrete-logarithm experiment: the "solver" takes the discrete logarithm of the public key and
then runs the leaky protocol itself.

So the content of `keyRecovery_eq_dlog` / `keyGoal_eq_pkGoal` is NOT "there is a solver"; it is
that the solver is the specific term `dlogSolver` / `pkSolver`, which a reader can check uses the
public key only through scalar multiplications.  That check is by inspection; Lean has no cost
model. -/
theorem keyRecoveryGame_leaky_eq_dlog_unbounded {g : G} (hg : IsGenerator F g)
    (choose : (M → F) → ι → M) (Adv : ViewLeaky F G M ι → PMF F) :
    ∃ S : G → PMF F, keyRecoveryGame (viewsLeaky g) choose Adv = dlogExp g S := by
  refine ⟨fun pk => (unif (M → F)).bind fun h => (unif (ι → Fˣ)).bind fun rs =>
    Adv (viewsLeaky g (hg.equiv.symm pk) h (choose h) rs), ?_⟩
  simp only [keyRecoveryGame, dlogExp, hg.equiv_symm_smul, PMF.map_bind]

omit [Fintype F] [DecidableEq F] [Fintype M] [DecidableEq M] [Fintype ι] [DecidableEq ι] in
/-- **Formal separation 1: the leaky protocol has no simulator from the public key that works for
every base.**  For the real protocol, `viewsSim` is a single function with
`viewsReal g k h ms rs = viewsSim (k • g) h ms rs` for ALL `g` (`viewsReal_eq_viewsSim`).  For
the leaky strawman no function at all (computable or not) has this property, as soon as there is
one session and one message.

Limit of this statement: the proof uses the degenerate base `g = 0`, where the public key is
independent of the key.  For one fixed generator `g` a (non-computable) simulator of the leaky
view does exist, via the discrete logarithm; no separation at a fixed generator is expressible
without a cost model. -/
theorem leaky_not_simulable (i : ι) (m₀ : M) :
    ¬ ∃ Sim : G → (M → F) → (ι → M) → (ι → Fˣ) → ViewLeaky F G M ι,
        ∀ (g : G) (k : F) (h : M → F) (ms : ι → M) (rs : ι → Fˣ),
          viewsLeaky g k h ms rs = Sim (k • g) h ms rs := by
  rintro ⟨Sim, hS⟩
  have h0 := hS 0 0 (fun _ => 0) (fun _ => m₀) (fun _ => 1)
  have h1 := hS 0 1 (fun _ => 0) (fun _ => m₀) (fun _ => 1)
  rw [smul_zero] at h0 h1
  have h2 := congrArg (fun v : ViewLeaky F G M ι => (v.2.2.2.2 i).2) (h0.trans h1.symm)
  simp [viewsLeaky, leakyEvaluate] at h2

/-- **Formal separation 2 (an inequality): at the degenerate base the real protocol beats the
leaky one in the same game.**  With `g = 0`, every adversary against the real protocol wins the
key-recovery game with probability `1/|F| < 1`, whereas the key-reading adversary wins against
the leaky strawman with probability `1`.

Limit of this statement: it is about the base `g = 0` only (see `leaky_not_simulable`). -/
theorem keyRecovery_zero_lt_leaky (choose : (M → F) → ι → M) (Adv : View F G M ι → PMF F)
    (i₀ : ι) :
    keyRecoveryGame (viewsReal (0 : G)) choose Adv true <
      keyRecoveryGame (viewsLeaky (0 : G)) choose (fun v => PMF.pure (v.2.2.2.2 i₀).2) true := by
  rw [← keyRecoveryExp_eq_game, keyRecoveryExp_zero, keyRecoveryGame_leaky, PMF.pure_apply,
    ite_eq_left rfl]
  exact ENNReal.inv_lt_one.mpr (by exact_mod_cast Fintype.one_lt_card)

end Sanity

/-! ## Non-vacuity: the hypotheses are satisfiable, and one of them is necessary -/

section NonVacuity

/-- The model `F = G = ZMod p`, `g = 1` (`p` prime) satisfies the generator hypothesis used in
sections B, C, D, F and G. -/
example (p : ℕ) [Fact p.Prime] : IsGenerator (ZMod p) (1 : ZMod p) :=
  ⟨one_ne_zero, fun x => ⟨x, by simp⟩⟩

/-- The random-oracle reduction instantiated in that model, with messages `Fin 4` and three
sessions. -/
example (p : ℕ) [Fact p.Prime] (choose : (Fin 4 → ZMod p) → Fin 3 → Fin 4)
    (Adv : ViewRO (ZMod p) (ZMod p) (Fin 4) (Fin 3) → PMF (ZMod p)) :
    keyRecoveryExpRO (1 : ZMod p) choose Adv =
      dlogExp (1 : ZMod p) (dlogSolver (fun h => choose (progHash 1 h)) fun v =>
        Adv (forgetExponents 1 v)) :=
  keyRecoveryRO_eq_dlog ⟨one_ne_zero, fun x => ⟨x, by simp⟩⟩ choose Adv

/-- The static lazy-sampling reduction instantiated in that model: the oracle table has 100
entries, it is looked at in 2 declared points, and the solver samples 2 exponents. -/
example (p : ℕ) [Fact p.Prime]
    (choose : ZMod p → (Fin 2 → ZMod p) → (Fin 3 → (ZMod p)ˣ) → Fin 3 → Fin 2)
    (Adv : View (ZMod p) (ZMod p) (Fin 2) (Fin 3) → PMF Bool) (bit : ZMod p → Bool) :
    keyGoalExpQueried (M := Fin 100) (1 : ZMod p) (Fin.castLE (by norm_num)) choose Adv
        (fun k b => decide (b = bit k)) =
      pkGoalExp (1 : ZMod p) (pkSolver choose Adv) fun k b => decide (b = bit k) :=
  keyGoalQueried_eq_pkGoal 1 (Fin.castLE_injective _) choose Adv _

/-- The adaptive lazy-sampling reduction instantiated in that model with 256-bit messages: the
experiment samples a hash table with `2 ^ 256` entries; the solver fixes an exponent only for the
points that the strategy touches. -/
example (p : ℕ) [Fact p.Prime]
    (t : ZMod p → Strategy (ZMod p) (ZMod p) (ZMod p) (Fin (2 ^ 256)) (ZMod p)) :
    keyGoalExpOracleRO (1 : ZMod p) t (fun k k' => decide (k' = k)) =
      dlogExp (1 : ZMod p)
        (lazySolver fun pk => (t pk).mapAns fun e : ZMod p => e • (1 : ZMod p)) :=
  keyRecoveryOracleRO_eq_dlog ⟨one_ne_zero, fun x => ⟨x, by simp⟩⟩ t

/-- A machine-checked proxy for "the lazy solver does not sample the oracle table": `lazySolver`
is well-typed for an INFINITE message space (here `ℕ`), for which no uniform table exists and
`pkSolver` cannot even be stated.  This is not a cost statement. -/
noncomputable example {β : Type*} [Fintype F] [DecidableEq F] (t : G → Strategy F F G ℕ β) :
    G → PMF β :=
  lazySolver t

/-- The generator hypothesis of section B cannot be dropped: in the two-dimensional module
`ZMod 5 × ZMod 5` the element `(0, 1)` is not a multiple of the nonzero element `(1, 0)`.  A
query outside the subgroup generated by `H m` is exactly what group-membership validation by B
has to exclude. -/
example : ¬ ∃ c : ZMod 5, ((0, 1) : ZMod 5 × ZMod 5) = c • ((1, 0) : ZMod 5 × ZMod 5) := by
  decide

end NonVacuity

end KeyPrivacy

end BlindPRF
