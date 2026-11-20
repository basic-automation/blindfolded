/-
  BlindPRF/Unlinkability.lean — blind-signature BLINDNESS against a MALICIOUS signer B, in the
  standard two-session game, where B also gets to see A's FINAL OUTPUTS.

  Why this file exists.  "B's view of one session is independent of the message" (the first
  protocol message `a = r • H m` is perfectly hiding) is NOT the blindness property of a blind
  signature scheme.  In the blindness game (Juels–Luby–Ostrovsky style) the signer B

      1. talks to party A in two sessions that carry the messages `m₀`, `m₁` in an order given by
         a hidden bit `β` (session 0 carries `m_β`),
      2. is then shown A's two final outputs, listed in MESSAGE order (signature on `m₀`,
         signature on `m₁`), or a single abort symbol,
      3. and has to guess `β`, i.e. which session produced which signature.

  B is malicious: it need not answer with `k • a`.  A signer that answers session 0 under key
  `k₀` and session 1 under a different key `k₁` leaves a recognisable mark on A's outputs and
  wins this game with certainty (`tagging_attack`), although — in a group of prime order and
  for non-identity hashes — everything it saw before the outputs were released is independent
  of `β` (`blindedPair_dist_eq`).  So the bare protocol is NOT blind in the blind-signature
  sense.  Blindness is recovered when A CHECKS B's reply against a public commitment to B's key
  and releases its outputs only if BOTH sessions pass (`blindness`, `blindness_pairing`);
  releasing the outputs per session instead is again insecure (`selective_abort`), and so is
  checking the two sessions against two different keys (`per_client_keys_tagging`).

  The game is defined exactly once (`blindnessGame`), with A's acceptance test `Valid` as a
  parameter, and that same definition is used in the positive and in the negative theorems.
  Three further games occur:
  * `perSessionGame` (per-session release) — a variant used only for the negative result
    `selective_abort`; the same signer run in `blindnessGame` only sees the abort symbol
    (`tagReply_aborts`);
  * `perClientGame` (one test per session) — a variant used only for the negative result
    `per_client_keys_tagging`; with twice the same test it IS `blindnessGame`
    (`perClientGame_same`);
  * `blindnessGameN` (any finite number of sessions) — a generalisation; `blindnessGame` is its
    two-session instance (`blindnessGame_eq_blindnessGameN`).

  Contents.
  * Algebra.  `exists_unit_blind_eq` (changing the message = multiplying the coin by a fixed
    unit), `exists_key_of_checkReply` (for ANY public key `pk`, the pairing check of
    `BlindPRF/PublicVerify.lean` is sound for one single scalar `k`).
  * Definitions.  The four games above, the explicit signers `honestReply`, `tagReply`,
    `sepReply`, `honestReplyN`, the guessers `tagGuess`, `abortGuess`, `sepGuess`, and the
    coin-free experiments `simGame`, `simGameN` (proof devices).
  * POSITIVE.  `blindnessGame_eq_sim` (with a sound check, B's whole experiment is a function of
    the two blinded elements), `blindness` (the game has the same output distribution for both
    values of `β`), `blindness_of_sound_on_nonzero` (the same, assuming soundness only for
    non-identity first messages), `blindness_view` (so does B's complete view),
    `blindness_guess_fair` (B guesses a uniform hidden `β` with probability exactly one half),
    `blindness_two_stage` (B may first choose the messages, the test and a state at random),
    `blindness_pairing` / `blindness_pairing_guess_fair` / `blindness_pairing_two_stage` (the
    same for the pairing check against an arbitrary, possibly maliciously chosen, public key).
  * NON-DEGENERACY.  `blindnessGame_honest`, `blindnessGame_honest_pairing`: against the honest
    signer A never aborts and outputs the two genuine signatures, so the positive theorems are
    not true merely because A always aborts.  `blindness_pairing_model`: all hypotheses of
    `blindness_pairing` are simultaneously satisfiable.
  * NEGATIVE.  `tagging_attack` (+ `_false`, `_true`, `_wins`, `tagging_not_blind`): without a
    check, a signer using two keys wins with certainty.  `per_client_keys_tagging`
    (+ `_pairing`): the same signer wins when each session is checked against its own key.
    `selective_abort` (+ `_pairing`, `_wins`, `selective_abort_not_blind`): with per-session
    release, even a sound and complete check does not help.
  * NECESSITY of the hypotheses of `blindness`, in the SAME game and for EVERY test (in
    particular for sound and complete ones).  `separating_test_wins`: a public test that
    separates the blinded forms of the two messages wins with certainty.  Instances:
    `hash_zero_left_wins`, `hash_zero_right_wins` (one hash is the identity) and
    `rank_two_wins` (`G = F × F` is not one-dimensional).  So a sound check does not make the
    game unlosable by construction.
  * One session.  `blinded_dist_eq`, `session_output_unlinkable`: B's view of a checked session,
    together with A's accepted output, is distributed as if the session had been run on an
    unrelated message.
  * Any number of sessions.  `blindnessGameN`, `blindnessN`, `blindnessN_pairing`: the signer's
    output distribution is the same for all assignments (permutations) of messages to sessions;
    `blindnessGameN_honest` (non-degeneracy).

  What this file does NOT prove.
  * The headline theorem `blindness` is about TWO sessions.  The `n`-session statement
    `blindnessN` is about a game in which B receives all blinded elements at once, answers all
    of them at once, and A releases all outputs together or none; schedules in which A releases
    some output before every session is answered, and clients that take part in further
    sessions, are not modelled.
  * The check must be PERFECTLY sound for one fixed key (`hV`).  A check that is only
    statistically sound (an interactive proof of discrete-log equality has soundness error about
    `1 / |F|`) or sound only in the random-oracle model (Fiat–Shamir) is not covered by
    `blindness`; for such checks one would expect closeness up to the soundness error, but no
    such statement is proven here.
  * The same test `Valid` — in the pairing instance: the same public key `pk` — is applied in
    both sessions.  A signer that can show different public keys to different clients tags them
    (`per_client_keys_tagging`); that every client sees the same `pk` is an assumption about the
    deployment, not something proven.
  * The messages `m₀`, `m₁` are fixed before the coins are drawn (in `blindness_two_stage`:
    chosen by the signer before the coins are drawn and independently of them) and satisfy
    `H m ≠ 0`; the coins are uniform on the nonzero scalars, independent, and never seen by B;
    `G` is one-dimensional over `F` (a cyclic group of prime order).  The hash function `H` is a
    fixed function, not a random oracle.
  * Nothing here is about unforgeability or about hiding B's key from A.  No hardness assumption
    is used or needed: every probabilistic statement is an exact equality (in the negative
    results: an exact computation) of probability distributions and holds for computationally
    unbounded strategies.
-/
import BlindPRF.Correctness
import BlindPRF.Prob
import BlindPRF.PublicVerify

namespace BlindPRF

namespace Unlinkability

/-! ## Algebra (no probability) -/

section Algebra

variable {F G M : Type*} [Field F] [AddCommGroup G] [Module F G] {g : G}

/-- A nonzero coin neither creates nor removes the identity: the blinded element is the identity
exactly when the hash of the message is. -/
theorem blinded_eq_zero_iff (H : M → G) (m : M) (r : Fˣ) : blind H m r = 0 ↔ H m = 0 := by
  show (r : F) • H m = 0 ↔ H m = 0
  rw [smul_eq_zero]
  exact ⟨fun h => h.resolve_left r.ne_zero, Or.inr⟩

/-- If the hash of the message is not the identity then neither is the blinded element. -/
theorem blinded_ne_zero (H : M → G) {m : M} (hm : H m ≠ 0) (r : Fˣ) : blind H m r ≠ 0 :=
  fun h => hm ((blinded_eq_zero_iff H m r).mp h)

/-- **Re-randomisation.**  In a group of prime order, for two messages whose hashes are not the
identity there is a fixed nonzero scalar `u` such that blinding `m'` with coin `r` gives exactly
the same group element as blinding `m` with coin `r * u`.  (A statement about group elements;
`u` is a discrete logarithm and nothing here says it can be computed.) -/
theorem exists_unit_blind_eq (hg : IsGenerator F g) (H : M → G) {m m' : M}
    (hm : H m ≠ 0) (hm' : H m' ≠ 0) :
    ∃ u : Fˣ, ∀ r : Fˣ, blind H m' r = blind H m (r * u) := by
  obtain ⟨c, hc⟩ := (hg.of_ne_zero hm).spans (H m')
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hm' (by simpa using hc.symm)
  refine ⟨Units.mk0 c hc0, fun r => ?_⟩
  show (r : F) • H m' = ((r * Units.mk0 c hc0 : Fˣ) : F) • H m
  rw [Units.val_mul, Units.val_mk0, mul_smul, hc]

/-- Replies to a non-identity element computed under two different keys are different. -/
theorem evaluate_ne_of_wrong_key {k k' : F} (hk : k' ≠ k) {a : G} (ha : a ≠ 0) :
    evaluate k' a ≠ evaluate k a :=
  fun h => hk (smul_left_injective F ha h)

/-- A test that is sound for the key `k` rejects the reply to a non-identity element computed
under any other key `k'`. -/
theorem wrong_key_rejected (Valid : G → G → Bool) {k k' : F} (hk : k' ≠ k)
    (hV : ∀ a b, Valid a b = true → b = evaluate k a) {a : G} (ha : a ≠ 0) :
    Valid a (evaluate k' a) = false := by
  by_contra hcon
  rw [Bool.not_eq_false] at hcon
  exact evaluate_ne_of_wrong_key hk ha (hV _ _ hcon)

end Algebra

/-! ## The pairing check as a Boolean test -/

section Pairing

variable {F G G₂ GT : Type*} [Field F] [AddCommGroup G] [Module F G] [AddCommGroup G₂]
  [Module F G₂] [AddCommGroup GT] [Module F GT]

/-- A's pairing check `e b g₂ = e a pk` is an equation in the target group, so A can evaluate it
as soon as equality in `GT` is decidable.  This instance lets the check be used as the Boolean
acceptance test `fun a b => decide (PublicVerify.checkReply e g₂ pk a b)` of the game.

The instance is `scoped`: it is active inside the namespace `BlindPRF.Unlinkability` and after
`open scoped BlindPRF.Unlinkability`, and it is NOT exported to every file that imports this one
(the predicate `checkReply` belongs to `BlindPRF/PublicVerify.lean`).  The Boolean `decide p`
does not depend on the decision procedure, so a caller whose goal mentions a different
`Decidable` instance for the same check can still apply the theorems below (`convert` bridges
the two). -/
scoped instance checkReplyDecidable [DecidableEq GT] (e : G →ₗ[F] G₂ →ₗ[F] GT) (g₂ pk : G₂)
    (a b : G) : Decidable (PublicVerify.checkReply e g₂ pk a b) :=
  inferInstanceAs (Decidable (e b g₂ = e a pk))

/-- **A public key that matches no secret key accepts nothing.**  Let `G` be one-dimensional
with generator `g`.  If `pk` pairs like no multiple of `g₂` (there is no scalar `k` with
`e g pk = k • e g g₂`), then the only first message `a` for which ANY reply passes A's check is
the identity.  No non-degeneracy of the pairing is needed.  It does NOT say that such a `pk`
exists, and it says nothing about replies to the identity. -/
theorem eq_zero_of_checkReply_of_no_key {g : G} (hg : IsGenerator F g)
    (e : G →ₗ[F] G₂ →ₗ[F] GT) (g₂ pk : G₂) (hno : ¬∃ k : F, e g pk = k • e g g₂) {a b : G}
    (hab : PublicVerify.checkReply e g₂ pk a b) : a = 0 := by
  obtain ⟨c, rfl⟩ := hg.spans a
  obtain ⟨d, rfl⟩ := hg.spans b
  have hab' : d • e g g₂ = c • e g pk := by
    simpa [PublicVerify.checkReply, map_smul, LinearMap.smul_apply] using hab
  by_cases hc : c = 0
  · rw [hc, zero_smul]
  · exact absurd ⟨c⁻¹ * d, by rw [mul_smul, hab', smul_smul, inv_mul_cancel₀ hc, one_smul]⟩ hno

/-- **The pairing check is sound for ONE key, whatever public key B published.**  Let `G` be
one-dimensional with generator `g` and let the pairing be non-degenerate at `g₂`.  Then for
EVERY element `pk : G₂` — honestly generated or not, and not even assumed to be a multiple of
`g₂` — there is a single scalar `k` such that every reply `b` that passes A's check on `a` is the
honest reply `evaluate k a = k • a` under that `k`.  (If `pk` is consistent with no key at all,
no reply to a non-identity element passes — `eq_zero_of_checkReply_of_no_key` — and the
statement holds trivially for that `pk`.)

It does NOT say that `k` can be computed from `pk`, that B knows `k`, or that the check ever
passes; completeness for honestly generated keys is `PublicVerify.checkReply_evaluate`. -/
theorem exists_key_of_checkReply {g : G} (hg : IsGenerator F g) (e : G →ₗ[F] G₂ →ₗ[F] GT)
    (g₂ pk : G₂) (hnd : Function.Injective fun x : G => e x g₂) :
    ∃ k : F, ∀ a b : G, PublicVerify.checkReply e g₂ pk a b → b = evaluate k a := by
  by_cases h : ∃ k : F, e g pk = k • e g g₂
  · obtain ⟨k, hk⟩ := h
    refine ⟨k, fun a b hab => hnd ?_⟩
    obtain ⟨c, rfl⟩ := hg.spans a
    show e b g₂ = e (k • c • g) g₂
    rw [hab, map_smul, map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply,
      LinearMap.smul_apply, hk]
    exact smul_comm c k _
  · refine ⟨0, fun a b hab => hnd ?_⟩
    have ha : a = 0 := eq_zero_of_checkReply_of_no_key hg e g₂ pk h hab
    subst ha
    have hab' : e b g₂ = e 0 pk := hab
    show e b g₂ = e (evaluate (0 : F) (0 : G)) g₂
    rw [hab']
    simp [evaluate]

end Pairing

/-! ## The games -/

/-- **The two-session blindness game** against a malicious signer, with all-or-nothing release
of A's outputs.

* `Valid a b` is A's acceptance test on (what A sent, what B replied).  It is a parameter of the
  game and a function of the transcript only (in particular it cannot depend on A's coins or on
  the hidden bit); the same test is used in both sessions.
* A draws two independent uniform nonzero coins `rs = (r₀, r₁)`.  Session 0 carries the message
  `m_β` (that is `m₁` if `β` is true and `m₀` otherwise) and session 1 carries the other one.
* B is an arbitrary randomized, stateful, computationally unbounded strategy.  `reply` sees BOTH
  blinded elements `(a₀, a₁)` (in session order) and returns its state together with both
  replies `(b₀, b₁)`.  B never sees the coins or `β`.
* If both replies pass the test, A unblinds them and B's second stage `guess` receives its state
  and `some (σ₀, σ₁)`, the outputs listed in MESSAGE order: `σ₀` is A's output for `m₀` and `σ₁`
  is A's output for `m₁`, whichever sessions produced them.  If at least one reply fails the
  test, `guess` receives `none` (A releases nothing at all).
* The game returns the output of B's second stage.  In the blindness game proper the output
  type `γ` is `Bool` and the output is B's guess of `β`: B "wins" if the guess equals `β`, and
  blindness means that the distribution of the guess is the same for `β = false` and
  `β = true`.  The output type is left arbitrary because that costs nothing and lets the
  theorems speak about anything B can compute, for instance its complete view
  (`blindness_view`).

The scalar field `F` is an explicit argument because nothing else in the type mentions it. -/
noncomputable def blindnessGame (F : Type*) {G M S γ : Type*} [Field F] [Fintype F]
    [DecidableEq F] [AddCommGroup G] [Module F G] (H : M → G) (Valid : G → G → Bool)
    (m₀ m₁ : M) (reply : G × G → PMF (S × G × G)) (guess : S → Option (G × G) → PMF γ)
    (β : Bool) : PMF γ :=
  (unif (Fˣ × Fˣ)).bind fun rs : Fˣ × Fˣ =>
    let a₀ := blind H (if β then m₁ else m₀) rs.1
    let a₁ := blind H (if β then m₀ else m₁) rs.2
    (reply (a₀, a₁)).bind fun t : S × G × G =>
      guess t.1
        (if Valid a₀ t.2.1 && Valid a₁ t.2.2 then
          some (if β then (unblind rs.2 t.2.2, unblind rs.1 t.2.1)
            else (unblind rs.1 t.2.1, unblind rs.2 t.2.2))
        else none)

/-- **The variant game with PER-SESSION release** (used only for the negative result
`selective_abort`).  Everything is as in `blindnessGame`, except that A decides for each session
separately: B's second stage receives a pair of optional outputs in MESSAGE order, the first
component being A's output for `m₀` if the session that carried `m₀` passed the test and `none`
otherwise, and likewise the second component for `m₁`. -/
noncomputable def perSessionGame (F : Type*) {G M S γ : Type*} [Field F] [Fintype F]
    [DecidableEq F] [AddCommGroup G] [Module F G] (H : M → G) (Valid : G → G → Bool)
    (m₀ m₁ : M) (reply : G × G → PMF (S × G × G))
    (guess : S → Option G × Option G → PMF γ) (β : Bool) : PMF γ :=
  (unif (Fˣ × Fˣ)).bind fun rs : Fˣ × Fˣ =>
    let a₀ := blind H (if β then m₁ else m₀) rs.1
    let a₁ := blind H (if β then m₀ else m₁) rs.2
    (reply (a₀, a₁)).bind fun t : S × G × G =>
      let o₀ : Option G := if Valid a₀ t.2.1 then some (unblind rs.1 t.2.1) else none
      let o₁ : Option G := if Valid a₁ t.2.2 then some (unblind rs.2 t.2.2) else none
      guess t.1 (if β then (o₁, o₀) else (o₀, o₁))

/-- **The variant game with ONE TEST PER SESSION** (used only for the negative result
`per_client_keys_tagging`).  Everything is as in `blindnessGame`, except that the reply of
session 0 is tested with `Valid₀` and the reply of session 1 with `Valid₁`.  This models a
signer that shows different public keys to different clients: the client of session 0 checks
against one key, the client of session 1 against another.  With `Valid₀ = Valid₁` it is
`blindnessGame` (`perClientGame_same`). -/
noncomputable def perClientGame (F : Type*) {G M S γ : Type*} [Field F] [Fintype F]
    [DecidableEq F] [AddCommGroup G] [Module F G] (H : M → G) (Valid₀ Valid₁ : G → G → Bool)
    (m₀ m₁ : M) (reply : G × G → PMF (S × G × G)) (guess : S → Option (G × G) → PMF γ)
    (β : Bool) : PMF γ :=
  (unif (Fˣ × Fˣ)).bind fun rs : Fˣ × Fˣ =>
    let a₀ := blind H (if β then m₁ else m₀) rs.1
    let a₁ := blind H (if β then m₀ else m₁) rs.2
    (reply (a₀, a₁)).bind fun t : S × G × G =>
      guess t.1
        (if Valid₀ a₀ t.2.1 && Valid₁ a₁ t.2.2 then
          some (if β then (unblind rs.2 t.2.2, unblind rs.1 t.2.1)
            else (unblind rs.1 t.2.1, unblind rs.2 t.2.2))
        else none)

/-- **The blindness game with any finite number of sessions.**  Sessions and messages are both
indexed by the finite type `ι` (think `Fin n`); `m j` is the `j`-th message and the hidden
permutation `π` says which message each session carries: session `i` carries `m (π i)`.

* A draws one uniform nonzero coin `r i` per session, independently.
* B (randomized, stateful, unbounded) receives ALL blinded elements at once, indexed by session,
  and returns its state together with one reply per session.  It never sees the coins or `π`.
* If EVERY reply passes the test `Valid`, B's second stage receives `some σ`, where `σ j` is A's
  output for the message `m j` — the unblinded reply of the session `π.symm j` that carried it —
  so the outputs are listed in MESSAGE order.  If at least one reply fails, it receives `none`.
* The game returns the output of B's second stage.  Blindness means that its distribution does
  not depend on `π` (`blindnessN`).

`blindnessGame` is the instance `ι = Bool`, with `π` the identity or the swap, up to the
translation of strategies between pairs and `Bool`-indexed families that is spelled out in
`blindnessGame_eq_blindnessGameN`. -/
noncomputable def blindnessGameN (F : Type*) {G M S γ ι : Type*} [Field F] [Fintype F]
    [DecidableEq F] [AddCommGroup G] [Module F G] [Fintype ι] [DecidableEq ι] (H : M → G)
    (Valid : G → G → Bool) (m : ι → M) (reply : (ι → G) → PMF (S × (ι → G)))
    (guess : S → Option (ι → G) → PMF γ) (π : Equiv.Perm ι) : PMF γ :=
  (unif (ι → Fˣ)).bind fun r : ι → Fˣ =>
    (reply fun i => blind H (m (π i)) (r i)).bind fun t : S × (ι → G) =>
      guess t.1
        (if ∀ i, Valid (blind H (m (π i)) (r i)) (t.2 i) = true then
          some fun j => unblind (r (π.symm j)) (t.2 (π.symm j))
        else none)

section Strategies

variable {F G M : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- A coin-free and bit-free experiment (a proof device for `blindness`): it depends only on two
group elements `p = (a₀, a₁)` and on the two constants `prf H k m₀`, `prf H k m₁`.  It computes
the replies and feeds the guessing stage with the two constants if both replies pass the test
and with the abort symbol otherwise.  Whether B could compute these constants by itself is
irrelevant for the information-theoretic statements of this file and is NOT claimed: in
`blindness_pairing` the key `k` is obtained non-constructively from the public key. -/
noncomputable def simGame {S γ : Type*} (H : M → G) (Valid : G → G → Bool) (k : F)
    (m₀ m₁ : M) (reply : G × G → PMF (S × G × G)) (guess : S → Option (G × G) → PMF γ)
    (p : G × G) : PMF γ :=
  (reply p).bind fun t : S × G × G =>
    guess t.1
      (if Valid p.1 t.2.1 && Valid p.2 t.2.2 then some (prf H k m₀, prf H k m₁) else none)

/-- The `n`-session analogue of `simGame` (a proof device for `blindnessN`): an experiment that
depends only on the family `a` of group elements and on the constants `prf H k (m j)`.  As for
`simGame`, nothing is claimed about who can compute it. -/
noncomputable def simGameN {ι S γ : Type*} [Fintype ι] (H : M → G) (Valid : G → G → Bool)
    (k : F) (m : ι → M) (reply : (ι → G) → PMF (S × (ι → G)))
    (guess : S → Option (ι → G) → PMF γ) (a : ι → G) : PMF γ :=
  (reply a).bind fun t : S × (ι → G) =>
    guess t.1 (if ∀ i, Valid (a i) (t.2 i) = true then some fun j => prf H k (m j) else none)

/-- The honest signer with key `k`: no state, both sessions answered with `k • a`. -/
noncomputable def honestReply (k : F) (p : G × G) : PMF (Unit × G × G) :=
  PMF.pure ((), evaluate k p.1, evaluate k p.2)

/-- The honest signer with key `k` in the `n`-session game: no state, every session answered
with `k • a`. -/
noncomputable def honestReplyN {ι : Type*} (k : F) (a : ι → G) : PMF (Unit × (ι → G)) :=
  PMF.pure ((), fun i => evaluate k (a i))

/-- The tagging signer: no state, session 0 answered under key `k₀`, session 1 under key `k₁`.
(`tagReply k k` is the honest signer.) -/
noncomputable def tagReply (k₀ k₁ : F) (p : G × G) : PMF (Unit × G × G) :=
  PMF.pure ((), evaluate k₀ p.1, evaluate k₁ p.2)

/-- The guessing stage of the tagging attack: guess `false` ("session 0 carried `m₀`") exactly
when A's outputs are the signature on `m₀` under `k₀` and the signature on `m₁` under `k₁`. -/
noncomputable def tagGuess [DecidableEq G] (H : M → G) (k₀ k₁ : F) (m₀ m₁ : M) (_ : Unit)
    (out : Option (G × G)) : PMF Bool :=
  PMF.pure (decide (out ≠ some (prf H k₀ m₀, prf H k₁ m₁)))

/-- The guessing stage of the selective-abort attack: guess `true` ("session 0 carried `m₁`")
exactly when A released no output for `m₀`. -/
noncomputable def abortGuess (_ : Unit) (out : Option G × Option G) : PMF Bool :=
  PMF.pure out.1.isNone

/-- A signer that follows the protocol with key `k` but remembers one bit: the result of a
public test `T` applied to the blinded element of session 0. -/
noncomputable def sepReply (T : G → Bool) (k : F) (p : G × G) : PMF (Bool × G × G) :=
  PMF.pure (T p.1, evaluate k p.1, evaluate k p.2)

/-- The guessing stage that outputs the remembered bit and ignores A's outputs. -/
noncomputable def sepGuess (s : Bool) (_ : Option (G × G)) : PMF Bool :=
  PMF.pure s

theorem tagReply_self (k : F) : (tagReply k k : G × G → PMF (Unit × G × G)) = honestReply k :=
  rfl

end Strategies

/-! ## Three general probability facts -/

section Prob

/-- If a guess `b'` is drawn from a distribution `P` that does not depend on the uniformly
random bit `b`, then the event "the guess is right" is a fair coin. -/
theorem guess_fair_of_independent (P : PMF Bool) :
    ((unif Bool).bind fun b : Bool => P.map fun b' : Bool => decide (b' = b)) = unif Bool := by
  have hsum : P true + P false = 1 := by
    have := P.tsum_coe
    rwa [tsum_fintype, Fintype.sum_bool] at this
  have hsum' : P false + P true = 1 := by rw [add_comm]; exact hsum
  have h1 : (fun b' : Bool => decide (b' = true)) = id := by funext b'; simp
  have h0 : (fun b' : Bool => decide (b' = false)) = not := by funext b'; simp
  have hnot : ∀ c, P.map not c = P (!c) := by
    intro c
    rw [PMF.map_apply, tsum_fintype, Fintype.sum_bool]
    cases c <;> simp
  ext c
  rw [PMF.bind_apply, tsum_fintype, Fintype.sum_bool, h1, h0, PMF.map_id, hnot, unif_apply,
    unif_apply, ← mul_add, unif_apply]
  cases c
  · rw [Bool.not_false, hsum', mul_one]
  · rw [Bool.not_true, hsum, mul_one]

/-- The two point masses on `Bool` are different distributions. -/
theorem pure_false_ne_pure_true : (PMF.pure false : PMF Bool) ≠ PMF.pure true := by
  intro h
  have h' := congrArg (fun p : PMF Bool => p true) h
  simp at h'

/-- Two experiments that continue in the same way from every outcome that the first stage
produces with positive probability have the same distribution. -/
theorem bind_congr_on_support {α β : Type*} (p : PMF α) (f f' : α → PMF β)
    (h : ∀ a ∈ p.support, f a = f' a) : p.bind f = p.bind f' := by
  ext b
  rw [PMF.bind_apply, PMF.bind_apply]
  refine tsum_congr fun a => ?_
  by_cases ha : p a = 0
  · rw [ha, zero_mul, zero_mul]
  · rw [h a ((PMF.mem_support_iff p a).mpr ha)]

end Prob

section Main

variable {F G M : Type*} [Field F] [Fintype F] [DecidableEq F] [AddCommGroup G] [Module F G]
  {g : G}

/-- With twice the same test, the per-client game is the blindness game (by definition). -/
theorem perClientGame_same (H : M → G) (Valid : G → G → Bool) (m₀ m₁ : M) {S γ : Type*}
    (reply : G × G → PMF (S × G × G)) (guess : S → Option (G × G) → PMF γ) (β : Bool) :
    perClientGame F H Valid Valid m₀ m₁ reply guess β =
      blindnessGame F H Valid m₀ m₁ reply guess β :=
  rfl

/-! ## What B sees before the outputs are released is independent of `β` -/

/-- One session: with a uniform nonzero coin, the blinded element has the same distribution for
any two messages with non-identity hashes.  (Re-proved here so that this file depends only on
`Basic`, `Prob`, `Correctness` and `PublicVerify`.) -/
theorem blinded_dist_eq (hg : IsGenerator F g) (H : M → G) {m m' : M} (hm : H m ≠ 0)
    (hm' : H m' ≠ 0) : (unif Fˣ).map (blind H m) = (unif Fˣ).map (blind H m') := by
  obtain ⟨u, hu⟩ := exists_unit_blind_eq hg H hm hm'
  exact (unif_map_eq_of_equiv (Equiv.mulRight u) (blind H m') (blind H m)
    (fun r => (hu r).symm)).symm

/-- Any experiment `W` that continues from the PAIR of blinded elements has the same
distribution whether the two sessions carry `(m₀, m₁)` or `(m₁, m₀)`: the two independent coins
are re-randomised by the bijection `(r₀, r₁) ↦ (r₀ * u, r₁ * u⁻¹)` of `Fˣ × Fˣ`. -/
theorem unif_bind_blind_swap {γ : Type*} (hg : IsGenerator F g) (H : M → G) {m₀ m₁ : M}
    (h₀ : H m₀ ≠ 0) (h₁ : H m₁ ≠ 0) (W : G × G → PMF γ) :
    ((unif (Fˣ × Fˣ)).bind fun rs : Fˣ × Fˣ => W (blind H m₀ rs.1, blind H m₁ rs.2)) =
      (unif (Fˣ × Fˣ)).bind fun rs : Fˣ × Fˣ => W (blind H m₁ rs.1, blind H m₀ rs.2) := by
  obtain ⟨u, hu⟩ := exists_unit_blind_eq hg H h₀ h₁
  refine (unif_bind_eq_of_equiv ((Equiv.mulRight u).prodCongr (Equiv.mulRight u⁻¹))
    (fun rs : Fˣ × Fˣ => W (blind H m₁ rs.1, blind H m₀ rs.2))
    (fun rs : Fˣ × Fˣ => W (blind H m₀ rs.1, blind H m₁ rs.2)) fun rs => ?_).symm
  have e1 : blind H m₀ (rs.1 * u) = blind H m₁ rs.1 := (hu rs.1).symm
  have e2 : blind H m₁ (rs.2 * u⁻¹) = blind H m₀ rs.2 := by
    rw [hu, inv_mul_cancel_right]
  simp only [Equiv.prodCongr_apply, Prod.map, Equiv.coe_mulRight, e1, e2]

/-- **Before the outputs are released, B has learned nothing about the order.**  The pair of
blinded elements that B receives (in session order) has exactly the same distribution whether
session 0 carries `m₀` and session 1 carries `m₁`, or the other way round.

This is a statement about B's view of the two protocol messages ONLY.  It does NOT say that B
cannot link sessions to signatures once A's outputs are revealed: without a reply check it can
(`tagging_attack`). -/
theorem blindedPair_dist_eq (hg : IsGenerator F g) (H : M → G) {m₀ m₁ : M}
    (h₀ : H m₀ ≠ 0) (h₁ : H m₁ ≠ 0) :
    (unif (Fˣ × Fˣ)).map (fun rs : Fˣ × Fˣ => (blind H m₀ rs.1, blind H m₁ rs.2)) =
      (unif (Fˣ × Fˣ)).map (fun rs : Fˣ × Fˣ => (blind H m₁ rs.1, blind H m₀ rs.2)) :=
  unif_bind_blind_swap hg H h₀ h₁ (fun p : G × G => PMF.pure p)

/-! ## POSITIVE: blindness with a sound reply check and all-or-nothing release -/

/-- The simulation step under the weakest form of soundness that the argument uses: the test is
sound for the key `k` on the elements A ACTUALLY SENDS, i.e. on the blinded forms of `m₀` and
`m₁`.  Then the blindness game, for either value of the hidden bit, is the same as drawing the
coins and handing the two blinded elements to the coin-free and bit-free experiment `simGame`.
This is the common core of `blindnessGame_eq_sim` and `blindness_of_sound_on_nonzero`; like the
former, it does NOT yet say that the two values of `β` give the same distribution. -/
theorem blindnessGame_eq_sim_of_sent (H : M → G) (Valid : G → G → Bool) (k : F) (m₀ m₁ : M)
    (hV : ∀ m : M, m = m₀ ∨ m = m₁ → ∀ (r : Fˣ) (b : G),
      Valid (blind H m r) b = true → b = evaluate k (blind H m r))
    {S γ : Type*} (reply : G × G → PMF (S × G × G)) (guess : S → Option (G × G) → PMF γ)
    (β : Bool) :
    blindnessGame F H Valid m₀ m₁ reply guess β =
      (unif (Fˣ × Fˣ)).bind fun rs : Fˣ × Fˣ =>
        simGame H Valid k m₀ m₁ reply guess
          (blind H (if β then m₁ else m₀) rs.1, blind H (if β then m₀ else m₁) rs.2) := by
  have hs₀ : (if β then m₁ else m₀) = m₀ ∨ (if β then m₁ else m₀) = m₁ := by
    cases β <;> simp
  have hs₁ : (if β then m₀ else m₁) = m₀ ∨ (if β then m₀ else m₁) = m₁ := by
    cases β <;> simp
  simp only [blindnessGame, simGame]
  congr 1
  funext rs
  congr 1
  funext t
  congr 1
  by_cases hv : (Valid (blind H (if β then m₁ else m₀) rs.1) t.2.1 &&
      Valid (blind H (if β then m₀ else m₁) rs.2) t.2.2) = true
  · rw [ite_eq_left hv, ite_eq_left hv]
    obtain ⟨hv0, hv1⟩ := Bool.and_eq_true_iff.mp hv
    rw [hV _ hs₀ _ _ hv0, hV _ hs₁ _ _ hv1]
    cases β <;> simp [unblind_evaluate_blind]
  · rw [ite_eq_right hv, ite_eq_right hv]

/-- **With a sound check, B's whole experiment is a function of the two blinded elements.**
Suppose A's test is sound for the key `k`: a reply that passes is the honest reply
`evaluate k a`.  Then the blindness game, for either value of the hidden bit, is the same as
drawing the coins, handing the two blinded elements to the coin-free and bit-free experiment
`simGame` and returning its result.  Reason: whenever A does not abort, its outputs are the
constants `prf H k m₀` and `prf H k m₁`, which carry no trace of the coins or of the session
order.

No assumption on the group or on the hashes is needed for this step.  It does NOT yet say the
two values of `β` give the same distribution: that is `blindness`. -/
theorem blindnessGame_eq_sim (H : M → G) (Valid : G → G → Bool) (k : F)
    (hV : ∀ a b, Valid a b = true → b = evaluate k a) (m₀ m₁ : M) {S γ : Type*}
    (reply : G × G → PMF (S × G × G)) (guess : S → Option (G × G) → PMF γ) (β : Bool) :
    blindnessGame F H Valid m₀ m₁ reply guess β =
      (unif (Fˣ × Fˣ)).bind fun rs : Fˣ × Fˣ =>
        simGame H Valid k m₀ m₁ reply guess
          (blind H (if β then m₁ else m₀) rs.1, blind H (if β then m₀ else m₁) rs.2) :=
  blindnessGame_eq_sim_of_sent H Valid k m₀ m₁ (fun _ _ _ _ h => hV _ _ h) reply guess β

/-- **Blindness, assuming soundness only for non-identity first messages.**  The same statement
as `blindness`, under a weaker hypothesis on A's test: a reply `b` that passes the test on a
NON-IDENTITY element `a` is the honest reply `evaluate k a`; nothing is assumed about what the
test does on `a = 0`.  This suffices because A never sends the identity (the hashes are
non-identity and the coins are nonzero).  `blindness` is the special case of a test that is
sound everywhere.  All limitations listed at `blindness` apply unchanged. -/
theorem blindness_of_sound_on_nonzero (hg : IsGenerator F g) (H : M → G) {m₀ m₁ : M}
    (h₀ : H m₀ ≠ 0) (h₁ : H m₁ ≠ 0) (Valid : G → G → Bool) (k : F)
    (hV : ∀ a b, a ≠ 0 → Valid a b = true → b = evaluate k a) {S γ : Type*}
    (reply : G × G → PMF (S × G × G)) (guess : S → Option (G × G) → PMF γ) :
    blindnessGame F H Valid m₀ m₁ reply guess false =
      blindnessGame F H Valid m₀ m₁ reply guess true := by
  have hV' : ∀ m : M, m = m₀ ∨ m = m₁ → ∀ (r : Fˣ) (b : G),
      Valid (blind H m r) b = true → b = evaluate k (blind H m r) := by
    intro m hm r b h
    rcases hm with hm | hm
    · exact hV _ _ (blinded_ne_zero H (hm ▸ h₀) r) h
    · exact hV _ _ (blinded_ne_zero H (hm ▸ h₁) r) h
  rw [blindnessGame_eq_sim_of_sent H Valid k m₀ m₁ hV',
    blindnessGame_eq_sim_of_sent H Valid k m₀ m₁ hV']
  exact unif_bind_blind_swap hg H h₀ h₁ _

/-- **Blindness against a malicious signer (two sessions, perfect).**

Setting: `G` is one-dimensional over `F` with generator `g` (a cyclic group of prime order),
`m₀`, `m₁` are two messages whose hashes are not the identity, and A's acceptance test `Valid`
is SOUND for one key `k`: a reply `b` to `a` that passes the test is the honest reply
`evaluate k a` (`hV`).

Claim: for every state type and every strategy `(reply, guess)` of the signer — randomized,
stateful, computationally unbounded, free to deviate from the protocol in any way, seeing both
blinded elements before it replies and A's final outputs (or the abort symbol) before it
guesses — the distribution of the signer's final output (its guess of `β` when `γ = Bool`; for a
general output type `γ`, anything else it may compute) is EXACTLY the same when session 0
carried `m₀` (`β = false`) and when it carried `m₁` (`β = true`).  So the signer cannot tell
which session produced which signature.  This is an equality of distributions; no hardness
assumption is used.

What this does NOT claim.
* Only two sessions.  The `n`-session game (guessing a permutation) is the separate theorem
  `blindnessN`, about the separately defined game `blindnessGameN`; see there for what that
  game does and does not model.
* `hV` demands PERFECT soundness with respect to ONE key for both sessions.  Checks that are
  only statistically sound (interactive proofs of discrete-log equality) or sound in the
  random-oracle model (Fiat–Shamir) do not satisfy `hV`, and are not covered.
* The same test `Valid` is used in both sessions, i.e. the signer shows the same public key to
  every client.  In the variant game in which the two sessions are checked against two
  different keys the signer wins with certainty (`per_client_keys_tagging`), and so it does in
  this game when there is no check at all (`tagging_attack`).
* A releases its outputs only if BOTH sessions pass; per-session release is insecure
  (`selective_abort`).  The outputs are released after both sessions are complete.
* The messages are fixed before the coins are drawn (they are universally quantified, so the
  signer may know and may have chosen them; for a randomized choice see `blindness_two_stage`),
  and both hashes must be non-identity.  That hypothesis and the hypothesis that `G` is
  one-dimensional cannot simply be dropped: `hash_zero_left_wins`, `hash_zero_right_wins`,
  `rank_two_wins`.
* A's coins are uniform on the nonzero scalars, independent, and secret.
* It says nothing about unforgeability, nor about what A learns about the key.
* By itself it does not say A ever accepts: for that see `blindnessGame_honest`. -/
theorem blindness (hg : IsGenerator F g) (H : M → G) {m₀ m₁ : M} (h₀ : H m₀ ≠ 0)
    (h₁ : H m₁ ≠ 0) (Valid : G → G → Bool) (k : F)
    (hV : ∀ a b, Valid a b = true → b = evaluate k a) {S γ : Type*}
    (reply : G × G → PMF (S × G × G)) (guess : S → Option (G × G) → PMF γ) :
    blindnessGame F H Valid m₀ m₁ reply guess false =
      blindnessGame F H Valid m₀ m₁ reply guess true :=
  blindness_of_sound_on_nonzero hg H h₀ h₁ Valid k (fun a b _ h => hV a b h) reply guess

/-- **The signer's complete view is independent of the session order.**  Under the hypotheses
of `blindness`, let the signer simply record everything: the two blinded elements it received,
its internal state, its two replies, and what A finally released (the two outputs in message
order, or the abort symbol).  The joint distribution of this record is exactly the same for both
values of the hidden bit.  This is `blindness` applied to the signer whose final output is its
whole view; the same limitations apply (two sessions, perfectly sound check for one key, same
test in both sessions, all-or-nothing release, coins not included in the view). -/
theorem blindness_view (hg : IsGenerator F g) (H : M → G) {m₀ m₁ : M} (h₀ : H m₀ ≠ 0)
    (h₁ : H m₁ ≠ 0) (Valid : G → G → Bool) (k : F)
    (hV : ∀ a b, Valid a b = true → b = evaluate k a) {S : Type*}
    (reply : G × G → PMF (S × G × G)) :
    blindnessGame F H Valid m₀ m₁
        (fun p : G × G => (reply p).map fun t : S × G × G => ((p, t), t.2))
        (fun (v : (G × G) × S × G × G) (out : Option (G × G)) => PMF.pure (v, out)) false =
      blindnessGame F H Valid m₀ m₁
        (fun p : G × G => (reply p).map fun t : S × G × G => ((p, t), t.2))
        (fun (v : (G × G) × S × G × G) (out : Option (G × G)) => PMF.pure (v, out)) true :=
  blindness hg H h₀ h₁ Valid k hV _ _

/-- **Advantage exactly zero.**  Under the hypotheses of `blindness`, if the hidden bit `β` is
uniform, then the event "the signer's guess equals `β`" is a fair coin: the malicious signer
identifies the session order with probability exactly one half, the success probability of a
blind guess.  The same limitations as for `blindness` apply (two sessions, perfectly sound check
for one key, same test in both sessions, all-or-nothing release). -/
theorem blindness_guess_fair (hg : IsGenerator F g) (H : M → G) {m₀ m₁ : M} (h₀ : H m₀ ≠ 0)
    (h₁ : H m₁ ≠ 0) (Valid : G → G → Bool) (k : F)
    (hV : ∀ a b, Valid a b = true → b = evaluate k a) {S : Type*}
    (reply : G × G → PMF (S × G × G)) (guess : S → Option (G × G) → PMF Bool) :
    ((unif Bool).bind fun β : Bool =>
      (blindnessGame F H Valid m₀ m₁ reply guess β).map fun b' : Bool => decide (b' = β)) =
      unif Bool := by
  have h : (fun β : Bool =>
      (blindnessGame F H Valid m₀ m₁ reply guess β).map fun b' : Bool => decide (b' = β)) =
      fun β : Bool =>
        (blindnessGame F H Valid m₀ m₁ reply guess false).map fun b' : Bool =>
          decide (b' = β) := by
    funext β
    cases β
    · rfl
    · rw [blindness hg H h₀ h₁ Valid k hV reply guess]
  rw [h]
  exact guess_fair_of_independent _

/-- **Blindness when the signer chooses the messages, the test and its state at random.**  The
signer's first stage `choose` outputs a value `c` from an arbitrary distribution; `c` determines
the two messages `m₀ c`, `m₁ c`, A's acceptance test `Valid c` (think: the public key that the
signer publishes) and whatever state the later stages `reply c`, `guess c` use.  Only then does
A draw its coins.  Suppose that for every `c` that occurs with positive probability both hashes
are non-identity and the test is sound for one key `k c`.  Then the distribution of the signer's
final output is the same for both values of the hidden bit.

This is `blindness` averaged over the first stage.  It does NOT cover a first stage that depends
on A's coins (the messages are still fixed before the coins are drawn), nor a signer that
influences the hash function `H`; all other limitations of `blindness` apply as well. -/
theorem blindness_two_stage (hg : IsGenerator F g) (H : M → G) {C S γ : Type*}
    (choose : PMF C) (m₀ m₁ : C → M) (Valid : C → G → G → Bool) (k : C → F)
    (h₀ : ∀ c ∈ choose.support, H (m₀ c) ≠ 0) (h₁ : ∀ c ∈ choose.support, H (m₁ c) ≠ 0)
    (hV : ∀ c ∈ choose.support, ∀ a b, Valid c a b = true → b = evaluate (k c) a)
    (reply : C → G × G → PMF (S × G × G)) (guess : C → S → Option (G × G) → PMF γ) :
    (choose.bind fun c : C =>
        blindnessGame F H (Valid c) (m₀ c) (m₁ c) (reply c) (guess c) false) =
      choose.bind fun c : C =>
        blindnessGame F H (Valid c) (m₀ c) (m₁ c) (reply c) (guess c) true :=
  bind_congr_on_support choose _ _ fun c hc =>
    blindness hg H (h₀ c hc) (h₁ c hc) (Valid c) (k c) (hV c hc) (reply c) (guess c)

/-- **Blindness with the public pairing check, for an ARBITRARY public key.**

A's test is the pairing equation `e b g₂ = e a pk` of `BlindPRF/PublicVerify.lean`; it uses only
the transcript `(a, b)` and public data.  The pairing is non-degenerate at `g₂` (`hnd`).  The
public key `pk` is ANY element of `G₂`: the signer may have chosen it maliciously, need not know
a corresponding secret key, and `pk` need not even be a multiple of `g₂`.  Then for every
strategy of the signer the two-session blindness game has the same output distribution for both
values of the hidden bit.

What this does NOT claim: see `blindness`.  In particular A uses the SAME `pk` in both sessions;
that is an assumption of the model (a signer able to show different public keys to different
clients is outside this theorem and can tag them: `per_client_keys_tagging_pairing`).  Only two
sessions are treated here (for more see `blindnessN_pairing`), and the check is the perfectly
sound pairing check, not a zero-knowledge proof of discrete-log equality.  That the signer
cannot make A accept a wrong signature is `PublicVerify.checked_run`, not this theorem. -/
theorem blindness_pairing {G₂ GT : Type*} [AddCommGroup G₂] [Module F G₂] [AddCommGroup GT]
    [Module F GT] [DecidableEq GT] (hg : IsGenerator F g) (H : M → G) {m₀ m₁ : M}
    (h₀ : H m₀ ≠ 0) (h₁ : H m₁ ≠ 0) (e : G →ₗ[F] G₂ →ₗ[F] GT) (g₂ : G₂)
    (hnd : Function.Injective fun x : G => e x g₂) (pk : G₂) {S γ : Type*}
    (reply : G × G → PMF (S × G × G)) (guess : S → Option (G × G) → PMF γ) :
    blindnessGame F H (fun a b => decide (PublicVerify.checkReply e g₂ pk a b)) m₀ m₁ reply
        guess false =
      blindnessGame F H (fun a b => decide (PublicVerify.checkReply e g₂ pk a b)) m₀ m₁ reply
        guess true := by
  obtain ⟨k, hk⟩ := exists_key_of_checkReply hg e g₂ pk hnd
  exact blindness hg H h₀ h₁ _ k (fun a b h => hk a b (of_decide_eq_true h)) reply guess

/-- With the pairing check against an arbitrary public key, the malicious signer guesses a
uniform hidden bit with probability exactly one half.  Same limitations as `blindness_pairing`. -/
theorem blindness_pairing_guess_fair {G₂ GT : Type*} [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup GT] [Module F GT] [DecidableEq GT] (hg : IsGenerator F g) (H : M → G)
    {m₀ m₁ : M} (h₀ : H m₀ ≠ 0) (h₁ : H m₁ ≠ 0) (e : G →ₗ[F] G₂ →ₗ[F] GT) (g₂ : G₂)
    (hnd : Function.Injective fun x : G => e x g₂) (pk : G₂) {S : Type*}
    (reply : G × G → PMF (S × G × G)) (guess : S → Option (G × G) → PMF Bool) :
    ((unif Bool).bind fun β : Bool =>
      (blindnessGame F H (fun a b => decide (PublicVerify.checkReply e g₂ pk a b)) m₀ m₁ reply
        guess β).map fun b' : Bool => decide (b' = β)) = unif Bool := by
  obtain ⟨k, hk⟩ := exists_key_of_checkReply hg e g₂ pk hnd
  exact blindness_guess_fair hg H h₀ h₁ _ k (fun a b h => hk a b (of_decide_eq_true h)) reply
    guess

/-- **Pairing check, with the public key and the messages chosen by the signer at random.**  The
signer's first stage outputs, from an arbitrary distribution, a value `c` that determines the
public key `pk c` (ANY element of `G₂`), the two messages and its later behaviour; then A draws
its coins and both sessions are checked against `pk c`.  If the messages chosen with positive
probability have non-identity hashes, the signer's final output has the same distribution for
both values of the hidden bit.

Same limitations as `blindness_pairing` and `blindness_two_stage`: one public key for both
sessions, two sessions, first stage independent of A's coins, fixed hash function. -/
theorem blindness_pairing_two_stage {G₂ GT : Type*} [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup GT] [Module F GT] [DecidableEq GT] (hg : IsGenerator F g) (H : M → G)
    (e : G →ₗ[F] G₂ →ₗ[F] GT) (g₂ : G₂) (hnd : Function.Injective fun x : G => e x g₂)
    {C S γ : Type*} (choose : PMF C) (m₀ m₁ : C → M) (pk : C → G₂)
    (h₀ : ∀ c ∈ choose.support, H (m₀ c) ≠ 0) (h₁ : ∀ c ∈ choose.support, H (m₁ c) ≠ 0)
    (reply : C → G × G → PMF (S × G × G)) (guess : C → S → Option (G × G) → PMF γ) :
    (choose.bind fun c : C =>
        blindnessGame F H (fun a b => decide (PublicVerify.checkReply e g₂ (pk c) a b))
          (m₀ c) (m₁ c) (reply c) (guess c) false) =
      choose.bind fun c : C =>
        blindnessGame F H (fun a b => decide (PublicVerify.checkReply e g₂ (pk c) a b))
          (m₀ c) (m₁ c) (reply c) (guess c) true :=
  bind_congr_on_support choose _ _ fun c hc =>
    blindness_pairing hg H (h₀ c hc) (h₁ c hc) e g₂ hnd (pk c) (reply c) (guess c)

/-! ## Non-degeneracy: against the honest signer A never aborts -/

/-- **The game is not degenerate.**  If A's test is COMPLETE for the key `k` (the honest reply
always passes), then against the honest signer with key `k` A never aborts, and for both values
of the hidden bit the guessing stage is run on exactly `some (prf H k m₀, prf H k m₁)`: the two
genuine signatures, in message order.  So `blindness` is not true merely because A refuses to
output anything.  (This is a statement about the honest signer only.) -/
theorem blindnessGame_honest (H : M → G) (Valid : G → G → Bool) (k : F)
    (hC : ∀ a, Valid a (evaluate k a) = true) (m₀ m₁ : M) {γ : Type*}
    (guess : Unit → Option (G × G) → PMF γ) (β : Bool) :
    blindnessGame F H Valid m₀ m₁ (honestReply k) guess β =
      guess () (some (prf H k m₀, prf H k m₁)) := by
  simp only [blindnessGame, honestReply, PMF.pure_bind, hC, Bool.and_self, ite_true]
  cases β <;> simp [unblind_evaluate_blind, PMF.bind_const]

/-- The pairing check against the honestly generated public key `pk = k • g₂` accepts the honest
signer in both sessions, and A's outputs are the two genuine signatures.  No non-degeneracy of
the pairing is needed for this direction.

This is a statement about the HONEST signer and an HONESTLY generated key only; it does NOT say
that A accepts a signer that deviates, nor anything about blindness. -/
theorem blindnessGame_honest_pairing {G₂ GT : Type*} [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup GT] [Module F GT] [DecidableEq GT] (H : M → G) (e : G →ₗ[F] G₂ →ₗ[F] GT)
    (g₂ : G₂) (k : F) (m₀ m₁ : M) {γ : Type*} (guess : Unit → Option (G × G) → PMF γ)
    (β : Bool) :
    blindnessGame F H
        (fun a b => decide (PublicVerify.checkReply e g₂ (PublicVerify.publicKey g₂ k) a b))
        m₀ m₁ (honestReply k) guess β =
      guess () (some (prf H k m₀, prf H k m₁)) :=
  blindnessGame_honest H _ k
    (fun a => decide_eq_true (PublicVerify.checkReply_evaluate e g₂ k a)) m₀ m₁ guess β

/-! ## NEGATIVE: without a common reply check the protocol is not blind (tagging attack) -/

/-- **Per-client keys: checking each session against its own key does not give blindness.**
Take the variant game `perClientGame`, in which session 0 is tested with `Valid₀` and session 1
with `Valid₁`, and suppose `Valid₀` is COMPLETE for a key `k₀` and `Valid₁` is complete for a
different key `k₁` (each test may in addition be perfectly sound for its own key, as the pairing
checks against `k₀ • g₂` and `k₁ • g₂` are: `per_client_keys_tagging_pairing`).  The signer that
answers session 0 under `k₀` and session 1 under `k₁` (`tagReply`) passes both tests, and
comparing A's outputs with `(k₀ • H m₀, k₁ • H m₁)` (`tagGuess`) reveals the hidden bit with
certainty.  At least one of the two hashes must be non-identity.

So the hypothesis of `blindness` that BOTH sessions are checked against ONE key cannot be
weakened to "each session is checked against some key".  It does NOT say anything about the
game `blindnessGame` with a single sound test — there, for non-identity hashes, the same signer
only ever sees the abort symbol (`tagReply_aborts`). -/
theorem per_client_keys_tagging [DecidableEq G] (H : M → G) {m₀ m₁ : M}
    (h : H m₀ ≠ 0 ∨ H m₁ ≠ 0) {k₀ k₁ : F} (hk : k₀ ≠ k₁) (Valid₀ Valid₁ : G → G → Bool)
    (hC₀ : ∀ a, Valid₀ a (evaluate k₀ a) = true) (hC₁ : ∀ a, Valid₁ a (evaluate k₁ a) = true)
    (β : Bool) :
    perClientGame F H Valid₀ Valid₁ m₀ m₁ (tagReply k₀ k₁) (tagGuess H k₀ k₁ m₀ m₁) β =
      PMF.pure β := by
  simp only [perClientGame, tagReply, tagGuess, PMF.pure_bind, hC₀, hC₁, Bool.and_self,
    ite_true]
  cases β
  · simp [unblind_evaluate_blind, PMF.bind_const]
  · rcases h with h | h
    · have hne : prf H k₁ m₀ ≠ prf H k₀ m₀ := fun h' => hk (smul_left_injective F h h').symm
      simp [unblind_evaluate_blind, PMF.bind_const, hne]
    · have hne : prf H k₀ m₁ ≠ prf H k₁ m₁ := fun h' => hk (smul_left_injective F h h')
      simp [unblind_evaluate_blind, PMF.bind_const, hne]

/-- The per-client-key attack against the pairing check: the client of session 0 checks against
the public key `k₀ • g₂` and the client of session 1 against `k₁ • g₂`, with `k₀ ≠ k₁`.  The
tagging signer passes both checks and learns the hidden bit with certainty.  (With a
non-degenerate pairing each of the two checks is perfectly sound for its own key,
`PublicVerify.checkReply_iff`; that does not help.)

It does NOT contradict `blindness_pairing`, which is about ONE public key for both sessions. -/
theorem per_client_keys_tagging_pairing {G₂ GT : Type*} [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup GT] [Module F GT] [DecidableEq GT] [DecidableEq G] (H : M → G) {m₀ m₁ : M}
    (h : H m₀ ≠ 0 ∨ H m₁ ≠ 0) (e : G →ₗ[F] G₂ →ₗ[F] GT) (g₂ : G₂) {k₀ k₁ : F} (hk : k₀ ≠ k₁)
    (β : Bool) :
    perClientGame F H
        (fun a b => decide (PublicVerify.checkReply e g₂ (PublicVerify.publicKey g₂ k₀) a b))
        (fun a b => decide (PublicVerify.checkReply e g₂ (PublicVerify.publicKey g₂ k₁) a b))
        m₀ m₁ (tagReply k₀ k₁) (tagGuess H k₀ k₁ m₀ m₁) β = PMF.pure β :=
  per_client_keys_tagging H h hk _ _
    (fun a => decide_eq_true (PublicVerify.checkReply_evaluate e g₂ k₀ a))
    (fun a => decide_eq_true (PublicVerify.checkReply_evaluate e g₂ k₁ a)) β

/-- **Tagging attack: the bare protocol is NOT blind.**  Take the game with NO check
(`Valid` always accepts), two different keys `k₀ ≠ k₁`, and the explicit signer that answers
session 0 under `k₀` and session 1 under `k₁` (`tagReply`), then compares A's outputs with
`(k₀ • H m₀, k₁ • H m₁)` (`tagGuess`).  Its guess equals the hidden bit with certainty: the game
for hidden bit `β` is the point mass at `β`.

So seeing A's final outputs lets a malicious signer link every signature to the session that
produced it, although (in a group of prime order and for non-identity hashes — hypotheses that
`blindedPair_dist_eq` needs and this theorem does not) everything the signer saw before the
outputs were released is independent of the session order.  The attack is cheap (a few scalar
multiplications and one comparison); it needs only `k₀ ≠ k₁` and that at least one of the two
hashes is not the identity, and no assumption on the group.

It does NOT say the protocol leaks the message during a session, and it does NOT apply when A
checks the replies against one committed key (`blindness`, `tagReply_aborts`). -/
theorem tagging_attack [DecidableEq G] (H : M → G) {m₀ m₁ : M} (h : H m₀ ≠ 0 ∨ H m₁ ≠ 0)
    {k₀ k₁ : F} (hk : k₀ ≠ k₁) (β : Bool) :
    blindnessGame F H (fun _ _ => true) m₀ m₁ (tagReply k₀ k₁) (tagGuess H k₀ k₁ m₀ m₁) β =
      PMF.pure β :=
  per_client_keys_tagging H h hk (fun _ _ => true) (fun _ _ => true) (fun _ => rfl)
    (fun _ => rfl) β

/-- Tagging attack, hidden bit `false`: the signer outputs `false` with certainty. -/
theorem tagging_attack_false [DecidableEq G] (H : M → G) {m₀ m₁ : M}
    (h : H m₀ ≠ 0 ∨ H m₁ ≠ 0) {k₀ k₁ : F} (hk : k₀ ≠ k₁) :
    blindnessGame F H (fun _ _ => true) m₀ m₁ (tagReply k₀ k₁) (tagGuess H k₀ k₁ m₀ m₁) false =
      PMF.pure false :=
  tagging_attack H h hk false

/-- Tagging attack, hidden bit `true`: the signer outputs `true` with certainty. -/
theorem tagging_attack_true [DecidableEq G] (H : M → G) {m₀ m₁ : M}
    (h : H m₀ ≠ 0 ∨ H m₁ ≠ 0) {k₀ k₁ : F} (hk : k₀ ≠ k₁) :
    blindnessGame F H (fun _ _ => true) m₀ m₁ (tagReply k₀ k₁) (tagGuess H k₀ k₁ m₀ m₁) true =
      PMF.pure true :=
  tagging_attack H h hk true

/-- Without a reply check, the two values of the hidden bit give DIFFERENT distributions of the
tagging signer's guess: the conclusion of `blindness` fails for the unchecked protocol. -/
theorem tagging_not_blind [DecidableEq G] (H : M → G) {m₀ m₁ : M} (h : H m₀ ≠ 0 ∨ H m₁ ≠ 0)
    {k₀ k₁ : F} (hk : k₀ ≠ k₁) :
    blindnessGame F H (fun _ _ => true) m₀ m₁ (tagReply k₀ k₁) (tagGuess H k₀ k₁ m₀ m₁) false ≠
      blindnessGame F H (fun _ _ => true) m₀ m₁ (tagReply k₀ k₁) (tagGuess H k₀ k₁ m₀ m₁)
        true := by
  rw [tagging_attack_false H h hk, tagging_attack_true H h hk]
  exact pure_false_ne_pure_true

/-- Without a reply check, the tagging signer guesses a uniform hidden bit correctly with
probability one (compare `blindness_guess_fair`: one half with a sound check). -/
theorem tagging_attack_wins [DecidableEq G] (H : M → G) {m₀ m₁ : M}
    (h : H m₀ ≠ 0 ∨ H m₁ ≠ 0) {k₀ k₁ : F} (hk : k₀ ≠ k₁) :
    ((unif Bool).bind fun β : Bool =>
      (blindnessGame F H (fun _ _ => true) m₀ m₁ (tagReply k₀ k₁)
        (tagGuess H k₀ k₁ m₀ m₁) β).map fun b' : Bool => decide (b' = β)) = PMF.pure true := by
  have h' : (fun β : Bool =>
      (blindnessGame F H (fun _ _ => true) m₀ m₁ (tagReply k₀ k₁)
        (tagGuess H k₀ k₁ m₀ m₁) β).map fun b' : Bool => decide (b' = β)) =
      fun _ : Bool => PMF.pure true := by
    funext β
    rw [tagging_attack H h hk β, PMF.pure_map, decide_eq_true rfl]
  rw [h', PMF.bind_const]

/-! ## NEGATIVE: per-session release is not blind even with a sound check (selective abort) -/

/-- **Selective-abort attack: all-or-nothing release is necessary.**  Take the variant game
`perSessionGame`, in which A releases the output of each session that passes the test, and let
the test be both COMPLETE (`hC`) and SOUND (`hV`) for the key `k` — for instance the pairing
check, see `selective_abort_pairing`.  The explicit signer that answers session 0 honestly under
`k` and session 1 under a different key `k' ≠ k` (`tagReply k k'`) makes session 1 fail, and then
looks at which message is missing from A's outputs (`abortGuess`).  Its guess equals the hidden
bit with certainty.

So a sound reply check alone does not give blindness: A must also withhold ALL its outputs when
any session fails, as `blindnessGame` does.  Both hashes must be non-identity (otherwise the
wrong-key reply to the identity element is the honest reply and passes).

It does NOT contradict `blindness`: that theorem is about `blindnessGame`, where the same signer
only ever sees the abort symbol (`tagReply_aborts`). -/
theorem selective_abort (H : M → G) {m₀ m₁ : M} (h₀ : H m₀ ≠ 0) (h₁ : H m₁ ≠ 0)
    (Valid : G → G → Bool) {k k' : F} (hk : k' ≠ k) (hC : ∀ a, Valid a (evaluate k a) = true)
    (hV : ∀ a b, Valid a b = true → b = evaluate k a) (β : Bool) :
    perSessionGame F H Valid m₀ m₁ (tagReply k k') abortGuess β = PMF.pure β := by
  have hbad : ∀ m : M, H m ≠ 0 → ∀ r : Fˣ,
      Valid (blind H m r) (evaluate k' (blind H m r)) = false :=
    fun m hm r => wrong_key_rejected Valid hk hV (blinded_ne_zero H hm r)
  simp only [perSessionGame, tagReply, abortGuess, PMF.pure_bind]
  cases β
  · simp [hC, hbad m₁ h₁, PMF.bind_const]
  · simp [hC, hbad m₀ h₀, PMF.bind_const]

/-- The selective-abort attack against the pairing check with an HONESTLY generated public key
`pk = k • g₂` and a non-degenerate pairing: with per-session release the signer learns the hidden
bit with certainty, although the very same check gives perfect blindness under all-or-nothing
release (`blindness_pairing`).

This is a statement about the variant game `perSessionGame` only; it does NOT say anything
against the all-or-nothing game `blindnessGame`, in which this signer makes A abort
(`tagReply_aborts`). -/
theorem selective_abort_pairing {G₂ GT : Type*} [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup GT] [Module F GT] [DecidableEq GT] (H : M → G) {m₀ m₁ : M} (h₀ : H m₀ ≠ 0)
    (h₁ : H m₁ ≠ 0) (e : G →ₗ[F] G₂ →ₗ[F] GT) (g₂ : G₂)
    (hnd : Function.Injective fun x : G => e x g₂) {k k' : F} (hk : k' ≠ k) (β : Bool) :
    perSessionGame F H
        (fun a b => decide (PublicVerify.checkReply e g₂ (PublicVerify.publicKey g₂ k) a b))
        m₀ m₁ (tagReply k k') abortGuess β = PMF.pure β :=
  selective_abort H h₀ h₁ _ hk
    (fun a => decide_eq_true (PublicVerify.checkReply_evaluate e g₂ k a))
    (fun _ _ h => PublicVerify.eq_evaluate_of_checkReply e g₂ hnd (of_decide_eq_true h)) β

/-- With per-session release the two values of the hidden bit give DIFFERENT distributions of
the selective-abort signer's guess, even for a sound and complete check. -/
theorem selective_abort_not_blind (H : M → G) {m₀ m₁ : M} (h₀ : H m₀ ≠ 0) (h₁ : H m₁ ≠ 0)
    (Valid : G → G → Bool) {k k' : F} (hk : k' ≠ k) (hC : ∀ a, Valid a (evaluate k a) = true)
    (hV : ∀ a b, Valid a b = true → b = evaluate k a) :
    perSessionGame F H Valid m₀ m₁ (tagReply k k') abortGuess false ≠
      perSessionGame F H Valid m₀ m₁ (tagReply k k') abortGuess true := by
  rw [selective_abort H h₀ h₁ Valid hk hC hV false, selective_abort H h₀ h₁ Valid hk hC hV true]
  exact pure_false_ne_pure_true

/-- With per-session release, the selective-abort signer guesses a uniform hidden bit correctly
with probability one. -/
theorem selective_abort_wins (H : M → G) {m₀ m₁ : M} (h₀ : H m₀ ≠ 0) (h₁ : H m₁ ≠ 0)
    (Valid : G → G → Bool) {k k' : F} (hk : k' ≠ k) (hC : ∀ a, Valid a (evaluate k a) = true)
    (hV : ∀ a b, Valid a b = true → b = evaluate k a) :
    ((unif Bool).bind fun β : Bool =>
      (perSessionGame F H Valid m₀ m₁ (tagReply k k') abortGuess β).map fun b' : Bool =>
        decide (b' = β)) = PMF.pure true := by
  have h : (fun β : Bool =>
      (perSessionGame F H Valid m₀ m₁ (tagReply k k') abortGuess β).map fun b' : Bool =>
        decide (b' = β)) = fun _ : Bool => PMF.pure true := by
    funext β
    rw [selective_abort H h₀ h₁ Valid hk hC hV β, PMF.pure_map, decide_eq_true rfl]
  rw [h, PMF.bind_const]

/-- **In the all-or-nothing game a wrong-key signer only ever sees the abort symbol.**  Let
A's test be sound for the key `k`, let both hashes be non-identity, and let the signer answer
session 0 under `k₀` and session 1 under `k₁` (`tagReply k₀ k₁`), where AT LEAST ONE of the two
keys differs from `k`.  Then, for both values of the hidden bit, the game `blindnessGame` is
exactly "run the guessing stage on `none`": A aborts with certainty and the signer's output
carries no information about the session order.

The hypothesis covers the signer of `selective_abort` (`k₀ = k`, `k₁ ≠ k`) and every tagging
signer (if `k₀ ≠ k₁`, at least one of them differs from `k`).  This is what all-or-nothing
release under ONE sound test buys, and it is why `selective_abort` and
`per_client_keys_tagging` do not contradict `blindness`.  It is a statement about these
particular signers only; for all signers see `blindness`. -/
theorem tagReply_aborts (H : M → G) {m₀ m₁ : M} (h₀ : H m₀ ≠ 0) (h₁ : H m₁ ≠ 0)
    (Valid : G → G → Bool) {k k₀ k₁ : F} (hk : k₀ ≠ k ∨ k₁ ≠ k)
    (hV : ∀ a b, Valid a b = true → b = evaluate k a) {γ : Type*}
    (guess : Unit → Option (G × G) → PMF γ) (β : Bool) :
    blindnessGame F H Valid m₀ m₁ (tagReply k₀ k₁) guess β = guess () none := by
  have hbad : ∀ k' : F, k' ≠ k → ∀ m : M, H m ≠ 0 → ∀ r : Fˣ,
      Valid (blind H m r) (evaluate k' (blind H m r)) = false :=
    fun k' hk' m hm r => wrong_key_rejected Valid hk' hV (blinded_ne_zero H hm r)
  simp only [blindnessGame, tagReply, PMF.pure_bind]
  rcases hk with hk | hk
  · cases β
    · simp [hbad k₀ hk m₀ h₀, PMF.bind_const]
    · simp [hbad k₀ hk m₁ h₁, PMF.bind_const]
  · cases β
    · simp [hbad k₁ hk m₁ h₁, PMF.bind_const]
    · simp [hbad k₁ hk m₀ h₀, PMF.bind_const]

/-! ## NECESSITY: the hypotheses on the hashes and on the group cannot be dropped -/

/-- **A sound check does not make the game unlosable.**  Suppose some public test `T` on group
elements separates the blinded forms of the two messages: it rejects every blinding of `m₀` and
accepts every blinding of `m₁`.  Then for EVERY acceptance test `Valid` — in particular for a
test that is sound and complete for the key `k` — the signer that follows the protocol with key
`k`, remembers `T` of the first blinded element (`sepReply`) and outputs that bit (`sepGuess`)
wins the blindness game with certainty.

So `blindness` is not true by construction of the game: it genuinely depends on the two blinded
elements being identically distributed, which is where `IsGenerator` and the non-identity hashes
enter.  This theorem does NOT say that such a test `T` exists: in a group of prime order with
non-identity hashes it does not (`no_separating_test`); see `hash_zero_left_wins`,
`hash_zero_right_wins` and `rank_two_wins` for situations in which it does. -/
theorem separating_test_wins (H : M → G) {m₀ m₁ : M} (T : G → Bool)
    (hT₀ : ∀ r : Fˣ, T (blind H m₀ r) = false) (hT₁ : ∀ r : Fˣ, T (blind H m₁ r) = true)
    (Valid : G → G → Bool) (k : F) (β : Bool) :
    blindnessGame F H Valid m₀ m₁ (sepReply T k) sepGuess β = PMF.pure β := by
  simp only [blindnessGame, sepReply, sepGuess, PMF.pure_bind]
  cases β
  · simp [hT₀, PMF.bind_const]
  · simp [hT₁, PMF.bind_const]

/-- In the situation of `separating_test_wins` the conclusion of `blindness` fails: the two
values of the hidden bit give different output distributions, whatever the test `Valid` is. -/
theorem separating_test_not_blind (H : M → G) {m₀ m₁ : M} (T : G → Bool)
    (hT₀ : ∀ r : Fˣ, T (blind H m₀ r) = false) (hT₁ : ∀ r : Fˣ, T (blind H m₁ r) = true)
    (Valid : G → G → Bool) (k : F) :
    blindnessGame F H Valid m₀ m₁ (sepReply T k) sepGuess false ≠
      blindnessGame F H Valid m₀ m₁ (sepReply T k) sepGuess true := by
  rw [separating_test_wins H T hT₀ hT₁ Valid k false,
    separating_test_wins H T hT₀ hT₁ Valid k true]
  exact pure_false_ne_pure_true

/-- Consistency of the positive and the negative results: under the hypotheses of `blindness`
(prime-order group, non-identity hashes) NO test on group elements separates the blinded forms
of the two messages.  Proof: otherwise `separating_test_not_blind` would contradict `blindness`
for the test that rejects everything, which is vacuously sound. -/
theorem no_separating_test (hg : IsGenerator F g) (H : M → G) {m₀ m₁ : M} (h₀ : H m₀ ≠ 0)
    (h₁ : H m₁ ≠ 0) (T : G → Bool) :
    ¬((∀ r : Fˣ, T (blind H m₀ r) = false) ∧ ∀ r : Fˣ, T (blind H m₁ r) = true) := by
  rintro ⟨hT₀, hT₁⟩
  exact separating_test_not_blind H T hT₀ hT₁ (fun _ _ => false) (0 : F)
    (blindness hg H h₀ h₁ (fun _ _ => false) 0 (fun _ _ h => absurd h Bool.false_ne_true) _ _)

/-- **The hypothesis `H m₀ ≠ 0` of `blindness` is necessary.**  If the hash of `m₀` is the
identity and the hash of `m₁` is not, then for every acceptance test (sound or not) the signer
that looks whether the first blinded element is the identity wins with certainty: a nonzero coin
cannot hide the identity.  No assumption on the group is used.  (The case in which BOTH hashes
are the identity is not treated.) -/
theorem hash_zero_left_wins [DecidableEq G] (H : M → G) {m₀ m₁ : M} (h₀ : H m₀ = 0)
    (h₁ : H m₁ ≠ 0) (Valid : G → G → Bool) (k : F) (β : Bool) :
    blindnessGame F H Valid m₀ m₁ (sepReply (fun a : G => decide (a ≠ 0)) k) sepGuess β =
      PMF.pure β :=
  separating_test_wins H _
    (fun r => by simp [(blinded_eq_zero_iff H m₀ r).mpr h₀])
    (fun r => by simp [blinded_ne_zero H h₁ r]) Valid k β

/-- **The hypothesis `H m₁ ≠ 0` of `blindness` is necessary.**  The mirror image of
`hash_zero_left_wins`: if the hash of `m₁` is the identity and the hash of `m₀` is not, the
signer that looks whether the first blinded element is the identity wins with certainty, for
every acceptance test. -/
theorem hash_zero_right_wins [DecidableEq G] (H : M → G) {m₀ m₁ : M} (h₀ : H m₀ ≠ 0)
    (h₁ : H m₁ = 0) (Valid : G → G → Bool) (k : F) (β : Bool) :
    blindnessGame F H Valid m₀ m₁ (sepReply (fun a : G => decide (a = 0)) k) sepGuess β =
      PMF.pure β :=
  separating_test_wins H _
    (fun r => by simp [blinded_ne_zero H h₀ r])
    (fun r => by simp [(blinded_eq_zero_iff H m₁ r).mpr h₁]) Valid k β

end Main

/-- Two hash values in the two-dimensional module `F × F` that are not multiples of each other:
`false ↦ (1, 0)` and `true ↦ (0, 1)`.  (Used only in `rank_two_wins`.) -/
def twoDimHash (F : Type*) [Zero F] [One F] (j : Bool) : F × F :=
  if j then (0, 1) else (1, 0)

/-- Both values of `twoDimHash` are non-identity. -/
theorem twoDimHash_ne_zero (F : Type*) [Field F] (j : Bool) : twoDimHash F j ≠ 0 := by
  cases j <;> simp [twoDimHash]

/-- The module `F × F` is not one-dimensional: no element generates it. -/
theorem twoDim_not_isGenerator (F : Type*) [Field F] (g : F × F) : ¬IsGenerator F g := by
  intro hg
  obtain ⟨c, hc⟩ := hg.spans (1, 0)
  obtain ⟨d, hd⟩ := hg.spans (0, 1)
  have h1 : c * g.1 = 1 := by simpa using congrArg Prod.fst hc
  have h2 : c * g.2 = 0 := by simpa using congrArg Prod.snd hc
  have h3 : d * g.2 = 1 := by simpa using congrArg Prod.snd hd
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at h1
  rcases mul_eq_zero.mp h2 with h | h
  · exact hc0 h
  · rw [h, mul_zero] at h3
    exact zero_ne_one h3

/-- **The hypothesis that `G` is one-dimensional (`IsGenerator`) is necessary.**  In the module
`G = F × F`, which has no generator (`twoDim_not_isGenerator`), with the two non-identity hash
values `(1, 0)` and `(0, 1)` (`twoDimHash_ne_zero`), blinding does not hide the message: a
nonzero multiple of `(1, 0)` has first coordinate nonzero, a nonzero multiple of `(0, 1)` has
first coordinate zero.  For EVERY acceptance test — in particular for one that is sound and
complete for the key `k` — the signer that looks at the first coordinate of the first blinded
element wins the blindness game with certainty.

So every hypothesis of `blindness` other than `hg` can hold while its conclusion fails.  This is
a statement about this toy module only; it says nothing about any concrete elliptic-curve
group. -/
theorem rank_two_wins (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (Valid : F × F → F × F → Bool) (k : F) (β : Bool) :
    blindnessGame F (twoDimHash F) Valid false true
        (sepReply (fun p : F × F => decide (p.1 = 0)) k) sepGuess β = PMF.pure β :=
  separating_test_wins (twoDimHash F) _ (fun r => by simp [blind, twoDimHash])
    (fun r => by simp [blind, twoDimHash]) Valid k β

section OneSession

variable {F G M : Type*} [Field F] [Fintype F] [DecidableEq F] [AddCommGroup G] [Module F G]
  {g : G}

/-! ## One session: the transcript is unlinkable to the accepted output -/

/-- **One checked session: transcript and signature are unlinkable.**  Consider a single session
on message `m` against an arbitrary randomized, stateful signer `reply` (it sees the blinded
element and returns its state and a reply), with A's test sound for the key `k`.  The signer's
complete view — the blinded element it received, its state, and A's output if A accepted (the
abort symbol otherwise) — is distributed EXACTLY like the following experiment that never blinds
`m`: run the session on an unrelated message `m'` and, if A accepts, hand out the constant
`prf H k m`.  In this sense the transcript of a checked session carries no information that
ties it to the message whose signature A walks away with.

It does NOT say that the output `prf H k m` hides `m` (it is a function of `m`).  It does NOT
cover a test that is not perfectly sound for one key.  And it is a statement about ONE session:
what a signer learns when the outputs of several sessions are revealed together is the subject
of `blindness` (two sessions, all-or-nothing release), not of this theorem. -/
theorem session_output_unlinkable (hg : IsGenerator F g) (H : M → G) {m m' : M}
    (hm : H m ≠ 0) (hm' : H m' ≠ 0) (Valid : G → G → Bool) (k : F)
    (hV : ∀ a b, Valid a b = true → b = evaluate k a) {S : Type*} (reply : G → PMF (S × G)) :
    ((unif Fˣ).bind fun r : Fˣ =>
      (reply (blind H m r)).map fun t : S × G =>
        (blind H m r, t.1, if Valid (blind H m r) t.2 then some (unblind r t.2) else none)) =
      (unif Fˣ).bind fun r : Fˣ =>
        (reply (blind H m' r)).map fun t : S × G =>
          (blind H m' r, t.1, if Valid (blind H m' r) t.2 then some (prf H k m) else none) := by
  obtain ⟨u, hu⟩ := exists_unit_blind_eq hg H hm hm'
  have hL : (fun r : Fˣ =>
      (reply (blind H m r)).map fun t : S × G =>
        (blind H m r, t.1, if Valid (blind H m r) t.2 then some (unblind r t.2) else none)) =
      fun r : Fˣ =>
        (reply (blind H m r)).map fun t : S × G =>
          (blind H m r, t.1, if Valid (blind H m r) t.2 then some (prf H k m) else none) := by
    funext r
    congr 1
    funext t
    by_cases hv : Valid (blind H m r) t.2 = true
    · rw [ite_eq_left hv, ite_eq_left hv, hV _ _ hv, unblind_evaluate_blind]
    · rw [ite_eq_right hv, ite_eq_right hv]
  rw [hL]
  exact (unif_bind_eq_of_equiv (Equiv.mulRight u)
    (fun r : Fˣ =>
      (reply (blind H m' r)).map fun t : S × G =>
        (blind H m' r, t.1, if Valid (blind H m' r) t.2 then some (prf H k m) else none))
    (fun r : Fˣ =>
      (reply (blind H m r)).map fun t : S × G =>
        (blind H m r, t.1, if Valid (blind H m r) t.2 then some (prf H k m) else none))
    (fun r => by rw [hu r]; rfl)).symm

end OneSession

/-! ## Any number of sessions: the permutation game -/

section ManySessions

variable {F G M ι : Type*} [Field F] [Fintype F] [DecidableEq F] [AddCommGroup G] [Module F G]
  [Fintype ι] [DecidableEq ι] {g : G}

/-- Any experiment `W` that continues from the FAMILY of blinded elements, one per session, has
the same distribution for any two assignments `μ`, `μ'` of messages with non-identity hashes to
the sessions: the independent coins are re-randomised session by session, by the bijection
`r ↦ (i ↦ r i * u i)` of `ι → Fˣ`. -/
theorem unif_bind_blind_family {γ : Type*} (hg : IsGenerator F g) (H : M → G) (μ μ' : ι → M)
    (hμ : ∀ i, H (μ i) ≠ 0) (hμ' : ∀ i, H (μ' i) ≠ 0) (W : (ι → G) → PMF γ) :
    ((unif (ι → Fˣ)).bind fun r : ι → Fˣ => W fun i => blind H (μ i) (r i)) =
      (unif (ι → Fˣ)).bind fun r : ι → Fˣ => W fun i => blind H (μ' i) (r i) := by
  choose u hu using fun i => exists_unit_blind_eq hg H (hμ i) (hμ' i)
  refine (unif_bind_eq_of_equiv (Equiv.piCongrRight fun i => Equiv.mulRight (u i))
    (fun r : ι → Fˣ => W fun i => blind H (μ' i) (r i))
    (fun r : ι → Fˣ => W fun i => blind H (μ i) (r i)) fun r => ?_).symm
  show (W fun i => blind H (μ i) (r i * u i)) = W fun i => blind H (μ' i) (r i)
  congr 1
  funext i
  exact (hu i (r i)).symm

/-- The simulation step for `n` sessions: if A's test is sound for the key `k` on non-identity
first messages and all hashes are non-identity, then for every assignment `π` of messages to
sessions the game is the same as drawing the coins and handing the family of blinded elements to
the coin-free and permutation-free experiment `simGameN`.  It does NOT yet say that different
permutations give the same distribution: that is `blindnessN`. -/
theorem blindnessGameN_eq_sim (H : M → G) (Valid : G → G → Bool) (k : F) (m : ι → M)
    (hm : ∀ j, H (m j) ≠ 0) (hV : ∀ a b, a ≠ 0 → Valid a b = true → b = evaluate k a)
    {S γ : Type*} (reply : (ι → G) → PMF (S × (ι → G))) (guess : S → Option (ι → G) → PMF γ)
    (π : Equiv.Perm ι) :
    blindnessGameN F H Valid m reply guess π =
      (unif (ι → Fˣ)).bind fun r : ι → Fˣ =>
        simGameN H Valid k m reply guess fun i => blind H (m (π i)) (r i) := by
  simp only [blindnessGameN, simGameN]
  congr 1
  funext r
  congr 1
  funext t
  congr 1
  by_cases hv : ∀ i, Valid (blind H (m (π i)) (r i)) (t.2 i) = true
  · rw [ite_eq_left hv, ite_eq_left hv]
    congr 1
    funext j
    rw [hV _ _ (blinded_ne_zero H (hm (π (π.symm j))) (r (π.symm j))) (hv (π.symm j)),
      unblind_evaluate_blind, Equiv.apply_symm_apply]
  · rw [ite_eq_right hv, ite_eq_right hv]

/-- **Blindness against a malicious signer, any finite number of sessions (perfect).**

Setting: `G` is one-dimensional over `F` with generator `g`; `m : ι → M` is a family of messages
(not necessarily distinct) whose hashes are all non-identity; A's acceptance test is sound for
ONE key `k` on non-identity first messages (`hV`; a test that is sound everywhere, as in
`blindness`, satisfies this).

Claim: in the game `blindnessGameN` — one session per message, the hidden permutation `π` decides
which session carries which message, the signer sees all blinded elements, answers all sessions,
and is finally shown all of A's outputs in MESSAGE order, or the abort symbol if some reply
failed the test — the distribution of the signer's final output is EXACTLY the same for any two
permutations `π`, `π'`.  The signer (randomized, stateful, unbounded, free to deviate) learns
nothing about which session produced which signature.

What this does NOT claim.
* The signer receives all blinded elements at once and answers all at once; A releases all
  outputs together, and only if EVERY session passed.  Other schedules are NOT formalised: a
  signer that answers the sessions one after another (informally a special case, since A's
  messages do not depend on the replies), and schedules in which A releases an output before
  all sessions are answered (per-session release is insecure already for two sessions:
  `selective_abort`).
* Perfect soundness for one key, the same test in every session, messages fixed before the
  coins are drawn, uniform independent secret nonzero coins, non-identity hashes, prime-order
  group: exactly as for `blindness`.
* Nothing about unforgeability; and by itself it does not say that A ever accepts
  (`blindnessGameN_honest`). -/
theorem blindnessN (hg : IsGenerator F g) (H : M → G) (m : ι → M) (hm : ∀ j, H (m j) ≠ 0)
    (Valid : G → G → Bool) (k : F) (hV : ∀ a b, a ≠ 0 → Valid a b = true → b = evaluate k a)
    {S γ : Type*} (reply : (ι → G) → PMF (S × (ι → G))) (guess : S → Option (ι → G) → PMF γ)
    (π π' : Equiv.Perm ι) :
    blindnessGameN F H Valid m reply guess π = blindnessGameN F H Valid m reply guess π' := by
  rw [blindnessGameN_eq_sim H Valid k m hm hV, blindnessGameN_eq_sim H Valid k m hm hV]
  exact unif_bind_blind_family hg H (fun i => m (π i)) (fun i => m (π' i)) (fun _ => hm _)
    (fun _ => hm _) _

/-- **`n`-session blindness with the public pairing check, for an ARBITRARY public key.**  A's
test in every session is the pairing equation `e b g₂ = e a pk`, the pairing is non-degenerate
at `g₂`, and `pk` is any element of `G₂`.  Then the signer's final output in `blindnessGameN`
has the same distribution for any two assignments of messages to sessions.  Same limitations as
`blindnessN` and `blindness_pairing` (one public key for all sessions, simultaneous
all-or-nothing release, perfectly sound check). -/
theorem blindnessN_pairing {G₂ GT : Type*} [AddCommGroup G₂] [Module F G₂] [AddCommGroup GT]
    [Module F GT] [DecidableEq GT] (hg : IsGenerator F g) (H : M → G) (m : ι → M)
    (hm : ∀ j, H (m j) ≠ 0) (e : G →ₗ[F] G₂ →ₗ[F] GT) (g₂ : G₂)
    (hnd : Function.Injective fun x : G => e x g₂) (pk : G₂) {S γ : Type*}
    (reply : (ι → G) → PMF (S × (ι → G))) (guess : S → Option (ι → G) → PMF γ)
    (π π' : Equiv.Perm ι) :
    blindnessGameN F H (fun a b => decide (PublicVerify.checkReply e g₂ pk a b)) m reply guess
        π =
      blindnessGameN F H (fun a b => decide (PublicVerify.checkReply e g₂ pk a b)) m reply guess
        π' := by
  obtain ⟨k, hk⟩ := exists_key_of_checkReply hg e g₂ pk hnd
  exact blindnessN hg H m hm _ k (fun a b _ h => hk a b (of_decide_eq_true h)) reply guess π π'

/-- **The `n`-session game is not degenerate.**  If A's test is complete for the key `k`, then
against the honest signer with key `k` A never aborts, and for every permutation the guessing
stage is run on exactly the family of genuine signatures `prf H k (m j)`, in message order.
(A statement about the honest signer only.) -/
theorem blindnessGameN_honest (H : M → G) (Valid : G → G → Bool) (k : F)
    (hC : ∀ a, Valid a (evaluate k a) = true) (m : ι → M) {γ : Type*}
    (guess : Unit → Option (ι → G) → PMF γ) (π : Equiv.Perm ι) :
    blindnessGameN F H Valid m (honestReplyN k) guess π =
      guess () (some fun j => prf H k (m j)) := by
  simp only [blindnessGameN, honestReplyN, PMF.pure_bind, hC, unblind_evaluate_blind,
    Equiv.apply_symm_apply, implies_true, ite_true]
  exact PMF.bind_const _ _

end ManySessions

section Bridge

variable {F G M : Type*} [Field F] [Fintype F] [DecidableEq F] [AddCommGroup G] [Module F G]

/-- **The two-session game is the `ι = Bool` instance of the `n`-session game.**  Index the two
sessions and the two messages by `Bool` (`false` for session 0 / message `m₀`, `true` for
session 1 / message `m₁`), let the permutation be the identity for `β = false` and the swap for
`β = true`, and translate the signer's strategy along the bijection between pairs and functions
on `Bool`.  Then the two games have exactly the same output distribution.  So every strategy
for `blindnessGame` is a strategy for the `ι = Bool` instance of `blindnessGameN`, and the
`n`-session game generalises the game used in the rest of this file.  (The converse translation,
from strategies on `Bool`-indexed families to strategies on pairs, is not stated.) -/
theorem blindnessGame_eq_blindnessGameN (H : M → G) (Valid : G → G → Bool) (m₀ m₁ : M)
    {S γ : Type*} (reply : G × G → PMF (S × G × G)) (guess : S → Option (G × G) → PMF γ)
    (β : Bool) :
    blindnessGame F H Valid m₀ m₁ reply guess β =
      blindnessGameN F H Valid (fun j : Bool => if j then m₁ else m₀)
        (fun a : Bool → G => (reply (a false, a true)).map fun t : S × G × G =>
          (t.1, fun i : Bool => if i then t.2.2 else t.2.1))
        (fun (s : S) (out : Option (Bool → G)) =>
          guess s (out.map fun o : Bool → G => (o false, o true)))
        (if β then Equiv.swap false true else Equiv.refl Bool) := by
  simp only [blindnessGame, blindnessGameN]
  refine unif_bind_eq_of_equiv (Equiv.boolArrowEquivProd Fˣ).symm _ _ fun rs => ?_
  rw [PMF.bind_map]
  cases β <;> simp [Function.comp_def, Bool.forall_bool]

end Bridge

/-! ## Non-vacuity of the hypotheses -/

/-- **The hypotheses of `blindness_pairing` are jointly satisfiable.**  In the toy model where
all three groups are the additive group of the finite field `F` itself, with generators `1` and
the multiplication pairing `e x y = x * y` (bilinear and non-degenerate at `1`), the theorem
applies to every hash function, every pair of messages with nonzero hashes and every public key.
This model is of course cryptographically worthless (discrete logarithms are trivial in it); it
only shows that `blindness_pairing` is not vacuously true. -/
theorem blindness_pairing_model (F : Type*) {M : Type*} [Field F] [Fintype F] [DecidableEq F]
    (H : M → F) {m₀ m₁ : M} (h₀ : H m₀ ≠ 0) (h₁ : H m₁ ≠ 0) (pk : F) {S γ : Type*}
    (reply : F × F → PMF (S × F × F)) (guess : S → Option (F × F) → PMF γ) :
    blindnessGame F H
        (fun a b => decide (PublicVerify.checkReply (LinearMap.mul F F) (1 : F) pk a b))
        m₀ m₁ reply guess false =
      blindnessGame F H
        (fun a b => decide (PublicVerify.checkReply (LinearMap.mul F F) (1 : F) pk a b))
        m₀ m₁ reply guess true :=
  blindness_pairing (g := (1 : F)) ⟨one_ne_zero, fun x => ⟨x, by simp⟩⟩ H h₀ h₁
    (LinearMap.mul F F) 1 (fun x y h => by simpa using h) pk reply guess

end Unlinkability

end BlindPRF
