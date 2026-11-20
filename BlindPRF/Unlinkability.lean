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
  wins this game with certainty (`tagging_attack`), although everything it saw before the outputs
  were released is independent of `β` (`blindedPair_dist_eq`).  So the bare protocol is NOT blind
  in the blind-signature sense.  Blindness is recovered when A CHECKS B's reply against a public
  commitment to B's key and releases its outputs only if BOTH sessions pass (`blindness`,
  `blindness_pairing`); releasing the outputs per session instead is again insecure
  (`selective_abort`).

  The game is defined exactly once (`blindnessGame`), with A's acceptance test `Valid` as a
  parameter, and that same definition is used in the positive and in the negative theorems.

  Contents.
  * Algebra.  `exists_unit_blind_eq` (changing the message = multiplying the coin by a fixed
    unit), `exists_key_of_checkReply` (for ANY public key `pk`, the pairing check of
    `BlindPRF/PublicVerify.lean` is sound for one single scalar `k`).
  * Definitions.  `blindnessGame` (all-or-nothing release), `perSessionGame` (per-session
    release), the explicit signers `honestReply`, `tagReply` and guessers `tagGuess`,
    `abortGuess`, and the simulated experiment `simGame`.
  * POSITIVE.  `blindnessGame_eq_sim` (with a sound check, B's whole experiment is a function of
    the two blinded elements), `blindness` (the game has the same output distribution for both
    values of `β`), `blindness_view` (so does B's complete view), `blindness_guess_fair` (B
    guesses a uniform hidden `β` with probability exactly one half), `blindness_pairing` /
    `blindness_pairing_guess_fair` (the same for the pairing check against an arbitrary,
    possibly maliciously chosen, public key).
  * NON-DEGENERACY.  `blindnessGame_honest`, `blindnessGame_honest_pairing`: against the honest
    signer A never aborts and outputs the two genuine signatures, so the positive theorems are
    not true merely because A always aborts.  `blindness_pairing_model`: all hypotheses of
    `blindness_pairing` are simultaneously satisfiable.
  * NEGATIVE.  `tagging_attack` (+ `_false`, `_true`, `_wins`, `tagging_not_blind`): without a
    check, a signer using two keys wins with certainty.  `selective_abort` (+ `_pairing`,
    `_wins`, `selective_abort_not_blind`): with per-session release, even a sound and complete
    check does not help.
  * One session.  `blinded_dist_eq`, `session_output_unlinkable`: B's view of a checked session,
    together with A's accepted output, is distributed as if the session had been run on an
    unrelated message.

  What this file does NOT prove.
  * Only TWO sessions.  The general `n`-session game (B has to guess a permutation) is not
    formalised here.
  * The check must be PERFECTLY sound for one fixed key (`hV`).  A check that is only
    statistically sound (an interactive proof of discrete-log equality has soundness error about
    `1 / |F|`) or sound only in the random-oracle model (Fiat–Shamir) is not covered by
    `blindness`; for such checks one would expect closeness up to the soundness error, but no
    such statement is proven here.
  * The same test `Valid` — in the pairing instance: the same public key `pk` — is applied in
    both sessions.  A signer that can show different public keys to different clients can tag
    them exactly as in `tagging_attack`; that every client sees the same `pk` is an assumption
    about the deployment, not something proven.
  * The messages `m₀`, `m₁` are fixed before the coins are drawn and satisfy `H m ≠ 0`; the
    coins are uniform on the nonzero scalars, independent, and never seen by B; `G` is
    one-dimensional over `F` (a cyclic group of prime order).
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

/-- A nonzero coin cannot hide a zero, and cannot create one: if the hash of the message is not
the identity then neither is the blinded element. -/
theorem blinded_ne_zero (H : M → G) {m : M} (hm : H m ≠ 0) (r : Fˣ) : blind H m r ≠ 0 := by
  intro h
  rcases smul_eq_zero.mp h with h' | h'
  · exact r.ne_zero h'
  · exact hm h'

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
theorem evaluate_ne_of_key_ne {k k' : F} (hk : k' ≠ k) {a : G} (ha : a ≠ 0) :
    evaluate k' a ≠ evaluate k a :=
  fun h => hk (smul_left_injective F ha h)

end Algebra

/-! ## The pairing check as a Boolean test -/

section Pairing

variable {F G G₂ GT : Type*} [Field F] [AddCommGroup G] [Module F G] [AddCommGroup G₂]
  [Module F G₂] [AddCommGroup GT] [Module F GT]

/-- A's pairing check `e b g₂ = e a pk` is an equation in the target group, so A can evaluate it
as soon as equality in `GT` is decidable.  This instance lets the check be used as the Boolean
acceptance test `fun a b => decide (PublicVerify.checkReply e g₂ pk a b)` of the game. -/
instance checkReplyDecidable [DecidableEq GT] (e : G →ₗ[F] G₂ →ₗ[F] GT) (g₂ pk : G₂)
    (a b : G) : Decidable (PublicVerify.checkReply e g₂ pk a b) :=
  inferInstanceAs (Decidable (e b g₂ = e a pk))

/-- **The pairing check is sound for ONE key, whatever public key B published.**  Let `G` be
one-dimensional with generator `g` and let the pairing be non-degenerate at `g₂`.  Then for
EVERY element `pk : G₂` — honestly generated or not, and not even assumed to be a multiple of
`g₂` — there is a single scalar `k` such that every reply `b` that passes A's check on `a` is the
honest reply `evaluate k a = k • a` under that `k`.  (If `pk` is consistent with no key at all,
no reply to a non-identity element passes, and the statement holds trivially for that `pk`.)

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
  · refine ⟨0, fun a b hab => ?_⟩
    obtain ⟨c, rfl⟩ := hg.spans a
    obtain ⟨d, rfl⟩ := hg.spans b
    have hab' : d • e g g₂ = c • e g pk := by
      simpa [PublicVerify.checkReply, map_smul, LinearMap.smul_apply] using hab
    by_cases hc : c = 0
    · subst hc
      have h0 : e (d • g) g₂ = e 0 g₂ := by
        rw [map_smul, LinearMap.smul_apply, hab', zero_smul, map_zero, LinearMap.zero_apply]
      rw [hnd h0]
      simp [evaluate]
    · exact absurd ⟨c⁻¹ * d, by rw [mul_smul, hab', smul_smul, inv_mul_cancel₀ hc, one_smul]⟩ h

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

section Strategies

variable {F G M : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- The experiment B could run by itself from two group elements `p = (a₀, a₁)` and the two
constants `prf H k m₀`, `prf H k m₁`: compute the replies, and feed the guessing stage with the
two genuine signatures if both replies pass the test and with the abort symbol otherwise.  No
coin of A and no hidden bit occurs in it. -/
noncomputable def simGame {S γ : Type*} (H : M → G) (Valid : G → G → Bool) (k : F)
    (m₀ m₁ : M) (reply : G × G → PMF (S × G × G)) (guess : S → Option (G × G) → PMF γ)
    (p : G × G) : PMF γ :=
  (reply p).bind fun t : S × G × G =>
    guess t.1
      (if Valid p.1 t.2.1 && Valid p.2 t.2.2 then some (prf H k m₀, prf H k m₁) else none)

/-- The honest signer with key `k`: no state, both sessions answered with `k • a`. -/
noncomputable def honestReply (k : F) (p : G × G) : PMF (Unit × G × G) :=
  PMF.pure ((), evaluate k p.1, evaluate k p.2)

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

theorem tagReply_self (k : F) : (tagReply k k : G × G → PMF (Unit × G × G)) = honestReply k :=
  rfl

end Strategies

/-! ## Two general probability facts -/

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

end Prob

section Main

variable {F G M : Type*} [Field F] [Fintype F] [DecidableEq F] [AddCommGroup G] [Module F G]
  {g : G}

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
          (blind H (if β then m₁ else m₀) rs.1, blind H (if β then m₀ else m₁) rs.2) := by
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
    rw [hV _ _ hv0, hV _ _ hv1]
    cases β <;> simp [unblind_evaluate_blind]
  · rw [ite_eq_right hv, ite_eq_right hv]

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
* Only two sessions; the `n`-session game (guessing a permutation) is not proven here.
* `hV` demands PERFECT soundness with respect to ONE key for both sessions.  Checks that are
  only statistically sound (interactive proofs of discrete-log equality) or sound in the
  random-oracle model (Fiat–Shamir) do not satisfy `hV`, and are not covered.
* The same test `Valid` is used in both sessions, i.e. the signer shows the same public key to
  every client.  With per-client keys the theorem fails (`tagging_attack`).
* A releases its outputs only if BOTH sessions pass; per-session release is insecure
  (`selective_abort`).  The outputs are released after both sessions are complete.
* The messages are fixed before the coins are drawn (they are universally quantified, so the
  signer may know and may have chosen them), and both hashes must be non-identity.
* A's coins are uniform on the nonzero scalars, independent, and secret.
* It says nothing about unforgeability, nor about what A learns about the key.
* By itself it does not say A ever accepts: for that see `blindnessGame_honest`. -/
theorem blindness (hg : IsGenerator F g) (H : M → G) {m₀ m₁ : M} (h₀ : H m₀ ≠ 0)
    (h₁ : H m₁ ≠ 0) (Valid : G → G → Bool) (k : F)
    (hV : ∀ a b, Valid a b = true → b = evaluate k a) {S γ : Type*}
    (reply : G × G → PMF (S × G × G)) (guess : S → Option (G × G) → PMF γ) :
    blindnessGame F H Valid m₀ m₁ reply guess false =
      blindnessGame F H Valid m₀ m₁ reply guess true := by
  rw [blindnessGame_eq_sim H Valid k hV, blindnessGame_eq_sim H Valid k hV]
  exact unif_bind_blind_swap hg H h₀ h₁ _

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

/-- **Blindness with the public pairing check, for an ARBITRARY public key.**

A's test is the pairing equation `e b g₂ = e a pk` of `BlindPRF/PublicVerify.lean`; it uses only
the transcript `(a, b)` and public data.  The pairing is non-degenerate at `g₂` (`hnd`).  The
public key `pk` is ANY element of `G₂`: the signer may have chosen it maliciously, need not know
a corresponding secret key, and `pk` need not even be a multiple of `g₂`.  Then for every
strategy of the signer the two-session blindness game has the same output distribution for both
values of the hidden bit.

What this does NOT claim: see `blindness`.  In particular A uses the SAME `pk` in both sessions;
that is an assumption of the model (a signer able to show different public keys to different
clients is outside this theorem and can tag them).  Only two sessions are treated, and the check
here is the perfectly sound pairing check, not a zero-knowledge proof of discrete-log equality.
That the signer cannot make A accept a wrong signature is `PublicVerify.checked_run`, not this
theorem. -/
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
the pairing is needed for this direction. -/
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

/-! ## NEGATIVE: without a reply check the protocol is not blind (tagging attack) -/

/-- **Tagging attack: the bare protocol is NOT blind.**  Take the game with NO check
(`Valid` always accepts), two different keys `k₀ ≠ k₁`, and the explicit signer that answers
session 0 under `k₀` and session 1 under `k₁` (`tagReply`), then compares A's outputs with
`(k₀ • H m₀, k₁ • H m₁)` (`tagGuess`).  Its guess equals the hidden bit with certainty: the game
for hidden bit `β` is the point mass at `β`.

So seeing A's final outputs lets a malicious signer link every signature to the session that
produced it, although everything the signer saw before the outputs were released is independent
of the session order (`blindedPair_dist_eq`).  The attack is cheap (a few scalar multiplications
and one comparison); only `H m₀ ≠ 0` and `k₀ ≠ k₁` are needed, no assumption on the group.

It does NOT say the protocol leaks the message during a session, and it does NOT apply when A
checks the replies against one committed key (`blindness`). -/
theorem tagging_attack [DecidableEq G] (H : M → G) {m₀ m₁ : M} (h₀ : H m₀ ≠ 0) {k₀ k₁ : F}
    (hk : k₀ ≠ k₁) (β : Bool) :
    blindnessGame F H (fun _ _ => true) m₀ m₁ (tagReply k₀ k₁) (tagGuess H k₀ k₁ m₀ m₁) β =
      PMF.pure β := by
  have hne : prf H k₁ m₀ ≠ prf H k₀ m₀ := fun h => hk (smul_left_injective F h₀ h).symm
  simp only [blindnessGame, tagReply, tagGuess, PMF.pure_bind]
  cases β
  · simp [unblind_evaluate_blind, PMF.bind_const]
  · simp [unblind_evaluate_blind, PMF.bind_const, hne]

/-- Tagging attack, hidden bit `false`: the signer outputs `false` with certainty. -/
theorem tagging_attack_false [DecidableEq G] (H : M → G) {m₀ m₁ : M} (h₀ : H m₀ ≠ 0)
    {k₀ k₁ : F} (hk : k₀ ≠ k₁) :
    blindnessGame F H (fun _ _ => true) m₀ m₁ (tagReply k₀ k₁) (tagGuess H k₀ k₁ m₀ m₁) false =
      PMF.pure false :=
  tagging_attack H h₀ hk false

/-- Tagging attack, hidden bit `true`: the signer outputs `true` with certainty. -/
theorem tagging_attack_true [DecidableEq G] (H : M → G) {m₀ m₁ : M} (h₀ : H m₀ ≠ 0)
    {k₀ k₁ : F} (hk : k₀ ≠ k₁) :
    blindnessGame F H (fun _ _ => true) m₀ m₁ (tagReply k₀ k₁) (tagGuess H k₀ k₁ m₀ m₁) true =
      PMF.pure true :=
  tagging_attack H h₀ hk true

/-- Without a reply check, the two values of the hidden bit give DIFFERENT distributions of the
tagging signer's guess: the conclusion of `blindness` fails for the unchecked protocol. -/
theorem tagging_not_blind [DecidableEq G] (H : M → G) {m₀ m₁ : M} (h₀ : H m₀ ≠ 0)
    {k₀ k₁ : F} (hk : k₀ ≠ k₁) :
    blindnessGame F H (fun _ _ => true) m₀ m₁ (tagReply k₀ k₁) (tagGuess H k₀ k₁ m₀ m₁) false ≠
      blindnessGame F H (fun _ _ => true) m₀ m₁ (tagReply k₀ k₁) (tagGuess H k₀ k₁ m₀ m₁)
        true := by
  rw [tagging_attack_false H h₀ hk, tagging_attack_true H h₀ hk]
  exact pure_false_ne_pure_true

/-- Without a reply check, the tagging signer guesses a uniform hidden bit correctly with
probability one (compare `blindness_guess_fair`: one half with a sound check). -/
theorem tagging_attack_wins [DecidableEq G] (H : M → G) {m₀ m₁ : M} (h₀ : H m₀ ≠ 0)
    {k₀ k₁ : F} (hk : k₀ ≠ k₁) :
    ((unif Bool).bind fun β : Bool =>
      (blindnessGame F H (fun _ _ => true) m₀ m₁ (tagReply k₀ k₁)
        (tagGuess H k₀ k₁ m₀ m₁) β).map fun b' : Bool => decide (b' = β)) = PMF.pure true := by
  have h : (fun β : Bool =>
      (blindnessGame F H (fun _ _ => true) m₀ m₁ (tagReply k₀ k₁)
        (tagGuess H k₀ k₁ m₀ m₁) β).map fun b' : Bool => decide (b' = β)) =
      fun _ : Bool => PMF.pure true := by
    funext β
    rw [tagging_attack H h₀ hk β, PMF.pure_map, decide_eq_true rfl]
  rw [h, PMF.bind_const]

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
only ever sees the abort symbol. -/
theorem selective_abort (H : M → G) {m₀ m₁ : M} (h₀ : H m₀ ≠ 0) (h₁ : H m₁ ≠ 0)
    (Valid : G → G → Bool) {k k' : F} (hk : k' ≠ k) (hC : ∀ a, Valid a (evaluate k a) = true)
    (hV : ∀ a b, Valid a b = true → b = evaluate k a) (β : Bool) :
    perSessionGame F H Valid m₀ m₁ (tagReply k k') abortGuess β = PMF.pure β := by
  have hbad : ∀ m : M, H m ≠ 0 → ∀ r : Fˣ,
      Valid (blind H m r) (evaluate k' (blind H m r)) = false := by
    intro m hm r
    by_contra hcon
    rw [Bool.not_eq_false] at hcon
    exact evaluate_ne_of_key_ne hk (blinded_ne_zero H hm r) (hV _ _ hcon)
  simp only [perSessionGame, tagReply, abortGuess, PMF.pure_bind]
  cases β
  · simp [hC, hbad m₁ h₁, PMF.bind_const]
  · simp [hC, hbad m₀ h₀, PMF.bind_const]

/-- The selective-abort attack against the pairing check with an HONESTLY generated public key
`pk = k • g₂` and a non-degenerate pairing: with per-session release the signer learns the hidden
bit with certainty, although the very same check gives perfect blindness under all-or-nothing
release (`blindness_pairing`). -/
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

end Main

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
