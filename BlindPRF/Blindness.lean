/-
  BlindPRF/Blindness.lean — perfect (information-theoretic) message privacy against party B.

  Everything party B sees in one session is `viewB H k m r = (k, blind H m r)`: its own key and
  the single group element `a = r • H m` that party A sends.  This file proves that, when the
  coin `r` is uniform over the NONZERO scalars and `H m ≠ 0`, the distribution of that view does
  not depend on the message `m` at all.  No hardness assumption is used anywhere in this file:
  the statements are equalities of probability distributions, so they hold against a
  computationally unbounded B.  The statements about B's view of a session also hold against a
  malicious B, because B receives exactly one protocol message and receives it before it sends
  anything: nothing B does can change what it sees.  (The unlinkability section is different: it
  also involves A's output, which a misbehaving B does influence; see below.)

  Contents.
  * Algebra.  `blind_eq_blind_mul`: changing the message amounts to multiplying the coin by a
    fixed unit.  `blindEquiv` / `blind_unique_coin`: for `H m ≠ 0`, blinding is a bijection from
    the nonzero scalars onto the nonzero group elements, so every possible transcript is
    explained by every message, by exactly one coin.
  * One session.  `blind_dist_eq`, `viewB_dist_eq`, `viewB_dist_eq_sim` (B could have produced
    its view by itself), `message_view_independent` (posterior = prior),
    `blind_uniform_nonzero`, `adversary_output_eq` (any randomized post-processing by B), and
    the guessing games `indGame_true`, `indGameAdaptive_true` (B wins with probability exactly
    one half).
  * Many sessions.  `multi_blind_dist_eq`, `multi_adversary_output_eq`.
  * Unlinkability of transcript and signature.  `unlinkability`, `linkGame_true`, together with
    the LIMITATION `output_eq_iff_reply_key`, `linkGame_tagging_true`: unlinkability holds for
    a B that answers every session with one fixed key, and FAILS for a B that uses a different
    key per session (A cannot detect this in the bare protocol).
  * Negative results showing that the hypotheses and the definition are not decorative:
    `blind_dist_ne_of_hash_zero` (the condition `H m ≠ 0` is necessary),
    `blind_same_coin_eq_iff` (coins must not be reused), and `noBlind_dist_ne`,
    `noBlindGame_true` (the protocol without blinding is distinguished with certainty).

  What this file does NOT prove.  Nothing here concerns party A learning the key `k`, or
  unforgeability; those are computational statements and live elsewhere.  The privacy statements
  are about B's protocol view only: they assume the coin is uniform on the nonzero scalars, is
  fresh for each session, and stays secret, and they say nothing about side channels or about
  information B obtains about `m` outside the protocol.
-/
import BlindPRF.Correctness
import BlindPRF.Prob

namespace BlindPRF

open scoped ENNReal

variable {F G M : Type*}

/-! ## Algebra of the blinding step (no probability) -/

section Algebra

variable [Field F] [AddCommGroup G] [Module F G] {g : G}

/-- **Necessity of the non-identity condition, algebraic form.**  The blinded element is the
identity exactly when the hash of the message is the identity (the coin is nonzero, so it
cannot hide a zero).  So party B can always tell whether `H m = 0`. -/
theorem blind_eq_zero_iff (H : M → G) (m : M) (r : Fˣ) : blind H m r = 0 ↔ H m = 0 := by
  simp [blind]

/-- If the hash of the message is not the identity, neither is the blinded element. -/
theorem blind_ne_zero (H : M → G) {m : M} (hm : H m ≠ 0) (r : Fˣ) : blind H m r ≠ 0 :=
  fun h => hm ((blind_eq_zero_iff H m r).mp h)

/-- For a message whose hash is not the identity, different coins give different blinded
elements. -/
theorem blind_injective (H : M → G) {m : M} (hm : H m ≠ 0) :
    Function.Injective (blind H m : Fˣ → G) := by
  intro r r' h
  exact Units.ext (smul_left_injective F hm h)

/-- In a group of prime order, any two non-identity points `P`, `Q` differ by a nonzero scalar,
so multiplying `Q` by `r` is the same as multiplying `P` by the shifted scalar `r * u`. -/
theorem Blindness.smul_eq_mul_smul (hg : IsGenerator F g) {P Q : G} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    ∃ u : Fˣ, ∀ r : Fˣ, (r : F) • Q = ((r * u : Fˣ) : F) • P := by
  obtain ⟨c, hc⟩ := (hg.of_ne_zero hP).spans Q
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hQ (by simpa using hc.symm)
  refine ⟨Units.mk0 c hc0, fun r => ?_⟩
  rw [Units.val_mul, Units.val_mk0, mul_smul, hc]

/-- **The algebraic heart of blindness.**  For two messages whose hashes are not the identity
there is a fixed nonzero scalar `u` such that blinding `m₁` with coin `r` produces exactly the
same group element as blinding `m₀` with coin `r * u`.  So a transcript never pins down the
message: it only relates the message to the (hidden) coin.  This is a statement about group
elements, not about distributions; the probabilistic consequences are below. -/
theorem blind_eq_blind_mul (hg : IsGenerator F g) (H : M → G) {m₀ m₁ : M}
    (h₀ : H m₀ ≠ 0) (h₁ : H m₁ ≠ 0) :
    ∃ u : Fˣ, ∀ r : Fˣ, blind H m₁ r = blind H m₀ (r * u) :=
  Blindness.smul_eq_mul_smul hg h₀ h₁

/-- Every non-identity group element is a possible first message for every message `m` with
`H m ≠ 0`. -/
theorem blind_surjective_nonzero (hg : IsGenerator F g) (H : M → G) {m : M} (hm : H m ≠ 0)
    {a : G} (ha : a ≠ 0) : ∃ r : Fˣ, blind H m r = a := by
  obtain ⟨c, hc⟩ := (hg.of_ne_zero hm).spans a
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact ha (by simpa using hc.symm)
  exact ⟨Units.mk0 c hc0, hc⟩

/-- For `H m ≠ 0`, the blinding map `r ↦ r • H m` is a bijection from the nonzero scalars onto
the non-identity group elements. -/
theorem blind_bijective_nonzero (hg : IsGenerator F g) (H : M → G) {m : M} (hm : H m ≠ 0) :
    Function.Bijective
      (fun r : Fˣ => (⟨blind H m r, blind_ne_zero H hm r⟩ : {x : G // x ≠ 0})) := by
  refine ⟨fun r r' h => blind_injective H hm (congrArg Subtype.val h), ?_⟩
  rintro ⟨a, ha⟩
  obtain ⟨r, hr⟩ := blind_surjective_nonzero hg H hm ha
  exact ⟨r, Subtype.ext hr⟩

/-- The blinding map as an equivalence between nonzero scalars and non-identity group elements.
(Its inverse is a discrete logarithm: it exists, but nothing here says it can be computed.) -/
noncomputable def blindEquiv (hg : IsGenerator F g) (H : M → G) {m : M} (hm : H m ≠ 0) :
    Fˣ ≃ {x : G // x ≠ 0} :=
  Equiv.ofBijective _ (blind_bijective_nonzero hg H hm)

@[simp]
theorem blindEquiv_apply_coe (hg : IsGenerator F g) (H : M → G) {m : M} (hm : H m ≠ 0)
    (r : Fˣ) : (blindEquiv hg H hm r : G) = blind H m r := rfl

/-- **Every transcript is explained by every message, by exactly one coin.**  Given any
non-identity element `a` that B might have received and any message `m` with `H m ≠ 0`, there is
one and only one coin `r` for which A, holding `m`, would have sent `a`.  Hence the transcript
alone rules out no message.  This is a counting statement; that all those coins are equally
likely is `blind_dist_eq` / `blind_uniform_nonzero`. -/
theorem blind_unique_coin (hg : IsGenerator F g) (H : M → G) {m : M} (hm : H m ≠ 0) :
    ∀ a : G, a ≠ 0 → ∃! r : Fˣ, blind H m r = a := by
  intro a ha
  obtain ⟨r, hr⟩ := blind_surjective_nonzero hg H hm ha
  exact ⟨r, hr, fun r' hr' => blind_injective H hm (hr'.trans hr.symm)⟩

/-- **Why coins must be fresh (negative result).**  If A reused the same coin for two messages,
the two blinded elements would coincide exactly when the two hashes coincide, so B would learn
whether the two sessions carry messages with the same hash (for a collision-free hash: the same
message).  The multi-session theorem `multi_blind_dist_eq` therefore really needs independent
coins. -/
theorem blind_same_coin_eq_iff (H : M → G) (m m' : M) (r : Fˣ) :
    blind H m r = blind H m' r ↔ H m = H m' :=
  (smul_right_injective G r.ne_zero).eq_iff

/-- **Limitation of unlinkability (negative result: key tagging).**  The value A outputs when B
answers with key `k` equals the value A outputs when B answers with key `k'` only if `k = k'`
(for `H m ≠ 0`).  So a malicious B that answers different sessions with different keys leaves a
recognisable mark on A's *output*: if A later publishes `(m, σ)`, B can test `σ = k' • H m` and
learn which session produced it (`linkGame_tagging_true` turns this into a winning strategy).
This does not contradict the message-privacy theorems of this file (those concern B's view of
the session, which is complete before B answers), but it is why `unlinkability` and
`linkGame_true` are stated for replies computed with one fixed key.  Ruling this attack out
needs A to verify B's reply (e.g. a proof of discrete-log equality against a public key), which
is outside this file. -/
theorem output_eq_iff_reply_key (H : M → G) {m : M} (hm : H m ≠ 0) (k k' : F) (r r' : Fˣ) :
    unblind r (evaluate k (blind H m r)) = unblind r' (evaluate k' (blind H m r')) ↔ k = k' := by
  rw [unblind_evaluate_blind, unblind_evaluate_blind]
  exact (smul_left_injective F hm).eq_iff

end Algebra

/-! ## General-purpose probability facts -/

namespace Blindness

/-- Every point has positive probability under the uniform distribution. -/
theorem mem_support_unif {α : Type*} [Fintype α] [Nonempty α] (a : α) :
    a ∈ (unif α).support := by
  rw [PMF.mem_support_iff, unif_apply]
  exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)

/-- Two continuations that agree on the support of `p` give the same experiment. -/
theorem bind_congr_of_support {α β : Type*} (p : PMF α) (f f' : α → PMF β)
    (h : ∀ a ∈ p.support, f a = f' a) : p.bind f = p.bind f' := by
  ext b
  rw [PMF.bind_apply, PMF.bind_apply]
  refine tsum_congr fun a => ?_
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · rw [PMF.mem_support_iff, not_not] at ha
    rw [ha, zero_mul, zero_mul]

/-- If a guess `b'` is drawn from a distribution `P` that does not depend on the uniformly
random bit `b`, then the event "the guess is right" is a fair coin. -/
theorem guess_independent_bit (P : PMF Bool) :
    ((unif Bool).bind fun b => P.map fun b' => decide (b' = b)) = unif Bool := by
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

/-- The uniform bit takes each value with probability one half. -/
theorem unif_bool_apply (c : Bool) : unif Bool c = 1 / 2 := by
  simp

end Blindness

open Blindness

/-! ## One session: B's view is independent of the message -/

section Privacy

variable [Field F] [Fintype F] [DecidableEq F] [AddCommGroup G] [Module F G] {g : G}

/-- Multiplying two non-identity points by a uniform nonzero scalar gives the same
distribution. -/
theorem Blindness.smul_dist_eq (hg : IsGenerator F g) {P Q : G} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    (unif Fˣ).map (fun r : Fˣ => (r : F) • P) = (unif Fˣ).map (fun r : Fˣ => (r : F) • Q) := by
  obtain ⟨u, hu⟩ := smul_eq_mul_smul hg hP hQ
  exact (unif_map_eq_of_equiv (Equiv.mulRight u) (fun r : Fˣ => (r : F) • Q)
    (fun r : Fˣ => (r : F) • P) (fun r => (hu r).symm)).symm

/-- **Perfect blindness of the first message.**  With a uniformly random nonzero coin, the group
element A sends has exactly the same distribution whichever of two messages (with non-identity
hashes) A holds.  This is an equality of distributions, not a computational approximation: it
holds for every hash function `H`, with no assumption on the hardness of any problem.
It does NOT say anything when a hash is the identity (see `blind_dist_ne_of_hash_zero`). -/
theorem blind_dist_eq (hg : IsGenerator F g) (H : M → G) {m₀ m₁ : M}
    (h₀ : H m₀ ≠ 0) (h₁ : H m₁ ≠ 0) :
    (unif Fˣ).map (blind H m₀) = (unif Fˣ).map (blind H m₁) :=
  smul_dist_eq hg h₀ h₁

/-- **B's whole view is independent of the message.**  For every key `k` (honestly generated or
not), the pair (key, received element) that constitutes everything party B sees in a session
has the same distribution for any two messages with non-identity hashes.  Since B receives this
single element before sending anything, the statement covers a malicious B as well.
It does NOT cover information about `m` that B obtains outside the session. -/
theorem viewB_dist_eq (hg : IsGenerator F g) (H : M → G) (k : F) {m₀ m₁ : M}
    (h₀ : H m₀ ≠ 0) (h₁ : H m₁ ≠ 0) :
    (unif Fˣ).map (viewB H k m₀) = (unif Fˣ).map (viewB H k m₁) := by
  have h : ∀ m, viewB H k m = (fun a : G => (k, a)) ∘ blind H m := fun m => rfl
  rw [h m₀, h m₁, ← PMF.map_comp, ← PMF.map_comp, blind_dist_eq hg H h₀ h₁]

/-- The simulator for party B: from the public generator `g` and B's own key alone (no message,
no hash function) it samples something distributed like B's view. -/
noncomputable def simB (g : G) (k : F) : PMF (F × G) :=
  (unif Fˣ).map fun r : Fˣ => (k, (r : F) • g)

/-- **Simulation form of message privacy.**  B's view in a real session on message `m` (with
`H m ≠ 0`) is distributed exactly like the output of `simB g k`, which is computed without `m`
and without `H`.  So whatever B derives from a session it could have derived alone. -/
theorem viewB_dist_eq_sim (hg : IsGenerator F g) (H : M → G) (k : F) {m : M} (hm : H m ≠ 0) :
    (unif Fˣ).map (viewB H k m) = simB g k := by
  have h1 : viewB H k m = (fun a : G => (k, a)) ∘ fun r : Fˣ => (r : F) • H m := rfl
  have h2 : (fun r : Fˣ => (k, (r : F) • g)) = (fun a : G => (k, a)) ∘ fun r : Fˣ => (r : F) • g :=
    rfl
  rw [simB, h1, h2, ← PMF.map_comp, ← PMF.map_comp, smul_dist_eq hg hm hg.ne_zero]

/-- **Perfect secrecy in Shannon's sense: the message and B's view are independent.**  Let the
message be drawn from ANY prior distribution `μ` (supported on messages with non-identity hash)
and then one session be run.  The joint distribution of (message, B's view) is the product of
`μ` with the message-free distribution `simB g k`.  Hence, after the session, B's posterior
distribution on the message equals its prior: the session tells B nothing it did not already
know.  It does NOT say the message is hidden from someone who also learns the coin `r`. -/
theorem message_view_independent (hg : IsGenerator F g) (H : M → G) (k : F) (μ : PMF M)
    (hμ : ∀ m ∈ μ.support, H m ≠ 0) :
    (μ.bind fun m => (unif Fˣ).map fun r => (m, viewB H k m r)) =
      μ.bind fun m => (simB g k).map fun v => (m, v) := by
  refine bind_congr_of_support _ _ _ fun m hm => ?_
  rw [← viewB_dist_eq_sim hg H k (hμ m hm), PMF.map_comp]
  rfl

/-- **The blinded element is uniform on the non-identity elements.**  Viewed as an element of
`{x : G // x ≠ 0}`, what A sends is uniformly distributed, whatever the message (with
`H m ≠ 0`).  The `Fintype` structure on the non-identity elements is an arbitrary instance
argument (for instance the one coming from `[Fintype G] [DecidableEq G]`). -/
theorem blind_uniform_nonzero [Fintype {x : G // x ≠ 0}] (hg : IsGenerator F g) (H : M → G)
    {m : M} (hm : H m ≠ 0) :
    (unif Fˣ).map (blindEquiv hg H hm) = @unif {x : G // x ≠ 0} _ ⟨⟨H m, hm⟩⟩ :=
  @unif_map_equiv _ _ _ _ _ ⟨⟨H m, hm⟩⟩ (blindEquiv hg H hm)

/-- The same fact without subtypes: every non-identity element `a` is sent with probability
exactly `1 / |Fˣ|`, a number that does not depend on the message. -/
theorem blind_dist_apply (hg : IsGenerator F g) (H : M → G) {m : M} (hm : H m ≠ 0)
    {a : G} (ha : a ≠ 0) :
    (unif Fˣ).map (blind H m) a = (Fintype.card Fˣ : ℝ≥0∞)⁻¹ := by
  obtain ⟨r₀, hr₀, huniq⟩ := blind_unique_coin hg H hm a ha
  rw [PMF.map_apply, tsum_eq_single r₀]
  · simp [hr₀]
  · intro r hr
    have : a ≠ blind H m r := fun h => hr (huniq r h.symm)
    simp [this]

/-- ... and the identity element is never sent when `H m ≠ 0`. -/
theorem blind_dist_apply_zero (H : M → G) {m : M} (hm : H m ≠ 0) :
    (unif Fˣ).map (blind H m) 0 = 0 := by
  rw [PMF.map_apply]
  have : ∀ r : Fˣ, (0 : G) ≠ blind H m r := fun r h => blind_ne_zero H hm r h.symm
  simp [this]

/-- **No strategy of B extracts anything about the message.**  Let `D` be ANY randomized
procedure that B applies to its view, with any output type `β` (a guess of the message, a
reply to send to A, internal notes, ...).  `D` is an arbitrary function into distributions: it
need not be efficient, so B is computationally unbounded.  Then the distribution of `D`'s
output is identical for any two messages with non-identity hashes.
It does NOT claim anything about procedures that receive more than B's view. -/
theorem adversary_output_eq {β : Type*} (hg : IsGenerator F g) (H : M → G) (k : F) {m₀ m₁ : M}
    (h₀ : H m₀ ≠ 0) (h₁ : H m₁ ≠ 0) (D : F × G → PMF β) :
    ((unif Fˣ).bind fun r => D (viewB H k m₀ r)) =
      (unif Fˣ).bind fun r => D (viewB H k m₁ r) := by
  have h : ∀ m, (fun r => D (viewB H k m r)) = D ∘ viewB H k m := fun m => rfl
  rw [h m₀, h m₁, ← PMF.bind_map, ← PMF.bind_map, viewB_dist_eq hg H k h₀ h₁]

/-! ### The indistinguishability game -/

/-- The message-indistinguishability game against party B.  A hidden bit `b` is drawn
uniformly; A runs one session on `m₁` if `b` is true and on `m₀` otherwise, with a fresh
uniform nonzero coin; B's (randomized) guessing procedure `D` is run on B's view.  The game
outputs `true` exactly when the guess equals `b`. -/
noncomputable def indGame (H : M → G) (k : F) (m₀ m₁ : M) (D : F × G → PMF Bool) : PMF Bool :=
  (unif Bool).bind fun b => (unif Fˣ).bind fun r =>
    (D (viewB H k (if b then m₁ else m₀) r)).map fun b' => decide (b' = b)

/-- The outcome of the indistinguishability game is a fair coin, for every guessing strategy. -/
theorem indGame_eq_unif (hg : IsGenerator F g) (H : M → G) (k : F) {m₀ m₁ : M}
    (h₀ : H m₀ ≠ 0) (h₁ : H m₁ ≠ 0) (D : F × G → PMF Bool) :
    indGame H k m₀ m₁ D = unif Bool := by
  have key : ∀ b : Bool, ((unif Fˣ).bind fun r =>
      (D (viewB H k (if b then m₁ else m₀) r)).map fun b' => decide (b' = b)) =
      ((unif Fˣ).bind fun r => D (viewB H k m₀ r)).map fun b' => decide (b' = b) := by
    intro b
    have hb : ((unif Fˣ).bind fun r => D (viewB H k (if b then m₁ else m₀) r)) =
        (unif Fˣ).bind fun r => D (viewB H k m₀ r) := by
      cases b
      · rfl
      · exact (adversary_output_eq hg H k h₀ h₁ D).symm
    rw [← hb, PMF.map_bind]
  unfold indGame
  simp only [key]
  exact guess_independent_bit _

/-- **Advantage exactly zero.**  In the indistinguishability game party B guesses which of the
two messages was submitted with probability exactly one half, i.e. no better than by ignoring
the session altogether.  This holds for EVERY key `k`, EVERY pair of messages `m₀`, `m₁` with
non-identity hashes (all universally quantified, so B may choose the pair itself, knowing its
key; see `indGameAdaptive_true` for a pair chosen by a randomized first stage), and EVERY
randomized, computationally unbounded guessing strategy `D`.
It does NOT say that B is ignorant of the message in an absolute sense: B may know a lot about
it from elsewhere (in this game it even knows both candidates).  The theorem says that the
session adds nothing to that knowledge. -/
theorem indGame_true (hg : IsGenerator F g) (H : M → G) (k : F) {m₀ m₁ : M}
    (h₀ : H m₀ ≠ 0) (h₁ : H m₁ ≠ 0) (D : F × G → PMF Bool) :
    indGame H k m₀ m₁ D true = 1 / 2 := by
  rw [indGame_eq_unif hg H k h₀ h₁ D, unif_bool_apply]

/-- The two-stage game in which party B itself chooses the challenge pair: a randomized first
stage `C`, given the key, outputs the two messages together with arbitrary state `s : S` that
is handed to the guessing stage `D s`. -/
noncomputable def indGameAdaptive {S : Type*} (H : M → G) (k : F)
    (C : F → PMF (M × M × S)) (D : S → F × G → PMF Bool) : PMF Bool :=
  (C k).bind fun c => indGame H k c.1 c.2.1 (D c.2.2)

/-- The outcome of the two-stage game is a fair coin as well. -/
theorem indGameAdaptive_eq_unif {S : Type*} (hg : IsGenerator F g) (H : M → G) (k : F)
    (C : F → PMF (M × M × S)) (D : S → F × G → PMF Bool)
    (hC : ∀ c ∈ (C k).support, H c.1 ≠ 0 ∧ H c.2.1 ≠ 0) :
    indGameAdaptive H k C D = unif Bool := by
  unfold indGameAdaptive
  rw [bind_congr_of_support (C k) _ (fun _ => unif Bool) fun c hc =>
    indGame_eq_unif hg H k (hC c hc).1 (hC c hc).2 (D c.2.2), PMF.bind_const]

/-- **Advantage exactly zero, with the challenge pair chosen by B.**  Even when B picks the two
candidate messages itself, by any randomized procedure that knows the key and keeps arbitrary
state, it identifies the submitted one with probability exactly one half.  The only requirement
is that every pair B can output consists of messages whose hashes are not the identity (which
is automatic when `H` never hits the identity). -/
theorem indGameAdaptive_true {S : Type*} (hg : IsGenerator F g) (H : M → G) (k : F)
    (C : F → PMF (M × M × S)) (D : S → F × G → PMF Bool)
    (hC : ∀ c ∈ (C k).support, H c.1 ≠ 0 ∧ H c.2.1 ≠ 0) :
    indGameAdaptive H k C D true = 1 / 2 := by
  rw [indGameAdaptive_eq_unif hg H k C D hC, unif_bool_apply]

/-! ## Many sessions -/

/-- **Multi-session blindness.**  Over any finite set `ι` of sessions with independent uniform
nonzero coins, the whole vector of first messages has the same distribution for any two vectors
of messages (all hashes non-identity).  In particular B cannot tell whether two sessions carry
the same message or different ones.
It does NOT cover coin reuse (`blind_same_coin_eq_iff`), and the message vectors are fixed in
advance: a party A that chooses later messages as a function of B's earlier replies is not
modelled here. -/
theorem multi_blind_dist_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (hg : IsGenerator F g)
    (H : M → G) (ms₀ ms₁ : ι → M) (h₀ : ∀ i, H (ms₀ i) ≠ 0) (h₁ : ∀ i, H (ms₁ i) ≠ 0) :
    (unif (ι → Fˣ)).map (fun rs i => blind H (ms₀ i) (rs i)) =
      (unif (ι → Fˣ)).map (fun rs i => blind H (ms₁ i) (rs i)) := by
  choose u hu using fun i => blind_eq_blind_mul hg H (h₀ i) (h₁ i)
  exact (unif_map_eq_of_equiv (Equiv.mulRight u) (fun rs i => blind H (ms₁ i) (rs i))
    (fun rs i => blind H (ms₀ i) (rs i)) (fun rs => funext fun i => (hu i (rs i)).symm)).symm

/-- **No strategy of B extracts anything from many sessions.**  Any randomized, unbounded
procedure `D` applied to B's key together with all the first messages of all sessions has the
same output distribution for any two message vectors with non-identity hashes. -/
theorem multi_adversary_output_eq {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (hg : IsGenerator F g) (H : M → G) (k : F) (ms₀ ms₁ : ι → M)
    (h₀ : ∀ i, H (ms₀ i) ≠ 0) (h₁ : ∀ i, H (ms₁ i) ≠ 0) (D : F × (ι → G) → PMF β) :
    ((unif (ι → Fˣ)).bind fun rs => D (k, fun i => blind H (ms₀ i) (rs i))) =
      (unif (ι → Fˣ)).bind fun rs => D (k, fun i => blind H (ms₁ i) (rs i)) := by
  have h : ∀ ms : ι → M, (fun rs : ι → Fˣ => D (k, fun i => blind H (ms i) (rs i))) =
      (fun t : ι → G => D (k, t)) ∘ fun rs i => blind H (ms i) (rs i) := fun ms => rfl
  rw [h ms₀, h ms₁, ← PMF.bind_map, ← PMF.bind_map, multi_blind_dist_eq hg H ms₀ ms₁ h₀ h₁]

/-! ## Unlinkability of transcript and signature -/

/-- **Unlinkability (joint distribution of transcript and output).**  Consider a session on
message `m` in which B answers honestly with its key `k`.  The pair (what B saw, the signature
A walks away with) is distributed exactly like (what B would have seen in a session on a
different message `m'`, the fixed value `prf H k m`).  So B's transcript is independent of the
signature and is equally consistent with any other message: when `(m, σ)` is published later, B
cannot link it to the session that produced it.
It does NOT cover a B that deviates in its reply: see `output_eq_iff_reply_key` and
`linkGame_tagging_true` for the key-tagging attack that defeats unlinkability of the output
when A has no way to verify B's reply. -/
theorem unlinkability (hg : IsGenerator F g) (H : M → G) (k : F) {m m' : M}
    (hm : H m ≠ 0) (hm' : H m' ≠ 0) :
    (unif Fˣ).map (fun r => (blind H m r, run H k m r)) =
      (unif Fˣ).map (fun r => (blind H m' r, prf H k m)) := by
  have h1 : (fun r : Fˣ => (blind H m r, run H k m r)) =
      (fun a : G => (a, prf H k m)) ∘ blind H m := by
    funext r
    simp [correctness]
  have h2 : (fun r : Fˣ => (blind H m' r, prf H k m)) =
      (fun a : G => (a, prf H k m)) ∘ blind H m' := rfl
  rw [h1, h2, ← PMF.map_comp, ← PMF.map_comp, blind_dist_eq hg H hm hm']

/-- In the linking game, the message handled by session `i` when the hidden bit is `b`:
session `i` handles `m₁` if `i ≠ b` and `m₀` if `i = b`.  So for `b = false` the sessions
`false, true` handle `m₀, m₁` in this order, and for `b = true` they handle `m₁, m₀`. -/
def sessionMsg (m₀ m₁ : M) (b i : Bool) : M := if xor i b then m₁ else m₀

/-- A's output in session `i` of the linking game, when B answers session `i` by multiplying
with the scalar `ks i` (an honest B uses the same key in both sessions). -/
def sessionOut (H : M → G) (ks : Bool → F) (m₀ m₁ : M) (b : Bool) (rs : Bool → Fˣ) (i : Bool) :
    G :=
  unblind (rs i) (evaluate (ks i) (blind H (sessionMsg m₀ m₁ b i) (rs i)))

omit [Fintype F] [DecidableEq F] in
/-- The signature on the `j`-th message comes out of session `xor j b`, and it is the PRF value
under whatever key B used in that session. -/
theorem sessionOut_xor (H : M → G) (ks : Bool → F) (m₀ m₁ : M) (b : Bool) (rs : Bool → Fˣ)
    (j : Bool) :
    sessionOut H ks m₀ m₁ b rs (xor j b) = prf H (ks (xor j b)) (if j then m₁ else m₀) := by
  have hmsg : sessionMsg m₀ m₁ b (xor j b) = if j then m₁ else m₀ := by
    cases b <;> cases j <;> rfl
  rw [sessionOut, unblind_evaluate_blind, hmsg]

/-- The linking game (the classical "blindness" game for blind signatures).  Two sessions are
run, on `m₀` and `m₁`, in an order determined by a hidden uniform bit `b`; B answers session `i`
with the key `ks i`.  B's procedure `D` (which may depend on the keys and on the two messages)
receives the two first messages in session order, and then the two signatures in MESSAGE order
(first the one on `m₀`, then the one on `m₁`, as they would appear once published).  The game
outputs `true` when `D` guesses `b`, i.e. when B correctly matches sessions to signatures. -/
noncomputable def linkGame (H : M → G) (ks : Bool → F) (m₀ m₁ : M)
    (D : (Bool → G) × (Bool → G) → PMF Bool) : PMF Bool :=
  (unif Bool).bind fun b => (unif (Bool → Fˣ)).bind fun rs =>
    (D (fun i => blind H (sessionMsg m₀ m₁ b i) (rs i),
      fun j => sessionOut H ks m₀ m₁ b rs (xor j b))).map fun b' => decide (b' = b)

/-- When B answers both sessions with the same key, the outcome of the linking game is a fair
coin. -/
theorem linkGame_eq_unif (hg : IsGenerator F g) (H : M → G) (k : F) {m₀ m₁ : M}
    (h₀ : H m₀ ≠ 0) (h₁ : H m₁ ≠ 0) (D : (Bool → G) × (Bool → G) → PMF Bool) :
    linkGame H (fun _ => k) m₀ m₁ D = unif Bool := by
  have hne : ∀ b i, H (sessionMsg m₀ m₁ b i) ≠ 0 := by
    intro b i
    unfold sessionMsg
    split_ifs
    · exact h₁
    · exact h₀
  have key : ∀ b : Bool, ((unif (Bool → Fˣ)).bind fun rs =>
      (D (fun i => blind H (sessionMsg m₀ m₁ b i) (rs i),
        fun j => sessionOut H (fun _ => k) m₀ m₁ b rs (xor j b))).map
        fun b' => decide (b' = b)) =
      ((unif (Bool → Fˣ)).bind fun rs =>
        D (fun i => blind H (sessionMsg m₀ m₁ false i) (rs i),
          fun j => prf H k (if j then m₁ else m₀))).map fun b' => decide (b' = b) := by
    intro b
    simp only [sessionOut_xor]
    rw [PMF.map_bind]
    exact multi_adversary_output_eq hg H k (sessionMsg m₀ m₁ b) (sessionMsg m₀ m₁ false)
      (hne b) (hne false) (fun v => (D (v.2, fun j => prf H k (if j then m₁ else m₀))).map
        fun b' => decide (b' = b))
  unfold linkGame
  simp only [key]
  exact guess_independent_bit _

/-- **Unlinkability, as a game with advantage exactly zero.**  A party B that answers both
sessions with the same key `k`, and later sees both published signatures, matches sessions to
signatures with probability exactly one half, whatever (randomized, unbounded) procedure it
uses and whichever two messages (with non-identity hashes) are involved.
It does NOT cover a B that answers the two sessions with different keys: such a B wins the same
game with certainty, see `linkGame_tagging_true`. -/
theorem linkGame_true (hg : IsGenerator F g) (H : M → G) (k : F) {m₀ m₁ : M}
    (h₀ : H m₀ ≠ 0) (h₁ : H m₁ ≠ 0) (D : (Bool → G) × (Bool → G) → PMF Bool) :
    linkGame H (fun _ => k) m₀ m₁ D true = 1 / 2 := by
  rw [linkGame_eq_unif hg H k h₀ h₁ D, unif_bool_apply]

/-- **Unlinkability FAILS against a signer that tags sessions (negative result).**  If B answers
the two sessions with two different keys, then the strategy "check whether the published
signature on `m₀` is the PRF value under the key used in session `true`" wins the linking game
with probability ONE (for `H m₀ ≠ 0`).  So the bare protocol does NOT give unlinkability against
a malicious B; `linkGame_true` is a statement about a B that uses one key throughout.  The
standard remedy, A verifying B's reply against a public key, is outside this file.  Message
privacy of the session itself (`viewB_dist_eq`, `indGame_true`, ...) is unaffected. -/
theorem linkGame_tagging_true [DecidableEq G] (H : M → G) (ks : Bool → F)
    (hks : ks false ≠ ks true) {m₀ : M} (m₁ : M) (h₀ : H m₀ ≠ 0) :
    linkGame H ks m₀ m₁ (fun v => PMF.pure (decide (v.2 false = prf H (ks true) m₀))) true
      = 1 := by
  have hne : prf H (ks false) m₀ ≠ prf H (ks true) m₀ :=
    fun h => hks (smul_left_injective F h₀ h)
  have key : ∀ b : Bool, ((unif (Bool → Fˣ)).bind fun rs =>
      (PMF.pure (decide (sessionOut H ks m₀ m₁ b rs (xor false b) = prf H (ks true) m₀))).map
        fun b' => decide (b' = b)) = PMF.pure true := by
    intro b
    simp only [sessionOut_xor]
    cases b <;> simp [PMF.pure_map, hne]
  unfold linkGame
  simp only [key]
  simp

/-! ## Negative results: the hypotheses and the definition have teeth -/

/-- **The non-identity condition is necessary (negative result).**  If one message hashes to
the identity and the other does not, the two first-message distributions are DIFFERENT: the
first is concentrated on the identity, the second never produces it.  So the hypothesis
`H m ≠ 0` in the privacy theorems cannot be dropped; a deployment must make sure the hash never
outputs the identity (or accept that B learns whether it did). -/
theorem blind_dist_ne_of_hash_zero (H : M → G) {m₀ m₁ : M} (h₀ : H m₀ = 0) (h₁ : H m₁ ≠ 0) :
    (unif Fˣ).map (blind H m₀) ≠ (unif Fˣ).map (blind H m₁) := by
  intro h
  have hmem : (0 : G) ∈ ((unif Fˣ).map (blind H m₀)).support :=
    (PMF.mem_support_map_iff _ _ _).mpr
      ⟨1, mem_support_unif _, (blind_eq_zero_iff H m₀ 1).mpr h₀⟩
  rw [h] at hmem
  obtain ⟨r, -, hr⟩ := (PMF.mem_support_map_iff _ _ _).mp hmem
  exact blind_ne_zero H h₁ r hr

end Privacy

section Strawman

variable [Field F] [Fintype F] [DecidableEq F]

/-- The strawman protocol without blinding: A ignores its coin and sends `H m` itself. -/
def noBlind (H : M → G) (m : M) (_r : Fˣ) : G := H m

/-- **The privacy property is not satisfied by every protocol (negative result).**  In the
strawman protocol where A sends the bare hash, two messages with different hashes induce
DIFFERENT first-message distributions.  Hence `blind_dist_eq` is a genuine property of the
blinding step and not an artefact of the way the property is phrased. -/
theorem noBlind_dist_ne (H : M → G) {m₀ m₁ : M} (h : H m₀ ≠ H m₁) :
    (unif Fˣ).map (noBlind H m₀) ≠ (unif Fˣ).map (noBlind H m₁) := by
  intro heq
  have hmem : H m₀ ∈ ((unif Fˣ).map (noBlind H m₀)).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨1, mem_support_unif _, rfl⟩
  rw [heq] at hmem
  obtain ⟨r, -, hr⟩ := (PMF.mem_support_map_iff _ _ _).mp hmem
  exact h hr.symm

/-- The indistinguishability game of `indGame`, played against the strawman protocol. -/
noncomputable def noBlindGame (H : M → G) (k : F) (m₀ m₁ : M) (D : F × G → PMF Bool) :
    PMF Bool :=
  (unif Bool).bind fun b => (unif Fˣ).bind fun r =>
    (D (k, noBlind H (if b then m₁ else m₀) r)).map fun b' => decide (b' = b)

/-- **The game is winnable when there is no blinding (negative result).**  Against the strawman
protocol, the obvious strategy "compare what you received with `H m₁`" wins the
indistinguishability game with probability ONE whenever the two hashes differ, in contrast with
the probability one half of `indGame_true`.  So the game really measures message privacy. -/
theorem noBlindGame_true [DecidableEq G] (H : M → G) (k : F) {m₀ m₁ : M} (h : H m₀ ≠ H m₁) :
    noBlindGame H k m₀ m₁ (fun v => PMF.pure (decide (v.2 = H m₁))) true = 1 := by
  have key : ∀ b : Bool, ((unif Fˣ).bind fun r =>
      (PMF.pure (decide (noBlind H (if b then m₁ else m₀) r = H m₁))).map
        fun b' => decide (b' = b)) = PMF.pure true := by
    intro b
    cases b <;> simp [noBlind, PMF.pure_map, h]
  unfold noBlindGame
  simp only [key]
  simp

end Strawman

/-! ## Non-vacuity: the hypotheses are satisfiable

In all three examples the scalars are an arbitrary finite field `F` (e.g. `ZMod p`), the group
is `F` itself with generator `1`, and the hash is the identity map. -/

/-- The hypotheses of the positive theorems can be met: the messages `1` and `-1` have nonzero
hashes. -/
example (F : Type) [Field F] [Fintype F] [DecidableEq F] (k : F) (D : F × F → PMF Bool) :
    indGame (fun m : F => m) k 1 (-1) D true = 1 / 2 :=
  indGame_true (g := (1 : F)) ⟨one_ne_zero, fun x => ⟨x, mul_one x⟩⟩ (fun m : F => m) k
    (m₀ := 1) (m₁ := -1) one_ne_zero (neg_ne_zero.mpr one_ne_zero) D

/-- The hypotheses of the necessity result can be met: the message `0` hashes to the identity,
the message `1` does not. -/
example (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    (unif Fˣ).map (blind (fun m : F => m) 0) ≠ (unif Fˣ).map (blind (fun m : F => m) 1) :=
  blind_dist_ne_of_hash_zero (fun m : F => m) rfl one_ne_zero

/-- The hypotheses of the strawman result can be met: the messages `0` and `1` have different
hashes. -/
example (F : Type) [Field F] [Fintype F] [DecidableEq F] (k : F) :
    noBlindGame (fun m : F => m) k 0 1 (fun v => PMF.pure (decide (v.2 = 1))) true = 1 :=
  noBlindGame_true (fun m : F => m) k zero_ne_one

end BlindPRF
