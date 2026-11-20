/-
  BlindPRF/Blindness.lean — perfect (information-theoretic) message privacy against party B.

  Everything party B sees in one session is `viewB H k m r = (k, blind H m r)`: its own key and
  the single group element `a = r • H m` that party A sends.  This file proves that the
  distribution of that view does not depend on the message `m` at all, PROVIDED

    (i)   the coin `r` is uniform over the NONZERO scalars, fresh for each session, and secret;
    (ii)  the group `G` has prime order: `IsGenerator F g`, i.e. `G` is one-dimensional over the
          scalar field `F`;
    (iii) the hash of the message is not the identity: `H m ≠ 0`.

  No hardness assumption is used anywhere in this file: the statements are equalities of
  probability distributions, so they hold against a computationally unbounded B.  The statements
  about B's view of a session also hold against a malicious B, because B receives exactly one
  protocol message and receives it before it sends anything: nothing B does can change what it
  sees.  (The section on transcripts and signatures is different: it also involves A's output,
  which a misbehaving B does influence; see below.)

  Contents.
  * Algebra.  `blind_eq_blind_mul`: changing the message amounts to multiplying the coin by a
    fixed unit.  `blindEquiv` / `blind_unique_coin`: for `H m ≠ 0`, blinding is a bijection from
    the nonzero scalars onto the nonzero group elements, so every possible transcript is
    explained by every message, by exactly one coin.
  * One session.  `blind_dist_eq`, `viewB_dist_eq`, `viewB_dist_eq_sim` (B could have produced
    its view by itself), `message_view_independent` (posterior = prior),
    `blind_uniform_nonzero`, `adversary_output_eq` (any randomized post-processing by B), and
    the guessing games `indGame_true`, `indGameAdaptive_true` (B wins with probability exactly
    one half).  The game is defined once, generically in A's first-message function
    (`indGameWith`): `indGame` is its instance for the real protocol and `noBlindGame` its
    instance for a strawman.  The two general facts about it are `indGameWith_eq_unif` (equal
    first-message distributions give a fair coin) and `indGameWith_win` (a test that separates
    the two first messages wins with certainty).
  * Many sessions.  `multi_blind_dist_eq`, `multi_adversary_output_eq`.
  * Transcript and signature.  `unlinkability` (the joint distribution of transcript and output
    of one honest session; for a fixed message this is a restatement of `blind_dist_eq`, see
    `unlinkability_iff`), `unlinkability_prior` (for a random message, the transcript is
    independent of the PAIR (message, signature); since an honest signature is a function of
    key and message, this is `message_view_independent` with the signature attached), and
    `linkGame_true` (two sessions: a B that answers both HONESTLY with one key cannot match
    published signatures to sessions; this is the statement about linking proper).
    LIMITATION: `linkGame` only expresses replies of the form `ks i • a` with scalars fixed in
    advance (`linkGame_eq_linkGameReply`), and already inside that class unlinkability FAILS
    for a B that uses two different scalars (`output_eq_iff_reply_key`,
    `linkGame_tagging_true`, `linkGameReply_exists_win`).  So this file gives unlinkability
    against an honest-but-curious B only.  No positive statement about a B that replies
    arbitrarily, or about a party A that checks the reply, is made in this file.
  * Tightness and negative results, showing that hypotheses (i)–(iii) and the definitions are
    not decorative:
    - `blind_dist_eq_iff_exists_unit`: in ANY module, two messages are perfectly
      indistinguishable exactly when their hashes differ by a nonzero scalar.  What a session
      reveals to B is therefore exactly the line through `H m`, no more and no less.
    - (iii) `blind_dist_eq_iff`, `viewB_dist_eq_iff`: in a group of prime order this reads
      "`H m₀ = 0 ↔ H m₁ = 0`": B learns exactly whether the hash is the identity, and nothing
      else.  `blind_dist_ne_of_hash_zero`, `indGame_zero_hash_win` (and its mirror image
      `indGame_zero_hash_win'`): if one hash is the identity and the other is not, the two
      distributions differ and B wins the game with certainty.
    - (ii) `blind_dist_ne_rank_two`: in the rank-two module `F × F` the conclusion of
      `blind_dist_eq` is false although both hashes are non-identity.
    - (i), freshness: `blind_same_coin_eq_iff`, `blind_same_coin_smul_iff`,
      `reused_coin_dist_eq_iff`, `reused_coin_dist_ne`: a reused coin reveals the two hashes up
      to one common scalar.  Secrecy: `unblind_blind` (transcript and coin together give
      `H m`).  Distribution: `noBlind_dist_ne`, `noBlindGame_true`: the protocol without
      blinding, which is the protocol with the constant coin `1` (`noBlind_eq_blind_one`), is
      distinguished with certainty, in the same game.  (No statement is made about coin
      distributions between these two extremes.)
  * Non-vacuity.  `Blindness.Model`: all hypotheses are met in `F = G = ZMod 5`.

  What this file does NOT prove.  Nothing here concerns party A learning the key `k`, or
  unforgeability; those are computational statements and live elsewhere.  The privacy statements
  are about B's protocol view only: they assume (i)–(iii) above, and they say nothing about side
  channels or about information B obtains about `m` outside the protocol.  Hypothesis (ii) is a
  real restriction: the model is a vector space over the scalar field, so a group whose order
  has a cofactor is not covered at all (it is not even expressible here), and A must make sure
  that the element it blinds lies in the prime-order group.

  Housekeeping.  The lemmas of the section "General-purpose probability facts" are not specific
  to this protocol.  They live here, in the sub-namespace `Blindness`, so that this file depends
  on `Correctness.lean` and `Prob.lean` only; they are candidates for `Prob.lean`.
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
elements, not about distributions; the probabilistic consequences are below.  It needs the
group to have prime order (`hg`): in general two non-identity elements need not be scalar
multiples of each other. -/
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

/-- **Why coins must be fresh (negative result, pointwise form).**  If A reused the same coin
for two messages, the two blinded elements would coincide exactly when the two hashes coincide,
so B would learn whether the two sessions carry messages with the same hash (for a
collision-free hash: the same message).  This is only the most visible part of the leak: see
`blind_same_coin_smul_iff` (B learns the whole ratio of the two hashes) and
`reused_coin_dist_eq_iff` / `reused_coin_dist_ne` (the statement about distributions).  The
multi-session theorem `multi_blind_dist_eq` therefore really needs independent coins. -/
theorem blind_same_coin_eq_iff (H : M → G) (m m' : M) (r : Fˣ) :
    blind H m r = blind H m' r ↔ H m = H m' :=
  (smul_right_injective G r.ne_zero).eq_iff

/-- **A reused coin leaks the ratio of the two hashes (negative result, pointwise form).**  With
one coin `r` used for both `m` and `m'`, every linear relation `H m' = c • H m` between the two
hashes holds between the two blinded elements as well, and conversely.  So a B that sees both
blinded elements learns the scalar `c` relating the two hashes (it is a discrete logarithm of
one blinded element with respect to the other, which an unbounded B can compute), not merely
whether the hashes are equal (`c = 1`, `blind_same_coin_eq_iff`).  The coin cancels out. -/
theorem blind_same_coin_smul_iff (H : M → G) (m m' : M) (r : Fˣ) (c : F) :
    blind H m' r = c • blind H m r ↔ H m' = c • H m := by
  unfold blind
  rw [smul_comm c (r : F) (H m)]
  exact (smul_right_injective G r.ne_zero).eq_iff

/-- **Why the coin must stay secret (negative result).**  From the blinded element together
with the coin, the hash of the message is recovered exactly, by unblinding.  So every privacy
statement of this file is about a party B that does NOT learn `r`; once the coin of a session
leaks, the transcript of that session determines `H m`. -/
theorem unblind_blind (H : M → G) (m : M) (r : Fˣ) : unblind r (blind H m r) = H m :=
  unblind_smul r (H m)

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

/-- Post-processing by a function that can be undone loses no information: pushing forward
along a function with a left inverse is injective on distributions. -/
theorem map_injective_of_leftInverse {α β : Type*} {f : α → β} {f' : β → α}
    (h : Function.LeftInverse f' f) : Function.Injective (PMF.map f) := by
  intro p q hpq
  have hc : f' ∘ f = id := funext h
  have hmap := congrArg (PMF.map f') hpq
  rwa [PMF.map_comp, PMF.map_comp, hc, PMF.map_id, PMF.map_id] at hmap

end Blindness

open Blindness

/-! ## The indistinguishability game, for an arbitrary first message of party A -/

section Games

variable [Field F] [Fintype F] [DecidableEq F]

/-- The message-indistinguishability game against party B, stated once for ANY rule
`send : M → Fˣ → G` by which party A computes its single protocol message from its message and
its coin.  A hidden bit `b` is drawn uniformly; A sends `send m₁ r` if `b` is true and
`send m₀ r` otherwise, for a fresh uniform nonzero coin `r`; B's (randomized) guessing
procedure `D` is run on B's view (its key and what it received).  The game outputs `true`
exactly when the guess equals `b`.

The real protocol is the instance `send = blind H` (`indGame`, `indGame_eq_indGameWith`); the
strawman without blinding is the instance `send = noBlind H` (`noBlindGame`).  So the positive
result `indGame_true` and the negative result `noBlindGame_true` are about the same game. -/
noncomputable def indGameWith (send : M → Fˣ → G) (k : F) (m₀ m₁ : M) (D : F × G → PMF Bool) :
    PMF Bool :=
  (unif Bool).bind fun b => (unif Fˣ).bind fun r =>
    (D (k, send (if b then m₁ else m₀) r)).map fun b' => decide (b' = b)

/-- **Perfect hiding of the first message implies advantage exactly zero, for any protocol.**
If the first messages for `m₀` and for `m₁` have the same distribution, then the outcome of the
indistinguishability game is a fair coin, whatever the guessing strategy.  (Nothing here is
specific to the blinding step; the protocol-specific input is the hypothesis `h`, which is
`blind_dist_eq` for the real protocol and is false for the strawman, `noBlind_dist_ne`.) -/
theorem indGameWith_eq_unif (send : M → Fˣ → G) (k : F) {m₀ m₁ : M}
    (h : (unif Fˣ).map (send m₀) = (unif Fˣ).map (send m₁)) (D : F × G → PMF Bool) :
    indGameWith send k m₀ m₁ D = unif Bool := by
  have hc : ∀ m, (fun r => D (k, send m r)) = (fun a : G => D (k, a)) ∘ send m := fun m => rfl
  have key : ∀ b : Bool, ((unif Fˣ).bind fun r =>
      (D (k, send (if b then m₁ else m₀) r)).map fun b' => decide (b' = b)) =
      ((unif Fˣ).bind fun r => D (k, send m₀ r)).map fun b' => decide (b' = b) := by
    intro b
    have hb : ((unif Fˣ).bind fun r => D (k, send (if b then m₁ else m₀) r)) =
        (unif Fˣ).bind fun r => D (k, send m₀ r) := by
      cases b
      · rfl
      · change ((unif Fˣ).bind fun r => D (k, send m₁ r)) =
          (unif Fˣ).bind fun r => D (k, send m₀ r)
        rw [hc m₁, hc m₀, ← PMF.bind_map, ← PMF.bind_map, h]
    rw [← hb, PMF.map_bind]
  unfold indGameWith
  simp only [key]
  exact guess_independent_bit _

/-- **A separating test wins the game with certainty, for any protocol.**  If a deterministic
test `d` on B's view always answers `false` on a first message for `m₀` and always answers
`true` on a first message for `m₁`, then the strategy "output `d`" wins the indistinguishability
game with probability ONE.  This is the opposite extreme of `indGameWith_eq_unif`, and it is
what happens for the strawman without blinding (`noBlindGame_true`) and for the real protocol
when exactly one hash is the identity (`indGame_zero_hash_win`).  So the game is not one that
every strategy loses. -/
theorem indGameWith_win (send : M → Fˣ → G) (k : F) (m₀ m₁ : M) (d : F × G → Bool)
    (h₀ : ∀ r, d (k, send m₀ r) = false) (h₁ : ∀ r, d (k, send m₁ r) = true) :
    indGameWith send k m₀ m₁ (fun v => PMF.pure (d v)) true = 1 := by
  have key : ∀ b : Bool, ((unif Fˣ).bind fun r =>
      (PMF.pure (d (k, send (if b then m₁ else m₀) r))).map fun b' => decide (b' = b)) =
      PMF.pure true := by
    intro b
    cases b <;> simp [PMF.pure_map, h₀, h₁]
  unfold indGameWith
  simp only [key]
  simp

end Games

/-! ## One session: B's view is independent of the message -/

section Privacy

variable [Field F] [Fintype F] [DecidableEq F] [AddCommGroup G] [Module F G] {g : G}

/-- Multiplying two non-identity points by a uniform nonzero scalar gives the same
distribution (in a group of prime order). -/
theorem Blindness.smul_dist_eq (hg : IsGenerator F g) {P Q : G} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    (unif Fˣ).map (fun r : Fˣ => (r : F) • P) = (unif Fˣ).map (fun r : Fˣ => (r : F) • Q) := by
  obtain ⟨u, hu⟩ := smul_eq_mul_smul hg hP hQ
  exact (unif_map_eq_of_equiv (Equiv.mulRight u) (fun r : Fˣ => (r : F) • Q)
    (fun r : Fˣ => (r : F) • P) (fun r => (hu r).symm)).symm

/-- The exact criterion, valid in EVERY module over the scalar field (no generator is assumed):
multiplying `P` and multiplying `Q` by a uniform nonzero scalar give the same distribution if
and only if `Q` is a nonzero scalar multiple of `P`. -/
theorem Blindness.smul_dist_eq_iff {P Q : G} :
    (unif Fˣ).map (fun r : Fˣ => (r : F) • P) = (unif Fˣ).map (fun r : Fˣ => (r : F) • Q) ↔
      ∃ u : Fˣ, Q = (u : F) • P := by
  constructor
  · intro h
    have hmem : Q ∈ ((unif Fˣ).map (fun r : Fˣ => (r : F) • Q)).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨1, mem_support_unif _, by simp⟩
    rw [← h] at hmem
    obtain ⟨u, -, hu⟩ := (PMF.mem_support_map_iff _ _ _).mp hmem
    exact ⟨u, hu.symm⟩
  · rintro ⟨u, rfl⟩
    exact (unif_map_eq_of_equiv (Equiv.mulRight u) (fun r : Fˣ => (r : F) • (u : F) • P)
      (fun r : Fˣ => (r : F) • P) (fun r => by simp [mul_smul])).symm

/-- **Perfect blindness of the first message.**  With a uniformly random nonzero coin, the group
element A sends has exactly the same distribution whichever of two messages (with non-identity
hashes) A holds.  This is an equality of distributions, not a computational approximation: it
holds for every hash function `H`, with no assumption on the hardness of any problem.

Hypotheses that matter, and what the theorem does NOT say.
* The group must have prime order (`hg : IsGenerator F g`, i.e. `G` is one-dimensional over
  `F`).  In a module of higher rank the conclusion is FALSE even when both hashes are
  non-identity (`blind_dist_ne_rank_two`); the criterion valid in every module is
  `blind_dist_eq_iff_exists_unit`.  A group whose order has a cofactor is not a module over
  the scalar field at all, so the theorem makes no claim about it (see the file header).
* It says nothing when a hash is the identity.  If exactly one of the two hashes is the
  identity the conclusion is false (`blind_dist_ne_of_hash_zero`); the exact statement for
  arbitrary hashes is `blind_dist_eq_iff`.
* The coin must be uniform on the nonzero scalars and used once (`reused_coin_dist_ne`). -/
theorem blind_dist_eq (hg : IsGenerator F g) (H : M → G) {m₀ m₁ : M}
    (h₀ : H m₀ ≠ 0) (h₁ : H m₁ ≠ 0) :
    (unif Fˣ).map (blind H m₀) = (unif Fˣ).map (blind H m₁) :=
  smul_dist_eq hg h₀ h₁

/-- **What exactly a session reveals, in any module.**  With NO assumption on the group beyond
being a module over the scalar field, and no assumption on the hashes: the first messages for
`m₀` and for `m₁` have the same distribution if and only if the two hashes differ by a nonzero
scalar.  So the blinded element reveals precisely the line through `H m` (the set of nonzero
multiples of `H m`), no more and no less.  In a group of prime order there are only two such
classes, the identity and everything else, which gives `blind_dist_eq_iff`. -/
theorem blind_dist_eq_iff_exists_unit (H : M → G) (m₀ m₁ : M) :
    (unif Fˣ).map (blind H m₀) = (unif Fˣ).map (blind H m₁) ↔
      ∃ u : Fˣ, H m₁ = (u : F) • H m₀ :=
  smul_dist_eq_iff

/-- **B's whole view is independent of the message.**  For every key `k` (honestly generated or
not), the pair (key, received element) that constitutes everything party B sees in a session
has the same distribution for any two messages with non-identity hashes.  Since B receives this
single element before sending anything, the statement covers a malicious B as well.
It does NOT cover information about `m` that B obtains outside the session, and it needs the
same hypotheses as `blind_dist_eq`: a group of prime order (`hg`), non-identity hashes, and a
fresh uniform nonzero coin.  The exact statement is `viewB_dist_eq_iff`. -/
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
outputs `true` exactly when the guess equals `b`.  It is the instance of the generic game
`indGameWith` for the real first message `blind H` (`indGame_eq_indGameWith`). -/
noncomputable def indGame (H : M → G) (k : F) (m₀ m₁ : M) (D : F × G → PMF Bool) : PMF Bool :=
  (unif Bool).bind fun b => (unif Fˣ).bind fun r =>
    (D (viewB H k (if b then m₁ else m₀) r)).map fun b' => decide (b' = b)

/-- `indGame` is, by definition, the generic game `indGameWith` played with the protocol's
blinding step as A's first message. -/
theorem indGame_eq_indGameWith (H : M → G) (k : F) (m₀ m₁ : M) (D : F × G → PMF Bool) :
    indGame H k m₀ m₁ D = indGameWith (blind H) k m₀ m₁ D := rfl

/-- The outcome of the indistinguishability game is a fair coin, for every guessing strategy. -/
theorem indGame_eq_unif (hg : IsGenerator F g) (H : M → G) (k : F) {m₀ m₁ : M}
    (h₀ : H m₀ ≠ 0) (h₁ : H m₁ ≠ 0) (D : F × G → PMF Bool) :
    indGame H k m₀ m₁ D = unif Bool := by
  rw [indGame_eq_indGameWith]
  exact indGameWith_eq_unif (blind H) k (blind_dist_eq hg H h₀ h₁) D

/-- **Advantage exactly zero.**  In the indistinguishability game party B guesses which of the
two messages was submitted with probability exactly one half, i.e. no better than by ignoring
the session altogether.  This holds for EVERY key `k`, EVERY pair of messages `m₀`, `m₁` with
non-identity hashes (all universally quantified, so B may choose the pair itself, knowing its
key; see `indGameAdaptive_true` for a pair chosen by a randomized first stage), and EVERY
randomized, computationally unbounded guessing strategy `D`.
It does NOT say that B is ignorant of the message in an absolute sense: B may know a lot about
it from elsewhere (in this game it even knows both candidates).  The theorem says that the
session adds nothing to that knowledge.  It needs a group of prime order (`hg`) and
non-identity hashes: if exactly one of the two hashes is the identity, B wins the same game
with certainty (`indGame_zero_hash_win`, `indGame_zero_hash_win'`). -/
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
It does NOT cover coin reuse (`reused_coin_dist_ne`: with one coin for two sessions the
corresponding statement is false), and the message vectors are fixed in advance: a party A that
chooses later messages as a function of B's earlier replies is not modelled here. -/
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

/-! ## Transcript and signature -/

/-- How much the joint statement `unlinkability` says: for ANY hash, key and pair of messages
(no hypothesis at all), the equation of `unlinkability` is equivalent to the equation of
`blind_dist_eq`.  The reason is `correctness`: for a fixed key and message the signature A
obtains from an honest B is the constant `prf H k m`, whatever the coin, so pairing the
transcript with it adds a point mass and nothing else. -/
theorem unlinkability_iff (H : M → G) (k : F) (m m' : M) :
    (unif Fˣ).map (fun r => (blind H m r, run H k m r)) =
        (unif Fˣ).map (fun r => (blind H m' r, prf H k m)) ↔
      (unif Fˣ).map (blind H m) = (unif Fˣ).map (blind H m') := by
  have h1 : (fun r : Fˣ => (blind H m r, run H k m r)) =
      (fun a : G => (a, prf H k m)) ∘ blind H m := by
    funext r
    simp [correctness]
  have h2 : (fun r : Fˣ => (blind H m' r, prf H k m)) =
      (fun a : G => (a, prf H k m)) ∘ blind H m' := rfl
  rw [h1, h2, ← PMF.map_comp, ← PMF.map_comp]
  exact (map_injective_of_leftInverse (f' := Prod.fst) fun _ => rfl).eq_iff

/-- **Transcript and output of one honest session (joint distribution).**  Consider a session on
message `m` in which B answers honestly with its key `k`.  The pair (what B saw, the signature
A walks away with) is distributed exactly like (what B would have seen in a session on a
different message `m'`, the fixed value `prf H k m`).  So B's record of the session is equally
consistent with any other message, also when it is considered together with A's output.

How much this says, and what it does NOT say.
* For a fixed key and message the signature is a deterministic function of `(k, m)`
  (`correctness`), so "independent of the signature" here means independent of a constant: the
  statement is a restatement of `blind_dist_eq` for an honest reply, and is in fact equivalent
  to it (`unlinkability_iff`).
* It concerns ONE session on a FIXED message, so by itself it is not a statement about linking
  published signatures to sessions.  With a random message, the transcript is independent of
  the pair (message, signature): `unlinkability_prior`.  The linking claim proper (two
  sessions, B later sees both signatures) is `linkGame_true`.
* It does NOT cover a B that deviates in its reply: see `output_eq_iff_reply_key` and
  `linkGame_tagging_true` for the key-tagging attack that defeats unlinkability of the output
  when A has no way to verify B's reply. -/
theorem unlinkability (hg : IsGenerator F g) (H : M → G) (k : F) {m m' : M}
    (hm : H m ≠ 0) (hm' : H m' ≠ 0) :
    (unif Fˣ).map (fun r => (blind H m r, run H k m r)) =
      (unif Fˣ).map (fun r => (blind H m' r, prf H k m)) :=
  (unlinkability_iff H k m m').mpr (blind_dist_eq hg H hm hm')

/-- **The transcript is independent of the pair (message, signature), for any prior.**  Let the
message be drawn from ANY prior distribution `μ` (supported on messages with non-identity hash)
and let one session be run with a B that answers honestly with key `k`.  Then the triple
(what B saw, the message, the signature A obtains) is distributed as: the pair
(message, signature) as before, together with a transcript drawn INDEPENDENTLY from the fixed
distribution of `r • g`, which involves neither the message nor the hash nor the key.  So when
the pair `(m, σ)` is published later, the transcript B recorded is exactly as likely under
every published pair: it carries no information about which pair the session produced.
It contains `unlinkability` as the case of point-mass priors (apply it at `m` and at `m'` and
compare), and adds to it the message as a random variable and a comparison distribution that
involves no message at all.

How much this says, and what it does NOT say.
* The signature of an honest session is a function of `(k, m)` (`correctness`), so the pair
  (message, signature) carries exactly the information of the message.  The statement is
  therefore the Shannon-secrecy theorem `message_view_independent` with the signature attached
  to the message; it is phrased separately because "transcript against published pair" is the
  form in which the question is usually asked.
* It does NOT cover a B that deviates in its reply (see `linkGame_tagging_true`), and it is
  about a single session; for two sessions see `linkGame_true`. -/
theorem unlinkability_prior (hg : IsGenerator F g) (H : M → G) (k : F) (μ : PMF M)
    (hμ : ∀ m ∈ μ.support, H m ≠ 0) :
    (μ.bind fun m => (unif Fˣ).map fun r => (blind H m r, m, run H k m r)) =
      μ.bind fun m =>
        ((unif Fˣ).map fun r : Fˣ => (r : F) • g).map fun a => (a, m, prf H k m) := by
  refine bind_congr_of_support _ _ _ fun m hm => ?_
  have h1 : (fun r : Fˣ => (blind H m r, m, run H k m r)) =
      (fun a : G => (a, m, prf H k m)) ∘ fun r : Fˣ => (r : F) • H m := by
    funext r
    simp [correctness, blind]
  rw [h1, ← PMF.map_comp, smul_dist_eq hg (hμ m hm) hg.ne_zero]

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

/-- The two-session linking game, RESTRICTED to a party B whose reply in session `i` is
`ks i • a` (`a` the element it received in that session) for scalars `ks` fixed before the
coins are drawn; an honest B uses its one key in both sessions.  Two sessions are run, on `m₀`
and `m₁`, in an order determined by a hidden uniform bit `b`.  B's procedure `D` (which may
depend on the scalars and on the two messages) receives the two first messages in session
order, and then the two signatures in MESSAGE order (first the one on `m₀`, then the one on
`m₁`, as they would appear once published).  The game outputs `true` when `D` guesses `b`,
i.e. when B correctly matches sessions to signatures.

This is NOT the full blindness game for blind signatures.  There the signer may compute each
reply as an arbitrary function of everything it has seen, and A releases its outputs only if
they pass a check.  Here the reply rule is hard-wired to scalar multiplication and nothing is
checked.  The game with arbitrary replies is `linkGameReply`, of which this one is a special
case (`linkGame_eq_linkGameReply`); no positive statement about arbitrary replies is proven in
this file (a B that deviates, against an A that checks the reply, is the subject of the
separate file `Unlinkability.lean` of this development, on which nothing here depends). -/
noncomputable def linkGame (H : M → G) (ks : Bool → F) (m₀ m₁ : M)
    (D : (Bool → G) × (Bool → G) → PMF Bool) : PMF Bool :=
  (unif Bool).bind fun b => (unif (Bool → Fˣ)).bind fun rs =>
    (D (fun i => blind H (sessionMsg m₀ m₁ b i) (rs i),
      fun j => sessionOut H ks m₀ m₁ b rs (xor j b))).map fun b' => decide (b' = b)

variable (F) in
/-- The two-session linking game for a party B with an ARBITRARY deterministic reply rule:
`reply i a` is what B sends back in session `i` when the two first messages (in session order)
are `a`, so each reply may depend on both sessions, as for concurrent sessions.  A unblinds
whatever it receives and performs no check.  Everything else is as in `linkGame`.  (The scalar
field `F` is an explicit argument because it cannot be read off the other arguments.)

This definition is here to make precise what `linkGame` leaves out.  No unlinkability theorem
holds for it in general: there are a reply rule and a guessing procedure that win it with
certainty (`linkGameReply_exists_win`). -/
noncomputable def linkGameReply (H : M → G) (reply : Bool → (Bool → G) → G) (m₀ m₁ : M)
    (D : (Bool → G) × (Bool → G) → PMF Bool) : PMF Bool :=
  (unif Bool).bind fun b => (unif (Bool → Fˣ)).bind fun rs =>
    (D (fun i => blind H (sessionMsg m₀ m₁ b i) (rs i),
      fun j => unblind (rs (xor j b)) (reply (xor j b)
        fun i => blind H (sessionMsg m₀ m₁ b i) (rs i)))).map fun b' => decide (b' = b)

/-- `linkGame` is, by definition, the game `linkGameReply` for the reply rule "multiply what
you received in session `i` by the scalar `ks i`".  So the theorems about `linkGame` quantify
over the scalars `ks` only, not over all the ways in which B could answer. -/
theorem linkGame_eq_linkGameReply (H : M → G) (ks : Bool → F) (m₀ m₁ : M)
    (D : (Bool → G) × (Bool → G) → PMF Bool) :
    linkGame H ks m₀ m₁ D = linkGameReply F H (fun i a => evaluate (ks i) (a i)) m₀ m₁ D := rfl

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

/-- **Unlinkability against an honest-but-curious B, as a game with advantage exactly zero.**
A party B that answers both sessions honestly, with the same key `k`, and later sees both
published signatures, matches sessions to signatures with probability exactly one half,
whatever (randomized, unbounded) procedure it uses to guess and whichever two messages (with
non-identity hashes) are involved.
It does NOT cover a B that deviates when it replies.  A B that answers the two sessions with
different scalars wins the same game with certainty (`linkGame_tagging_true`), and replies that
are not scalar multiples of what B received are not even expressible in `linkGame` (see
`linkGameReply`).  So this is not blindness against a malicious signer; that needs A to check
B's reply, which is outside this file. -/
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

/-- **Without a check by A, the linking game with arbitrary replies can be won with certainty
(negative result over the full reply space).**  For every hash and every pair of messages with
`H m₀ ≠ 0` there exist a reply rule for B and a guessing procedure that win `linkGameReply` with
probability ONE.  (The witness is the tagging signer of `linkGame_tagging_true` with the two
scalars `0` and `1`, which are different in every field.)  Hence no theorem of the form "every
reply rule and every guessing procedure win with probability one half" can hold for the bare
protocol: some restriction on B's replies (the honest replies of `linkGame_true`, or a check by
A, which this file does not model) is necessary, not a convenience.
It does NOT say which other reply rules help B, nor by how much; only that some rule wins. -/
theorem linkGameReply_exists_win (H : M → G) {m₀ : M} (m₁ : M) (h₀ : H m₀ ≠ 0) :
    ∃ (reply : Bool → (Bool → G) → G) (D : (Bool → G) × (Bool → G) → PMF Bool),
      linkGameReply F H reply m₀ m₁ D true = 1 := by
  classical
  let ks : Bool → F := fun i => if i then 1 else 0
  have hks : ks false ≠ ks true := by simp [ks]
  refine ⟨fun i a => evaluate (ks i) (a i),
    fun v => PMF.pure (decide (v.2 false = prf H (ks true) m₀)), ?_⟩
  rw [← linkGame_eq_linkGameReply]
  exact linkGame_tagging_true H ks hks m₁ h₀

/-! ## Tightness and negative results: the hypotheses and the definitions have teeth -/

/-- **The non-identity condition cannot be dropped (negative result).**  If one message hashes
to the identity and the other does not, the two first-message distributions are DIFFERENT: the
first is concentrated on the identity, the second never produces it.  So the hypothesis
`H m ≠ 0` in the privacy theorems cannot be dropped; a deployment must make sure the hash never
outputs the identity (or accept that B learns whether it did).  When BOTH hashes are the
identity the two distributions coincide again; the exact condition is `blind_dist_eq_iff`. -/
theorem blind_dist_ne_of_hash_zero (H : M → G) {m₀ m₁ : M} (h₀ : H m₀ = 0) (h₁ : H m₁ ≠ 0) :
    (unif Fˣ).map (blind H m₀) ≠ (unif Fˣ).map (blind H m₁) := by
  intro h
  have hmem : (0 : G) ∈ ((unif Fˣ).map (blind H m₀)).support :=
    (PMF.mem_support_map_iff _ _ _).mpr
      ⟨1, mem_support_unif _, (blind_eq_zero_iff H m₀ 1).mpr h₀⟩
  rw [h] at hmem
  obtain ⟨r, -, hr⟩ := (PMF.mem_support_map_iff _ _ _).mp hmem
  exact blind_ne_zero H h₁ r hr

/-- **Exactly what B learns in a group of prime order.**  For ANY two messages (no hypothesis on
their hashes), the first messages for `m₀` and for `m₁` have the same distribution if and only
if either both hashes are the identity or neither is.  So the one bit "is `H m` the identity?"
is revealed to B (`blind_eq_zero_iff`), and it is the ONLY thing revealed: the positive theorem
`blind_dist_eq` and the negative theorem `blind_dist_ne_of_hash_zero` are the two halves of
this equivalence, and neither can be improved. -/
theorem blind_dist_eq_iff (hg : IsGenerator F g) (H : M → G) (m₀ m₁ : M) :
    (unif Fˣ).map (blind H m₀) = (unif Fˣ).map (blind H m₁) ↔ (H m₀ = 0 ↔ H m₁ = 0) := by
  constructor
  · intro h
    constructor
    · intro h0
      by_contra h1
      exact blind_dist_ne_of_hash_zero H h0 h1 h
    · intro h1
      by_contra h0
      exact blind_dist_ne_of_hash_zero H h1 h0 h.symm
  · intro h
    by_cases h0 : H m₀ = 0
    · have h1 := h.mp h0
      have : (blind H m₀ : Fˣ → G) = blind H m₁ := by
        funext r
        simp [blind, h0, h1]
      rw [this]
    · exact blind_dist_eq hg H h0 (fun h1 => h0 (h.mpr h1))

/-- The same exact statement for B's whole view (key and received element), for every key. -/
theorem viewB_dist_eq_iff (hg : IsGenerator F g) (H : M → G) (k : F) (m₀ m₁ : M) :
    (unif Fˣ).map (viewB H k m₀) = (unif Fˣ).map (viewB H k m₁) ↔ (H m₀ = 0 ↔ H m₁ = 0) := by
  rw [← blind_dist_eq_iff hg H m₀ m₁]
  have hv : ∀ m, viewB H k m = (fun a : G => (k, a)) ∘ blind H m := fun m => rfl
  rw [hv m₀, hv m₁, ← PMF.map_comp, ← PMF.map_comp]
  exact (map_injective_of_leftInverse (f' := Prod.snd) fun _ => rfl).eq_iff

/-- **The game is lost by A when exactly one hash is the identity (negative result).**  In the
real game `indGame`, if `H m₀ = 0` and `H m₁ ≠ 0`, the strategy "guess `m₁` exactly when the
received element is not the identity" wins with probability ONE.  So `indGame` is not a game
that every strategy loses, and the hypothesis `H m ≠ 0` of `indGame_true` is necessary. -/
theorem indGame_zero_hash_win [DecidableEq G] (H : M → G) (k : F) {m₀ m₁ : M}
    (h₀ : H m₀ = 0) (h₁ : H m₁ ≠ 0) :
    indGame H k m₀ m₁ (fun v => PMF.pure (decide (v.2 ≠ 0))) true = 1 :=
  indGameWith_win (blind H) k m₀ m₁ (fun v => decide (v.2 ≠ 0))
    (fun r => by simp [blind_eq_zero_iff, h₀]) (fun r => by simp [blind_eq_zero_iff, h₁])

/-- The mirror image of `indGame_zero_hash_win`: if `H m₀ ≠ 0` and `H m₁ = 0`, the strategy
"guess `m₁` exactly when the received element is the identity" wins `indGame` with probability
ONE.  Together the two statements cover every pair of messages of which exactly one hashes to
the identity. -/
theorem indGame_zero_hash_win' [DecidableEq G] (H : M → G) (k : F) {m₀ m₁ : M}
    (h₀ : H m₀ ≠ 0) (h₁ : H m₁ = 0) :
    indGame H k m₀ m₁ (fun v => PMF.pure (decide (v.2 = 0))) true = 1 :=
  indGameWith_win (blind H) k m₀ m₁ (fun v => decide (v.2 = 0))
    (fun r => by simp [blind_eq_zero_iff, h₀]) (fun r => by simp [blind_eq_zero_iff, h₁])

/-- **The prime-order hypothesis cannot be dropped (negative result).**  Take for `G` the
rank-two module `F × F` (a non-cyclic group) and the two-message hash with values `(1, 0)` and
`(0, 1)`.  Both hashes are non-identity, so hypothesis `H m ≠ 0` of `blind_dist_eq` holds, and
yet the two first-message distributions are DIFFERENT: multiplying by a scalar never leaves the
line through the point.  The only hypothesis of `blind_dist_eq` that fails here is
`IsGenerator`.  So perfect message privacy really uses that the group has prime order; in
general B learns the line through `H m` (`blind_dist_eq_iff_exists_unit`).
It is NOT a model of an elliptic curve with a cofactor (such a group is not a module over the
scalar field and is outside this development); it is the nearest failure the model can state. -/
theorem blind_dist_ne_rank_two :
    ∃ H : Bool → F × F, H false ≠ 0 ∧ H true ≠ 0 ∧
      (unif Fˣ).map (blind H false) ≠ (unif Fˣ).map (blind H true) := by
  refine ⟨fun b => if b then (0, 1) else (1, 0), by simp, by simp, fun h => ?_⟩
  obtain ⟨u, hu⟩ := (blind_dist_eq_iff_exists_unit _ false true).mp h
  simp at hu

/-- **What a reused coin reveals, exactly (negative result).**  Suppose A uses ONE coin for two
sessions.  Then two pairs of messages `(m₀, m₀')` and `(m₁, m₁')` give B the same distribution
of (first message of session 1, first message of session 2) if and only if the two pairs of
hashes differ by one COMMON nonzero scalar.  So B learns the pair of hashes up to a common
scalar, in particular the scalar relating the two hashes of a pair, whereas with independent
coins it learns nothing (`multi_blind_dist_eq`).  No hypothesis on the group or on the hashes
is needed. -/
theorem reused_coin_dist_eq_iff (H : M → G) (m₀ m₀' m₁ m₁' : M) :
    (unif Fˣ).map (fun r => (blind H m₀ r, blind H m₀' r)) =
        (unif Fˣ).map (fun r => (blind H m₁ r, blind H m₁' r)) ↔
      ∃ u : Fˣ, H m₁ = (u : F) • H m₀ ∧ H m₁' = (u : F) • H m₀' := by
  have h := smul_dist_eq_iff (F := F) (P := (H m₀, H m₀')) (Q := (H m₁, H m₁'))
  simp only [Prod.smul_mk, Prod.mk.injEq] at h
  exact h

/-- **Coins must not be reused (negative result).**  If A used the same coin for two sessions,
then "the same message twice" and "two messages with different hashes" would give B DIFFERENT
distributions: B could tell whether two sessions carry the same message.  Contrast with
`multi_blind_dist_eq`, where the coins are independent and the two distributions coincide. -/
theorem reused_coin_dist_ne (H : M → G) {m m' : M} (h : H m ≠ H m') :
    (unif Fˣ).map (fun r => (blind H m r, blind H m r)) ≠
      (unif Fˣ).map (fun r => (blind H m r, blind H m' r)) := by
  intro heq
  obtain ⟨u, hu, hu'⟩ := (reused_coin_dist_eq_iff H m m m m').mp heq
  exact h (hu.trans hu'.symm)

end Privacy

section Strawman

variable [Field F] [Fintype F] [DecidableEq F]

/-- The strawman protocol without blinding: A ignores its coin and sends `H m` itself. -/
def noBlind (H : M → G) (m : M) (_r : Fˣ) : G := H m

omit [Fintype F] [DecidableEq F] in
/-- The strawman is the real protocol run with the constant coin `1` instead of a uniform one.
So the negative results below (`noBlind_dist_ne`, `noBlindGame_true`) also show, in the most
extreme case, that the privacy theorems depend on how the coin is distributed. -/
theorem noBlind_eq_blind_one [AddCommGroup G] [Module F G] (H : M → G) (m : M) (r : Fˣ) :
    noBlind H m r = blind H m (1 : Fˣ) := by
  simp [noBlind, blind]

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

/-- The indistinguishability game played against the strawman protocol.  It is literally the
same game as `indGame`: both are the generic `indGameWith`, here with A's first message
`noBlind H` in place of `blind H` (compare `indGame_eq_indGameWith`). -/
noncomputable def noBlindGame (H : M → G) (k : F) (m₀ m₁ : M) (D : F × G → PMF Bool) :
    PMF Bool :=
  indGameWith (noBlind H) k m₀ m₁ D

/-- **The game is winnable when there is no blinding (negative result).**  Against the strawman
protocol, the obvious strategy "compare what you received with `H m₁`" wins the
indistinguishability game with probability ONE whenever the two hashes differ, in contrast with
the probability one half of `indGame_true`.  So the game really measures message privacy. -/
theorem noBlindGame_true [DecidableEq G] (H : M → G) (k : F) {m₀ m₁ : M} (h : H m₀ ≠ H m₁) :
    noBlindGame H k m₀ m₁ (fun v => PMF.pure (decide (v.2 = H m₁))) true = 1 :=
  indGameWith_win (noBlind H) k m₀ m₁ (fun v => decide (v.2 = H m₁))
    (fun r => by simp [noBlind, h]) (fun r => by simp [noBlind])

end Strawman

/-! ## Non-vacuity: a concrete model in which every hypothesis holds

The scalars and the group are both `ZMod 5`, with generator `1`; there are three messages.
This is a group in which discrete logarithms are trivial, so the model says nothing about
security; its only role is to show that the hypotheses of the theorems above can all be met at
once, with messages whose hashes are pairwise different. -/

namespace Blindness.Model

local instance fact5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- In `ZMod 5`, as a module over itself, the element `1` is a generator. -/
theorem isGenerator_one : IsGenerator (ZMod 5) (1 : ZMod 5) :=
  ⟨one_ne_zero, fun x => ⟨x, mul_one x⟩⟩

/-- A hash on three messages with values `1, 2, 3`: pairwise different, never the identity. -/
def hash : Fin 3 → ZMod 5 := ![1, 2, 3]

/-- No message of the model hashes to the identity. -/
theorem hash_ne_zero : ∀ m, hash m ≠ 0 := by decide

/-- A hash on three messages that sends message `0` to the identity. -/
def zeroHash : Fin 3 → ZMod 5 := ![0, 2, 3]

/-- Two scalars with which a tagging signer answers the two sessions of the linking game. -/
def tagKeys : Bool → ZMod 5 := fun i => if i then 2 else 1

/-- Item 1: the two messages `0`, `1` have different, non-identity hashes. -/
example : ∃ u : (ZMod 5)ˣ, ∀ r : (ZMod 5)ˣ, blind hash 1 r = blind hash 0 (r * u) :=
  blind_eq_blind_mul isGenerator_one hash (hash_ne_zero 0) (hash_ne_zero 1)

/-- Items 2 and 3. -/
example (k : ZMod 5) :
    (unif (ZMod 5)ˣ).map (viewB hash k 0) = (unif (ZMod 5)ˣ).map (viewB hash k 2) :=
  viewB_dist_eq isGenerator_one hash k (hash_ne_zero 0) (hash_ne_zero 2)

/-- Item 4: each non-identity element is sent with probability exactly one quarter. -/
example : (unif (ZMod 5)ˣ).map (blind hash 1) 4 = 4⁻¹ := by
  have hcard : Fintype.card (ZMod 5)ˣ = 4 := by decide
  rw [blind_dist_apply isGenerator_one hash (hash_ne_zero 1) (by decide), hcard]
  norm_num

/-- Item 4, subtype form. -/
example : (unif (ZMod 5)ˣ).map (blindEquiv isGenerator_one hash (hash_ne_zero 1)) =
    @unif {x : ZMod 5 // x ≠ 0} _ ⟨⟨hash 1, hash_ne_zero 1⟩⟩ :=
  blind_uniform_nonzero isGenerator_one hash (hash_ne_zero 1)

/-- Shannon secrecy and the prior form of unlinkability, for the uniform prior. -/
example (k : ZMod 5) :
    ((unif (Fin 3)).bind fun m => (unif (ZMod 5)ˣ).map fun r => (m, viewB hash k m r)) =
      (unif (Fin 3)).bind fun m => (simB (1 : ZMod 5) k).map fun v => (m, v) :=
  message_view_independent isGenerator_one hash k (unif (Fin 3)) (fun m _ => hash_ne_zero m)

example (k : ZMod 5) :
    ((unif (Fin 3)).bind fun m =>
        (unif (ZMod 5)ˣ).map fun r => (blind hash m r, m, run hash k m r)) =
      (unif (Fin 3)).bind fun m =>
        ((unif (ZMod 5)ˣ).map fun r : (ZMod 5)ˣ => (r : ZMod 5) • (1 : ZMod 5)).map
          fun a => (a, m, prf hash k m) :=
  unlinkability_prior isGenerator_one hash k (unif (Fin 3)) (fun m _ => hash_ne_zero m)

/-- Items 5 and 6. -/
example (k : ZMod 5) (D : ZMod 5 × ZMod 5 → PMF Bool) : indGame hash k 0 1 D true = 1 / 2 :=
  indGame_true isGenerator_one hash k (hash_ne_zero 0) (hash_ne_zero 1) D

/-- Item 6 with the pair chosen by B, here by a genuinely randomized first stage. -/
example (k : ZMod 5) (D : Fin 3 → ZMod 5 × ZMod 5 → PMF Bool) :
    indGameAdaptive hash k (fun _ => (unif (Fin 3 × Fin 3)).map fun p => (p.1, p.2, p.1)) D true
      = 1 / 2 :=
  indGameAdaptive_true isGenerator_one hash k _ D (fun _ _ => ⟨hash_ne_zero _, hash_ne_zero _⟩)

/-- Item 7: two sessions on the same message against two sessions on different messages. -/
example :
    (unif (Fin 2 → (ZMod 5)ˣ)).map
        (fun rs i => blind hash ((![0, 0] : Fin 2 → Fin 3) i) (rs i)) =
      (unif (Fin 2 → (ZMod 5)ˣ)).map
        (fun rs i => blind hash ((![0, 1] : Fin 2 → Fin 3) i) (rs i)) :=
  multi_blind_dist_eq isGenerator_one hash ![0, 0] ![0, 1] (fun _ => hash_ne_zero _)
    (fun _ => hash_ne_zero _)

/-- Item 8 and the linking game against an honest-but-curious B. -/
example (k : ZMod 5) :
    (unif (ZMod 5)ˣ).map (fun r => (blind hash 0 r, run hash k 0 r)) =
      (unif (ZMod 5)ˣ).map (fun r => (blind hash 2 r, prf hash k 0)) :=
  unlinkability isGenerator_one hash k (hash_ne_zero 0) (hash_ne_zero 2)

example (k : ZMod 5) (D : (Bool → ZMod 5) × (Bool → ZMod 5) → PMF Bool) :
    linkGame hash (fun _ => k) 0 1 D true = 1 / 2 :=
  linkGame_true isGenerator_one hash k (hash_ne_zero 0) (hash_ne_zero 1) D

/-- The tagging attack: with the two scalars `1` and `2` the linking game is won. -/
example : linkGame hash tagKeys 0 1
    (fun v => PMF.pure (decide (v.2 false = prf hash (tagKeys true) 0))) true = 1 :=
  linkGame_tagging_true hash tagKeys (by decide) 1 (hash_ne_zero 0)

/-- Item 9: a hash that hits the identity is detected, in distribution and in the game. -/
example : (unif (ZMod 5)ˣ).map (blind zeroHash 0) ≠ (unif (ZMod 5)ˣ).map (blind zeroHash 1) :=
  blind_dist_ne_of_hash_zero zeroHash (by decide) (by decide)

example (k : ZMod 5) :
    indGame zeroHash k 0 1 (fun v => PMF.pure (decide (v.2 ≠ 0))) true = 1 :=
  indGame_zero_hash_win zeroHash k (by decide) (by decide)

/-- Item 10: without blinding, the messages `0` and `1` are told apart with certainty. -/
example (k : ZMod 5) :
    noBlindGame hash k 0 1 (fun v => PMF.pure (decide (v.2 = hash 1))) true = 1 :=
  noBlindGame_true hash k (by decide)

/-- Coin reuse: "message `0` twice" against "message `0`, then message `1`". -/
example :
    (unif (ZMod 5)ˣ).map (fun r => (blind hash 0 r, blind hash 0 r)) ≠
      (unif (ZMod 5)ˣ).map (fun r => (blind hash 0 r, blind hash 1 r)) :=
  reused_coin_dist_ne hash (by decide)

end Blindness.Model

end BlindPRF
