/-
  BlindPRF/DLEQ.lean — making party B ACCOUNTABLE without a pairing: the Chaum–Pedersen proof of
  discrete-logarithm equality (the "V" in VOPRF, RFC 9497).

  Problem.  In the bare protocol of `Basic.lean` party A has no way to tell whether B's reply `b`
  really is `k • a` for B's long-term key `k`.  A malicious B could answer under a different key
  for every client (to tag and later recognise clients), or simply return garbage.

  Fix.  B publishes `pk = k • g` once, for a fixed public group element `g ≠ 0`.  After replying
  `b` to A's blinded element `a`, B proves that the SAME scalar `k` links `(g, pk)` and `(a, b)`,
  i.e. `pk = k • g` and `b = k • a`, without revealing `k`:

      B (knows k)                                    A (knows g, pk, a, b)
      ---------------------------------------------------------------------
      t ← F uniformly
      T := (t • g, t • a)          ── T ──▶
                                   ◀── c ──           c ← F uniformly
      s := t + c * k               ── s ──▶
                                                      accept iff  s • g = T.1 + c • pk
                                                             and  s • a = T.2 + c • b

  What is proven here (every statement is exact and unconditional: no hardness assumption is
  used, and none is needed, because soundness and zero knowledge of this proof system are
  information-theoretic):

  * `completeness`             an honest B is always accepted;
  * `special_soundness`        two accepting transcripts with the same commitment and different
                               challenges yield a witness `w` with `pk = w • g` and `b = w • a`;
  * `soundness`                hence, if `pk = k • g` and `g ≠ 0`, then `b = evaluate k a`;
  * `same_key_across_sessions` and the same scalar explains every session checked against `pk`;
  * `at_most_one_challenge`    if B cheated (`b ≠ evaluate k a`), then for ANY commitment at most
                               one challenge can be answered;
  * `soundness_error`,
    `soundness_error_randomized`
                               so a cheating B, however powerful and however it randomises, is
                               accepted with probability at most `1 / |F|` over A's challenge;
  * `soundness_error_tight`    and `1 / |F|` cannot be improved (guess the challenge);
  * `hvzk_fixed_challenge`, `hvzk`, `hvzk_prod`
                               honest-verifier zero knowledge: the transcript of an honest proof
                               has EXACTLY the distribution produced by a simulator that is not
                               given `k`;
  * `output_correct_of_honest_reply`, `output_wrong_of_wrong_reply`
                               end to end with the blind protocol: A's output is `prf H k m` if
                               and only if B's reply was the honest one;
  * `verifiability`, `verifiedSession_honest`
                               A, who outputs only if the proof verifies, outputs a value
                               different from `prf H k m` with probability at most `1 / |F|`
                               against ANY B, and outputs `prf H k m` against an honest B;
  * `challenge_preserves_blindness`
                               A's extra message (the challenge) is independent of the message
                               `m`, so the proof step cannot break blindness.

  What is NOT covered (and is not claimed anywhere in this file):

  * The NON-INTERACTIVE variant used in practice (Fiat–Shamir: `c := Hash(g, pk, a, b, T)`), which
    is what RFC 9497 specifies.  Its soundness and zero knowledge hold only in the random-oracle
    model and are not formalised here.  Soundness in this file is for the INTERACTIVE, public-coin
    protocol in which A draws `c` uniformly AFTER receiving `T`.
  * Zero knowledge against a verifier that deviates from the protocol.  The simulation result is
    HONEST-VERIFIER zero knowledge only: the challenge must be chosen independently of the
    commitment.
  * A probabilistic knowledge extractor (rewinding).  `special_soundness` is the algebraic core
    of such an extractor, nothing more.
  * Any statement that `k` is hard to compute from `pk = k • g` (discrete logarithm).  That is a
    computational assumption on the concrete group; it is neither proven nor assumed here.
  * That `pk` is the "right" key.  A must have obtained `pk` authentically; the proof only ties
    B's reply to whatever key is behind `pk`.
-/
import BlindPRF.Correctness
import BlindPRF.Prob

namespace BlindPRF

namespace DLEQ

open scoped ENNReal

variable {F G M Ω : Type*}

/-! ### The protocol -/

section Protocol

variable [Field F] [AddCommGroup G] [Module F G]

/-- Prover's first message: with fresh randomness `t`, commit to `t` on both bases `g` and `a`. -/
def commit (g a : G) (t : F) : G × G := (t • g, t • a)

/-- Prover's last message: the response `s = t + c * k` to challenge `c`. -/
def respond (k t c : F) : F := t + c * k

/-- Verifier's check on a transcript `(T, c, s)` for the statement "the same scalar links
`(g, pk)` and `(a, b)`".  It uses only public values: the key `k` does not appear. -/
def accepts (g pk a b : G) (T : G × G) (c s : F) : Prop :=
  s • g = T.1 + c • pk ∧ s • a = T.2 + c • b

/-- The verifier's check is a pair of equalities in `G`, so it is decidable as soon as equality
in `G` is.  All probability statements below are phrased with this instance; since `Decidable`
is a subsingleton they hold verbatim for any other decision procedure. -/
instance accepts.instDecidable [DecidableEq G] (g pk a b : G) (T : G × G) (c s : F) :
    Decidable (accepts g pk a b T c s) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The witness computed from two accepting transcripts `(T, c, s)` and `(T, c', s')` with the
same commitment (see `special_soundness`). -/
def extract (c c' s s' : F) : F := (s - s') / (c - c')

/-- The honest-verifier simulator.  Given only the PUBLIC statement `(g, pk, a, b)`, a challenge
`c` and a response `s`, it solves the verification equations for the commitment.  Note the
type: no key is passed in. -/
def simulate (g pk a b : G) (c s : F) : (G × G) × F × F :=
  ((s • g - c • pk, s • a - c • b), c, s)

end Protocol

/-! ### Completeness -/

section Algebra

variable [Field F] [AddCommGroup G] [Module F G]

/-- **Completeness.**  If B really holds `k` with `pk = k • g`, replied `b = evaluate k a = k • a`
and follows the protocol, then A's check succeeds, for every base `g`, every blinded element `a`,
every prover coin `t` and every challenge `c`. -/
theorem completeness (g a : G) (k t c : F) :
    accepts g (k • g) a (evaluate k a) (commit g a t) c (respond k t c) := by
  simp [accepts, commit, respond, evaluate, add_smul, mul_smul]

/-! ### Special soundness and soundness -/

/-- **Special soundness.**  From two accepting transcripts with the SAME commitment `T` and
DIFFERENT challenges `c ≠ c'` one can compute a scalar `w = (s - s') / (c - c')` with
`pk = w • g` and `b = w • a`: the statement is true and `w` is a witness for it.

This holds for arbitrary `g, pk, a, b` (no generator assumption).  It is a purely algebraic
fact; it does NOT by itself say how a verifier would obtain two such transcripts from a prover
(that would need rewinding, which is not modelled). -/
theorem special_soundness {g pk a b : G} {T : G × G} {c c' s s' : F} (hc : c ≠ c')
    (h : accepts g pk a b T c s) (h' : accepts g pk a b T c' s') :
    pk = extract c c' s s' • g ∧ b = extract c c' s s' • a := by
  have hne : c - c' ≠ 0 := sub_ne_zero.mpr hc
  have key : ∀ {x y U : G}, s • x = U + c • y → s' • x = U + c' • y →
      y = extract c c' s s' • x := by
    intro x y U h1 h2
    have h3 : (s - s') • x = (c - c') • y := by
      rw [sub_smul, sub_smul, h1, h2]
      abel
    rw [extract, div_eq_inv_mul, mul_smul, h3, smul_smul, inv_mul_cancel₀ hne, one_smul]
  exact ⟨key h.1 h'.1, key h.2 h'.2⟩

/-- **Soundness for the protocol's purpose.**  Let `pk = k • g` be B's public key with `g ≠ 0`.
If B can answer two different challenges for the same commitment, then its reply to A was the
honest one: `b = evaluate k a = k • a`.  (The witness extracted by `special_soundness` is forced
to be `k` because discrete logarithms to the base `g ≠ 0` are unique.)

Only `g ≠ 0` is needed, which is weaker than `IsGenerator F g`. -/
theorem soundness {g pk a b : G} {k : F} (hg : g ≠ 0) (hpk : pk = k • g) {T : G × G}
    {c c' s s' : F} (hc : c ≠ c') (h : accepts g pk a b T c s)
    (h' : accepts g pk a b T c' s') : b = evaluate k a := by
  obtain ⟨h1, h2⟩ := special_soundness hc h h'
  have hk : k = extract c c' s s' := smul_left_injective F hg (hpk.symm.trans h1)
  rw [h2, ← hk, evaluate]

/-- `soundness`, phrased with the generator structure of `Basic.lean`. -/
theorem soundness_of_isGenerator {g pk a b : G} {k : F} (hg : IsGenerator F g)
    (hpk : pk = k • g) {T : G × G} {c c' s s' : F} (hc : c ≠ c')
    (h : accepts g pk a b T c s) (h' : accepts g pk a b T c' s') : b = evaluate k a :=
  soundness hg.ne_zero hpk hc h h'

/-- If the statement is false (no scalar links both pairs), then for ANY commitment `T` at most
one challenge has an accepting response.  No assumption on `g` at all. -/
theorem at_most_one_challenge_of_no_witness {g pk a b : G}
    (hfalse : ¬∃ w : F, pk = w • g ∧ b = w • a) {T : G × G} {c c' s s' : F}
    (h : accepts g pk a b T c s) (h' : accepts g pk a b T c' s') : c = c' := by
  by_contra hc
  exact hfalse ⟨_, special_soundness hc h h'⟩

/-- A reply that differs from the honest one makes the DLEQ statement false: with `pk = k • g`
and `g ≠ 0`, the only candidate witness is `k`. -/
theorem no_witness_of_wrong_reply {g pk a b : G} {k : F} (hg : g ≠ 0) (hpk : pk = k • g)
    (hb : b ≠ evaluate k a) : ¬∃ w : F, pk = w • g ∧ b = w • a := by
  rintro ⟨w, h1, h2⟩
  have hk : k = w := smul_left_injective F hg (hpk.symm.trans h1)
  exact hb (by rw [h2, hk, evaluate])

/-- **At most one challenge can be answered by a cheater.**  Let `pk = k • g` with `g ≠ 0` and
suppose B's reply is wrong, `b ≠ evaluate k a`.  Then for ANY commitment `T` (chosen by B however
it likes) there is at most one challenge `c` for which an accepting response exists at all.

This is information-theoretic: it does not depend on B's computational power. -/
theorem at_most_one_challenge {g pk a b : G} {k : F} (hg : g ≠ 0) (hpk : pk = k • g)
    (hb : b ≠ evaluate k a) {T : G × G} {c c' s s' : F} (h : accepts g pk a b T c s)
    (h' : accepts g pk a b T c' s') : c = c' :=
  at_most_one_challenge_of_no_witness (no_witness_of_wrong_reply hg hpk hb) h h'

/-- `at_most_one_challenge`, phrased with the generator structure of `Basic.lean`. -/
theorem at_most_one_challenge_of_isGenerator {g pk a b : G} {k : F} (hg : IsGenerator F g)
    (hpk : pk = k • g) (hb : b ≠ evaluate k a) {T : G × G} {c c' s s' : F}
    (h : accepts g pk a b T c s) (h' : accepts g pk a b T c' s') : c = c' :=
  at_most_one_challenge hg.ne_zero hpk hb h h'

/-- **The published key pins the reply down, even if `pk` was generated maliciously.**  In a
cyclic group of prime order (`IsGenerator F g`) every `pk` has a unique discrete logarithm
`hg.equiv.symm pk`.  If B can answer two challenges on one commitment, its reply is the
evaluation of `a` under exactly that scalar.  No assumption is made about how `pk` was produced
or about B "knowing" its discrete logarithm. -/
theorem reply_determined_by_pk {g a b : G} (hg : IsGenerator F g) (pk : G) {T : G × G}
    {c c' s s' : F} (hc : c ≠ c') (h : accepts g pk a b T c s)
    (h' : accepts g pk a b T c' s') : b = evaluate (hg.equiv.symm pk) a :=
  soundness hg.ne_zero (hg.smul_equiv_symm pk).symm hc h h'

/-- **No per-client keys ("anti-tagging"), extraction form.**  Two sessions, with blinded
elements `a₁`, `a₂` and replies `b₁`, `b₂`, are checked against the SAME public value `pk`
(`g ≠ 0`; `pk` arbitrary).  If in each session B can answer two different challenges on its
commitment, then one single scalar `k` explains everything: `pk = k • g`, `b₁ = k • a₁` and
`b₂ = k • a₂`.  B cannot serve different clients under different keys. -/
theorem same_key_across_sessions {g pk a₁ b₁ a₂ b₂ : G} (hg : g ≠ 0) {T₁ T₂ : G × G}
    {c₁ c₁' s₁ s₁' c₂ c₂' s₂ s₂' : F}
    (hc₁ : c₁ ≠ c₁') (h₁ : accepts g pk a₁ b₁ T₁ c₁ s₁) (h₁' : accepts g pk a₁ b₁ T₁ c₁' s₁')
    (hc₂ : c₂ ≠ c₂') (h₂ : accepts g pk a₂ b₂ T₂ c₂ s₂) (h₂' : accepts g pk a₂ b₂ T₂ c₂' s₂') :
    ∃ k : F, pk = k • g ∧ b₁ = evaluate k a₁ ∧ b₂ = evaluate k a₂ := by
  obtain ⟨hpk, hb₁⟩ := special_soundness hc₁ h₁ h₁'
  exact ⟨_, hpk, hb₁, soundness hg hpk hc₂ h₂ h₂'⟩

/-- Cardinality form of `at_most_one_challenge`: for a wrong reply and any commitment, the set of
challenges that can be answered has at most one element. -/
theorem answerable_challenges_subsingleton {g pk a b : G} {k : F} (hg : g ≠ 0)
    (hpk : pk = k • g) (hb : b ≠ evaluate k a) (T : G × G) :
    {c : F | ∃ s, accepts g pk a b T c s}.Subsingleton := by
  rintro c ⟨s, h⟩ c' ⟨s', h'⟩
  exact at_most_one_challenge hg hpk hb h h'

/-! ### The simulator always produces accepting transcripts -/

/-- The simulated transcript passes verification for ANY statement `(g, pk, a, b)`, true or
false.  (This is why the order of messages matters: the simulator picks the commitment AFTER the
challenge, which a real prover cannot do.) -/
theorem simulate_accepts (g pk a b : G) (c s : F) :
    accepts g pk a b (simulate g pk a b c s).1 (simulate g pk a b c s).2.1
      (simulate g pk a b c s).2.2 := by
  simp [accepts, simulate]

/-- For a true statement, the simulator run on the honest response reproduces the honest
transcript exactly. -/
theorem simulate_respond (g a : G) (k t c : F) :
    simulate g (k • g) a (evaluate k a) c (respond k t c) =
      (commit g a t, c, respond k t c) := by
  simp [simulate, commit, respond, evaluate, add_smul, mul_smul]

/-! ### End to end with the blind protocol: algebra -/

/-- Unblinding is injective: different replies give different outputs. -/
theorem unblind_injective (r : Fˣ) : Function.Injective (unblind (G := G) r) := by
  intro b b' h
  have h2 : (r : F) • unblind r b = (r : F) • unblind r b' := by rw [h]
  simpa [unblind, smul_smul] using h2

/-- A's output equals the signature `prf H k m` exactly when B's reply was the honest one. -/
theorem unblind_eq_prf_iff (H : M → G) (k : F) (m : M) (r : Fˣ) (b : G) :
    unblind r b = prf H k m ↔ b = evaluate k (blind H m r) := by
  rw [← unblind_evaluate_blind H k m r]
  exact (unblind_injective r).eq_iff

/-- **End to end, positive direction.**  If A blinded honestly and B's reply satisfies
`b = evaluate k (blind H m r)` (which is what the DLEQ proof enforces, up to soundness error
`1 / |F|`, see `soundness_error`), then A's unblinded output is the signature `prf H k m`. -/
theorem output_correct_of_honest_reply (H : M → G) (k : F) (m : M) (r : Fˣ) {b : G}
    (hb : b = evaluate k (blind H m r)) : unblind r b = prf H k m :=
  (unblind_eq_prf_iff H k m r b).mpr hb

/-- **End to end, negative direction.**  A wrong reply ALWAYS gives a wrong output: if
`b ≠ evaluate k (blind H m r)` then `unblind r b ≠ prf H k m`.  So without the proof, a
misbehaving B silently corrupts A's signature; this is what the DLEQ proof is there to catch. -/
theorem output_wrong_of_wrong_reply (H : M → G) (k : F) (m : M) (r : Fˣ) {b : G}
    (hb : b ≠ evaluate k (blind H m r)) : unblind r b ≠ prf H k m :=
  fun h => hb ((unblind_eq_prf_iff H k m r b).mp h)

/-- **End to end, extraction form.**  If, for A's honestly blinded element, B can answer two
different challenges on the same commitment under the public key `pk = k • g` (`g ≠ 0`), then
A's unblinded output is the genuine signature `prf H k m`. -/
theorem output_correct_of_two_transcripts {g pk : G} {k : F} (hg : g ≠ 0) (hpk : pk = k • g)
    (H : M → G) (m : M) (r : Fˣ) {b : G} {T : G × G} {c c' s s' : F} (hc : c ≠ c')
    (h : accepts g pk (blind H m r) b T c s) (h' : accepts g pk (blind H m r) b T c' s') :
    unblind r b = prf H k m :=
  output_correct_of_honest_reply H k m r (soundness hg hpk hc h h')

end Algebra

/-! ### Two general probability facts -/

section ProbLemmas

/-- An event that at most one sample point satisfies has probability at most `1 / |α|` under the
uniform distribution. -/
theorem unif_map_decide_le {α : Type*} [Fintype α] [Nonempty α] (p : α → Prop) [DecidablePred p]
    (hp : ∀ x y, p x → p y → x = y) :
    ((unif α).map fun x => decide (p x)) true ≤ (Fintype.card α : ℝ≥0∞)⁻¹ := by
  rw [PMF.map_apply]
  by_cases hex : ∃ x, p x
  · obtain ⟨x₀, hx₀⟩ := hex
    rw [tsum_eq_single x₀]
    · simp [hx₀]
    · intro x hx
      have hnp : ¬p x := fun h => hx (hp x x₀ h hx₀)
      simp [hnp]
  · have hnp : ∀ x, ¬p x := fun x h => hex ⟨x, h⟩
    simp [hnp]

/-- The same bound when the event may depend on independent extra randomness `ω` drawn first
from an arbitrary distribution: if for every `ω` at most one uniform sample satisfies the event,
the overall probability is at most `1 / |α|`. -/
theorem bind_unif_map_decide_le {α : Type*} [Fintype α] [Nonempty α] (coins : PMF Ω)
    (p : Ω → α → Prop) [∀ ω, DecidablePred (p ω)] (hp : ∀ ω x y, p ω x → p ω y → x = y) :
    (coins.bind fun ω => (unif α).map fun x => decide (p ω x)) true ≤
      (Fintype.card α : ℝ≥0∞)⁻¹ := by
  rw [PMF.bind_apply]
  calc ∑' ω, coins ω * ((unif α).map fun x => decide (p ω x)) true
      ≤ ∑' ω, coins ω * (Fintype.card α : ℝ≥0∞)⁻¹ :=
        tsum_le_tsum fun ω => mul_le_mul_right (unif_map_decide_le (p ω) (hp ω)) _
    _ = (Fintype.card α : ℝ≥0∞)⁻¹ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end ProbLemmas

/-! ### Quantitative soundness -/

section Soundness

variable [Field F] [Fintype F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- **Soundness error `≤ 1 / |F|`.**  Let `pk = k • g` with `g ≠ 0` and let B's reply be wrong,
`b ≠ evaluate k a`.  Fix ANY commitment `T` and ANY response strategy `resp : F → F` (an
arbitrary function of the challenge: unbounded, adaptive, allowed to know `k`).  Then the
probability, over A's uniformly random challenge `c`, that A accepts is at most `1 / |F|`.

Here `decide (accepts …)` uses the instance `accepts.instDecidable` (from `DecidableEq G`).

This is for the INTERACTIVE protocol, where `c` is drawn after `T` is fixed.  It says nothing
about the Fiat–Shamir (non-interactive) variant, whose analysis needs the random-oracle model. -/
theorem soundness_error {g pk a b : G} {k : F} (hg : g ≠ 0) (hpk : pk = k • g)
    (hb : b ≠ evaluate k a) (T : G × G) (resp : F → F) :
    ((unif F).map fun c => decide (accepts g pk a b T c (resp c))) true ≤
      (Fintype.card F : ℝ≥0∞)⁻¹ :=
  unif_map_decide_le _ fun _ _ h h' => at_most_one_challenge hg hpk hb h h'

/-- `soundness_error` for a false statement in general: if no scalar links `(g, pk)` and
`(a, b)`, a prover is accepted with probability at most `1 / |F|`.  No assumption on `g`. -/
theorem soundness_error_of_no_witness {g pk a b : G} (hfalse : ¬∃ w : F, pk = w • g ∧ b = w • a)
    (T : G × G) (resp : F → F) :
    ((unif F).map fun c => decide (accepts g pk a b T c (resp c))) true ≤
      (Fintype.card F : ℝ≥0∞)⁻¹ :=
  unif_map_decide_le _ fun _ _ h h' => at_most_one_challenge_of_no_witness hfalse h h'

/-- **Soundness against a randomised cheating B.**  B draws private coins `ω` from an arbitrary
distribution, and its reply `b ω`, its commitment `T ω` and its response `resp ω c` may all
depend on them.  The probability, over B's coins and A's independent uniform challenge, of the
event "A accepts AND the reply was wrong" is at most `1 / |F|`.

(The honest reply is never "wrong", so this bounds exactly the probability that the proof makes
A accept a bad reply.  The functions `b`, `T`, `resp` are quantified after `g`, `pk`, `a`, so
they may depend on everything B has seen.) -/
theorem soundness_error_randomized {g pk a : G} {k : F} (hg : g ≠ 0) (hpk : pk = k • g)
    (coins : PMF Ω) (b : Ω → G) (T : Ω → G × G) (resp : Ω → F → F) :
    (coins.bind fun ω => (unif F).map fun c =>
        decide (accepts g pk a (b ω) (T ω) c (resp ω c) ∧ b ω ≠ evaluate k a)) true ≤
      (Fintype.card F : ℝ≥0∞)⁻¹ :=
  bind_unif_map_decide_le coins _ fun _ _ _ h h' =>
    at_most_one_challenge hg hpk h.2 h.1 h'.1

/-- **The bound `1 / |F|` is tight.**  For ANY statement, true or false, a prover that guesses
the challenge `c₀` in advance and prepares the simulated commitment for it is accepted with
probability at least `1 / |F|`.  Together with `soundness_error`, a cheating prover's best
acceptance probability is exactly `1 / |F|`; in particular the scalar field must be large. -/
theorem soundness_error_tight (g pk a b : G) (c₀ s₀ : F) :
    (Fintype.card F : ℝ≥0∞)⁻¹ ≤
      ((unif F).map fun c =>
        decide (accepts g pk a b (simulate g pk a b c₀ s₀).1 c s₀)) true := by
  rw [PMF.map_apply]
  refine le_trans ?_ (le_tsum _ c₀)
  have h := simulate_accepts g pk a b c₀ s₀
  simp only [simulate] at h
  simp [simulate, h]

end Soundness

/-! ### Honest-verifier zero knowledge -/

section ZeroKnowledge

variable [Field F] [Fintype F] [AddCommGroup G] [Module F G]

/-- **Honest-verifier zero knowledge, fixed challenge.**  For a true statement (`pk = k • g`,
`b = evaluate k a`) and every fixed challenge `c`, the honest transcript
`(commit g a t, c, respond k t c)` with `t` uniform has EXACTLY the same distribution as the
simulated transcript `simulate g pk a b c s` with `s` uniform.

The simulator is not given `k`: it sees only the public statement.  So the transcript an honest
verifier sees could have been produced by the verifier itself, and therefore carries no
information about `k` beyond the truth of the statement.

What this does NOT claim: zero knowledge against a verifier that picks `c` as a function of the
commitment (malicious verifier), and anything about the Fiat–Shamir variant. -/
theorem hvzk_fixed_challenge (g a : G) (k c : F) :
    ((unif F).map fun t => (commit g a t, c, respond k t c)) =
      (unif F).map fun s => simulate g (k • g) a (evaluate k a) c s :=
  unif_map_eq_of_equiv (Equiv.addRight (c * k)) _ _ fun t => simulate_respond g a k t c

/-- Honest-verifier zero knowledge for ANY challenge distribution `D` that is independent of the
prover's commitment (the honest verifier uses the uniform one). -/
theorem hvzk_challenge_dist (D : PMF F) (g a : G) (k : F) :
    (D.bind fun c => (unif F).map fun t => (commit g a t, c, respond k t c)) =
      D.bind fun c => (unif F).map fun s => simulate g (k • g) a (evaluate k a) c s := by
  congr 1
  funext c
  exact hvzk_fixed_challenge g a k c

/-- The honest protocol as an experiment, in the order in which it is really executed: the prover
draws `t` and sends the commitment, then the verifier draws the challenge `c` uniformly, then the
prover responds.  The result is the full transcript `(T, c, s)`. -/
noncomputable def realTranscript (g a : G) (k : F) : PMF ((G × G) × F × F) :=
  (unif F).bind fun t => (unif F).map fun c => (commit g a t, c, respond k t c)

/-- The simulated experiment: draw the challenge and the response uniformly and solve for the
commitment.  Its inputs are public; no key is used. -/
noncomputable def simTranscript (g pk a b : G) : PMF ((G × G) × F × F) :=
  (unif F).bind fun c => (unif F).map fun s => simulate g pk a b c s

/-- **Honest-verifier zero knowledge.**  For a true statement, the transcript distribution of the
real protocol (prover holding `k`, verifier honest) EQUALS the output distribution of the
simulator, which is run on the public values `(g, k • g, a, k • a)` only.

Hence a transcript with an honest verifier reveals nothing about `k` beyond what `pk = k • g`
and `b = k • a` already determine.  HONEST-verifier only; perfect (not merely computational)
indistinguishability; says nothing about what `pk` and `b` themselves reveal about `k` (that is
the discrete-logarithm question, which is not addressed here). -/
theorem hvzk (g a : G) (k : F) :
    realTranscript g a k = simTranscript g (k • g) a (evaluate k a) := by
  have hswap : realTranscript g a k =
      (unif F).bind fun c => (unif F).map fun t => (commit g a t, c, respond k t c) := by
    unfold realTranscript
    simp only [← PMF.bind_pure_comp]
    exact PMF.bind_comm _ _ _
  rw [hswap]
  exact hvzk_challenge_dist (unif F) g a k

/-- `hvzk` with the public statement named: whenever `pk = k • g` and `b = evaluate k a`, the
real transcript distribution is the simulator's output on `(g, pk, a, b)`. -/
theorem hvzk_of_statement {g pk a b : G} {k : F} (hpk : pk = k • g) (hb : b = evaluate k a) :
    realTranscript g a k = simTranscript g pk a b := by
  subst hpk hb
  exact hvzk g a k

/-- Honest-verifier zero knowledge with the prover coin and the challenge drawn as one uniform
pair: the map `(t, c) ↦ (c, t + c * k)` is a bijection of `F × F` carrying the honest
transcript to the simulated one. -/
theorem hvzk_prod (g a : G) (k : F) :
    ((unif (F × F)).map fun tc => (commit g a tc.1, tc.2, respond k tc.1 tc.2)) =
      (unif (F × F)).map fun cs => simulate g (k • g) a (evaluate k a) cs.1 cs.2 := by
  let e : F × F ≃ F × F :=
    { toFun := fun tc => (tc.2, tc.1 + tc.2 * k)
      invFun := fun cs => (cs.2 - cs.1 * k, cs.1)
      left_inv := fun tc => by simp
      right_inv := fun cs => by simp }
  exact unif_map_eq_of_equiv e _ _ fun tc => simulate_respond g a k tc.1 tc.2

/-- Every transcript the simulator can output is accepting, for any statement. -/
theorem simTranscript_accepts (g pk a b : G) (x : (G × G) × F × F)
    (hx : x ∈ (simTranscript g pk a b).support) : accepts g pk a b x.1 x.2.1 x.2.2 := by
  unfold simTranscript at hx
  rw [PMF.mem_support_bind_iff] at hx
  obtain ⟨c, -, hx⟩ := hx
  rw [PMF.mem_support_map_iff] at hx
  obtain ⟨s, -, rfl⟩ := hx
  exact simulate_accepts g pk a b c s

end ZeroKnowledge

/-! ### End to end: the verified session -/

section Session

variable [Field F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- A's output in a session with a proof: A unblinds and outputs `some σ` only if the DLEQ
transcript verifies against the public key; otherwise A aborts (`none`). -/
def verifiedOutput (g pk : G) (H : M → G) (m : M) (r : Fˣ) (b : G) (T : G × G) (c s : F) :
    Option G :=
  if accepts g pk (blind H m r) b T c s then some (unblind r b) else none

/-- Against an honest B (reply `evaluate k a`, commitment `commit g a t`, response
`respond k t c`), A never aborts and outputs the signature `prf H k m`, whatever the coins. -/
theorem verifiedOutput_honest (g : G) (H : M → G) (k : F) (m : M) (r : Fˣ) (t c : F) :
    verifiedOutput g (k • g) H m r (evaluate k (blind H m r)) (commit g (blind H m r) t) c
      (respond k t c) = some (prf H k m) := by
  rw [verifiedOutput, ite_eq_left (completeness g (blind H m r) k t c), unblind_evaluate_blind]

/-- If A outputs a value that is not the genuine signature, then A accepted a wrong reply. -/
theorem accepts_wrong_of_verifiedOutput {g pk : G} {H : M → G} {k : F} {m : M} {r : Fˣ} {b : G}
    {T : G × G} {c s : F} (h1 : verifiedOutput g pk H m r b T c s ≠ none)
    (h2 : verifiedOutput g pk H m r b T c s ≠ some (prf H k m)) :
    accepts g pk (blind H m r) b T c s ∧ b ≠ evaluate k (blind H m r) := by
  unfold verifiedOutput at h1 h2
  by_cases hacc : accepts g pk (blind H m r) b T c s
  · rw [ite_eq_left hacc] at h2
    refine ⟨hacc, fun hb => h2 ?_⟩
    rw [output_correct_of_honest_reply H k m r hb]
  · rw [ite_eq_right hacc] at h1
    exact absurd rfl h1

variable [Fintype F]

/-- One session of the blind protocol WITH the proof, against an arbitrary (malicious,
randomised, unbounded) party B.  A has message `m` and blinding scalar `r` and sends
`a = blind H m r`.  B draws private coins `ω`, replies `reply ω`, commits to `commitment ω`, and
after A's uniform challenge `c` responds `response ω c`.  A outputs `verifiedOutput …`.

B's three functions are arbitrary, so they may depend on `a` and on anything else. -/
noncomputable def verifiedSession (g pk : G) (H : M → G) (m : M) (r : Fˣ) (coins : PMF Ω)
    (reply : Ω → G) (commitment : Ω → G × G) (response : Ω → F → F) : PMF (Option G) :=
  coins.bind fun ω => (unif F).map fun c =>
    verifiedOutput g pk H m r (reply ω) (commitment ω) c (response ω c)

/-- **Verifiability of the blind protocol.**  Let `pk = k • g` be B's public key, `g ≠ 0`.
Whatever B does in a session (any coins, reply, commitment, response strategy), the probability
that A outputs something OTHER than the genuine signature `prf H k m`, i.e. that A neither
aborts nor outputs `prf H k m`, is at most `1 / |F|`.

This holds for every fixed message `m` and blinding scalar `r`, hence also for random ones.  It
is a statement about the interactive proof with a uniformly random challenge chosen after B's
commitment; the Fiat–Shamir variant is not covered.  It does not say that B cannot make A abort
(B always can, by refusing to answer). -/
theorem verifiability {g pk : G} {k : F} (hg : g ≠ 0) (hpk : pk = k • g) (H : M → G) (m : M)
    (r : Fˣ) (coins : PMF Ω) (reply : Ω → G) (commitment : Ω → G × G) (response : Ω → F → F) :
    ((verifiedSession g pk H m r coins reply commitment response).map fun o =>
        decide (o ≠ none ∧ o ≠ some (prf H k m))) true ≤ (Fintype.card F : ℝ≥0∞)⁻¹ := by
  unfold verifiedSession
  rw [PMF.map_bind]
  simp only [PMF.map_comp]
  refine bind_unif_map_decide_le coins
    (fun ω c => verifiedOutput g pk H m r (reply ω) (commitment ω) c (response ω c) ≠ none ∧
      verifiedOutput g pk H m r (reply ω) (commitment ω) c (response ω c) ≠ some (prf H k m))
    fun ω c c' h h' => ?_
  obtain ⟨hacc, hwrong⟩ := accepts_wrong_of_verifiedOutput h.1 h.2
  obtain ⟨hacc', -⟩ := accepts_wrong_of_verifiedOutput h'.1 h'.2
  exact at_most_one_challenge hg hpk hwrong hacc hacc'

/-- **Completeness of the verified session.**  Against the honest B (coins `t` uniform, reply
`evaluate k a`, commitment `commit g a t`, response `respond k t c`), A outputs the signature
`prf H k m` with probability one. -/
theorem verifiedSession_honest (g : G) (H : M → G) (k : F) (m : M) (r : Fˣ) :
    verifiedSession g (k • g) H m r (unif F) (fun _ => evaluate k (blind H m r))
        (fun t => commit g (blind H m r) t) (fun t c => respond k t c) =
      PMF.pure (some (prf H k m)) := by
  unfold verifiedSession
  simp only [verifiedOutput_honest]
  rw [show (fun _ : F => some (prf H k m)) = Function.const F (some (prf H k m)) from rfl,
    PMF.map_const, unif_bind_const]

/-- **End to end, probabilistic form.**  If B's reply would make A's output wrong
(`unblind r b ≠ prf H k m`), then for any commitment and any response strategy the proof is
accepted with probability at most `1 / |F|` over A's challenge. -/
theorem wrong_output_accept_prob_le {g pk : G} {k : F} (hg : g ≠ 0) (hpk : pk = k • g)
    (H : M → G) (m : M) (r : Fˣ) {b : G} (hwrong : unblind r b ≠ prf H k m) (T : G × G)
    (resp : F → F) :
    ((unif F).map fun c => decide (accepts g pk (blind H m r) b T c (resp c))) true ≤
      (Fintype.card F : ℝ≥0∞)⁻¹ :=
  soundness_error hg hpk (fun hb => hwrong (output_correct_of_honest_reply H k m r hb)) T resp

end Session

/-! ### The proof step does not hurt message privacy -/

section Privacy

variable [Field F] [Fintype F] [AddCommGroup G] [Module F G]

/-- **Adding the proof preserves blindness.**  In a verified session, what A sends to B is the
blinded element `a = blind H m r` and then the challenge `c`, which is uniform and independent
of `(m, r)`.  So if the blinded element alone has the same distribution for two messages `m`,
`m'` (for A's coin distribution `R`), then so does the pair `(a, c)`: the joint distribution of
everything A sends in a verified session is the same for `m` and `m'`.

This is a composition statement.  It does NOT prove the hypothesis `hblind` (blindness of the
bare protocol, the subject of `Blindness.lean`); it shows that A's two messages in the verified
session are jointly as hiding as the first one alone.

Informal remark, not part of the formal statement: everything else B sees in the session (its
own coins and messages, and whether A's check passes) is computed from `(a, c)` and data B
already holds.  A's final output `σ` is never sent to B. -/
theorem challenge_preserves_blindness (R : PMF Fˣ) (H : M → G) (m m' : M)
    (hblind : R.map (blind H m) = R.map (blind H m')) :
    (R.bind fun r => (unif F).map fun c => (blind H m r, c)) =
      R.bind fun r => (unif F).map fun c => (blind H m' r, c) := by
  have key : ∀ x : M, (R.bind fun r => (unif F).map fun c => (blind H x r, c)) =
      (R.map (blind H x)).bind fun a => (unif F).map fun c => (a, c) := by
    intro x
    rw [PMF.bind_map]
    rfl
  rw [key m, key m', hblind]

end Privacy

/-! ### Sanity checks: the hypotheses are satisfiable -/

section Sanity

/-- `5` is prime (used only for the examples below). -/
local instance fact5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- Non-vacuity of the cheating hypotheses of `soundness_error`: in `F = G = ZMod 5` with
`g = 1`, key `k = 2` (so `pk = 2`), blinded element `a = 1`, the reply `b = 3` is wrong. -/
example : (1 : ZMod 5) ≠ 0 ∧ (2 : ZMod 5) = (2 : ZMod 5) • (1 : ZMod 5) ∧
    (3 : ZMod 5) ≠ evaluate (2 : ZMod 5) (1 : ZMod 5) := by
  decide

/-- ... and the bound then reads: whatever B commits to and however it responds, A accepts the
wrong reply with probability at most `1/5`. -/
example (T : ZMod 5 × ZMod 5) (resp : ZMod 5 → ZMod 5) :
    ((unif (ZMod 5)).map fun c => decide (accepts (1 : ZMod 5) 2 1 3 T c (resp c))) true ≤
      (5 : ℝ≥0∞)⁻¹ := by
  have h := soundness_error (g := (1 : ZMod 5)) (pk := 2) (a := 1) (b := 3) (k := 2)
    (by decide) (by decide) (by decide) T resp
  simpa [ZMod.card] using h

/-- The honest transcript in the same toy group: key `2`, coin `t = 4`, challenge `c = 3`. -/
example : accepts (1 : ZMod 5) 2 1 2 (commit (1 : ZMod 5) 1 (4 : ZMod 5)) (3 : ZMod 5)
    (respond 2 4 3) := by
  decide

end Sanity

end DLEQ

end BlindPRF
