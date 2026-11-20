/-
  BlindPRF/PublicVerify.lean — optional public verifiability (the "blind BLS" layer).

  The bare protocol produces `σ = k • H m`, which only the key holder can check.  If the group
  `G₁` carries a bilinear pairing `e : G₁ × G₂ → GT` and B publishes `pk = k • g₂`, then

  * anyone can verify a signature:      `e σ g₂ = e (H m) pk`            (the BLS equation), and
  * A can verify B's *blinded* reply:   `e b g₂ = e a pk`                (before unblinding).

  The second check is what protects A against a B that answers with a wrong key (for example a
  different key per client, in order to tag and later recognise clients).

  The pairing is modelled abstractly as an `F`-bilinear map.  Non-degeneracy is the explicit
  hypothesis `Function.Injective (fun x => e x g₂)`; `BlindPRF/Instance.lean` exhibits a model in
  which it holds, so the theorems below are not vacuous.
-/
import BlindPRF.Correctness

namespace BlindPRF

namespace PublicVerify

variable {F G₁ G₂ GT M : Type*} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [AddCommGroup GT] [Module F GT]

/-- B's public key for secret key `k`, relative to the public base point `g₂`. -/
def publicKey (g₂ : G₂) (k : F) : G₂ := k • g₂

/-- Public signature verification (the BLS equation).  Uses only public data. -/
def verify (e : G₁ →ₗ[F] G₂ →ₗ[F] GT) (H : M → G₁) (g₂ pk : G₂) (m : M) (σ : G₁) : Prop :=
  e σ g₂ = e (H m) pk

/-- A's check on B's reply `b` to the blinded element `a`.  Uses only the transcript `(a, b)` and
the public key — in particular it does not depend on the message or on the blinding scalar, so
whether A accepts is something B can compute by itself and reveals nothing to B. -/
def checkReply (e : G₁ →ₗ[F] G₂ →ₗ[F] GT) (g₂ pk : G₂) (a b : G₁) : Prop :=
  e b g₂ = e a pk

variable (e : G₁ →ₗ[F] G₂ →ₗ[F] GT) (H : M → G₁) (g₂ : G₂)

/-- Bilinearity moves the key from the first slot to the second. -/
theorem pairing_smul_comm (k : F) (P : G₁) : e (k • P) g₂ = e P (k • g₂) := by
  rw [map_smul, LinearMap.smul_apply, map_smul]

/-- **Completeness of public verification.**  The genuine signature verifies. -/
theorem verify_prf (k : F) (m : M) : verify e H g₂ (publicKey g₂ k) m (prf H k m) :=
  pairing_smul_comm e g₂ k (H m)

/-- **Soundness / uniqueness.**  If the pairing is non-degenerate at `g₂`, the *only* group
element that verifies for message `m` under `pk = k • g₂` is the genuine signature `k • H m`. -/
theorem eq_prf_of_verify (hnd : Function.Injective fun x : G₁ => e x g₂) {k : F} {m : M}
    {σ : G₁} (h : verify e H g₂ (publicKey g₂ k) m σ) : σ = prf H k m := by
  apply hnd
  show e σ g₂ = e (prf H k m) g₂
  rw [h, prf, pairing_smul_comm]
  rfl

/-- Verification accepts exactly the genuine signature. -/
theorem verify_iff (hnd : Function.Injective fun x : G₁ => e x g₂) (k : F) (m : M) (σ : G₁) :
    verify e H g₂ (publicKey g₂ k) m σ ↔ σ = prf H k m :=
  ⟨eq_prf_of_verify e H g₂ hnd, fun h => h ▸ verify_prf e H g₂ k m⟩

/-- **Unique signatures**, for an arbitrary (possibly maliciously generated) public key: two
signatures that both verify for the same message are equal. -/
theorem verify_unique (hnd : Function.Injective fun x : G₁ => e x g₂) {pk : G₂} {m : M}
    {σ σ' : G₁} (h : verify e H g₂ pk m σ) (h' : verify e H g₂ pk m σ') : σ = σ' :=
  hnd (h.trans h'.symm)

/-- An honest reply passes A's check. -/
theorem checkReply_evaluate (k : F) (a : G₁) :
    checkReply e g₂ (publicKey g₂ k) a (evaluate k a) :=
  pairing_smul_comm e g₂ k a

/-- **Soundness of A's check.**  A reply that passes the check is the honest reply, whatever B
actually did to produce it. -/
theorem eq_evaluate_of_checkReply (hnd : Function.Injective fun x : G₁ => e x g₂) {k : F}
    {a b : G₁} (h : checkReply e g₂ (publicKey g₂ k) a b) : b = evaluate k a := by
  apply hnd
  show e b g₂ = e (evaluate k a) g₂
  rw [h, evaluate, pairing_smul_comm]
  rfl

/-- A's check accepts exactly the honest reply. -/
theorem checkReply_iff (hnd : Function.Injective fun x : G₁ => e x g₂) (k : F) (a b : G₁) :
    checkReply e g₂ (publicKey g₂ k) a b ↔ b = evaluate k a :=
  ⟨eq_evaluate_of_checkReply e g₂ hnd, fun h => h ▸ checkReply_evaluate e g₂ k a⟩

/-- **Correctness against a malicious B.**  If A blinds honestly and B's reply — produced in any
way whatsoever — passes A's check, then A's unblinded output is the genuine signature under the
key behind the published `pk`, and it passes public verification. -/
theorem checked_run (hnd : Function.Injective fun x : G₁ => e x g₂) (k : F) (m : M) (r : Fˣ)
    {b : G₁} (h : checkReply e g₂ (publicKey g₂ k) (blind H m r) b) :
    unblind r b = prf H k m ∧ verify e H g₂ (publicKey g₂ k) m (unblind r b) := by
  have hb : b = evaluate k (blind H m r) := eq_evaluate_of_checkReply e g₂ hnd h
  have hσ : unblind r b = prf H k m := by rw [hb, unblind_evaluate_blind]
  exact ⟨hσ, hσ ▸ verify_prf e H g₂ k m⟩

/-- The check on the blinded pair is equivalent to public verification of the unblinded
signature: A may check either before or after unblinding. -/
theorem checkReply_blind_iff_verify (pk : G₂) (m : M) (r : Fˣ) (b : G₁) :
    checkReply e g₂ pk (blind H m r) b ↔ verify e H g₂ pk m (unblind r b) := by
  have hr : ((r⁻¹ : Fˣ) : F) * (r : F) = 1 := by simp
  simp only [checkReply, verify, unblind, blind, map_smul, LinearMap.smul_apply]
  constructor
  · intro h
    rw [h, smul_smul, hr, one_smul]
  · intro h
    have h2 := congrArg (fun x => (r : F) • x) h
    simpa [smul_smul] using h2

end PublicVerify

end BlindPRF
