/-
  BlindPRF/Correctness.lean — an honest run gives party A exactly the signature `k • H m`.
-/
import BlindPRF.Basic

namespace BlindPRF

variable {F G M : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- Unblinding undoes blinding, for *any* reply `b` of the form `k • a`. -/
theorem unblind_evaluate_blind (H : M → G) (k : F) (m : M) (r : Fˣ) :
    unblind r (evaluate k (blind H m r)) = prf H k m := by
  simp only [unblind, evaluate, blind, prf, smul_smul]
  rw [mul_comm k, ← mul_assoc]
  simp

/-- **Correctness.**  For every hash function, key, message and nonzero blinding scalar, an
honest execution outputs the signature `prf H k m = k • H m`. -/
theorem correctness (H : M → G) (k : F) (m : M) (r : Fˣ) : run H k m r = prf H k m :=
  unblind_evaluate_blind H k m r

/-- The output does not depend on the blinding scalar: the protocol computes a *function* of
`(k, m)`, so two runs on the same message give the same signature. -/
theorem run_independent_of_coin (H : M → G) (k : F) (m : M) (r r' : Fˣ) :
    run H k m r = run H k m r' := by
  rw [correctness, correctness]

/-- The signature A obtains is accepted by the key holder's check. -/
theorem run_verifies (H : M → G) (k : F) (m : M) (r : Fˣ) :
    verifyWithKey H k m (run H k m r) :=
  correctness H k m r

/-- Post-processing (e.g. the outer hash `H₂(m, ·)` of the 2HashDH construction) commutes with
correctness: whatever A derives from its output, it derives from `prf H k m`. -/
theorem correctness_finalize {Out : Type*} (fin : M → G → Out) (H : M → G) (k : F) (m : M)
    (r : Fˣ) : fin m (run H k m r) = fin m (prf H k m) := by
  rw [correctness]

/-- Blinding with scalar `r` and unblinding with the same scalar is the identity on the group:
the blinding is a bijection of `G` for each fixed `r`. -/
theorem unblind_smul (r : Fˣ) (P : G) : unblind r ((r : F) • P) = P := by
  simp [unblind, smul_smul]

end BlindPRF
