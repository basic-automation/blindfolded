/-
  BlindPRF/Closed.lean — the headline theorems with EVERY hypothesis discharged.

  The general theorems are stated for an abstract field `F`, module `G`, generator `g` and hash
  `H`, under hypotheses such as `IsGenerator F g` and `H m ≠ 0`.  A reader is entitled to ask
  whether those hypotheses can all hold at once.  This file answers by restating each headline
  theorem as a closed statement — no hypotheses left — in two concrete models from
  `BlindPRF/Instance.lean`:

  * `Schnorr`: the order-11 subgroup of `(ℤ/23)ˣ`, scalars `ZMod 11`, four messages with pairwise
    distinct non-identity hashes.  Used wherever no pairing is needed.
  * `Toy`: `ZMod 101` acting on itself, which carries a non-degenerate bilinear map.  Used for the
    statements that need a pairing.

  What this file shows: the hypotheses are jointly satisfiable, so the general theorems are not
  vacuously true.  What it does NOT show: that either model is secure.  Both are trivially
  breakable (the groups are tiny, the demo hashes have known discrete logarithms, and in `Toy`
  one division recovers the key).  The reductions below hold in them all the same, because a
  reduction is an identity between two experiments and says nothing about whether either is hard.
-/
import BlindPRF.Instance
import BlindPRF.Blindness
import BlindPRF.Unlinkability
import BlindPRF.KeyPrivacy
import BlindPRF.PRFSecurity
import BlindPRF.Unforgeability
import BlindPRF.DLEQ

namespace BlindPRF

/-! ### Closed statements in the order-11 subgroup of `(ℤ/23)ˣ` -/

namespace Schnorr

/-- None of the four demo hash values is the identity element. -/
theorem demoHash_ne_zero (m : Fin 4) : demoHash m ≠ 0 := by
  unfold demoHash
  rw [← Nat.cast_smul_eq_nsmul (ZMod 11), Ne, isGenerator_gen.smul_eq_zero_iff]
  fin_cases m <;> decide

/-- The four demo hash values are pairwise distinct, so the privacy statements below are about
genuinely different messages. -/
theorem demoHash_injective : Function.Injective demoHash := by
  intro i j h
  unfold demoHash at h
  rw [← Nat.cast_smul_eq_nsmul (ZMod 11), ← Nat.cast_smul_eq_nsmul (ZMod 11),
    isGenerator_gen.smul_eq_smul_iff] at h
  revert h
  fin_cases i <;> fin_cases j <;> decide

/-- **Correctness**, closed: every honest run outputs the signature. -/
theorem correct (k : ZMod 11) (m : Fin 4) (r : (ZMod 11)ˣ) :
    run demoHash k m r = prf demoHash k m :=
  correctness demoHash k m r

/-- **Message privacy**, closed: what B receives has the same distribution for any two of the
four messages. -/
theorem message_privacy (m₀ m₁ : Fin 4) :
    (unif (ZMod 11)ˣ).map (blind demoHash m₀) = (unif (ZMod 11)ˣ).map (blind demoHash m₁) :=
  blind_dist_eq isGenerator_gen demoHash (demoHash_ne_zero m₀) (demoHash_ne_zero m₁)

/-- **Message privacy as a game**, closed: for every key, every pair of messages and every
strategy of B (any function, however expensive), B names the submitted message with probability
exactly one half. -/
theorem guess_probability_half (k : ZMod 11) (m₀ m₁ : Fin 4) (D : ZMod 11 × QR → PMF Bool) :
    indGame demoHash k m₀ m₁ D true = 1 / 2 :=
  indGame_true isGenerator_gen demoHash k (demoHash_ne_zero m₀) (demoHash_ne_zero m₁) D

/-- **Many sessions**, closed: the joint distribution of three blinded elements is the same for
any two message vectors. -/
theorem multi_session_privacy (ms₀ ms₁ : Fin 3 → Fin 4) :
    (unif (Fin 3 → (ZMod 11)ˣ)).map (fun rs i => blind demoHash (ms₀ i) (rs i)) =
      (unif (Fin 3 → (ZMod 11)ˣ)).map (fun rs i => blind demoHash (ms₁ i) (rs i)) :=
  multi_blind_dist_eq isGenerator_gen demoHash ms₀ ms₁ (fun i => demoHash_ne_zero (ms₀ i))
    (fun i => demoHash_ne_zero (ms₁ i))

/-- **What A sees is the signature and nothing else**, closed: A's whole view of a session is
produced by the explicit simulator from the signature alone. -/
theorem view_simulated (k : ZMod 11) (m : Fin 4) (r : (ZMod 11)ˣ) :
    viewA demoHash k m r = KeyPrivacy.simViewA m r (prf demoHash k m) :=
  KeyPrivacy.viewA_eq_simViewA demoHash k m r

/-- **The signature determines the key**, closed: this is why "A learns nothing about the key"
is not, and cannot be, a theorem. -/
theorem signature_determines_key (m : Fin 4) :
    Function.Injective fun k : ZMod 11 => prf demoHash k m :=
  KeyPrivacy.prf_injective_key demoHash (demoHash_ne_zero m)

/-- **Key recovery is discrete log**, closed: for an honest-but-curious A running two sessions,
with any rule for choosing its messages and any key-guessing procedure, the key-recovery
experiment equals the discrete-log experiment for the explicit solver. -/
theorem key_recovery_is_dlog (choose : (Fin 4 → ZMod 11) → Fin 2 → Fin 4)
    (Adv : KeyPrivacy.View (ZMod 11) QR (Fin 4) (Fin 2) → PMF (ZMod 11)) :
    KeyPrivacy.keyRecoveryExp gen choose Adv =
      KeyPrivacy.dlogExp gen (KeyPrivacy.dlogSolver choose Adv) :=
  KeyPrivacy.keyRecovery_eq_dlog gen choose Adv

/-- **Pseudorandomness reduces to DDH**, closed: every distinguisher's advantage against the
keyed function is at most the DDH advantage of the explicit distinguisher built from it, plus
`1/11`. -/
theorem prf_advantage_le_ddh (D : PRFSecurity.Tables (Fin 4) QR → PMF Bool) :
    PRFSecurity.prfAdvantage (ZMod 11) gen D ≤
      PRFSecurity.ddhAdvantage (ZMod 11) gen (PRFSecurity.ddhDistinguisher (ZMod 11) gen D) +
        1 / (Fintype.card (ZMod 11) : ℝ) :=
  PRFSecurity.prfAdvantage_le_ddhAdvantage_add gen D

/-- **Forgery is CDH**, closed: for every target message and every forger, the forgery
experiment equals the Computational Diffie–Hellman experiment for the explicit solver. -/
theorem forgery_is_cdh (mstar : Fin 4)
    (Adv : Unforgeability.ForgerInput QR (Fin 4) → PMF QR) :
    Unforgeability.forgeExp (ZMod 11) gen mstar Adv =
      Unforgeability.cdhExp (ZMod 11) gen (Unforgeability.cdhSolver (ZMod 11) gen mstar Adv) :=
  Unforgeability.forge_eq_cdh gen mstar Adv

/-- **B's equality proof is sound**, closed: if B's reply to a blinded element is not the honest
one, then whatever commitment B sent, at most one challenge can be answered. -/
theorem dleq_sound (k : ZMod 11) (a b : QR) (hb : b ≠ evaluate k a) (T : QR × QR)
    {c c' s s' : ZMod 11} (h : DLEQ.accepts gen (k • gen) a b T c s)
    (h' : DLEQ.accepts gen (k • gen) a b T c' s') : c = c' :=
  DLEQ.at_most_one_challenge_of_isGenerator isGenerator_gen rfl hb h h'

end Schnorr

/-! ### Closed statements that need a pairing, in `ZMod 101` -/

namespace Toy

/-- None of the four demo hash values is the identity element. -/
theorem demoHash_ne_zero (m : Fin 4) : demoHash m ≠ 0 := by
  fin_cases m <;> simp [demoHash] <;> decide

/-- **Blindness against a malicious signer**, closed.  B picks any public key `pk`, sees both
blinded elements, replies in any way (randomised, with state), then sees A's two finished
signatures in message order, or an abort.  Its final output has the same distribution whichever
of the two messages went into the first session. -/
theorem malicious_signer_blindness (pk : ZMod 101) (m₀ m₁ : Fin 4) {S γ : Type}
    (reply : ZMod 101 × ZMod 101 → PMF (S × ZMod 101 × ZMod 101))
    (guess : S → Option (ZMod 101 × ZMod 101) → PMF γ) :
    Unlinkability.blindnessGame (ZMod 101) demoHash
        (fun a b => decide (PublicVerify.checkReply (pairing 101) 1 pk a b)) m₀ m₁ reply guess
        false =
      Unlinkability.blindnessGame (ZMod 101) demoHash
        (fun a b => decide (PublicVerify.checkReply (pairing 101) 1 pk a b)) m₀ m₁ reply guess
        true :=
  Unlinkability.blindness_pairing (isGenerator_one 101) demoHash (demoHash_ne_zero m₀)
    (demoHash_ne_zero m₁) (pairing 101) 1 (pairing_nondegenerate 101) pk reply guess

/-- **Public verification**, closed: exactly the genuine signature verifies. -/
theorem public_verification (k : ZMod 101) (m : Fin 4) (σ : ZMod 101) :
    PublicVerify.verify (pairing 101) demoHash 1 (PublicVerify.publicKey 1 k) m σ ↔
      σ = prf demoHash k m :=
  PublicVerify.verify_iff (pairing 101) demoHash 1 (pairing_nondegenerate 101) k m σ

end Toy

end BlindPRF
