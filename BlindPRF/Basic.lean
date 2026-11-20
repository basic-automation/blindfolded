/-
  BlindPRF/Basic.lean — the protocol, as plain functions, and the algebraic setting.

  Setting.  `F` is the field of scalars (think `ZMod q`, `q` prime) and `G` is an `F`-module
  written additively (think: the points of an elliptic-curve group of prime order `q`, where
  `k • P` is scalar multiplication).  `M` is the message space and `H : M → G` is a hash-to-group
  function.  Nothing in this file is probabilistic.

  The protocol ("blinded Diffie–Hellman PRF", the core of the 2HashDH oblivious PRF):

      A holds m, picks r ≠ 0 at random            B holds the key k
      ---------------------------------------------------------------
      a := r • H m            ── a ──▶
                              ◀── b ──            b := k • a
      σ := r⁻¹ • b   ( = k • H m )

  The "signature" on `m` under `k` is `σ = prf H k m = k • H m`.
-/
import Mathlib

namespace BlindPRF

variable {F G M : Type*}

section Protocol

variable [Field F] [AddCommGroup G] [Module F G]

/-- The keyed function `F_k(m) = k • H(m)`.  This is the value party A ends up with: the
signature (authentication tag) on message `m` under party B's key `k`. -/
def prf (H : M → G) (k : F) (m : M) : G := k • H m

/-- Step 1 (party A): hide the hashed message under a *nonzero* random scalar `r`. -/
def blind (H : M → G) (m : M) (r : Fˣ) : G := (r : F) • H m

/-- Step 2 (party B): multiply the received group element by the secret key.
B applies this to whatever it receives; it never sees `m`. -/
def evaluate (k : F) (a : G) : G := k • a

/-- Step 3 (party A): strip the blinding scalar from B's reply. -/
def unblind (r : Fˣ) (b : G) : G := ((r⁻¹ : Fˣ) : F) • b

/-- One complete honest execution: A's output on message `m` with coin `r` against key `k`. -/
def run (H : M → G) (k : F) (m : M) (r : Fˣ) : G :=
  unblind r (evaluate k (blind H m r))

/-- Everything party B sees in one session: its own key and the single message from A. -/
def viewB (H : M → G) (k : F) (m : M) (r : Fˣ) : F × G := (k, blind H m r)

/-- Everything party A sees in one session: its message, its coin, and B's reply. -/
def viewA (H : M → G) (k : F) (m : M) (r : Fˣ) : M × Fˣ × G :=
  (m, r, evaluate k (blind H m r))

/-- Verification by the key holder (the PRF output is a MAC: checking it needs the key). -/
def verifyWithKey (H : M → G) (k : F) (m : M) (σ : G) : Prop := σ = prf H k m

end Protocol

/-- `IsGenerator F g` says that `g` generates `G` as an `F`-module and is nonzero: `G` is a
one-dimensional vector space over `F`.  With `F = ZMod q` this is exactly "`G` is a cyclic
group of prime order `q` and `g` is a generator". -/
structure IsGenerator (F : Type*) {G : Type*} [Field F] [AddCommGroup G] [Module F G]
    (g : G) : Prop where
  /-- the generator is not the identity element -/
  ne_zero : g ≠ 0
  /-- every group element is a scalar multiple of the generator -/
  spans : ∀ x : G, ∃ c : F, c • g = x

namespace IsGenerator

variable [Field F] [AddCommGroup G] [Module F G] {g : G}

/-- Discrete logarithms with respect to a generator are unique. -/
theorem smul_injective (hg : IsGenerator F g) : Function.Injective fun c : F => c • g := by
  intro c c' h
  have h0 : (c - c') • g = 0 := by
    rw [sub_smul]
    exact sub_eq_zero.mpr h
  rcases smul_eq_zero.mp h0 with h1 | h1
  · exact sub_eq_zero.mp h1
  · exact absurd h1 hg.ne_zero

theorem smul_eq_smul_iff (hg : IsGenerator F g) {c c' : F} : c • g = c' • g ↔ c = c' :=
  hg.smul_injective.eq_iff

theorem smul_eq_zero_iff (hg : IsGenerator F g) {c : F} : c • g = 0 ↔ c = 0 := by
  constructor
  · intro h
    exact hg.smul_injective (by simpa using h)
  · rintro rfl
    simp

/-- Scalars and group elements are in bijection via `c ↦ c • g` (the inverse is the discrete
logarithm, which exists but is of course not assumed to be efficiently computable). -/
noncomputable def equiv (hg : IsGenerator F g) : F ≃ G :=
  Equiv.ofBijective (fun c : F => c • g) ⟨hg.smul_injective, hg.spans⟩

@[simp]
theorem equiv_apply (hg : IsGenerator F g) (c : F) : hg.equiv c = c • g := rfl

theorem equiv_symm_smul (hg : IsGenerator F g) (c : F) : hg.equiv.symm (c • g) = c :=
  hg.equiv.symm_apply_apply c

theorem smul_equiv_symm (hg : IsGenerator F g) (x : G) : hg.equiv.symm x • g = x :=
  hg.equiv.apply_symm_apply x

/-- In a group of prime order every non-identity element is a generator. -/
theorem of_ne_zero (hg : IsGenerator F g) {P : G} (hP : P ≠ 0) : IsGenerator F P := by
  refine ⟨hP, fun x => ?_⟩
  obtain ⟨p, rfl⟩ := hg.spans P
  obtain ⟨c, rfl⟩ := hg.spans x
  have hp : p ≠ 0 := by
    rintro rfl
    exact hP (by simp)
  exact ⟨c * p⁻¹, by rw [smul_smul, mul_assoc, inv_mul_cancel₀ hp, mul_one]⟩

end IsGenerator

end BlindPRF
