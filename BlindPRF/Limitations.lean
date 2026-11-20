/-
  BlindPRF/Limitations.lean — machine-checked NEGATIVE results and attack surface.

  Every other file of this development proves something the protocol DOES give.  This file
  proves, with the same rigour, what it does NOT give, and which hypotheses cannot be dropped,
  so that the positive theorems cannot be over-read.  Nothing here is a hardness statement and
  nothing here is assumed: every theorem is an unconditional fact about the protocol functions
  of `BlindPRF/Basic.lean`.

  L1  `zero_coin_output`, `no_unblind_of_zero_coin`
        A zero blinding scalar destroys CORRECTNESS (not privacy): this is why coins are units.
  L2  `rankTwo_smul_dist_ne`, `rankTwo_blind_dist_ne`, `rankTwo_distinguisher`
        Message privacy FAILS in a non-cyclic group: the cyclic hypothesis is necessary.
  L3  `coin_reuse_dist_ne`, `coin_reuse_distinguisher`
        Reusing one coin in two sessions lets B link them.
  L4  `iterate_evaluate`, `evaluate_add`, `evaluate_smul`, `evaluate_hash_add`
        B is a static Diffie–Hellman oracle for anyone who deviates from the protocol.
  L5  `forge_of_known_hash_dlog`, `exists_forger`
        Unforgeability rests entirely on the hash, and can only ever be computational.
  L6  `toy_key_recovery`, `toy_run_key_recovery`, `toy_isGenerator`, `toy_pairing_nondegenerate`
        All hypotheses hold in a totally broken group: "verified" does not mean "secure".
  L7  `verify_random_prob`, `verify_genuine_prob`
        Public verifiability excludes pseudorandomness.
  L8  `exists_simulator_for_any_leak`
        An existential simulation statement would be vacuous.
  L9  `prf_add_key`, `prf_mul_key`
        Outputs under related keys are related (key homomorphism).

  What this file does NOT contain: any complexity statement.  The attacks that the algebraic
  facts of L4 enable (Brown–Gallant, Cheon) and the assumptions that bound a deviating party
  (discrete log, CDH, DDH, one-more-DH) are mentioned in docstrings for orientation only; they
  are neither formalised, nor proven, nor assumed.
-/
import BlindPRF.Correctness
import BlindPRF.Prob
import BlindPRF.PublicVerify

namespace BlindPRF

namespace Limitations

open scoped ENNReal

variable {F G M : Type*}

/-! ## Two small tools for separating distributions -/

/-- If no value of `f` is a value of `g`, then *every* distribution of `f`-values differs from
*every* distribution of `g`-values (their supports are disjoint). -/
theorem map_ne_map_of_forall_ne {α β γ : Type*} (p : PMF α) (q : PMF β) (f : α → γ) (g : β → γ)
    (h : ∀ a b, f a ≠ g b) : p.map f ≠ q.map g := by
  intro heq
  obtain ⟨a, ha⟩ := p.support_nonempty
  have hmem : f a ∈ (p.map f).support := (PMF.mem_support_map_iff _ _ _).mpr ⟨a, ha, rfl⟩
  rw [heq] at hmem
  obtain ⟨b, -, hb⟩ := (PMF.mem_support_map_iff _ _ _).mp hmem
  exact h a b hb.symm

/-- A test whose answer is the same on every sample has that answer with probability one. -/
theorem map_eq_pure_of_forall {α γ : Type*} (p : PMF α) (f : α → γ) (c : γ) (h : ∀ a, f a = c) :
    p.map f = PMF.pure c := by
  have hf : f = Function.const α c := funext h
  rw [hf, PMF.map_const]

/-! ## L1. A zero blinding scalar breaks correctness -/

section ZeroCoin

variable [Field F] [AddCommGroup G] [Module F G]

/-- **L1(a). With the blinding scalar `0` the protocol outputs the identity, not the
signature.**  Running the three protocol steps with "coin" `r = 0` (and Lean's convention
`0⁻¹ = 0`) yields `0` for every key `k` and every hashed message `P`.

Practical consequence: an implementation must reject (or never sample) `r = 0`; this is why the
coin of `blind`/`unblind` has type `Fˣ`.

What this does NOT claim: that `r = 0` leaks anything.  It does not: B then receives `0 • P = 0`
whatever the message is (`zero_coin_blinded`).  The failure is one of correctness only. -/
theorem zero_coin_output (k : F) (P : G) : ((0 : F)⁻¹) • (k • ((0 : F) • P)) = 0 := by
  simp

/-- With blinding scalar `0`, B receives the identity element for every message: the zero coin
is not a privacy problem. -/
theorem zero_coin_blinded (P Q : G) : (0 : F) • P = (0 : F) • Q := by
  rw [zero_smul, zero_smul]

/-- **L1(b). No unblinding procedure whatsoever can repair a zero blinding scalar.**  If
`P ≠ 0` (the hashed message) there is NO function `unb`, however it is defined and even if it
is allowed to depend on `P`, that turns B's reply `k • (0 • P)` into the signature `k • P` for
all keys `k`: the reply is `0` for every key, while the signatures under the keys `0` and `1`
differ.

Practical consequence: the failure in `zero_coin_output` is not an artefact of the convention
`0⁻¹ = 0`; the information needed to compute the signature is simply absent from the reply, so
the non-zero requirement on the coin cannot be dropped.

What this does NOT claim: anything about nonzero coins (for those, `unblind` works:
`unblind_evaluate_blind`), or anything about privacy. -/
theorem no_unblind_of_zero_coin {P : G} (hP : P ≠ 0) :
    ¬ ∃ unb : G → G, ∀ k : F, unb (k • ((0 : F) • P)) = k • P := by
  rintro ⟨unb, h⟩
  have h0 := h 0
  have h1 := h 1
  simp only [zero_smul, smul_zero, one_smul] at h0 h1
  exact hP (h1.symm.trans h0)

end ZeroCoin

/-! ## L2. The cyclic (rank-one) hypothesis is necessary for message privacy -/

section NonCyclic

/-- A two-message "hash" into the rank-two module `F × F` (a NON-cyclic group): message `false`
is sent to `(1, 0)` and message `true` to `(0, 1)`.  Both values are nonzero. -/
def rankTwoHash (F : Type*) [Field F] : Bool → F × F := fun b => if b then (0, 1) else (1, 0)

variable [Field F]

/-- Neither hash value of the counterexample is the identity: the failure of privacy below is
NOT caused by the (separately necessary) condition `H m ≠ 0`. -/
theorem rankTwoHash_ne_zero (b : Bool) : rankTwoHash F b ≠ 0 := by
  cases b <;> simp [rankTwoHash]

/-- The module `F × F` has no generator: it is exactly the hypothesis `IsGenerator F g` of the
privacy theorems that fails in the counterexample. -/
theorem not_isGenerator_prod (g : F × F) : ¬ IsGenerator F g := by
  intro hg
  obtain ⟨c, hc⟩ := hg.spans ((1 : F), (0 : F))
  obtain ⟨d, hd⟩ := hg.spans ((0 : F), (1 : F))
  have hc1 : c * g.1 = 1 := congrArg Prod.fst hc
  have hc2 : c * g.2 = 0 := congrArg Prod.snd hc
  have hd2 : d * g.2 = 1 := congrArg Prod.snd hd
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc1
  have hg2 : g.2 = 0 := (mul_eq_zero.mp hc2).resolve_left hc0
  rw [hg2, mul_zero] at hd2
  exact zero_ne_one hd2

variable [Fintype F] [DecidableEq F]

/-- **L2. In a non-cyclic group the blinded element depends on the message** (raw form).  In
the rank-two module `F × F`, the uniformly blinded versions of the points `(1, 0)` and `(0, 1)`
have DIFFERENT distributions: blinding by a scalar never leaves the line through the point.

See `rankTwo_blind_dist_ne` for the same statement phrased through the protocol function
`blind`, and for the practical consequence. -/
theorem rankTwo_smul_dist_ne :
    (unif Fˣ).map (fun r : Fˣ => (r : F) • ((1 : F), (0 : F))) ≠
      (unif Fˣ).map (fun r : Fˣ => (r : F) • ((0 : F), (1 : F))) := by
  apply map_ne_map_of_forall_ne
  intro r r' h
  have h1 : (r : F) * 1 = (r' : F) * 0 := congrArg Prod.fst h
  rw [mul_one, mul_zero] at h1
  exact r.ne_zero h1

/-- **L2. The cyclic hypothesis is necessary for message privacy (negative result).**  Run the
protocol's blinding step in the rank-two group `G = F × F` with the two-message hash
`rankTwoHash F` (both hash values nonzero).  Then B's view of message `false` and B's view of
message `true` are DIFFERENT distributions.  So the hypothesis `IsGenerator F g` of the privacy
theorems cannot be dropped (`not_isGenerator_prod` confirms it is the hypothesis that fails).

Practical consequence: scalar blinding hides a point only inside the cyclic subgroup it
generates, so in a non-cyclic group the blinded element leaks which subgroup / line the hash
lies on; real implementations must work in a prime-order group (or clear cofactors) and
validate that points lie in it.

What this does NOT claim: that privacy fails in a cyclic group of prime order (there it holds
perfectly; that is the positive theorem elsewhere).  Nor is it a model of a curve with a
cofactor: such a group is not a module over the scalar field and cannot even be expressed in
this development; the rank-two module is the nearest counterexample the model can state.  What
leaks in general is the line `F • H m` through the hash (here: the whole message bit). -/
theorem rankTwo_blind_dist_ne :
    (unif Fˣ).map (blind (rankTwoHash F) false) ≠ (unif Fˣ).map (blind (rankTwoHash F) true) :=
  rankTwo_smul_dist_ne

/-- **L2, quantitatively: B reads the message off the blinded element with certainty.**  In the
rank-two counterexample, the test "is the first coordinate zero?" applied to A's single
protocol message returns the message bit `b` with probability ONE.  (In a cyclic group the best
possible success probability for a uniformly random bit is one half.)

What this does NOT claim: see `rankTwo_blind_dist_ne`. -/
theorem rankTwo_distinguisher (b : Bool) :
    ((unif Fˣ).map (blind (rankTwoHash F) b)).map (fun a : F × F => decide (a.1 = 0)) =
      PMF.pure b := by
  rw [PMF.map_comp]
  apply map_eq_pure_of_forall
  intro r
  cases b <;> simp [blind, rankTwoHash]

end NonCyclic

/-! ## L3. Coin reuse links sessions -/

section CoinReuse

variable [Field F] [Fintype F] [DecidableEq F] [AddCommGroup G] [Module F G]

/-- **L3. Reusing a blinding scalar links sessions (negative result).**  Suppose A uses ONE coin
`r` for two sessions.  If the hashes of `m` and `m'` differ, then what B sees when A asks for
`m` twice and what B sees when A asks for `m` and then `m'` are DIFFERENT distributions.

Practical consequence: the blinding scalar must be sampled freshly and independently for every
session; a client with a stuck or repeated random number generator loses unlinkability (B
learns at least whether two requests were for the same message).

What this does NOT claim: that B learns the messages themselves, or that sessions with
independent coins can be linked (they cannot, in a prime-order group; that is the positive
privacy theorem elsewhere, whose hypothesis "one fresh uniform coin per session" is thereby
shown to be necessary). -/
theorem coin_reuse_dist_ne (H : M → G) {m m' : M} (h : H m ≠ H m') :
    (unif Fˣ).map (fun r : Fˣ => (blind H m r, blind H m r)) ≠
      (unif Fˣ).map (fun r : Fˣ => (blind H m r, blind H m' r)) := by
  apply map_ne_map_of_forall_ne
  intro r r' heq
  have h1 : blind H m r = blind H m r' := congrArg Prod.fst heq
  have h2 : blind H m r = blind H m' r' := congrArg Prod.snd heq
  exact h (smul_right_injective G r'.ne_zero (h1.symm.trans h2))

/-- **L3, quantitatively: B links coin-reusing sessions with certainty.**  The test "are the two
received group elements equal?" answers `true` with probability ONE when A asked for the same
message twice with one coin, and `false` with probability ONE when A asked for two messages
with different hashes with one coin.

What this does NOT claim: see `coin_reuse_dist_ne`. -/
theorem coin_reuse_distinguisher [DecidableEq G] (H : M → G) {m m' : M} (h : H m ≠ H m') :
    ((unif Fˣ).map (fun r : Fˣ => (blind H m r, blind H m r))).map
        (fun v : G × G => decide (v.1 = v.2)) = PMF.pure true ∧
      ((unif Fˣ).map (fun r : Fˣ => (blind H m r, blind H m' r))).map
        (fun v : G × G => decide (v.1 = v.2)) = PMF.pure false := by
  constructor
  · rw [PMF.map_comp]
    apply map_eq_pure_of_forall
    intro r
    simp
  · rw [PMF.map_comp]
    apply map_eq_pure_of_forall
    intro r
    have hne : blind H m r ≠ blind H m' r := fun heq => h (smul_right_injective G r.ne_zero heq)
    simp [hne]

end CoinReuse

/-! ## L4. B is a static Diffie–Hellman oracle -/

section StaticDH

variable [Field F] [AddCommGroup G] [Module F G]

/-- **L4(a). Feeding replies back in yields the powers of the key.**  Querying B on `a`, then on
B's reply, and so on `n` times, returns `k ^ n • a`.  A party that deviates from the protocol
in this way collects the tuple `(a, k • a, k² • a, …, kⁿ • a)`, the "`n`-strong Diffie–Hellman"
tuple.

Practical consequence: the key holder is a static Diffie–Hellman oracle, and this tuple is the
input of the Brown–Gallant / Cheon key-recovery speed-ups, which is why deployments limit the
number of evaluations per key, rotate keys, or choose the group order with these attacks in
mind.

What this does NOT claim: the Brown–Gallant / Cheon algorithms and their running times are NOT
formalised here; this theorem is only the algebraic identity that makes the tuple available.
Nothing is proven about how hard the key is to recover from the tuple. -/
theorem iterate_evaluate (k : F) (n : ℕ) (a : G) : (evaluate k)^[n] a = (k ^ n) • a := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, evaluate, smul_smul, pow_succ']

/-- **L4(b). B's reply is additive in the query.**  One query on a sum returns the sum of the
replies.  See `evaluate_hash_add` for the consequence. -/
theorem evaluate_add (k : F) (a a' : G) : evaluate k (a + a') = evaluate k a + evaluate k a' :=
  smul_add k a a'

/-- **L4(b). B's reply is homogeneous in the query.**  From B's reply to `a`, anyone computes
B's reply to every scalar multiple `c • a` without talking to B again.

Practical consequence: one reply yields valid replies on every scalar multiple of the query,
so replies are malleable and a transcript `(a, b)` does not show which point B was "really"
asked about (this is the very mechanism of blinding, seen from the other side).

What this does NOT claim: that signatures on NEW messages can be derived this way; relating
`c • H m` to `H m'` for another message is a discrete-logarithm relation between hash outputs
(see `forge_of_known_hash_dlog` for what happens when such relations are known). -/
theorem evaluate_smul (k c : F) (a : G) : evaluate k (c • a) = c • evaluate k a :=
  smul_comm k c a

/-- **L4(b), consequence: a malicious query returns a combination of signatures.**  The query
`a = H m + H m'`, which no honest A would send, is answered with the SUM of the signatures on
`m` and `m'`.

Practical consequence: an A that deviates from the protocol obtains more than "one signature on
one message of its choice" per session (sums of signatures, strong-DH tuples, …).  Bounding
what such an A can do with `n` sessions — namely, not produce `n + 1` signatures — is the
one-more-Diffie–Hellman assumption, which is NOT proven (nor assumed) anywhere in this
development.

What this does NOT claim: that the sum reveals either signature individually, or that the
protocol is insecure against a malicious A; it shows only that security against a malicious A
cannot be argued session-by-session and rests on an unproven interactive assumption. -/
theorem evaluate_hash_add (H : M → G) (k : F) (m m' : M) :
    evaluate k (H m + H m') = prf H k m + prf H k m' :=
  smul_add k (H m) (H m')

end StaticDH

/-! ## L5. Security rests entirely on the hash -/

section Hash

variable [Field F] [AddCommGroup G] [Module F G]

/-- **L5(a). Known discrete logarithms of hash outputs make every signature forgeable.**  If
the hash is `m ↦ h m • g` for a publicly computable exponent `h m`, then the signature on `m`
is `h m • pk` where `pk = k • g` is the public key: anyone computes every signature with one
scalar multiplication, without the key and without ever interacting with B.

Practical consequence: `H` must behave like a random oracle into the group whose outputs have
discrete logarithms unknown to everybody (use a standard hash-to-curve construction; never
"hash to an exponent and multiply the generator").  The demo hashes in `BlindPRF/Instance.lean`
are lookup tables of exactly this forgeable kind: they are functional tests of the arithmetic
and nothing more.

What this does NOT claim: that signatures are forgeable for a hash with unknown discrete
logarithms.  That question is computational (see `exists_forger`) and is not decided here. -/
theorem forge_of_known_hash_dlog (g : G) (h : M → F) (k : F) (m : M) :
    prf (fun m => h m • g) k m = h m • (k • g) :=
  smul_comm k (h m) g

/-- L5(b), general form: the forger exists as soon as the public base point is not the
identity (no cyclicity is needed).  See `exists_forger`. -/
theorem exists_forger_of_ne_zero {g : G} (hg : g ≠ 0) (H : M → G) :
    ∃ forge : G → M → G, ∀ (k : F) (m : M), forge (k • g) m = prf H k m := by
  have hinj : Function.Injective fun c : F => c • g := smul_left_injective F hg
  refine ⟨fun pk m => prf H (Function.invFun (fun c : F => c • g) pk) m, fun k m => ?_⟩
  have hk : Function.invFun (fun c : F => c • g) (k • g) = k := Function.leftInverse_invFun hinj k
  simp only [hk]

/-- **L5(b). Unforgeability can only ever be computational.**  In a cyclic group with generator
`g`, for EVERY hash function `H` there exists a function `forge` that maps the public key
`k • g` and a message to the signature on that message — for all keys and all messages, with
no interaction.  (The function takes the discrete logarithm of the public key.)

Practical consequence: no theorem of the form "for all adversaries, forging succeeds with small
probability" can be true for this scheme when adversaries are arbitrary functions and the
public key is known (or, by `exists_simulator_for_any_leak`, a single signature is known);
unforgeability necessarily rests on an unproven computational hardness assumption about the
concrete group, and can enter a development like this one only through explicit reductions.

What this does NOT claim: that `forge` is efficiently computable.  It is obtained from the
(non-constructive) inverse of `c ↦ c • g`; computing it is a discrete-logarithm computation,
about whose cost nothing is said. -/
theorem exists_forger {g : G} (hg : IsGenerator F g) (H : M → G) :
    ∃ forge : G → M → G, ∀ (k : F) (m : M), forge (k • g) m = prf H k m :=
  exists_forger_of_ne_zero hg.ne_zero H

end Hash

/-! ## L6. The verified theorems hold in a totally broken group -/

section Toy

variable [Field F]

/-- **L6. In the toy group one division recovers the key from one signature.**  Take the group
to be the scalar field itself (`G := F`, acting on itself by multiplication; for `F = ZMod p`
this is the additive group of integers modulo `p`).  Then for any message whose hash is not
zero, `signature / hash = key`.

Practical consequence: "machine-verified" does NOT mean "secure".  The hypotheses under which
this development proves its theorems — a field of scalars, a module over it, a generator
(`toy_isGenerator`), for the pairing layer a non-degenerate bilinear map
(`toy_pairing_nondegenerate`), and finiteness / decidable equality (take `F = ZMod p`) — are
all satisfied by this group, so every theorem proven from them holds in it; yet in it the key
is recovered from a single signature by one field division.  Security is exactly the unproven
hardness of discrete-logarithm-type problems in the concrete group that is deployed, and no
theorem here can supply it.

What this does NOT claim: that key recovery is easy in elliptic-curve groups, or in any group
other than this toy one. -/
theorem toy_key_recovery (H : M → F) (k : F) {m : M} (hm : H m ≠ 0) :
    prf H k m * (H m)⁻¹ = k := by
  rw [prf, smul_eq_mul, mul_inv_cancel_right₀ hm]

/-- L6, from A's side: in the toy group, A's output of ONE honest session, divided by the hash
of its own message, is B's key.  (Same caveats as `toy_key_recovery`.) -/
theorem toy_run_key_recovery (H : M → F) (k : F) {m : M} (hm : H m ≠ 0) (r : Fˣ) :
    run H k m r * (H m)⁻¹ = k := by
  rw [correctness, toy_key_recovery H k hm]

/-- The toy group satisfies the cyclic-group hypothesis of the security theorems: `1` generates
`F` as a module over itself. -/
theorem toy_isGenerator : IsGenerator F (1 : F) :=
  ⟨one_ne_zero, fun x => ⟨x, by simp⟩⟩

/-- The toy group satisfies the pairing hypothesis of `BlindPRF/PublicVerify.lean`:
multiplication `F × F → F` is bilinear and non-degenerate at the base point `1`. -/
theorem toy_pairing_nondegenerate :
    Function.Injective fun x : F => LinearMap.mul F F x 1 := by
  intro x y h
  simpa using h

end Toy

/-! ## L7. Public verifiability excludes pseudorandomness -/

section PublicVerifiability

variable {G₁ G₂ GT : Type*} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [AddCommGroup GT] [Module F GT]

/-- The public test accepts the genuine signature with probability one (a restatement of
`PublicVerify.verify_prf` in the form needed to compare with `verify_random_prob`). -/
theorem verify_genuine_prob (e : G₁ →ₗ[F] G₂ →ₗ[F] GT) (H : M → G₁) (g₂ : G₂) (k : F) (m : M)
    [∀ σ : G₁, Decidable (PublicVerify.verify e H g₂ (PublicVerify.publicKey g₂ k) m σ)] :
    ((PMF.pure (prf H k m)).map fun σ : G₁ =>
      decide (PublicVerify.verify e H g₂ (PublicVerify.publicKey g₂ k) m σ)) true = 1 := by
  rw [PMF.pure_map, decide_eq_true (PublicVerify.verify_prf e H g₂ k m), PMF.pure_apply_self]

/-- **L7. Public verifiability excludes pseudorandomness.**  In the pairing setting of
`BlindPRF/PublicVerify.lean` (pairing non-degenerate at `g₂`, public key `pk = k • g₂`), the
PUBLIC verification test accepts a uniformly random element of `G₁` with probability exactly
`1 / |G₁|`, whereas it accepts the genuine signature with probability one
(`verify_genuine_prob`).  The test uses only public data, so everybody can run it.

Practical consequence: once a pairing is available and the key `k • g₂` is published, anyone
distinguishes signatures from random group elements (acceptance probability `1` against
`1/|G₁|`); the pairing variant is a unique (verifiable) signature scheme and NOT a
pseudorandom function towards parties who know the public key, and the DDH-based
pseudorandomness statement of this development does not apply to it.

What this does NOT claim: that the publicly verifiable variant is forgeable, or that the
key-only (MAC) variant without a pairing is distinguishable from random; neither is decided
here. -/
theorem verify_random_prob [Fintype G₁] (e : G₁ →ₗ[F] G₂ →ₗ[F] GT) (H : M → G₁) (g₂ : G₂)
    (hnd : Function.Injective fun x : G₁ => e x g₂) (k : F) (m : M)
    [∀ σ : G₁, Decidable (PublicVerify.verify e H g₂ (PublicVerify.publicKey g₂ k) m σ)] :
    ((unif G₁).map fun σ : G₁ =>
      decide (PublicVerify.verify e H g₂ (PublicVerify.publicKey g₂ k) m σ)) true
      = (Fintype.card G₁ : ℝ≥0∞)⁻¹ := by
  rw [PMF.map_apply, tsum_eq_single (prf H k m)]
  · simp [PublicVerify.verify_prf e H g₂ k m]
  · intro σ hσ
    have hno : ¬ PublicVerify.verify e H g₂ (PublicVerify.publicKey g₂ k) m σ :=
      fun hv => hσ (PublicVerify.eq_prf_of_verify e H g₂ hnd hv)
    simp [hno]

end PublicVerifiability

/-! ## L8. An existential simulation statement would be vacuous -/

section Simulation

variable [Field F] [AddCommGroup G] [Module F G]

/-- **L8. "There exists a simulator" is true of every protocol, including leaky ones.**  Fix a
message with `H m ≠ 0`.  For ANY function `leak : F → X` of B's key whatsoever — for instance
`leak := id`, a protocol in which B sends its key to A in the clear — there EXISTS a
"simulator" that computes `leak k` from A's legitimate output `prf H k m` alone.  (No cyclicity
is needed, so this holds in particular under `IsGenerator F g`.  The type `X` is arbitrary: it
may be a function type or a type of distributions, so `leak k` can be A's entire view of any
protocol, as a function of A's inputs and coins.)

Practical consequence: because one signature information-theoretically determines the key, a
security definition of the shape "there exists a function that reproduces A's view from A's
output" is satisfied by every protocol and says nothing.  This is why the key-privacy theorems
of this development exhibit an EXPLICIT simulator (one scalar multiplication, no discrete
logarithm) instead of asserting that one exists; a reader should distrust any simulation claim,
here or elsewhere, whose simulator is only asserted to exist.

What this does NOT claim: that the protocol leaks the key in any practical sense.  The
simulator `sim` produced here is non-constructive (it inverts `k ↦ k • H m`, a discrete
logarithm); nothing is said about its cost. -/
theorem exists_simulator_for_any_leak (H : M → G) {m : M} (hm : H m ≠ 0) {X : Type*}
    (leak : F → X) : ∃ sim : G → X, ∀ k : F, sim (prf H k m) = leak k := by
  have hinj : Function.Injective fun c : F => c • H m := smul_left_injective F hm
  refine ⟨fun σ => leak (Function.invFun (fun c : F => c • H m) σ), fun k => ?_⟩
  have hk : Function.invFun (fun c : F => c • H m) (prf H k m) = k :=
    Function.leftInverse_invFun hinj k
  simp only [hk]

end Simulation

/-! ## L9. Key homomorphism -/

section KeyHomomorphism

variable [Field F] [AddCommGroup G] [Module F G]

/-- **L9. The signature is additive in the key.**  The signature under the sum of two keys is
the sum of the signatures.

Practical consequence: outputs under related keys are related.  This is useful (threshold
signing by additive key shares, key rotation by a public offset), and it is also a reason why
deployments pass the output through an outer hash before using it as a random-looking value:
the raw group element is not "independent-looking" across related keys.

What this does NOT claim: any security property of threshold or key-rotation schemes built on
this identity. -/
theorem prf_add_key (H : M → G) (k k' : F) (m : M) :
    prf H (k + k') m = prf H k m + prf H k' m :=
  add_smul k k' (H m)

/-- **L9. The signature is homogeneous in the key.**  Scaling the key by a public factor `c`
scales every signature by `c`: from a signature under `k`, anyone computes the signature under
`c * k`.  (Same consequence and same caveat as `prf_add_key`.) -/
theorem prf_mul_key (H : M → G) (c k : F) (m : M) : prf H (c * k) m = c • prf H k m :=
  mul_smul c k (H m)

end KeyHomomorphism

end Limitations

end BlindPRF
