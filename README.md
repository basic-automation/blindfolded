# Blind PRF signing — a protocol specified and verified in Lean 4

Party **A** holds a message `m`. Party **B** holds a secret key `k`. A obtains a signature on `m`
under B's key without showing `m` to B and without being handed `k`.

This directory contains the protocol and machine-checked proofs about it: Lean 4 with Mathlib,
zero `sorry`, no axioms beyond Lean's three standard ones. It is a self-contained Lake project and
touches nothing else in the repository.

**Read this first.** "Machine-verified" here means that the theorems listed below are proved. It
does not mean the protocol is secure in every sense one might hope for. Three things in particular
are not what a quick reading would suggest, and each is itself a theorem in this development:

1. **"A learns nothing about the key" is false, and is not claimed.** The signature `k • H(m)`
   determines `k` mathematically (`KeyPrivacy.prf_injective_key`). What is proved instead: the
   protocol gives A nothing beyond the signature, and recovering `k` from what an
   honest-but-curious A sees is exactly the discrete-logarithm problem.
2. **The bare protocol hides the message but is not "blind" in the blind-signature sense.** A
   dishonest B that answers each client under a different key can later tell which session produced
   which signature, with certainty (`Unlinkability.tagging_attack`). A must check B's reply.
3. **Every hypothesis of the generic theorems is satisfied in a group where the key falls out by
   one division** (`Limitations.toy_isGenerator`, `Limitations.toy_key_recovery`), so the theorems
   cannot by themselves imply any hardness. Security rests on the hardness of discrete log and
   Diffie–Hellman problems in the concrete group, which no proof assistant can establish.

## The protocol

A blinded Diffie–Hellman pseudorandom function: the core of the 2HashDH oblivious PRF. `G` is a
cyclic group of prime order `q`, written additively (`k • P` is scalar multiplication; read
`P ^ k` for a multiplicative group). Scalars live in the field `F = ℤ/q`. `H` hashes messages
into `G`.

```
A holds m, picks a fresh random r ≠ 0          B holds key k, has published pk = k • g
a := r • H(m)            ── a ──▶
                         ◀── b ──              b := k • a
A checks b against pk (see below), then
σ := r⁻¹ • b   =   k • H(m)
```

The signature on `m` is `σ = k • H(m)`. It is a pseudorandom-function value, so by itself it is
an authentication tag that only the key holder can check. Two optional layers address that:

- **Pairing check** (`PublicVerify.lean`, "blind BLS"). If the group has a bilinear pairing `e`,
  anyone can verify a signature via `e(σ, g₂) = e(H(m), pk)`, and A can check B's reply via
  `e(b, g₂) = e(a, pk)` before unblinding.
- **Equality proof** (`DLEQ.lean`, Chaum–Pedersen). Without a pairing, B proves interactively
  that the same `k` links `(g, pk)` and `(a, b)`.

These two layers are alternatives with different consequences: a publicly verifiable signature
cannot also be pseudorandom to someone holding `pk` (`Limitations.verify_random_prob`).

## What is proved

"Unconditional" means: holds for every hash function and against every adversary, including a
computationally unbounded one, with no hardness assumption. "Reduction" means: an exact identity
between an attack experiment on the protocol and an experiment on a standard hard problem, for an
explicitly defined solver. "Negative" means: a proof that something does *not* hold.

### Correctness

| Claim | Theorem | Kind |
|---|---|---|
| An honest run outputs exactly `k • H(m)`, for every key, message and nonzero coin. | `correctness` | unconditional |

### B learns nothing about the message

These results are about what B sees *while signing*. B can compute `k • H(m')` for any guessed
`m'`, so once B (or anyone holding `k`) sees a message together with its signature — as happens
whenever a base-protocol signature is verified — the message is known to B. Hiding *which session*
it came from is the separate property "Blindness against a malicious signer" below, which needs a
sound reply check.

They require a prime-order group, `H(m)` not the identity element, and a fresh uniform coin per
session; the group and hash conditions, and freshness, are each shown to matter by a negative
result below. (The coin is also nonzero, but only because A must invert it to unblind; that is a
correctness requirement, not a privacy one.)

| Claim | Theorem | Kind |
|---|---|---|
| What B receives has the same distribution for any two messages. | `blind_dist_eq`, `viewB_dist_eq` | unconditional |
| For any pair of messages and any strategy, B names the submitted one with probability exactly 1/2. | `indGame_true` | unconditional |
| The same for many sessions jointly, with independent coins. | `multi_blind_dist_eq` | unconditional |
| For any prior on messages, B's posterior equals its prior. | `message_view_independent` | unconditional |
| **Blindness against a malicious signer**: B sees both blinded elements, replies arbitrarily, then sees both finished signatures, and still cannot tell which session was which — *provided A's reply check is perfectly sound*. The two messages are fixed in advance; with the pairing check the signer may also choose them and the public key itself (`Unlinkability.blindness_pairing_two_stage`). | `Unlinkability.blindness` | unconditional |
| The pairing check is such a check, for any public key B chooses. | `Unlinkability.blindness_pairing` | unconditional |
| The same for any number of sessions: B cannot tell any assignment of messages to sessions from any other. B answers all sessions at once and A releases all outputs together. | `Unlinkability.blindnessN`, `Unlinkability.blindnessN_pairing` | unconditional |
| Without a reply check, B links sessions to signatures with certainty. | `Unlinkability.tagging_attack` | negative |
| If A releases outputs per session instead of all-or-nothing, B learns the order with certainty even with a sound check. | `Unlinkability.selective_abort` | negative |
| If each session is checked against its own key rather than one common key, B links with certainty even though every check is sound. | `Unlinkability.per_client_keys_tagging` | negative |
| If a hash value is the identity, B can tell. | `blind_dist_ne_of_hash_zero` | negative |
| Sending `H(m)` unblinded fails the same definition. | `noBlind_dist_ne` | negative |
| In a non-cyclic group, blinding can leak which line the hash lies on. | `Limitations.rankTwo_blind_dist_ne` | negative |
| Reusing one coin for two sessions reveals whether the messages were equal. | `Limitations.coin_reuse_dist_ne` | negative |

### What A learns about the key

| Claim | Theorem | Kind |
|---|---|---|
| A's whole view of a session is produced from the signature alone by an explicit simulator (one scalar multiplication; no key, no discrete log). | `KeyPrivacy.viewA_eq_simViewA` | unconditional |
| One signature determines the key; no correct protocol for this function can hide it perfectly. | `KeyPrivacy.prf_injective_key`, `KeyPrivacy.no_protocol_hides_key_perfectly` | negative |
| For an honest-but-curious A over any number of sessions, on messages chosen by a fixed rule (adaptive choice: `KeyPrivacy.keyRecoveryAdaptive_eq_dlog`), key recovery equals the discrete-log experiment for an explicit solver. | `KeyPrivacy.keyRecovery_eq_dlog`, `KeyPrivacy.keyRecoveryRO_eq_dlog` | reduction |
| The same for an A that chooses messages, oracle queries (answered with exponents) and deviating queries `x • g` adaptively, with the solver sampling the oracle lazily (deviations cover every group element when `g` generates the group). | `KeyPrivacy.keyRecoveryOracle_eq_dlog` | reduction |
| An A that sends arbitrary group elements gets `k • a` for a point of its choice each session; repeated, `kⁿ • a`. | `KeyPrivacy.malicious_query_is_one_signature`, `Limitations.iterate_evaluate` | negative |

### The output is a pseudorandom function (random-oracle model)

| Claim | Theorem | Kind |
|---|---|---|
| An explicit map turns a Diffie–Hellman triple into the real hash-and-value tables, and a non-Diffie–Hellman triple into uniformly random tables. | `PRFSecurity.reduction_real`, `PRFSecurity.reduction_rand` | reduction |
| Every distinguisher that sees the whole hash table and value table (but has no evaluation oracle) has advantage at most the DDH advantage of an explicit distinguisher built from it, plus `1/q`; the same with the public key also in view. | `PRFSecurity.prfAdvantage_le_ddhAdvantage_add`, `PRFSecurity.prfPkAdvantage_le_ddhAdvantage_add` | reduction |
| The same for adaptive oracle adversaries, with lazy sampling. | `PRFSecurity.prfAdvantage_oracle_le` | reduction |
| The real and random worlds are different distributions, so pseudorandomness can only be computational. | `PRFSecurity.prfReal_ne_prfRand` | negative |

### The output is unforgeable (random-oracle model)

| Claim | Theorem | Kind |
|---|---|---|
| Forging a signature on a target message fixed in advance — given the public key, the whole hash table and the signatures on all other messages — equals the Computational Diffie–Hellman experiment for an explicit solver. | `Unforgeability.forge_eq_cdh` | reduction |
| The same for an honest-but-curious A that ran sessions on messages fixed in advance and all different from the target (this restriction is necessary), and for an eavesdropper on others' sessions on messages fixed in advance. | `Unforgeability.hbc_eq_cdh`, `Unforgeability.passive_eq_cdh` | reduction |
| If discrete logs of hash outputs are known, anyone forges from the public key. | `Limitations.forge_of_known_hash_dlog` | negative |

### Checking B's reply

| Claim | Theorem | Kind |
|---|---|---|
| Pairing: public verification accepts exactly the genuine signature; A's check accepts exactly the honest reply; a passing check forces a correct output. | `PublicVerify.verify_iff`, `PublicVerify.checkReply_iff`, `PublicVerify.checked_run` | unconditional |
| Equality proof: honest proofs verify. | `DLEQ.completeness` | unconditional |
| Equality proof: two accepting transcripts with one commitment yield the key relation. | `DLEQ.special_soundness` | unconditional |
| Equality proof: a B that replied dishonestly is accepted with probability at most `1/q`, whatever it does. | `DLEQ.soundness_error` | unconditional |
| Equality proof: an honest verifier's transcript is reproduced exactly by a simulator that does not know the key. | `DLEQ.hvzk` | unconditional |

`BlindPRF/Closed.lean` restates the headline theorems with every hypothesis discharged in a
concrete group, so none of them is true merely because its hypotheses cannot be met.

## What is not proved

- **Hardness.** Discrete log, CDH and DDH are assumptions. They appear only as the right-hand
  side of reductions, never as axioms or hypotheses.
- **Security against an A that deviates from the protocol.** Such an A can make B multiply
  arbitrary group elements by `k`. Bounding what that yields is the one-more Diffie–Hellman
  assumption, and known attacks on such an oracle (Brown–Gallant, Cheon) cost less than a
  discrete log. Neither is formalised. The key-recovery and unforgeability reductions above
  cover honest-but-curious and eavesdropping adversaries only.
- **Efficiency of the reductions and simulators.** Lean has no cost model here. That a solver is
  cheap is a matter of reading its (short) definition. `Audit.lean` checks one proxy: the
  deterministic cores do not use classical choice, so they cannot take a discrete log that way.
  The table-based reductions build one entry per message, so they are cheap only for message
  spaces small enough to tabulate. The lazy-sampling versions give solvers whose definitions touch
  only the queried points (by inspection); the theorems themselves still assume a finite message
  type, because the real experiment samples the whole oracle.
- **A real hash function.** The random oracle is a uniformly random function on a finite message
  type. No concrete hash-to-group map is modelled.
- **The outer hash.** Deployed 2HashDH applies a second hash to `(m, k • H(m))`. It is treated
  as an arbitrary function and nothing is proved about it.
- **Non-interactive equality proofs.** `DLEQ.lean` covers the interactive protocol, with
  honest-verifier zero knowledge. The Fiat–Shamir variant used in practice is not covered.
- **Blindness with a merely statistically sound check.** `Unlinkability.blindness` needs a
  perfectly sound check, which the pairing gives. Combining it with the equality proof, whose
  soundness error is `1/q`, is not proved.
- **Other session schedules.** In the blindness theorems B answers all sessions at once and A
  releases all outputs together. Interleaved or concurrent sessions, and universally composable
  security, are not proved.
- **A concrete pairing group**, and unforgeability of the pairing variant. The pairing is an
  abstract bilinear map; its only instance in the tree is multiplication modulo a prime.
- **Anything about implementations**: group-membership and subgroup checks, cofactors, rejection
  of identity elements, constant-time arithmetic, side channels, randomness quality.
- **Post-quantum security.** The Diffie–Hellman-based statements do not survive a quantum
  adversary. Message privacy and blindness are information-theoretic and are unaffected.

## How to read a reduction here

Adversaries in Lean are arbitrary functions, so they are computationally unbounded. A statement
of the form "every adversary succeeds with small probability" would simply be false: an unbounded
adversary takes the discrete log (`KeyPrivacy.dlogExp_unbounded_solver`). So every computational
claim has the shape

```
attack experiment (adversary)  =  hard-problem experiment (solver built from adversary)
```

as an equality of probability distributions, with the solver given by an explicit definition. If
the problem is hard for efficient solvers and the solver is efficient, the attack fails for
efficient adversaries. The first premise is the assumption; the second is by inspection.

## Obligations on anyone implementing this

The theorems assume, and an implementation must ensure:

- the group has prime order, and received elements are checked to lie in it;
- `H(m)` is never the identity (reject and retry), and `H` behaves like a random oracle whose
  outputs have unknown discrete logs;
- the blinding scalar is nonzero, uniform, and fresh for every session;
- A checks B's reply against a public key that is the same for every client, and releases
  outputs all-or-nothing when running several sessions;
- B limits how many evaluations it performs per key.

## Checking it yourself

```
lake exe cache get          # prebuilt Mathlib, a few minutes
lake build BlindPRF Audit
```

`lake build Audit` fails unless: every file under `BlindPRF/` is imported; every declaration in
the `BlindPRF` namespace depends only on `propext`, `Classical.choice` and `Quot.sound` (so no
`sorry`, no added axiom, no `native_decide`); and the listed simulator and reduction cores do not
use classical choice.

Toolchain `leanprover/lean4:v4.36.0`, Mathlib `v4.36.0`. What you are trusting is the Lean
kernel, Mathlib's definitions, and that the definitions in `Basic.lean` and the experiment
definitions say what this document says they say. The last of these is the part worth reading.

## Files

| File | Content |
|---|---|
| `BlindPRF/Basic.lean` | The protocol as plain functions; the group setting. |
| `BlindPRF/Prob.lean` | Uniform distributions on finite types. |
| `BlindPRF/Correctness.lean` | Correctness. |
| `BlindPRF/Blindness.lean` | Message privacy against B. |
| `BlindPRF/Unlinkability.lean` | The blindness game against a malicious signer; tagging and selective-abort attacks. |
| `BlindPRF/KeyPrivacy.lean` | Simulation; impossibility of perfect key hiding; reduction to discrete log. |
| `BlindPRF/PRFSecurity.lean` | Pseudorandomness as a reduction to DDH. |
| `BlindPRF/Unforgeability.lean` | Unforgeability as a reduction to CDH. |
| `BlindPRF/PublicVerify.lean` | Pairing-based verification. |
| `BlindPRF/DLEQ.lean` | Chaum–Pedersen equality proof. |
| `BlindPRF/Limitations.lean` | Negative results. |
| `BlindPRF/Instance.lean` | Two concrete models, with executable tests. |
| `BlindPRF/Closed.lean` | Headline theorems with all hypotheses discharged. |
| `Audit.lean` | The trust-base checks. |
