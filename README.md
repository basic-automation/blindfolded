# Blind PRF signing — a Lean 4 verified protocol

**Status: work in progress.** Everything in the tree is machine-checked; seven modules are
still going through adversarial review, as marked below.

## The problem

Party **A** holds a message `m`. Party **B** holds a secret key `k`. A wants a signature on `m`
under B's key, without showing `m` to B and without being handed `k`.

One caveat shapes everything that follows. The signature `k • H(m)` determines `k`
mathematically, so "A learns nothing about the key" is false in the absolute sense for any
protocol that computes this function, and it is not claimed here. What is proven instead is that
the protocol gives A nothing beyond the signature, and that recovering `k` from what an
honest-but-curious A sees is exactly the discrete-logarithm problem.

## The protocol

A blinded Diffie–Hellman pseudorandom function (the core of the 2HashDH oblivious PRF used in
RFC 9497). `G` is a cyclic group of prime order `q`, written additively; scalars live in the
field `F = ℤ/q`; `H` hashes messages into `G`.

```
A holds m, picks random r ≠ 0            B holds key k
a := r • H(m)          ── a ──▶
                       ◀── b ──          b := k • a
σ := r⁻¹ • b  =  k • H(m)
```

The signature is `σ = k • H(m)`.

## Proven so far

Every module below compiles with zero `sorry`, and the whole tree passes the axiom audit
(535 declarations, 404 theorems, standard axioms only).

Reviewed and final:

| File | Content |
|---|---|
| `BlindPRF/Basic.lean` | The protocol as plain functions; the group setting (`IsGenerator`). |
| `BlindPRF/Prob.lean` | Uniform distributions on finite types; bijection, fibre and marginal rules. |
| `BlindPRF/Correctness.lean` | An honest run outputs exactly `k • H(m)`, for every key, message and nonzero coin. |
| `BlindPRF/PublicVerify.lean` | Optional pairing layer ("blind BLS"): public verification is complete and accepts only the genuine signature; A's check on B's reply accepts only the honest reply. |
| `BlindPRF/Instance.lean` | Two concrete models satisfying every hypothesis (a toy group, and the order-11 subgroup of `(ℤ/23)ˣ`), with executable tests. |
| `Audit.lean` | Fails the build on any un-imported proof file, or any axiom beyond `propext`, `Classical.choice`, `Quot.sound`. |

Proved and machine-checked, but **adversarial review fixes still pending** — statements and
docstrings may still change, and nothing here should be quoted as final:

| File | Content |
|---|---|
| `BlindPRF/Blindness.lean` | Message privacy against B: B's view has the same distribution for every message. |
| `BlindPRF/Unlinkability.lean` | Two-session blindness game against a malicious signer, with a reply check; the tagging attack without one. |
| `BlindPRF/KeyPrivacy.lean` | What A learns about the key: an explicit simulator, and key recovery as a discrete-log reduction. |
| `BlindPRF/PRFSecurity.lean` | Pseudorandomness as a reduction to Decisional Diffie–Hellman (random-oracle model). |
| `BlindPRF/Unforgeability.lean` | Passive unforgeability as a reduction to Computational Diffie–Hellman. |
| `BlindPRF/DLEQ.lean` | Chaum–Pedersen proof that B used the committed key. |
| `BlindPRF/Limitations.lean` | Negative results: what the protocol does not give. |

## Build

```
lake exe cache get      # prebuilt Mathlib
lake build BlindPRF Audit
```

Toolchain: `leanprover/lean4:v4.36.0`, Mathlib `v4.36.0`.
