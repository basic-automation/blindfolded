# Blind PRF signing — a Lean 4 verified protocol

**Status: work in progress.** The modules listed under "Proven so far" build with zero `sorry`
and pass the axiom audit. The modules under "In progress" are not in the tree yet; nothing about
them is claimed here.

## The problem

Party **A** holds a message `m`. Party **B** holds a secret key `k`. A wants a signature on `m`
under B's key such that B learns nothing about `m` and A learns nothing about `k` beyond the
signature itself.

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

| File | Content |
|---|---|
| `BlindPRF/Basic.lean` | The protocol as plain functions; the group setting (`IsGenerator`). |
| `BlindPRF/Prob.lean` | Uniform distributions on finite types; bijection, fibre and marginal rules. |
| `BlindPRF/Correctness.lean` | An honest run outputs exactly `k • H(m)`, for every key, message and nonzero coin. |
| `BlindPRF/PublicVerify.lean` | Optional pairing layer ("blind BLS"): public verification is complete and accepts only the genuine signature; A's check on B's reply accepts only the honest reply. |
| `BlindPRF/Instance.lean` | Two concrete models satisfying every hypothesis (a toy group, and the order-11 subgroup of `(ℤ/23)ˣ`), with executable end-to-end tests. |
| `Audit.lean` | Fails the build unless every declaration depends only on `propext`, `Classical.choice`, `Quot.sound`. |

## In progress

Message privacy against B, key privacy against A, PRF security, and a pairing-free
accountability proof for B.

## Build

```
lake exe cache get      # prebuilt Mathlib
lake build BlindPRF Audit
```

Toolchain: `leanprover/lean4:v4.36.0`, Mathlib `v4.36.0`.
