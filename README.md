# Blindfolded

Party A holds a message. Party B holds a secret key. Blindfolded lets A obtain B's signature on
the message without B seeing it: A sends the message with a random blinding factor applied, B
evaluates its keyed function on what it receives, and A strips the blinding factor to get the
result.

```
A holds m, picks a fresh random r ≠ 0          B holds key k, has published pk = k • g
a := r • H(m)            ── a ──▶
                         ◀── b ──              b := k • a
A checks b against pk, then
σ := r⁻¹ • b   =   k • H(m)
```

The construction is the blinded Diffie–Hellman PRF at the core of 2HashDH (Jarecki–Kiayias–
Krawczyk; RFC 9497), with an optional pairing-based check (blind BLS) and a Chaum–Pedersen proof
that B used its committed key. Blindfolded does not introduce a new protocol. It provides a
machine-checked account of what this one does and does not guarantee, and an implementation that
follows that account.

- **[`lean/`](lean/)** — the formal specification and proofs in Lean 4 + Mathlib. They cover
  correctness, message privacy against B, blindness against a malicious signer, simulation-based
  key privacy, and reductions to discrete log, CDH and DDH, plus negative results for the ways it
  fails. There is no `sorry`, and the build fails on any non-standard axiom.
  **Start with [`lean/README.md`](lean/README.md)**: it states exactly what is and is not proved.
- **`rust/`** — *planned:* an implementation that follows the Lean specification, to be
  published as the `blindfolded` crate.

## Before relying on it

1. The signature determines the key, so "A learns nothing about the key" is false in the
   absolute sense and is not claimed. What is proved: A learns nothing beyond the signature, and
   recovering the key is exactly the discrete-log problem.
2. Without a check on B's reply, B can link sessions to signatures. The check is part of the
   protocol.
3. Machine-verified is not the same as secure: security rests on discrete-log and Diffie–Hellman
   hardness in the concrete group, which no proof assistant can establish.

## License

MIT — see [LICENSE](LICENSE).
