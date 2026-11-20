# Blindfolded

**Get a signature on data the signer never sees.**

Blindfolded is a blind-signing protocol. A client holds a message; a server holds a secret key.
The client gets the server's signature on the message, and the server never learns what it
signed. The server's key never leaves the server.

Every security claim Blindfolded makes is backed by a machine-checked proof.

> **Status:** the specification and proofs are complete. The Rust library is in development and
> is not yet available. Watch this repository for the first release.

---

## Why you would use it

Some services need to vouch for something without being able to see it, or without being able to
connect it back to who asked.

- **Anonymous access tokens.** Issue a token to a verified user, then accept it later without
  being able to tell which user it was issued to. This is the idea behind Privacy Pass.
- **Private lookups.** Let a client check whether its data (a password, an identifier, a file
  hash) appears in your database without sending you the data itself.
- **Password protection.** Harden passwords with a server-side key so a stolen database can't be
  cracked offline, while the server never receives the password. This is the building block
  behind OPAQUE.
- **Rate limiting without tracking.** Hand out a fixed number of unlinkable tokens per user per
  day.

## How it works

```
Client                                        Server
holds a message                               holds a secret key

1. Scramble the message with a
   fresh random value              ──────▶   2. Apply the secret key to
                                                  whatever arrives
3. Check the reply, then
   unscramble it                   ◀──────

Result: the server's signature on the original message.
```

The server only ever sees a scrambled value that looks completely random, so it learns nothing
about the message. The client only ever receives the signature it asked for, so it learns nothing
about the key beyond that signature.

Blindfolded is built on a well-studied, standardized construction: the oblivious pseudorandom
function from [RFC 9497](https://www.rfc-editor.org/rfc/rfc9497), also known as 2HashDH. Two
optional additions let clients confirm that the server used the same key for everyone:

- **Pairing check**: anyone can verify a signature against the server's public key.
- **Equality proof**: the server proves, without revealing its key, that each reply was made with
  its published key.

## What is guaranteed

Each of these is a proved theorem, not a test result.

| Guarantee | Strength |
|---|---|
| The client always ends up with the correct signature. | Always holds. |
| The server learns nothing about the message during signing. | Holds against any attacker, however powerful. |
| A server that checks its replies cannot later tell which client a signature came from, for any number of clients. | Holds against any attacker, however powerful. |
| The client learns nothing about the key beyond the signatures it receives. | Holds against any attacker, however powerful. |
| Recovering the server's key, forging a signature, or telling signatures apart from random is as hard as standard, widely trusted problems (discrete logarithm and Diffie–Hellman). | Holds as long as those problems stay hard. |

The proofs are written in [Lean 4](https://lean-lang.org/), a proof assistant that checks every
step mechanically. They contain no gaps, and the build fails automatically if one is ever
introduced.

## What you need to know

Strong guarantees come with conditions. These are part of using Blindfolded correctly:

- **Clients must check the server's reply.** Without that check, a dishonest server could use a
  different key for each client and later recognise their signatures. The check is built into the
  protocol; don't skip it.
- **Showing a signature reveals its message.** Blindfolded hides which client a signature came
  from, not what the message was: the server can confirm a message and signature it is shown. If
  the message itself must stay secret, never show it to the server alongside its signature.
- **Release signatures together.** A client running several sessions at once should keep all
  results, or none, if any session fails.
- **Limit requests per key.** A misbehaving client can send crafted inputs that make the server's
  key slightly easier to attack over many queries. Rate-limit signing and rotate keys.
- **Not quantum-resistant.** The privacy guarantees survive a quantum computer; the
  unforgeability guarantees do not.
- **Proofs cover the design, not the code.** The Rust library will follow the proven
  specification, but implementation bugs and side channels are outside what the proofs cover.

The full list of what is proved, and what is not, is in
[`lean/README.md`](lean/README.md).

## Repository

| Directory | Contents |
|---|---|
| [`lean/`](lean/) | The formal specification and proofs (Lean 4 + Mathlib). |
| `rust/` | The Rust library: *coming soon*. It will be published on crates.io as `blindfolded`. |

To check the proofs yourself:

```
cd lean
lake exe cache get
lake build BlindPRF Audit
```

## License

MIT. See [LICENSE](LICENSE).
