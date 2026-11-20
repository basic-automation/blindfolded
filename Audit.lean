/-
  Audit.lean — machine check of the trust base.

  `lake build Audit` (or `lake env lean Audit.lean`) fails unless EVERY declaration in the
  `BlindPRF` namespace depends on no axioms beyond Lean's three standard ones
  (`propext`, `Classical.choice`, `Quot.sound`).  In particular it fails on any `sorry`
  (`sorryAx`), any user-declared `axiom`, and any `native_decide` (`Lean.ofReduceBool`).

  It then prints the axioms of the headline theorems one by one, for the record.
-/
import BlindPRF

open Lean Elab Command in
/-- Fail unless every `BlindPRF.*` declaration uses only the three standard axioms. -/
elab "#audit_blindprf_axioms" : command => do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked := 0
  let mut theorems := 0
  let mut bad : Array (Name × Array Name) := #[]
  for (n, ci) in env.constants.toList do
    if (`BlindPRF).isPrefixOf n && !n.isInternal then
      checked := checked + 1
      if ci matches .thmInfo _ then theorems := theorems + 1
      let axs ← Lean.collectAxioms n
      let extra := axs.filter fun a => !allowed.contains a
      if !extra.isEmpty then bad := bad.push (n, extra)
  if bad.isEmpty then
    logInfo m!"axiom audit passed: {checked} declarations in namespace BlindPRF \
      ({theorems} theorems) depend only on propext, Classical.choice, Quot.sound"
  else
    throwError "axiom audit FAILED: {bad}"

#audit_blindprf_axioms
