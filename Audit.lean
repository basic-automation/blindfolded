/-
  Audit.lean — machine checks of the trust base.  `lake build Audit` fails unless ALL hold:

  1. Coverage.  Every file `BlindPRF/*.lean` on disk is imported (directly or transitively) by
     `BlindPRF.lean`.  Without this, a file containing `sorry` that nobody imports would escape
     check 2.

  2. Axioms.  Every declaration in the `BlindPRF` namespace depends on no axioms beyond Lean's
     three standard ones (`propext`, `Classical.choice`, `Quot.sound`).  In particular this
     rejects any `sorry` (`sorryAx`), any user-declared `axiom`, and any `native_decide`
     (`Lean.ofReduceBool` / `Lean.trustCompiler`).

  3. Explicit simulators and reductions.  The deterministic cores of the simulators and
     reductions (listed at the bottom) do not depend on `Classical.choice` at all.  Lean has no
     cost model, so "the simulator is efficient" cannot be stated; this check is a proxy that
     rules out one specific way of cheating — a "simulator" that obtains the secret key by
     taking a discrete logarithm through the classical inverse of `c ↦ c • g`.  It does not
     prove efficiency: that remains a matter of reading the (short) definitions.
-/
import BlindPRF

open Lean Elab Command

/-- Check 1: every `BlindPRF/*.lean` file is part of the build that is being audited. -/
elab "#audit_blindprf_coverage" : command => do
  let env ← getEnv
  let dir : System.FilePath := "BlindPRF"
  unless ← dir.isDir do
    throwError "coverage audit: directory `BlindPRF` not found relative to the working \
      directory; run from the package root (`lake build Audit`)"
  let mut missing : Array Name := #[]
  let mut seen : Nat := 0
  for entry in ← dir.readDir do
    if entry.path.extension == some "lean" then
      seen := seen + 1
      let modName := Name.mkStr `BlindPRF (entry.path.fileStem.getD "")
      unless env.header.moduleNames.contains modName do
        missing := missing.push modName
  if seen == 0 then
    throwError "coverage audit: no source files found in `BlindPRF/`"
  if missing.isEmpty then
    logInfo m!"coverage audit passed: all {seen} files in BlindPRF/ are imported by BlindPRF.lean"
  else
    throwError "coverage audit FAILED: these files are not imported by BlindPRF.lean and are \
      therefore not audited: {missing}"

/-- Check 2: every `BlindPRF.*` declaration uses only the three standard axioms. -/
elab "#audit_blindprf_axioms" : command => do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  let mut theorems : Nat := 0
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

/-- Check 3: the listed definitions do not depend on `Classical.choice`. -/
elab "#audit_choice_free " ids:ident+ : command => do
  let mut bad : Array (Name × Array Name) := #[]
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let axs ← Lean.collectAxioms n
    let extra := axs.filter fun a => a != ``propext && a != ``Quot.sound
    if !extra.isEmpty then bad := bad.push (n, extra)
  if bad.isEmpty then
    logInfo m!"choice-free audit passed: {ids.size} simulator/reduction cores use no \
      Classical.choice"
  else
    throwError "choice-free audit FAILED: {bad}"

/-- Control for check 3: assert that a definition DOES depend on `Classical.choice`.  Used to
show that check 3 can fail: the discrete-logarithm bijection is caught by it. -/
elab "#audit_expect_choice " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axs ← Lean.collectAxioms n
  if axs.contains ``Classical.choice then
    logInfo m!"control passed: {n} depends on Classical.choice, as expected"
  else
    throwError "control FAILED: {n} was expected to depend on Classical.choice"

#audit_blindprf_coverage
#audit_blindprf_axioms

-- Check 3.  Simulators: what a party's view is rebuilt from, without the secret.
#audit_choice_free
  BlindPRF.KeyPrivacy.simReply BlindPRF.KeyPrivacy.simViewA BlindPRF.KeyPrivacy.viewsSim
  BlindPRF.KeyPrivacy.forgetExponents BlindPRF.KeyPrivacy.viewsKESim
  BlindPRF.KeyPrivacy.simInteractiveChoose BlindPRF.KeyPrivacy.Strategy.mapAns
  BlindPRF.DLEQ.simulate BlindPRF.DLEQ.extract

-- Check 3.  Reductions: how a hard-problem instance is turned into the adversary's input.
#audit_choice_free
  BlindPRF.PRFSecurity.reductionCore BlindPRF.PRFSecurity.reductionPkCore
  BlindPRF.PRFSecurity.reductionEntry
  BlindPRF.Unforgeability.cdhSolverInput BlindPRF.Unforgeability.solverInput
  BlindPRF.Unforgeability.hbcSimInput BlindPRF.Unforgeability.wireSim
  BlindPRF.Unforgeability.leakCore

-- Control: the discrete-logarithm bijection `F ≃ G` is exactly what check 3 is meant to catch.
#audit_expect_choice BlindPRF.IsGenerator.equiv
