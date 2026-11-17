import ProjectAinos
import Lean.Util.CollectAxioms

/-!
Transitive axiom audit for the assembled project. Run after building the root:
`lake env lean -DwarningAsError=true checks/AxiomAudit.lean`.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  let mut smoothCount : Nat := 0
  let mut geometryCount : Nat := 0
  let mut mechanicsCount : Nat := 0
  let mut relativityCount : Nat := 0
  let mut generalRelativityCount : Nat := 0
  let mut electrodynamicsCount : Nat := 0
  let mut yangMillsCount : Nat := 0
  for (name, _) in env.constants do
    let some idx := env.getModuleIdxFor? name | continue
    let modName := modules[idx.toNat]!
    if (`ProjectAinos).isPrefixOf modName then
      count := count + 1
      if (`ProjectAinos.External.YM).isPrefixOf modName then
        yangMillsCount := yangMillsCount + 1
      if (`ProjectAinos.SmoothAlgebra).isPrefixOf modName then
        smoothCount := smoothCount + 1
      if (`ProjectAinos.SmoothGeometry).isPrefixOf modName then
        geometryCount := geometryCount + 1
      if (`ProjectAinos.Mechanics).isPrefixOf modName then
        mechanicsCount := mechanicsCount + 1
      if (`ProjectAinos.SpecialRelativity).isPrefixOf modName then
        relativityCount := relativityCount + 1
      if (`ProjectAinos.GeneralRelativity).isPrefixOf modName then
        generalRelativityCount := generalRelativityCount + 1
      if (`ProjectAinos.Electrodynamics).isPrefixOf modName then
        electrodynamicsCount := electrodynamicsCount + 1
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "{name} depends on disallowed axiom {axiomName}"
  unless count > 0 ∧ smoothCount > 0 ∧ geometryCount > 0 ∧ mechanicsCount > 0 ∧ relativityCount > 0 do
    throwError "Audit found no project, smooth-algebra, smooth-geometry, mechanics, or special-relativity declarations"
  unless yangMillsCount > 0 do
    throwError "Audit found no Yang–Mills declarations"
  unless electrodynamicsCount > 0 do
    throwError "Audit found no electrodynamics declarations"
  unless generalRelativityCount > 0 do
    throwError "Audit found no general-relativity declarations"
  logInfo m!"Axiom audit passed for {count} project declarations, including {smoothCount} smooth-algebra, {geometryCount} smooth-geometry, {mechanicsCount} mechanics, {relativityCount} special-relativity, {generalRelativityCount} general-relativity, {electrodynamicsCount} electrodynamics, and {yangMillsCount} Yang–Mills declarations."
