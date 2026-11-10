import ProjectAInos
import Lean.Util.CollectAxioms

/-!
Local counterpart of the CI transitive axiom audit. Run after building the root:
`lake env lean -DwarningAsError=true checks/AxiomAudit.lean`.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  let mut smoothCount : Nat := 0
  for (name, _) in env.constants do
    let userName := privateToUserName name
    if (`ProjectAInos).isPrefixOf userName then
      count := count + 1
      if (`ProjectAInos.Variational.SmoothAlgebra).isPrefixOf userName then
        smoothCount := smoothCount + 1
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "{name} depends on disallowed axiom {axiomName}"
  unless count > 0 ∧ smoothCount > 0 do
    throwError "Audit found no project declarations or no smooth-algebra declarations"
  logInfo m!"Axiom audit passed for {count} project declarations, including {smoothCount} smooth-algebra declarations."
