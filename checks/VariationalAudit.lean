import ProjectAInos
import Lean

/-! Run with `lake env lean checks/VariationalAudit.lean` after building the root.
This checks transitive axiom dependencies of every declaration in the project
namespace, including the prototype. It is a local review check, not a CI change.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  let mut prototypeCount : Nat := 0
  for (name, _) in env.constants.toList do
    if (`ProjectAInos).isPrefixOf name then
      count := count + 1
      if (`ProjectAInos.Variational).isPrefixOf name then
        prototypeCount := prototypeCount + 1
      let axioms ← Lean.collectAxioms name
      let unexpected := axioms.filter fun ax => !allowed.contains ax
      unless unexpected.isEmpty do
        throwError "Unexpected transitive axioms for {name}: {unexpected}"
  if prototypeCount == 0 then
    throwError "No prototype declarations were imported"
  logInfo m!"Axiom audit passed: {count} project declarations, including {prototypeCount} variational declarations."
  logInfo "Allowed axioms: propext, Classical.choice, Quot.sound."

#print axioms ProjectAInos.Variational.hasDerivAt_action
#print axioms ProjectAInos.Variational.interval_firstVariation_identity
#print axioms ProjectAInos.Variational.finite_firstVariation_identity
#print axioms ProjectAInos.Variational.mechanics_quadratic_hasDerivAt
#print axioms ProjectAInos.Variational.spacetime_quadratic_hasDerivAt
