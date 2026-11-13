module

import ProjectAInos
import Lean.Util.CollectAxioms

/-! Root visibility and transitive axiom audit for the qubit prototype. -/

open ProjectAInos.QuantumMechanics.Qubit
open Lean Elab Command

#check pairing_eq_inner
#check projector_finrank
#check projector_eq_iff_ray
#check expectation_rescale
#check vectorState_expectation
#check expectation_real
#check rayEquivRankOneProjectors
#check rayState_injective
#check pauli_born
#check pauli_probability_mem_Icc
#check pauli_probabilities_sum
#check yPlus_probabilities

#print axioms rayEquivRankOneProjectors
#print axioms vectorState_expectation
#print axioms pauli_probability_mem_Icc
#print axioms yPlus_probabilities

run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants do
    if (`ProjectAInos.QuantumMechanics).isPrefixOf (privateToUserName name) then
      count := count + 1
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "{name} depends on disallowed axiom {axiomName}"
  unless count > 0 do
    throwError "No QuantumMechanics declarations were imported by the root"
  logInfo m!"Quantum axiom audit passed for {count} declarations."
