module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.Linarith

/-!
# Unique splitting with an affine joined entropy

At fixed work coordinates, a linear reservoir entropy and a logarithmic body
entropy have a unique maximizing energy allocation. Nevertheless the maximized
joined entropy is affine in total energy, and two copies of that joined energy
function have every allocation as a maximizer.

This is a diagnostic energy-allocation example, not a construction of a full
thermal family satisfying all physical axioms. It prevents treating uniqueness
of a split alone as a proof of nonconstant joined temperature.
-/

@[expose] public section

namespace ProjectAInos.Thermodynamics.ThermalSplitExample

/-- Total entropy when a logarithmic body has positive energy `u` and the
linear reservoir has the remaining unrestricted energy `E - u`. -/
noncomputable def allocationEntropy (E u : ℝ) : ℝ := E - u + Real.log u

/-- The maximum entropy after thermal equilibration at fixed total energy. -/
def joinedEntropy (E : ℝ) : ℝ := E - 1

theorem allocationEntropy_le (E : ℝ) {u : ℝ} (hu : 0 < u) :
    allocationEntropy E u ≤ joinedEntropy E := by
  dsimp [allocationEntropy, joinedEntropy]
  linarith [Real.log_le_sub_one_of_pos hu]

/-- The equilibrium split is unique for every total energy. -/
theorem allocationEntropy_eq_iff (E : ℝ) {u : ℝ} (hu : 0 < u) :
    allocationEntropy E u = joinedEntropy E ↔ u = 1 := by
  constructor
  · intro heq
    by_contra hne
    have h := Real.log_lt_sub_one_of_pos hu hne
    dsimp [allocationEntropy, joinedEntropy] at heq
    linarith
  · rintro rfl
    simp [allocationEntropy, joinedEntropy]

/-- In contrast, splitting energy between two copies of the joined system
leaves their total entropy unchanged. -/
theorem joined_pair_entropy_constant (E u : ℝ) :
    joinedEntropy u + joinedEntropy (E - u) = E - 2 := by
  dsimp [joinedEntropy]
  ring

/-- The maximum-entropy thermal criterion for two joined copies is universal,
although the original reservoir/body split was unique. -/
theorem joined_pair_maximum (E u : ℝ) :
    IsMaxOn (fun v => joinedEntropy v + joinedEntropy (E - v)) Set.univ u := by
  intro v _
  change joinedEntropy v + joinedEntropy (E - v) ≤ joinedEntropy u + joinedEntropy (E - u)
  rw [joined_pair_entropy_constant, joined_pair_entropy_constant]

end ProjectAInos.Thermodynamics.ThermalSplitExample
