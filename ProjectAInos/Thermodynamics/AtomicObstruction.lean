module
public import ProjectAInos.Thermodynamics.AtomicProcesses

/-! # A checked obstruction to atomic-only mixing (issue #27) -/
@[expose] public section
noncomputable section
open scoped NNReal
namespace ProjectAInos.Thermodynamics.Physical.AtomicReservoir

def atomicHeating := Nonreactive.accessibility domains.State
  (fun _ x y => x.val.1 ≤ y.val.1)

/-- This extensive convex diagnostic requires no continuous atomic topology. -/
def excess : Raw →+ ℝ := CompositeState.label (fun a => max (a.2.val.1 - 5/2) 0)

@[simp] theorem excess_atom (u : Energy) : excess (atom u) = max (u.val - 5/2) 0 := rfl
@[simp] theorem excess_scale (r : ℝ≥0) (x : Raw) : excess (r • x) = (r : ℝ) * excess x :=
  CompositeState.label_scale _ r x

theorem atomicHeating_excess_le {x y : Raw} (h : atomicHeating.relation x y) :
    excess x ≤ excess y := by
  apply Nonreactive.Generated.eval_le excess (fun r x => excess_scale r x) _ h
  intro x y h
  cases h with
  | atom h => exact max_le_max (sub_le_sub_right h _) le_rfl

def energyOne : Energy := ⟨1, by norm_num⟩
def energyTwo : Energy := ⟨2, by norm_num⟩
def energyThree : Energy := ⟨3, by norm_num⟩

/-- A7 would require this process, but every atomic-only generated process
increases `excess`, which here would have to decrease from 1/4 to zero. -/
theorem atomicOnly_mixing_impossible :
    ¬ atomicHeating.relation
      ((1/2 : ℝ≥0) • atom energyOne + (1/2 : ℝ≥0) • atom energyThree)
      (atom energyTwo) := by
  intro h
  have hh := atomicHeating_excess_le h
  norm_num [energyOne, energyTwo, energyThree] at hh

/-- The composite model contains the genuine mixing process obstructed above. -/
theorem mixing_example :
    accessibility.relation
      ((1/2 : ℝ≥0) • atom energyOne + (1/2 : ℝ≥0) • atom energyThree)
      (atom energyTwo) := by
  rw [relation_iff]
  norm_num [energyOne, energyTwo, energyThree]

theorem mixing_raw_distinct :
    (1/2 : ℝ≥0) • atom energyOne + (1/2 : ℝ≥0) • atom energyThree ≠ atom energyTwo := by
  intro h
  have hh := congrArg excess h
  norm_num [energyOne, energyTwo, energyThree] at hh

theorem heating_irreversible :
    accessibility.relation (atom energyOne) (atom energyTwo) ∧
    ¬ accessibility.relation (atom energyTwo) (atom energyOne) := by
  simp [relation_iff, energyOne, energyTwo]

end ProjectAInos.Thermodynamics.Physical.AtomicReservoir
