module

public import ProjectAInos.Thermodynamics.Basic
public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Cancellation of spectator systems

Stability implies cancellation when composition and nonnegative scaling
preserve adiabatic accessibility.
-/

@[expose] public section

open Filter
open scoped NNReal Topology

namespace ProjectAInos.Thermodynamics

variable {M : Type*} [AddCommMonoid M] [PartialOrder M] [Module ℝ≥0 M]
  [IsOrderedAddMonoid M] [PosSMulMono ℝ≥0 M]

/-- A spectator can be removed from an accessible process by stability. -/
theorem Stability.le_of_add_le_add_right (hS : Stability M) {x y z : M}
    (h : x + z ≤ y + z) : x ≤ y := by
  have copies (n : ℕ) : n • x + z ≤ n • y + z := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        (n + 1) • x + z = n • x + (x + z) := by simp [add_smul, add_assoc]
        _ ≤ n • x + (y + z) := add_le_add le_rfl h
        _ = y + (n • x + z) := by ac_rfl
        _ ≤ y + (n • y + z) := add_le_add le_rfl ih
        _ = (n + 1) • y + z := by simp [add_smul, add_comm, add_left_comm]
  apply hS x y z z (fun n => 1 / ((n : ℝ≥0) + 1))
  · intro n
    positivity
  · exact tendsto_one_div_add_atTop_nhds_zero_nat
  · intro n
    have hn : (n : ℝ≥0) + 1 ≠ 0 := by positivity
    have hscaled := smul_le_smul_of_nonneg_left (copies (n + 1))
      (show (0 : ℝ≥0) ≤ 1 / ((n : ℝ≥0) + 1) from zero_le)
    simpa only [smul_add, ← Nat.cast_smul_eq_nsmul ℝ≥0, Nat.cast_add,
      Nat.cast_one, smul_smul, one_div_mul_cancel hn, one_smul] using hscaled

/-- Equality cancellation follows from the two order-cancellation directions. -/
theorem Stability.eq_of_add_eq_add_right (hS : Stability M) {x y z : M}
    (h : x + z = y + z) : x = y :=
  le_antisymm (hS.le_of_add_le_add_right h.le) (hS.le_of_add_le_add_right h.ge)

/-- Stability supplies the standard ordered cancellation structure. -/
theorem Stability.isOrderedCancelAddMonoid (hS : Stability M) :
    IsOrderedCancelAddMonoid M where
  le_of_add_le_add_left a b c h :=
    hS.le_of_add_le_add_right (by simpa only [add_comm a] using h)

end ProjectAInos.Thermodynamics
