/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Mechanics.Oscillations.ParametricTrace
public import ProjectAinos.Mechanics.Oscillations.Damped
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Constant coefficients as instances of the stability criterion

A constant coefficient has every period, so the theorems of `ParametricTrace`
apply to it with their hypotheses proved. The three cases of the trace of the
monodromy matrix occur:

* `ẍ + ω² x = 0`: with the period `π/(2|ω|)` the trace is zero, and every
  solution is bounded;
* `ẍ = 0`: the monodromy matrix is `!![1, T; 0, 1]`, of trace two and different
  from one, and a solution is bounded exactly when its velocity vanishes;
* `ẍ = κ² x`: the trace is `2 cosh κT > 2`, and there is an unbounded solution.
-/

@[expose] public section

noncomputable section

namespace ProjectAinos.Mechanics.Parametric

open Matrix SmoothAlgebra

/-- A constant coefficient has every period. -/
theorem shift_algebraMap (T c : ℝ) :
    TimeFunction.shift T (algebraMap ℝ TimeFunction c) = algebraMap ℝ TimeFunction c := by
  refine TimeFunction.ext_apply_const fun t => ?_
  rw [TimeFunction.shift_apply, TimeFunction.algebraMap_apply, TimeFunction.algebraMap_apply]

/-! ### The oscillator -/

/-- The criterion applied to the oscillator: every solution of `ẍ + ω² x = 0` is
bounded, since the trace of the monodromy matrix over the period `π/(2|ω|)` is
zero. -/
theorem exists_abs_apply_le_harmonic {ω : ℝ} (hω : ω ≠ 0) {x : TimeFunction}
    (hx : IsHill (algebraMap ℝ TimeFunction (ω ^ 2)) x) :
    ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t → |x fun _ => t| ≤ B := by
  have hT : 0 < Real.pi / (2 * |ω|) := by
    have := abs_pos.mpr hω
    positivity
  refine (forall_isHill_bounded_iff (shift_algebraMap _ _) hT).mpr (Or.inl ?_) x hx
  rw [trace_monodromy_harmonic hω]
  have hcos : Real.cos (ω * (Real.pi / (2 * |ω|))) = 0 := by
    rcases lt_or_gt_of_ne hω with h | h
    · rw [abs_of_neg h]
      have e : ω * (Real.pi / (2 * -ω)) = -(Real.pi / 2) := by
        field_simp
      rw [e, Real.cos_neg, Real.cos_pi_div_two]
    · rw [abs_of_pos h]
      have e : ω * (Real.pi / (2 * ω)) = Real.pi / 2 := by
        field_simp
      rw [e, Real.cos_pi_div_two]
  rw [hcos]
  norm_num

/-! ### Free motion -/

/-- The fundamental system `1`, `t` of `ẍ = 0`. -/
def FundamentalSystem.free : FundamentalSystem (algebraMap ℝ TimeFunction 0) where
  x₁ := 1
  x₂ := TimeFunction.time
  isHill₁ := by
    unfold IsHill
    simp
  isHill₂ := by
    unfold IsHill
    rw [TimeFunction.timeDerivative_time]
    simp
  x₁_zero := rfl
  dx₁_zero := by simp
  x₂_zero := rfl
  dx₂_zero := by
    rw [TimeFunction.timeDerivative_time]
    rfl

/-- The monodromy matrix of free motion. -/
theorem monodromy_free (T : ℝ) :
    monodromy (algebraMap ℝ TimeFunction 0) T = !![1, T; 0, 1] := by
  rw [← FundamentalSystem.free.matrix_eq_monodromy]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [FundamentalSystem.matrix, FundamentalSystem.free, TimeFunction.timeDerivative_time]

theorem trace_monodromy_free (T : ℝ) :
    (monodromy (algebraMap ℝ TimeFunction 0) T).trace = 2 * 1 := by
  rw [monodromy_free, Matrix.trace_fin_two]
  simp
  norm_num

/-- The parabolic case in an instance: a solution of `ẍ = 0` is bounded for
`t ≥ 0` exactly when its velocity at time zero vanishes. -/
theorem IsHill.exists_abs_apply_le_free_iff {x : TimeFunction}
    (hx : IsHill (algebraMap ℝ TimeFunction 0) x) :
    (∃ B : ℝ, ∀ t : ℝ, 0 ≤ t → |x fun _ => t| ≤ B) ↔ timeDerivative x (fun _ => 0) = 0 := by
  rw [hx.exists_abs_apply_le_iff_of_trace_eq (T := 1) (σ := 1) (shift_algebraMap 1 0) one_pos
    (by norm_num) (trace_monodromy_free 1), monodromy_free, one_smul]
  constructor
  · intro h
    have h0 := congrFun h 0
    simpa [state, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h0
  · intro h
    ext i
    fin_cases i <;> simp [state, Matrix.mulVec, dotProduct, Fin.sum_univ_two, h]

/-- Free motion has an unbounded solution. -/
theorem exists_isHill_free_not_bounded :
    ∃ x, IsHill (algebraMap ℝ TimeFunction 0) x ∧
      ¬ ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t → |x fun _ => t| ≤ B := by
  apply exists_isHill_not_bounded_of_trace_eq (T := 1) (σ := 1) (shift_algebraMap 1 0) one_pos
    (by norm_num) (trace_monodromy_free 1)
  rw [monodromy_free, one_smul]
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp at h01

/-! ### A repulsive linear force -/

theorem isHill_expMul (κ : ℝ) :
    IsHill (algebraMap ℝ TimeFunction (-(κ ^ 2))) (TimeFunction.expMul κ) := by
  unfold IsHill
  rw [TimeFunction.timeDerivative_expMul, SmoothDerivation.map_algebraMap_mul, smul_eq_mul,
    TimeFunction.timeDerivative_expMul]
  refine TimeFunction.ext_apply_const fun t => ?_
  simp only [TimeFunction.mul_apply, TimeFunction.algebraMap_apply, TimeFunction.neg_apply]
  ring

theorem isHill_expMul_neg (κ : ℝ) :
    IsHill (algebraMap ℝ TimeFunction (-(κ ^ 2))) (TimeFunction.expMul (-κ)) := by
  have h := isHill_expMul (-κ)
  rwa [neg_sq] at h

/-- The fundamental system `cosh κt`, `sinh κt / κ` of `ẍ = κ² x`. -/
def FundamentalSystem.hyperbolic {κ : ℝ} (hκ : κ ≠ 0) :
    FundamentalSystem (algebraMap ℝ TimeFunction (-(κ ^ 2))) where
  x₁ := algebraMap ℝ TimeFunction (1 / 2) *
    (TimeFunction.expMul κ + TimeFunction.expMul (-κ))
  x₂ := algebraMap ℝ TimeFunction (1 / (2 * κ)) *
    (TimeFunction.expMul κ + algebraMap ℝ TimeFunction (-1) * TimeFunction.expMul (-κ))
  isHill₁ := ((isHill_expMul κ).add (isHill_expMul_neg κ)).const_mul _
  isHill₂ := ((isHill_expMul κ).add ((isHill_expMul_neg κ).const_mul _)).const_mul _
  x₁_zero := by
    simp [TimeFunction.mul_apply, TimeFunction.add_apply, TimeFunction.algebraMap_apply]
    norm_num
  dx₁_zero := by
    rw [SmoothDerivation.map_algebraMap_mul, map_add, TimeFunction.timeDerivative_expMul,
      TimeFunction.timeDerivative_expMul]
    simp [TimeFunction.mul_apply, TimeFunction.add_apply, TimeFunction.algebraMap_apply]
  x₂_zero := by
    simp [TimeFunction.mul_apply, TimeFunction.add_apply, TimeFunction.algebraMap_apply]
  dx₂_zero := by
    rw [SmoothDerivation.map_algebraMap_mul, map_add, SmoothDerivation.map_algebraMap_mul,
      TimeFunction.timeDerivative_expMul, TimeFunction.timeDerivative_expMul]
    simp [TimeFunction.mul_apply, TimeFunction.add_apply, TimeFunction.algebraMap_apply]
    field_simp
    ring

/-- The trace of the monodromy matrix of `ẍ = κ² x` is `2 cosh κT`. -/
theorem trace_monodromy_hyperbolic {κ : ℝ} (hκ : κ ≠ 0) (T : ℝ) :
    (monodromy (algebraMap ℝ TimeFunction (-(κ ^ 2))) T).trace = 2 * Real.cosh (κ * T) := by
  rw [← (FundamentalSystem.hyperbolic hκ).matrix_eq_monodromy, Matrix.trace_fin_two]
  simp only [FundamentalSystem.matrix, FundamentalSystem.hyperbolic, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [SmoothDerivation.map_algebraMap_mul, map_add, SmoothDerivation.map_algebraMap_mul,
    TimeFunction.timeDerivative_expMul, TimeFunction.timeDerivative_expMul]
  simp only [smul_eq_mul, TimeFunction.mul_apply, TimeFunction.add_apply,
    TimeFunction.algebraMap_apply, TimeFunction.expMul_apply, Real.cosh_eq]
  field_simp
  ring

/-- The hyperbolic case in an instance: `ẍ = κ² x` has an unbounded solution. -/
theorem exists_isHill_hyperbolic_not_bounded {κ : ℝ} (hκ : κ ≠ 0) :
    ∃ x, IsHill (algebraMap ℝ TimeFunction (-(κ ^ 2))) x ∧
      ¬ ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t → |x fun _ => t| ≤ B := by
  apply exists_isHill_not_bounded_of_two_lt_abs_trace (T := 1) (shift_algebraMap 1 _) one_pos
  rw [trace_monodromy_hyperbolic hκ, mul_one]
  have h := Real.one_lt_cosh.mpr hκ
  rw [abs_of_pos (by linarith)]
  linarith

/-- The bounded solutions of `ẍ = κ² x`: those whose state at time zero is an
eigenvector of the monodromy matrix with an eigenvalue of absolute value less
than one. -/
theorem IsHill.exists_abs_apply_le_hyperbolic_iff {κ : ℝ} (hκ : κ ≠ 0) {x : TimeFunction}
    (hx : IsHill (algebraMap ℝ TimeFunction (-(κ ^ 2))) x) :
    (∃ B : ℝ, ∀ t : ℝ, 0 ≤ t → |x fun _ => t| ≤ B) ↔
      ∃ ν : ℝ, |ν| < 1 ∧
        monodromy (algebraMap ℝ TimeFunction (-(κ ^ 2))) 1 *ᵥ state x 0 = ν • state x 0 := by
  apply hx.exists_abs_apply_le_iff_of_two_lt_abs_trace (shift_algebraMap 1 _) one_pos
  rw [trace_monodromy_hyperbolic hκ, mul_one]
  have h := Real.one_lt_cosh.mpr hκ
  rw [abs_of_pos (by linarith)]
  linarith

end ProjectAinos.Mechanics.Parametric
