/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.GeneralRelativity.NewtonianExamples
public import ProjectAInos.GeneralRelativity.NewtonianLimit
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-! # A nonstatic trajectory limit with mixed and spatial corrections -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open ContinuousLinearMap Set Filter Metric
open scoped Topology

namespace ProjectAInos.GeneralRelativity.NewtonianExamples

local notation "E" => NewtonianCoordinates
local notation "S" => NewtonianSpace
local notation "P" => (S × S)

/-- The Newtonian phase trajectory for `Φ=t x¹` with zero initial data. -/
def trajectory (t : ℝ) : P := (![-(t^3)/6, 0, 0], ![-(t^2)/2, 0, 0])

theorem trajectory_zero : trajectory 0 = 0 := by
  apply Prod.ext <;> ext i <;> fin_cases i <;> norm_num [trajectory]

theorem trajectory_position_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (Fin.cons t (trajectory t).1 : E) ∈ domain := by
  change dist (Fin.cons t (trajectory t).1 : E) 0 < 2
  rw [dist_zero_right]
  have h₀ : 0 ≤ t := ht.1
  have h₁ : t ≤ 1 := ht.2
  have hcube : t^3 ≤ 1 := by simpa using pow_le_pow_left₀ h₀ h₁ 3
  apply (pi_norm_lt_iff (by norm_num : (0 : ℝ) < 2)).mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change ‖t‖ < 2
    rw [Real.norm_eq_abs, abs_of_nonneg h₀]
    linarith
  · fin_cases j
    · change ‖-(t^3)/6‖ < 2
      rw [Real.norm_eq_abs, abs_div, abs_neg, abs_of_nonneg (pow_nonneg h₀ _)]
      norm_num
      linarith
    · change ‖(0 : ℝ)‖ < 2
      norm_num
    · change ‖(0 : ℝ)‖ < 2
      norm_num

theorem trajectory_hasDerivAt (t : ℝ) :
    HasDerivAt trajectory (family.newtonianPhaseField t (trajectory t)) t := by
  have hg (q : E) (i : Fin 3) :
      family.spatialGradient q i = if i = 0 then q 0 else 0 := by
    unfold NewtonianMetricFamily.spatialGradient
    rw [family_potential]
    have h := ((proj 0 : E →L[ℝ] ℝ).hasFDerivAt (x := q)).mul
      (proj 1 : E →L[ℝ] ℝ).hasFDerivAt
    change HasFDerivAt potential _ q at h
    rw [h.fderiv]
    fin_cases i <;> simp
  apply HasDerivAt.prodMk
  · apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · change HasDerivAt (fun x : ℝ => -(x^3)/6) (-(t^2)/2) t
      have h : HasDerivAt (fun x : ℝ => -(x^3)/6) (-(3 * t^2)/6) t := by
        simpa using (((hasDerivAt_id t).pow 3).neg.div_const 6)
      convert h using 1
      ring
    · exact hasDerivAt_const _ _
    · exact hasDerivAt_const _ _
  · apply hasDerivAt_pi.mpr
    intro i
    change HasDerivAt (fun u => (trajectory u).2 i)
      (-(family.spatialGradient (Fin.cons t (trajectory t).1) i)) t
    rw [hg]
    refine Fin.cases ?_ (fun j => ?_) i
    · change HasDerivAt (fun x : ℝ => -(x^2)/2) (-t) t
      have h : HasDerivAt (fun x : ℝ => -(x^2)/2) (-(2*t)/2) t := by
        simpa using (((hasDerivAt_id t).pow 2).neg.div_const 2)
      convert h using 1
      ring
    · rw [ite_eq_right (Fin.succ_ne_zero j), neg_zero]
      fin_cases j <;> exact hasDerivAt_const t (0 : ℝ)

/-- The nonstatic polynomial family has relativistic trajectories on
`[0,1]` with the same initial data and uniform inverse-square error. -/
theorem polynomial_trajectory_limit :
    ∃ C ≥ (0 : ℝ), ∃ z : ℝ → ℝ → P, TendstoUniformlyOn z trajectory atTop (Icc 0 1) ∧
      ∀ᶠ c : ℝ in atTop, z c 0 = 0 ∧
        (∀ t ∈ Icc 0 1,
          HasDerivWithinAt (z c) (family.relativisticPhaseField c t (z c t)) (Icc 0 1) t) ∧
        (∀ t ∈ Icc 0 1, (Fin.cons t (z c t).1 : E) ∈ domain ∧
          ‖z c t - trajectory t‖ ≤ C/c^2) := by
  apply family.exists_newtonian_limit_with_rate (by norm_num) trajectory
    (fun t _ => (trajectory_hasDerivAt t).hasDerivWithinAt)
    (fun _ ht => trajectory_position_mem ht) (fun _ => 0) (D := 0) le_rfl
  exact Eventually.of_forall fun c => by simp [trajectory_zero]

end ProjectAInos.GeneralRelativity.NewtonianExamples
