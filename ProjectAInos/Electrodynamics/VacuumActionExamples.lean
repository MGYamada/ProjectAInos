/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
-/
module

public import ProjectAInos.Electrodynamics.Examples
public import ProjectAInos.Electrodynamics.VacuumAction

/-! # A nonzero vacuum field on a bounded spacetime region -/

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace ProjectAInos.Electrodynamics.VacuumAction

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity

/-- With time-first orientation, the electric field gives positive action
density for the specified Lorentzian sign. -/
theorem uniform_electric_density (x : Spacetime) :
    Variational.density lagrangian (Examples.uniformPotential 1 0) x = 1 / 2 := by
  rw [density_eq, Examples.uniformPotential_field]
  have hF : Examples.uniformField 1 0 = -(coordinateForm (n := 4) ![0, 1]) := by
    unfold Examples.uniformField
    rw [zero_smul, add_zero]
    change (-1 : ℝ) • coordinateForm (n := 4) ![0, 1] = _
    exact neg_one_smul ℝ (coordinateForm (n := 4) ![0, 1])
  have hstar : star (-(coordinateForm (n := 4) ![0, 1])) = coordinateForm ![2, 3] := by
    change hodgeFiber .timeNegative .standard (by decide : 2 + 2 = 3 + 1)
      (-(coordinateForm ![0, 1])) = coordinateForm ![2, 3]
    rw [map_neg, hodge_dt_dx, neg_neg]
  rw [hF, hstar, map_neg]
  have hw : wedgeFiber (coordinateForm (n := 4) ![0, 1]) (coordinateForm ![2, 3]) =
      coordinateForm (n := 4) id := by
    unfold coordinateForm
    rw [wedge_ofCovectors]
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [LinearMap.neg_apply, hw, map_neg]
  have hc : coefficient (coordinateForm (n := 4) id) = 1 := by
    exact (Minkowski.coordinateVolume_toExterior 4 (coordinateForm id)).symm.trans
      (Minkowski.coordinateVolume_coordinateForm 4)
  rw [hc]
  norm_num

theorem uniform_electric_nonzero (x : Spacetime) :
    fieldTensor (Examples.uniformPotential 1 0) x ≠ 0 := by
  intro hz
  have h := uniform_electric_density x
  rw [density_eq, hz] at h
  norm_num at h

/-- The constant nonzero field is stationary on a finite-volume open ball. -/
theorem uniform_electric_stationary :
    Variational.Stationary volume (Metric.ball (0 : Spacetime) 1) lagrangian
      (Examples.uniformPotential 1 0) := by
  have hfin : Integrable (Variational.density lagrangian (Examples.uniformPotential 1 0))
      (volume.restrict (Metric.ball (0 : Spacetime) 1)) := by
    have : IsFiniteMeasure (volume.restrict (Metric.ball (0 : Spacetime) 1)) :=
      ⟨by
        rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
        exact measure_ball_lt_top⟩
    rw [show Variational.density lagrangian (Examples.uniformPotential 1 0) =
      fun _ => (1 / 2 : ℝ) from funext uniform_electric_density]
    exact integrable_const _
  apply (stationary_iff_residual_zero Metric.isOpen_ball
    (Examples.uniformPotential 1 0).contDiff hfin).mpr
  intro x _hx
  unfold residual
  simp_rw [Examples.uniformPotential_field]
  change ContinuousAlternatingMap.alternatizeUncurryFin
    (fderiv ℝ (fun _ : Spacetime => star (Examples.uniformField 1 0)) x) = 0
  rw [fderiv_const_apply]
  exact map_zero (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ Spacetime ℝ)

end ProjectAInos.Electrodynamics.VacuumAction
