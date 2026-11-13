/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Electrodynamics.CurrentExamples
public import ProjectAInos.SmoothGeometry.Lorentzian.TwoFormDivergence
public import ProjectAInos.SmoothGeometry.Lorentzian.CurvatureExamples

/-! # Covariant two-form divergence and the nonzero electric source -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Manifold ContDiff

namespace ProjectAInos.Electrodynamics.Curved.Examples
open SmoothGeometry SmoothGeometry.DifferentialForm SmoothGeometry.LorentzMetric

local notation "E" => SpecialRelativity.Spacetime
local notation "g" => minkowskiMetric LorentzConvention.timeNegative 3
local notation "o" => OrientedAtlas.standard 4

theorem electric_twoFormDerivative (x u v w : E) :
    (g).twoFormDerivative electric x (modelField v x) (modelField w x) (modelField u x) =
      u 0 * (v 0 * w 1 - v 1 * w 0) := by
  rw [(g).twoFormDerivative_apply electric
    ((modelField_contMDiff _ x).mdifferentiableAt (by simp))
    ((modelField_contMDiff _ x).mdifferentiableAt (by simp))]
  have hz (a b : E) : (g).leviCivita (modelField b) x (modelField a x) = 0 :=
    congrFun (minkowski_covariantField_model .timeNegative 3 a b) x
  rw [hz, hz]
  have hm (y : E) (v : E) : modelField v y = v := rfl
  simp only [electric, ofFlat, hm]
  change mvfderiv 𝓘(ℝ, E) (fun y : E => y 0 * coordinateForm (n := 4) ![0, 1] ![v, w]) x u -
    x 0 * coordinateForm (n := 4) ![0, 1] ![0, w] -
    x 0 * coordinateForm (n := 4) ![0, 1] ![v, 0] = _
  have hd := (ContinuousLinearMap.proj 0 : E →L[ℝ] ℝ).hasFDerivAt (x := x) |>.mul_const
    (coordinateForm (n := 4) ![0, 1] ![v, w])
  change HasFDerivAt (fun y : E => y 0 * coordinateForm (n := 4) ![0, 1] ![v, w])
    ((coordinateForm (n := 4) ![0, 1] ![v, w]) • (ContinuousLinearMap.proj 0 : E →L[ℝ] ℝ)) x at hd
  rw [mvfderiv_eq_fderiv]
  change fderiv ℝ (fun y : E => y 0 * coordinateForm (n := 4) ![0, 1] ![v, w]) x u -
    x 0 * coordinateForm (n := 4) ![0, 1] ![0, w] -
    x 0 * coordinateForm (n := 4) ![0, 1] ![v, 0] = _
  rw [hd.fderiv]
  simp [coordinateForm_apply, Matrix.det_fin_two]
  ring

/-- The intrinsic contraction gives `-∂x`, agreeing with the source constructed from `dH`. -/
theorem electric_twoFormDivergence : (g).twoFormDivergence electric = negativeSpatial := by
  ext x : 1
  apply (NormedSpace.fromTangentSpace x).injective
  ext j
  rw [(g).twoFormDivergence_components electric x (NormedSpace.fromTangentSpace x)]
  have hi (a b : Fin 4) : (g).inverseComponent x (NormedSpace.fromTangentSpace x) a b =
      lorentzSign .timeNegative a * (Pi.single a 1 : E) b := by
    simp only [inverseComponent, minkowskiMetric_sharp]
    rfl
  change (∑ b : Fin 4, ∑ a : Fin 4, ∑ i : Fin 4,
    (g).twoFormDerivative electric x (modelField (Pi.single a 1) x)
      (modelField (Pi.single b 1) x) (modelField (Pi.single i 1) x) *
      (g).inverseComponent x (NormedSpace.fromTangentSpace x) a i *
      (g).inverseComponent x (NormedSpace.fromTangentSpace x) j b) = -(Pi.single 1 1 : E) j
  simp_rw [electric_twoFormDerivative, hi]
  fin_cases j <;> norm_num [Fin.sum_univ_succ, Pi.single_apply, lorentzSign]

theorem electric_twoFormDivergence_eq_source :
    (g).twoFormDivergence electric = source g o electric := by
  rw [electric_twoFormDivergence, electric_source]

end ProjectAInos.Electrodynamics.Curved.Examples
