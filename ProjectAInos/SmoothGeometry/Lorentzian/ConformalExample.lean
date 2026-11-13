/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.Conformal
public import ProjectAInos.SmoothGeometry.Lorentzian.ChartCurvature
public import ProjectAInos.SmoothGeometry.Lorentzian.Ricci

/-! # A curved conformal Lorentz plane

For `g = exp(2x²) (-dt² + dx²)`, the native connection vanishes at the
origin but curvature does not. This example fixes the curvature and Ricci
sign conventions using the constructed tangent-bundle objects.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle ContinuousLinearMap
open scoped Manifold ContDiff

namespace ProjectAInos.SmoothGeometry.LorentzianConformalExample

open LorentzMetric

abbrev Plane := MinkowskiModel 1

/-- The smooth conformal exponent `φ(t,x) = x²`. -/
def potential : C^∞⟮𝓘(ℝ, Plane), Plane; ℝ⟯ :=
  ⟨fun p => (p 1)^2, (show ContDiff ℝ ∞ (fun p : Plane => (p 1)^2) by fun_prop).contMDiff⟩

/-- A curved metric on the actual tangent bundle, with signature `(-+)`. -/
def metric : LorentzMetric .timeNegative 1 Plane :=
  (minkowskiMetric .timeNegative 1).conformal potential

theorem metric_coordinates (p v w : Plane) :
    metric.form p v w = Real.exp (2 * (p 1)^2) * (-(v 0 * w 0) + v 1 * w 1) := by
  change Real.exp (2 * (p 1)^2) * minkowskiForm .timeNegative 1 v w = _
  simp [minkowskiForm_apply, lorentzSign, Fin.sum_univ_succ]

/-- Differentiate the metric pairing of constant coordinate fields exactly. -/
theorem hasFDerivAt_metric_pair (p v w : Plane) :
    HasFDerivAt (fun q => metric.form q (modelField v q) (modelField w q))
      ((4 * p 1 * Real.exp (2 * (p 1)^2) * (-(v 0 * w 0) + v 1 * w 1)) •
        (proj 1 : Plane →L[ℝ] ℝ)) p := by
  change HasFDerivAt (fun q : Plane => metric.form q v w) _ p
  simp_rw [metric_coordinates]
  have hp := (proj 1 : Plane →L[ℝ] ℝ).hasFDerivAt (x := p)
  convert! (((hp.pow 2).const_mul 2).exp).mul_const (-(v 0 * w 0) + v 1 * w 1) using 1
  ext u
  simp
  ring

/-- The intrinsic connection applied to constant coordinate fields. -/
theorem leviCivita_modelField (p v w : Plane) :
    metric.leviCivita (modelField w) p (modelField v p) =
      modelField ![2 * p 1 * (v 0 * w 1 + v 1 * w 0),
        2 * p 1 * (v 0 * w 0 + v 1 * w 1)] p := by
  apply (metric.flat p).injective
  ext z
  change metric.form p (metric.leviCivita (modelField w) p (modelField v p)) z =
    metric.form p ![2 * p 1 * (v 0 * w 1 + v 1 * w 0),
      2 * p 1 * (v 0 * w 0 + v 1 * w 1)] z
  have hz : modelField (NormedSpace.fromTangentSpace p z) p = z :=
    (NormedSpace.fromTangentSpace p).symm_apply_apply z
  have h := metric.modelField_leviCivita_pairing p v w (NormedSpace.fromTangentSpace p z)
  rw [hz] at h
  rw [h, (hasFDerivAt_metric_pair p w _).fderiv,
    (hasFDerivAt_metric_pair p _ v).fderiv, (hasFDerivAt_metric_pair p v w).fderiv]
  simp [metric_coordinates, NormedSpace.fromTangentSpace, tangentSpaceCastModel]
  ring

/-- All eight Christoffel coefficients of the actual connection. -/
theorem christoffel_eq (p : Plane) (k i j : Fin 2) :
    metric.christoffel p k i j =
      if (k = 0 ∧ i ≠ j) ∨ (k = 1 ∧ i = j) then 2 * p 1 else 0 := by
  rw [christoffel, leviCivita_modelField]
  simp only [modelField, ContinuousLinearEquiv.apply_symm_apply]
  fin_cases k <;> fin_cases i <;> fin_cases j <;> norm_num [Pi.single_apply]

/-- Vanishing coefficients at one point do not imply flatness. -/
theorem christoffel_origin (k i j : Fin 2) : metric.christoffel 0 k i j = 0 := by
  simp [christoffel_eq]

/-- Derivatives of the connection coefficients in the fixed coordinate chart. -/
theorem hasFDerivAt_christoffel (p : Plane) (k i j : Fin 2) :
    HasFDerivAt (fun q => metric.christoffel q k i j)
      ((if (k = 0 ∧ i ≠ j) ∨ (k = 1 ∧ i = j) then (2 : ℝ) else 0) •
        (proj 1 : Plane →L[ℝ] ℝ)) p := by
  simp_rw [christoffel_eq]
  split_ifs with h
  · exact (proj 1 : Plane →L[ℝ] ℝ).hasFDerivAt.const_mul 2
  · simpa using hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) p

/-- All sixteen components of the native Riemann tensor. -/
theorem curvature_component (p : Plane) (l i j k : Fin 2) :
    NormedSpace.fromTangentSpace p
      (metric.curvature p (modelField (Pi.single i 1) p)
        (modelField (Pi.single j 1) p) (modelField (Pi.single k 1) p)) l =
      if i = j ∨ l = k then 0 else if i = 0 then -2 else 2 := by
  rw [metric.curvature_model_coordinates]
  simp_rw [(hasFDerivAt_christoffel _ _ _ _).fderiv, christoffel_eq]
  fin_cases l <;> fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [Fin.sum_univ_succ, Pi.single_apply]

/-- The Ricci contraction has coordinate matrix `diag (2, -2)`. -/
theorem ricci_component (p : Plane) (i j : Fin 2) :
    metric.ricci p (modelField (Pi.single i 1) p) (modelField (Pi.single j 1) p) =
      if i ≠ j then 0 else if i = 0 then 2 else -2 := by
  rw [metric.ricci_eq_sum p (NormedSpace.fromTangentSpace p)]
  change (∑ a : Fin 2, NormedSpace.fromTangentSpace p
    (metric.curvature p (modelField (Pi.single a 1) p)
      (modelField (Pi.single i 1) p) (modelField (Pi.single j 1) p)) a) = _
  simp_rw [curvature_component]
  fin_cases i <;> fin_cases j <;> norm_num [Fin.sum_univ_succ]

/-- The inverse metric coefficients are derived from `sharp`. -/
theorem inverseComponent_eq (p : Plane) (i j : Fin 2) :
    metric.inverseComponent p (NormedSpace.fromTangentSpace p) i j =
      if i = j then (if i = 0 then -Real.exp (-(2 * (p 1)^2))
        else Real.exp (-(2 * (p 1)^2))) else 0 := by
  let α := Tensor.coordinateCovector p (NormedSpace.fromTangentSpace p) j
  have h := metric.form_sharp_left p α (modelField (Pi.single i 1) p)
  change metric.form p (metric.sharp p α) (Pi.single i 1) = _ at h
  rw [metric_coordinates] at h
  change Real.exp (2 * (p 1)^2) *
    (-(metric.sharp p α 0 * (Pi.single i 1 : Plane) 0) +
      metric.sharp p α 1 * (Pi.single i 1 : Plane) 1) = (Pi.single i 1 : Plane) j at h
  change metric.sharp p α i = _
  have he : Real.exp (2 * (p 1)^2) * Real.exp (-(2 * (p 1)^2)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  apply mul_left_cancel₀ (Real.exp_ne_zero (2 * (p 1)^2))
  fin_cases i <;> fin_cases j <;> simp only [Pi.single_apply, Fin.isValue,
    Fin.zero_eta, Fin.mk_one, ite_true, ite_false, zero_ne_one, one_ne_zero,
    mul_one, mul_zero, add_zero, neg_zero, zero_add] at h ⊢ <;> nlinarith only [h, he]

/-- The scalar curvature fixes the prescribed `R(X,Y)Z` and Ricci convention. -/
theorem scalarCurvature_eq (p : Plane) :
    metric.scalarCurvature p = -4 * Real.exp (-(2 * (p 1)^2)) := by
  rw [metric.scalarCurvature_eq_sum p (NormedSpace.fromTangentSpace p)]
  change (∑ i : Fin 2, ∑ j : Fin 2,
    metric.ricci p (modelField (Pi.single i 1) p) (modelField (Pi.single j 1) p) *
      metric.inverseComponent p (NormedSpace.fromTangentSpace p) i j) = _
  simp_rw [ricci_component, inverseComponent_eq]
  norm_num [Fin.sum_univ_succ]
  ring

theorem scalarCurvature_origin : metric.scalarCurvature 0 = -4 := by
  rw [scalarCurvature_eq]
  norm_num

/-- The actual curvature tensor is nonzero even where every coefficient
of the connection vanishes. -/
theorem curvature_origin_ne_zero : metric.curvature 0 ≠ 0 := by
  intro hz
  have h := curvature_component 0 1 0 1 0
  norm_num [hz] at h

end ProjectAInos.SmoothGeometry.LorentzianConformalExample
