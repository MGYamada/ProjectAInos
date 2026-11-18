/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateConnection
public import ProjectAinos.SmoothGeometry.Lorentzian.Einstein

/-!
# A curved conformally flat metric in four dimensions

The metric `g = e^{2z}(−dt² + dx² + dy² + dz²)` on all of `ℝ⁴`, with co-ordinates `(t, x, y, z)`
at the indices `0, 1, 2, 3`, is a regression for the Bianchi identities and the Einstein
tensor. In two dimensions the cyclic sum of the second Bianchi identity and the Einstein tensor
vanish for every metric, so the existing two-dimensional examples cannot test them.

* `metric_leviCivita`: `∇_{∂_v} ∂_w = ∂_{Γ(v, w)}` with the constant map
  `Γ(v, w) = v₃ w + w₃ v − η(v, w) e₃`.
* `metric_curvature`: `R(∂_u, ∂_v)∂_w = ∂_{ℛ(u, v, w)}` with
  `ℛ(u, v, w) = (v₃w₃ − η(v, w)) u − (u₃w₃ − η(u, w)) v + (u₃ η(v, w) − v₃ η(u, w)) e₃`.
* `metric_ricci_chartField`, `metric_scalarCurvature`, `metric_einstein_chartField`:
  `Ric = diag(2, −2, −2, 0)`, `R = −6 e^{−2z}`, `G = diag(−1, 1, 1, 3)`; `G ≠ 0`.
* `metric_curvatureDerivative_dz`: `∇_{∂_z} R = −2 R` in components, so `∇R ≠ 0`.
* `metric_ricci_divergence`: `∇^a Ric_{az} = 6 e^{−2z} ≠ 0`, half of `∂_z R`, by the contracted
  Bianchi identity.
-/

@[expose] public section

noncomputable section

open Bundle ContinuousLinearMap TopologicalSpace
open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry.ExponentialConformalExample

open LorentzMetric CoordinateMetric

local notation "E" => MinkowskiModel 3
local notation "η" => minkowskiForm LorentzConvention.timeNegative 3

/-- The form `e^{2z} η` at the point `q = (t, x, y, z)`. -/
def form (q : E) : E →L[ℝ] E →L[ℝ] ℝ := Real.exp (2 * q 3) • minkowskiForm .timeNegative 3

theorem form_apply (q v w : E) : form q v w = Real.exp (2 * q 3) * η v w := by
  simp only [form, smul_apply, smul_eq_mul]

theorem contDiff_form : ContDiff ℝ ∞ form := by
  refine contDiff_clm_apply_iff.mpr fun v => contDiff_clm_apply_iff.mpr fun w => ?_
  simp only [form_apply]
  fun_prop

/-- The conformally flat metric `e^{2z} η` on all of `ℝ⁴`. -/
def metric : CoordinateMetric .timeNegative 3 ⊤ where
  form := form
  smooth := contDiff_form.contDiffOn
  signature q _ := by
    refine ⟨(LinearEquiv.smulOfNeZero ℝ E (Real.exp (q 3))
      (Real.exp_ne_zero _)).toContinuousLinearEquiv, fun v w => ?_⟩
    change Real.exp (2 * q 3) * η v w = η (Real.exp (q 3) • v) (Real.exp (q 3) • w)
    simp only [map_smul, smul_apply, smul_eq_mul, two_mul, Real.exp_add]
    ring

theorem minkowskiForm_single_three (v : E) : η (Pi.single 3 1) v = v 3 := by
  simp [minkowskiForm_apply, Fin.sum_univ_four, lorentzSign, LorentzConvention.timeSign]

theorem minkowskiForm_single_three_right (v : E) : η v (Pi.single 3 1) = v 3 := by
  rw [minkowskiForm_symmetric, minkowskiForm_single_three]

/-- The Christoffel map `Γ(v, w) = v₃ w + w₃ v − η(v, w) e₃`. It does not depend on the
point. -/
def connection (v w : E) : E := v 3 • w + w 3 • v - η v w • Pi.single 3 1

theorem connection_single_three (v : E) : connection (Pi.single 3 1) v = v := by
  simp [connection, minkowskiForm_single_three]

theorem hasFDerivAt_form_apply (q v w : E) :
    HasFDerivAt (fun p => form p v w)
      ((2 * Real.exp (2 * q 3) * η v w) • (proj 3 : E →L[ℝ] ℝ)) q := by
  simp_rw [form_apply]
  have hp := (proj 3 : E →L[ℝ] ℝ).hasFDerivAt (x := q)
  convert! ((hp.const_mul 2).exp).mul_const (η v w) using 1
  ext u
  simp
  ring

/-- The Levi-Civita connection on co-ordinate fields is the constant map `Γ`. -/
theorem metric_leviCivita (x y : (⊤ : Opens E)) (v w : E) :
    metric.toLorentzMetric.leviCivita (chartField (physicalChart x) w) y
      (chartField (physicalChart x) v y) = chartField (physicalChart x) (connection v w) y := by
  apply metric.toLorentzMetric_leviCivita_eq x y v w (connection v w)
  intro z
  change form y (connection v w) z = (fderiv ℝ (fun q => form q w z) (y : E) v +
    fderiv ℝ (fun q => form q z v) (y : E) w - fderiv ℝ (fun q => form q v w) (y : E) z) / 2
  rw [(hasFDerivAt_form_apply y w z).fderiv, (hasFDerivAt_form_apply y z v).fderiv,
    (hasFDerivAt_form_apply y v w).fderiv]
  simp only [form_apply, connection, map_add, map_sub, map_smul, add_apply, sub_apply,
    smul_apply, smul_eq_mul, proj_apply, minkowskiForm_single_three]
  rw [minkowskiForm_symmetric _ z v]
  ring

/-- The curvature `ℛ(u, v, w)` in components; it does not depend on the point. -/
def curvatureVector (u v w : E) : E :=
  (v 3 * w 3 - η v w) • u - (u 3 * w 3 - η u w) • v +
    (u 3 * η v w - v 3 * η u w) • Pi.single 3 1

theorem connection_connection (u v w : E) :
    connection u (connection v w) - connection v (connection u w) = curvatureVector u v w := by
  simp only [connection, curvatureVector, map_add, map_sub, map_smul, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, minkowskiForm_single_three_right,
    Pi.single_eq_same, mul_one]
  rw [minkowskiForm_symmetric _ v u]
  module

/-- The curvature on co-ordinate fields. -/
theorem metric_curvature (x y : (⊤ : Opens E)) (u v w : E) :
    metric.toLorentzMetric.curvature y (chartField (physicalChart x) u y)
      (chartField (physicalChart x) v y) (chartField (physicalChart x) w y) =
      chartField (physicalChart x) (curvatureVector u v w) y := by
  rw [metric.toLorentzMetric_curvature_of_connection x connection (metric_leviCivita x) y,
    connection_connection]

/-- The metric on co-ordinate fields. -/
theorem metric_form_chartField (x y : (⊤ : Opens E)) (v w : E) :
    metric.toLorentzMetric.form y (chartField (physicalChart x) v y)
      (chartField (physicalChart x) w y) = Real.exp (2 * (y : E) 3) * η v w := by
  rw [toLorentzMetric_form, physicalChart_chartField, physicalChart_chartField]
  exact form_apply _ _ _

/-- `dz` on co-ordinate fields. -/
theorem chartCovector_three (x y : (⊤ : Opens E)) (v : E) :
    chartCovector (physicalChart x) y 3 (chartField (physicalChart x) v y) = v 3 :=
  congrFun (chartTangentMap_field (physicalChart_mem x) (by simp) v) 3

/-- The Ricci tensor on co-ordinate fields: `Ric(∂_v, ∂_w) = 2 (v₃ w₃ − η(v, w))`. -/
theorem metric_ricci_chartField (x y : (⊤ : Opens E)) (v w : E) :
    metric.toLorentzMetric.ricci y (chartField (physicalChart x) v y)
      (chartField (physicalChart x) w y) = 2 * (v 3 * w 3 - η v w) := by
  have hy : y ∈ (physicalChart x).source := by simp
  rw [metric.toLorentzMetric.ricci_eq_sum y (chartTangentEquiv (physicalChart_mem x) hy)]
  simp only [chartTangentEquiv_symm, chartTangentEquiv_apply, metric_curvature,
    chartTangentMap_field (physicalChart_mem x) hy]
  simp [Fin.sum_univ_four, curvatureVector, minkowskiForm_apply, lorentzSign,
    LorentzConvention.timeSign, Pi.single_apply]
  ring

/-- The Ricci tensor is `2 dz ⊗ dz − 2 e^{−2z} g`. -/
theorem metric_ricci (x y : (⊤ : Opens E)) :
    metric.toLorentzMetric.ricci y =
      (2 : ℝ) • (chartCovector (physicalChart x) y 3).smulRight
          (chartCovector (physicalChart x) y 3) -
        (2 * Real.exp (-(2 * (y : E) 3))) • metric.toLorentzMetric.form y := by
  have he := physicalChart_mem x
  have hy : y ∈ (physicalChart x).source := by simp
  have hexp : Real.exp (-(2 * (y : E) 3)) * Real.exp (2 * (y : E) 3) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  refine ext_chartField he hy fun j => ext_chartField he hy fun k => ?_
  rw [metric_ricci_chartField]
  simp only [sub_apply, smul_apply, smulRight_apply, smul_eq_mul, chartCovector_three,
    metric_form_chartField]
  linear_combination (2 * η (Pi.single j 1) (Pi.single k 1)) * hexp

/-- Raising `dz` gives `e^{−2z} ∂_z`. -/
theorem metric_sharp_dz (x y : (⊤ : Opens E)) :
    metric.toLorentzMetric.sharp y (chartCovector (physicalChart x) y 3) =
      Real.exp (-(2 * (y : E) 3)) • chartField (physicalChart x) (Pi.single 3 1) y := by
  have he := physicalChart_mem x
  have hy : y ∈ (physicalChart x).source := by simp
  rw [sharp_eq_iff]
  intro t
  rw [← chartField_tangentMap he hy t]
  simp only [map_smul, smul_apply, smul_eq_mul, metric_form_chartField, chartCovector_three,
    minkowskiForm_single_three]
  rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

/-- The scalar curvature `R = −6 e^{−2z}`. -/
theorem metric_scalarCurvature (y : (⊤ : Opens E)) :
    metric.toLorentzMetric.scalarCurvature y = -6 * Real.exp (-(2 * (y : E) 3)) := by
  rw [scalarCurvature_apply, metric_ricci y y, metric.toLorentzMetric.contract_sub,
    metric.toLorentzMetric.contract_smul, metric.toLorentzMetric.contract_smul,
    contract_smulRight, contract_metric, metric_sharp_dz, map_smul, smul_eq_mul,
    chartCovector_three, Pi.single_eq_same]
  push_cast
  ring

/-- The Einstein tensor on co-ordinate fields: `G(∂_v, ∂_w) = 2 v₃ w₃ + η(v, w)`. -/
theorem metric_einstein_chartField (x y : (⊤ : Opens E)) (v w : E) :
    metric.toLorentzMetric.einstein y (chartField (physicalChart x) v y)
      (chartField (physicalChart x) w y) = 2 * (v 3 * w 3) + η v w := by
  have hexp : Real.exp (-(2 * (y : E) 3)) * Real.exp (2 * (y : E) 3) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rw [einstein_apply, metric_ricci_chartField, metric_scalarCurvature, metric_form_chartField]
  linear_combination (3 * η v w) * hexp

/-- The Einstein tensor does not vanish: `G(∂_z, ∂_z) = 3`. -/
theorem metric_einstein_ne_zero (y : (⊤ : Opens E)) : metric.toLorentzMetric.einstein y ≠ 0 := by
  intro h
  have h' := metric_einstein_chartField y y (Pi.single 3 1) (Pi.single 3 1)
  rw [h, zero_apply, zero_apply, Pi.single_eq_same, minkowskiForm_single_three,
    Pi.single_eq_same] at h'
  norm_num at h'

/-- The covariant derivative of the curvature along `∂_z` is `−2 R` in components. -/
theorem metric_curvatureDerivative_dz (x y : (⊤ : Opens E)) (u v w : E) :
    metric.toLorentzMetric.curvatureDerivative y (chartField (physicalChart x) u y)
        (chartField (physicalChart x) v y) (chartField (physicalChart x) w y)
        (chartField (physicalChart x) (Pi.single 3 1) y) =
      chartField (physicalChart x) ((-2 : ℝ) • curvatureVector u v w) y := by
  rw [metric.toLorentzMetric_curvatureDerivative_of_connection x connection (metric_leviCivita x)
    curvatureVector (metric_curvature x)]
  simp only [connection_single_three]
  rw [show curvatureVector u v w - curvatureVector u v w - curvatureVector u v w -
    curvatureVector u v w = (-2 : ℝ) • curvatureVector u v w by module]

/-- The covariant derivative of the curvature does not vanish:
`(∇_{∂_z} R)(∂_t, ∂_x)∂_t = 2 ∂_x`. -/
theorem metric_curvatureDerivative_ne_zero (y : (⊤ : Opens E)) :
    metric.toLorentzMetric.curvatureDerivative y ≠ 0 := by
  intro h
  have hy : y ∈ (physicalChart y).source := by simp
  have h' := congrArg (fun c => chartTangentMap (physicalChart y) y c 1)
    (metric_curvatureDerivative_dz y y (Pi.single 0 1) (Pi.single 1 1) (Pi.single 0 1))
  simp only [h, zero_apply, map_zero, Pi.zero_apply,
    chartTangentMap_field (physicalChart_mem y) hy] at h'
  simp [curvatureVector, minkowskiForm_apply, lorentzSign, LorentzConvention.timeSign,
    Pi.single_apply] at h'

/-- The derivative of the scalar curvature along `∂_z` is `12 e^{−2z}`. -/
theorem metric_scalarCurvature_derivative (x y : (⊤ : Opens E)) :
    mvfderiv 𝓘(ℝ, E) (fun z => metric.toLorentzMetric.scalarCurvature z) y
        (chartField (physicalChart x) (Pi.single 3 1) y) =
      12 * Real.exp (-(2 * (y : E) 3)) := by
  have hfun : (fun z => metric.toLorentzMetric.scalarCurvature z) =
      fun z : (⊤ : Opens E) => -6 * Real.exp (-(2 * (z : E) 3)) :=
    funext metric_scalarCurvature
  have hcd : ContDiff ℝ ∞ (fun q : E => -6 * Real.exp (-(2 * q 3))) := by fun_prop
  have hG : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ)
      (fun z : (⊤ : Opens E) => -6 * Real.exp (-(2 * (z : E) 3))) y :=
    ((hcd.contMDiff.comp (contMDiff_subtype_val (U := (⊤ : Opens E)))) y).mdifferentiableAt
      (by simp)
  have hd : HasFDerivAt (fun q : E => -6 * Real.exp (-(2 * q 3)))
      ((12 * Real.exp (-(2 * (y : E) 3))) • (proj 3 : E →L[ℝ] ℝ)) (y : E) := by
    have hp := (proj 3 : E →L[ℝ] ℝ).hasFDerivAt (x := (y : E))
    convert! (((hp.const_mul 2).neg).exp).const_mul (-6) using 1
    ext u
    simp
    ring
  have hcomp : (fun z : (⊤ : Opens E) => -6 * Real.exp (-(2 * (z : E) 3))) ∘
      (physicalChart x).symm = fun q : E => -6 * Real.exp (-(2 * q 3)) := by
    funext q
    simp only [Function.comp]
    rw [← physicalChart_apply x ((physicalChart x).symm q),
      (physicalChart x).right_inv (by simp)]
  rw [hfun, mvfderiv_chartField (physicalChart_mem x) (by simp) hG, hcomp, physicalChart_apply,
    hd.fderiv]
  simp

/-- The divergence of the Ricci tensor along `∂_z` is `6 e^{−2z}`, half of `∂_z R`. -/
theorem metric_ricci_divergence (x y : (⊤ : Opens E)) :
    metric.toLorentzMetric.bilinearDivergenceCovector metric.toLorentzMetric.ricciBilinear y
        (chartField (physicalChart x) (Pi.single 3 1) y) =
      6 * Real.exp (-(2 * (y : E) 3)) := by
  rw [ricci_contracted_bianchi, metric_scalarCurvature_derivative]
  ring

end ProjectAinos.SmoothGeometry.ExponentialConformalExample
