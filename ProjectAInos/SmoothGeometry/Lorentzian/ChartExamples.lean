/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.Dual
public import ProjectAInos.SmoothGeometry.Lorentzian.Tensor
public import ProjectAInos.SmoothGeometry.Tensor.Bilinear
public import ProjectAInos.SmoothGeometry.Tensor.Pullback
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # A Lorentz metric in two nonlinear coordinate charts

The coordinates `(T,X) = (t,x+t²)` describe the same Minkowski geometry.
The `(t,x)` metric coefficients and transition Jacobian are nonconstant. Both
charts are actual members of the smooth maximal atlas, not just formal
coordinate arrays. Connections and curvature are not assumed here.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle ContinuousLinearMap
open scoped Manifold ContDiff

namespace ProjectAInos.SmoothGeometry.LorentzianCharts

abbrev Plane := MinkowskiModel 1

/-- A linear shear and its explicit inverse. -/
def shearLinear (a : ℝ) : Plane ≃L[ℝ] Plane :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun v := ![v 0, v 1 + a * v 0]
      invFun v := ![v 0, v 1 - a * v 0]
      left_inv v := by ext i; fin_cases i <;> simp
      right_inv v := by ext i; fin_cases i <;> simp
      map_add' v w := by ext i; fin_cases i <;> simp; ring
      map_smul' r v := by ext i; fin_cases i <;> simp; ring }

@[simp] theorem shearLinear_zero (a : ℝ) (v : Plane) : shearLinear a v 0 = v 0 := rfl
@[simp] theorem shearLinear_one (a : ℝ) (v : Plane) :
    shearLinear a v 1 = v 1 + a * v 0 := rfl

/-- A nonlinear global coordinate map, used below as an overlapping chart. -/
def shear (p : Plane) : Plane := ![p 0, p 1 + (p 0)^2]

def unshear (p : Plane) : Plane := ![p 0, p 1 - (p 0)^2]

theorem unshear_shear (p : Plane) : unshear (shear p) = p := by
  ext i
  fin_cases i <;> simp [shear, unshear]

theorem shear_unshear (p : Plane) : shear (unshear p) = p := by
  ext i
  fin_cases i <;> simp [shear, unshear]

theorem shear_contDiff : ContDiff ℝ ∞ shear := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun x : Plane => x 0)
    fun_prop
  · change ContDiff ℝ ∞ (fun x : Plane => x 1 + (x 0)^2)
    fun_prop

theorem unshear_contDiff : ContDiff ℝ ∞ unshear := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun x : Plane => x 0)
    fun_prop
  · change ContDiff ℝ ∞ (fun x : Plane => x 1 - (x 0)^2)
    fun_prop

def shearDiffeomorph : Plane ≃ₘ[ℝ] Plane where
  toEquiv := ⟨shear, unshear, unshear_shear, shear_unshear⟩
  contMDiff_toFun := shear_contDiff.contMDiff
  contMDiff_invFun := unshear_contDiff.contMDiff

theorem hasFDerivAt_shear (p : Plane) :
    HasFDerivAt shear (shearLinear (2 * p 0)).toContinuousLinearMap p := by
  apply hasFDerivAt_pi''
  intro i
  fin_cases i
  · convert (proj 0 : Plane →L[ℝ] ℝ).hasFDerivAt (x := p) using 1
    · rfl
    · ext v
      rfl
  · have h := (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) 1 p).add
      ((hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) 0 p).pow 2)
    convert h using 1 <;> ext v <;> simp [shear]

theorem mfderiv_shear (p : Plane) :
    mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shear p =
      (shearLinear (2 * p 0)).toContinuousLinearMap := by
  rw [mfderiv_eq_fderiv, (hasFDerivAt_shear p).fderiv]
  rfl

theorem shearLinear_toContinuousLinearMap (a : ℝ) :
    (shearLinear a).toContinuousLinearMap = ContinuousLinearMap.id ℝ Plane +
      a • (proj 0 : Plane →L[ℝ] ℝ).smulRight (Pi.single 1 1) := by
  ext v i
  fin_cases i <;> simp [shearLinear]

theorem shearLinear_contDiff :
    ContDiff ℝ ∞ (fun a => (shearLinear a).toContinuousLinearMap) := by
  simp only [shearLinear_toContinuousLinearMap]
  exact contDiff_const.add (contDiff_id.smul contDiff_const)

/-- Nonconstant metric coefficients in the `(t,x)` chart. -/
def coefficients (p : Plane) : Plane →L[ℝ] Plane →L[ℝ] ℝ :=
  BilinearTensor.pullback (minkowskiForm .timeNegative 1)
    (shearLinear (2 * p 0)).toContinuousLinearMap

theorem coefficients_contDiff : ContDiff ℝ ∞ coefficients :=
  BilinearTensor.contDiff_pullback contDiff_const
    (shearLinear_contDiff.comp (contDiff_const.mul (contDiff_apply ℝ _ 0)))

/-- The same flat Lorentz metric, expressed in a nonlinear coordinate chart. -/
def metric : LorentzMetric .timeNegative 1 Plane where
  form := coefficients
  smooth := by
    intro x
    rw [contMDiffAt_section]
    convert coefficients_contDiff.contMDiff.contMDiffAt (x := x) using 1
    funext y
    ext v w
    simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates]
    rfl
  signature p := ⟨shearLinear (2 * p 0), fun _ _ => rfl⟩

/-- The nonlinear metric uses the existing Lorentz-manifold/scheme interface. -/
def spacetime : LorentzManifold .timeNegative 1 where
  carrier := Plane
  metric := metric

theorem spacetime_toScheme :
    spacetime.toScheme = (minkowski .timeNegative 1).toScheme := rfl

theorem metric_coordinates (p v w : Plane) :
    metric.form p v w = -(v 0 * w 0) +
      (v 1 + 2 * p 0 * v 0) * (w 1 + 2 * p 0 * w 0) := by
  simp [metric, coefficients, BilinearTensor.pullback_apply, minkowskiForm_apply,
    lorentzSign, Fin.sum_univ_succ, shearLinear]

theorem metric_time_time (p : Plane) :
    metric.form p (Pi.single 0 1) (Pi.single 0 1) = -1 + 4 * (p 0)^2 := by
  rw [metric_coordinates]
  simp
  ring

theorem metric_time_space (p : Plane) :
    metric.form p (Pi.single 0 1) (Pi.single 1 1) = 2 * p 0 := by
  rw [metric_coordinates]
  simp

theorem metric_space_space (p : Plane) :
    metric.form p (Pi.single 1 1) (Pi.single 1 1) = 1 := by
  rw [metric_coordinates]
  simp

/-- A substantive metric covariance identity for the actual manifold derivative. -/
theorem metric_covariance (p v w : Plane) :
    metric.form p v w = (minkowskiMetric .timeNegative 1).form (shear p)
      (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shear p v)
      (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shear p w) := by
  rw [mfderiv_shear]
  rfl

theorem flat_covariance (p v : Plane) :
    metric.flat p v = (Minkowski.flat .timeNegative (shearLinear (2 * p 0) v)).comp
      (shearLinear (2 * p 0)).toContinuousLinearMap := by
  ext w
  rfl

theorem sharp_covariance (p : Plane) (α : Plane →L[ℝ] ℝ) :
    metric.sharp p (α.comp (shearLinear (2 * p 0)).toContinuousLinearMap) =
      (shearLinear (2 * p 0)).symm (Minkowski.sharp .timeNegative α) := by
  apply (metric.sharp_eq_iff p _ _).mpr
  intro w
  change minkowskiForm .timeNegative 1
    (shearLinear (2 * p 0) ((shearLinear (2 * p 0)).symm
      (Minkowski.sharp .timeNegative α))) (shearLinear (2 * p 0) w) =
    α (shearLinear (2 * p 0) w)
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact congrArg (fun β : Plane →L[ℝ] ℝ => β (shearLinear (2 * p 0) w))
    (Minkowski.flat_sharp .timeNegative α)

/-- An arbitrary covariant tensor has the same contraction in both charts. -/
theorem contract_covariance (p : Plane) (B : Plane →L[ℝ] Plane →L[ℝ] ℝ) :
    metric.contract p (BilinearTensor.pullback B
      (shearLinear (2 * p 0)).toContinuousLinearMap) =
      (minkowskiMetric .timeNegative 1).contract (shear p) B :=
  metric.contract_naturality (minkowskiMetric .timeNegative 1) p (shear p)
    (shearLinear (2 * p 0)) (fun _ _ => rfl) _ B (fun _ _ => rfl)

/-- The pullback of `dX ⊗ dX`; its components vary although its contraction is one. -/
def spatialTensorCoefficients (p : Plane) : Plane →L[ℝ] Plane →L[ℝ] ℝ :=
  BilinearTensor.pullback ((proj 1 : Plane →L[ℝ] ℝ).smulRight (proj 1))
    (shearLinear (2 * p 0)).toContinuousLinearMap

def spatialTensor : CovariantTwoTensor 1 Plane :=
  ⟨spatialTensorCoefficients, by
    have h : ContDiff ℝ ∞ spatialTensorCoefficients :=
      BilinearTensor.contDiff_pullback contDiff_const
        (shearLinear_contDiff.comp (contDiff_const.mul (contDiff_apply ℝ _ 0)))
    intro x
    rw [contMDiffAt_section]
    convert h.contMDiff.contMDiffAt (x := x) using 1
    funext y
    ext v w
    simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates]
    rfl⟩

theorem spatialTensor_coordinates (p v w : Plane) :
    spatialTensor p v w = (v 1 + 2 * p 0 * v 0) * (w 1 + 2 * p 0 * w 0) := rfl

theorem spatialTensor_contract (p : Plane) : metric.contractField spatialTensor p = 1 := by
  change metric.contract p (spatialTensorCoefficients p) = 1
  rw [spatialTensorCoefficients, contract_covariance, LorentzMetric.contract_smulRight,
    LorentzMetric.minkowskiMetric_sharp]
  change Minkowski.sharp .timeNegative (proj 1 : Plane →L[ℝ] ℝ) 1 = 1
  simp [Minkowski.sharp_apply, lorentzSign]

/-- The nonlinear metric is the pullback of the Minkowski metric as a smooth
tensor field, using the general manifold pullback operation. -/
theorem metric_tensor_pullback :
    metric.toTensor = CovariantTwoTensor.pullback (d := 1)
      shearDiffeomorph (minkowskiMetric .timeNegative 1).toTensor := by
  ext p v w
  rw [CovariantTwoTensor.pullback_apply (d := 1)]
  exact metric_covariance p v w

def standardChart : OpenPartialHomeomorph Plane Plane :=
  (Homeomorph.refl Plane).toOpenPartialHomeomorph

def inertialChart : OpenPartialHomeomorph Plane Plane :=
  shearDiffeomorph.toHomeomorph.toOpenPartialHomeomorph

theorem standardChart_mem_maximalAtlas :
    standardChart ∈ IsManifold.maximalAtlas 𝓘(ℝ, Plane) ∞ Plane :=
  standardChart.mem_maximalAtlas_of_contMDiffOn
    contMDiff_id.contMDiffOn contMDiff_id.contMDiffOn

theorem inertialChart_mem_maximalAtlas :
    inertialChart ∈ IsManifold.maximalAtlas 𝓘(ℝ, Plane) ∞ Plane :=
  inertialChart.mem_maximalAtlas_of_contMDiffOn
    shearDiffeomorph.contMDiff.contMDiffOn shearDiffeomorph.symm.contMDiff.contMDiffOn

/-- Both charts cover the plane, so their overlap is nonempty and open. -/
theorem chart_overlap : standardChart.source ∩ inertialChart.source = Set.univ := by
  simp [standardChart, inertialChart]

theorem transition_apply (p : Plane) :
    (standardChart.symm.trans inertialChart) p = shear p := rfl

/-- The mixed Jacobian entry varies with the time coordinate. -/
theorem jacobian_time_space (p : Plane) :
    mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shear p (Pi.single 0 1) 1 = 2 * p 0 := by
  rw [mfderiv_shear]
  change (Pi.single 0 1 : Plane) 1 +
    2 * p 0 * (Pi.single 0 1 : Plane) 0 = 2 * p 0
  simp

theorem metric_nonconstant : metric.form ![0, 0] ≠ metric.form ![1, 0] := by
  intro h
  have h' := congrArg (fun B : Plane →L[ℝ] Plane →L[ℝ] ℝ =>
    B (Pi.single 0 1) (Pi.single 0 1)) h
  change metric.form ![0, 0] (Pi.single 0 1) (Pi.single 0 1) =
    metric.form ![1, 0] (Pi.single 0 1) (Pi.single 0 1) at h'
  rw [metric_time_time, metric_time_time] at h'
  norm_num at h'

theorem jacobian_nonconstant :
    mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shear ![0, 0] ≠
      mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shear ![1, 0] := by
  intro h
  have h' := congrArg (fun A : Plane →L[ℝ] Plane => A (Pi.single 0 1) 1) h
  change mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shear ![0, 0] (Pi.single 0 1) 1 =
    mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shear ![1, 0] (Pi.single 0 1) 1 at h'
  rw [jacobian_time_space, jacobian_time_space] at h'
  norm_num at h'

theorem opposite_metric_covariance (p v w : Plane) :
    metric.opposite.form p v w = (minkowskiMetric .timePositive 1).form (shear p)
      (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shear p v)
      (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shear p w) := by
  change -(metric.form p v w) = minkowskiForm .timePositive 1 _ _
  rw [metric_covariance]
  exact (congrArg (fun B : Plane →L[ℝ] Plane →L[ℝ] ℝ =>
    B (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shear p v)
      (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shear p w))
    (minkowskiForm_opposite .timeNegative 1)).symm

end ProjectAInos.SmoothGeometry.LorentzianCharts
