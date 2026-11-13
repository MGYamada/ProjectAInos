/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.Ricci
public import ProjectAInos.SmoothGeometry.Lorentzian.ConnectionExamples

/-! # Native curvature checks in flat spacetime

Both the standard Minkowski model and its nonlinear shear presentation have
zero curvature. The shear connection has the nonzero coefficient `Γˣ_tt = 2`.
These are evaluations of the constructed tangent-bundle curvature tensor.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle VectorField
open scoped Manifold ContDiff

namespace ProjectAInos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ}

/-- Constant model fields can be used to evaluate the intrinsic curvature. -/
theorem curvature_modelField (g : LorentzMetric σ d (MinkowskiModel d))
    (x u v w : MinkowskiModel d) :
    g.curvature x (modelField u x) (modelField v x) (modelField w x) =
      g.curvatureField (modelField u) (modelField v) (modelField w) x :=
  g.curvature_apply ((modelField_contMDiff u x).of_le (by simp))
    ((modelField_contMDiff v x).of_le (by simp)) ((modelField_contMDiff w x).of_le (by simp))

/-- The standard Minkowski connection annihilates constant model fields. -/
@[simp] theorem minkowski_covariantField_model (σ : LorentzConvention) (d : ℕ)
    (u v : MinkowskiModel d) :
    (minkowskiMetric σ d).covariantField (modelField u) (modelField v) = 0 := by
  funext x
  apply (NormedSpace.fromTangentSpace x).injective
  ext k
  simpa [covariantField] using
    (minkowskiMetric σ d).leviCivita_model_coordinates
      (Y := fun _ => v) (differentiableAt_const v) u k

/-- Flat Minkowski curvature in every dimension and both Lorentz conventions. -/
@[simp] theorem minkowski_curvature (σ : LorentzConvention) (d : ℕ)
    (x : MinkowskiModel d) : (minkowskiMetric σ d).curvature x = 0 := by
  ext u v w
  obtain ⟨a, rfl⟩ := (NormedSpace.fromTangentSpace x).symm.surjective u
  obtain ⟨b, rfl⟩ := (NormedSpace.fromTangentSpace x).symm.surjective v
  obtain ⟨c, rfl⟩ := (NormedSpace.fromTangentSpace x).symm.surjective w
  change (minkowskiMetric σ d).curvature x (modelField a x) (modelField b x)
    (modelField c x) = 0
  rw [curvature_modelField]
  simp only [curvatureField, minkowski_covariantField_model]
  simp [covariantField]

@[simp] theorem minkowski_ricci (σ : LorentzConvention) (d : ℕ)
    (x : MinkowskiModel d) : (minkowskiMetric σ d).ricci x = 0 :=
  ricci_eq_zero_of_curvature_eq_zero _ x (minkowski_curvature σ d x)

@[simp] theorem minkowski_scalarCurvature (σ : LorentzConvention) (d : ℕ)
    (x : MinkowskiModel d) : (minkowskiMetric σ d).scalarCurvature x = 0 := by
  simp [scalarCurvature_apply, contract]

end ProjectAInos.SmoothGeometry.LorentzMetric

namespace ProjectAInos.SmoothGeometry.LorentzianCharts

open LorentzMetric

/-- The constant-field derivative in shear coordinates is again a constant field. -/
theorem covariantField_model (v w : Plane) :
    metric.covariantField (modelField v) (modelField w) = modelField ![0, 2 * v 0 * w 0] :=
  funext (fun p => leviCivita_modelField p v w)

/-- Nonzero connection coefficients in the nonlinear chart still give zero
intrinsic curvature; the same tensor is evaluated in either chart. -/
@[simp] theorem curvature_shear (p : Plane) : metric.curvature p = 0 := by
  ext u v w
  obtain ⟨a, rfl⟩ := (NormedSpace.fromTangentSpace p).symm.surjective u
  obtain ⟨b, rfl⟩ := (NormedSpace.fromTangentSpace p).symm.surjective v
  obtain ⟨c, rfl⟩ := (NormedSpace.fromTangentSpace p).symm.surjective w
  change metric.curvature p (modelField a p) (modelField b p) (modelField c p) = 0
  rw [curvature_modelField]
  simp only [curvatureField, covariantField_model]
  simp [covariantField, modelField_bracket, modelField]

@[simp] theorem ricci_shear (p : Plane) : metric.ricci p = 0 :=
  metric.ricci_eq_zero_of_curvature_eq_zero p (curvature_shear p)

@[simp] theorem scalarCurvature_shear (p : Plane) : metric.scalarCurvature p = 0 := by
  simp [scalarCurvature_apply, contract]

end ProjectAInos.SmoothGeometry.LorentzianCharts
