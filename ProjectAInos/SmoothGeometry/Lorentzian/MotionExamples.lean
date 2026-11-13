/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.Geodesic
public import ProjectAInos.SmoothGeometry.Lorentzian.ParallelTransport
public import ProjectAInos.SmoothGeometry.Lorentzian.ConnectionExamples
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-! # Motion in the standard and nonlinear Minkowski charts -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle FiberBundle VectorField ContinuousLinearMap
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ}
local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)

/-- Model-coordinate curves and vector components give genuine regular
sections along the curve. -/
theorem modelAlong_contMDiffAt {n : ℕ∞ω} {γ V : ℝ → E} {t : ℝ}
    (hγ : ContDiffAt ℝ n γ t) (hV : ContDiffAt ℝ n V t) :
    ContMDiffAt 𝓘(ℝ) ((I).prod I) n
      (fun s => TotalSpace.mk' E (γ s) (modelField (V s) (γ s))) t := by
  rw [contMDiffAt_totalSpace]
  refine ⟨hγ.contMDiffAt, ?_⟩
  simpa [modelField, NormedSpace.fromTangentSpace, tangentSpaceCastModel,
    TangentBundle.trivializationAt_apply] using! hV.contMDiffAt

/-- Model velocity is the ordinary derivative in the canonical fibre identification. -/
theorem curveVelocity_model (γ : ℝ → E) (t : ℝ) :
    curveVelocity γ t = modelField (deriv γ t) (γ t) := by
  rw [curveVelocity, mfderiv_eq_fderiv]
  rfl

/-- The model-coordinate expression still evaluates the native connection. -/
theorem covariantAlong_model (g : LorentzMetric σ d E) (γ V : ℝ → E) (t : ℝ) :
    g.covariantAlong (fun s => modelField (V s) (γ s)) t =
      modelField (deriv V t) (γ t) +
        g.leviCivita (modelField (V t)) (γ t) (modelField (deriv γ t) (γ t)) := by
  let e := (Homeomorph.refl E).toOpenPartialHomeomorph
  have he : e ∈ IsManifold.maximalAtlas I ∞ E := IsManifold.chart_mem_maximalAtlas (γ t)
  have hf (v : E) : chartField e v = modelField v := by
    funext y
    simp [e, chartField, mpullback_apply]
  have hc : alongComponents e (fun s => modelField (V s) (γ s)) = V := by
    funext s
    change chartTangentMap e (γ s) (modelField (V s) (γ s)) = V s
    rw [← hf]
    exact chartTangentMap_field he (Set.mem_univ _) _
  change g.chartCovariantAlong e (fun s => modelField (V s) (γ s)) t = _
  simp only [chartCovariantAlong, hc, hf, curveVelocity_model]

/-- In Minkowski coordinates covariant differentiation along every curve
is ordinary differentiation of the vector components. -/
theorem minkowski_covariantAlong (σ : LorentzConvention) (γ V : ℝ → E) (t : ℝ) :
    (minkowskiMetric σ d).covariantAlong (fun s => modelField (V s) (γ s)) t =
      modelField (deriv V t) (γ t) := by
  rw [covariantAlong_model]
  have hz : (minkowskiMetric σ d).leviCivita (modelField (V t)) (γ t)
      (modelField (deriv γ t) (γ t)) = 0 := by
    apply (NormedSpace.fromTangentSpace (γ t)).injective
    ext k
    simpa using (minkowskiMetric σ d).leviCivita_model_coordinates
      (Y := fun _ => V t) (differentiableAt_const (V t)) (deriv γ t) k
  rw [hz, add_zero]

/-- Every affine model line is an affine geodesic for either Minkowski
signature, including timelike, spacelike, null and zero velocities. -/
theorem minkowski_affine_geodesic (σ : LorentzConvention) (p v : E) :
    (minkowskiMetric σ d).IsGeodesicOn Set.univ (fun t : ℝ => p + t • v) := by
  let γ : ℝ → E := fun t => p + t • v
  have hγ : ContDiff ℝ ∞ γ := by dsimp [γ]; fun_prop
  have hd (t : ℝ) : deriv γ t = v := by
    simpa [γ] using ((hasDerivAt_id t).smul_const v |>.const_add p).deriv
  have hv : curveVelocity γ = fun t => modelField v (γ t) := by
    funext t
    rw [curveVelocity_model, hd]
  intro t _
  refine ⟨(hγ.of_le (by simp)).contMDiff.contMDiffAt, ?_⟩
  change (minkowskiMetric σ d).covariantAlong (curveVelocity γ) t = 0
  rw [hv, minkowski_covariantAlong, deriv_const]
  exact map_zero _

end ProjectAInos.SmoothGeometry.LorentzMetric

namespace ProjectAInos.SmoothGeometry.LorentzianCharts

open LorentzMetric

/-- The inertial time axis in the nonlinear `(t,x)` chart. -/
def inertialTimePath (s : ℝ) : Plane := ![s, -s^2]

theorem inertialTimePath_contDiff : ContDiff ℝ ∞ inertialTimePath := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun s : ℝ => s)
    fun_prop
  · change ContDiff ℝ ∞ (fun s : ℝ => -s^2)
    fun_prop

theorem inertialTimePath_hasDerivAt (s : ℝ) :
    HasDerivAt inertialTimePath ![1, -2 * s] s := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasDerivAt_id s
  · change HasDerivAt (fun r : ℝ => -r^2) (-2 * s) s
    convert ((hasDerivAt_id s).pow 2).neg using 1
    · rfl
    · norm_num [neg_mul]

/-- Constant inertial vector components in the nonlinear chart. -/
def parallelComponents (a b : ℝ) (s : ℝ) : Plane := ![a, b - 2 * s * a]

theorem parallelComponents_contDiff (a b : ℝ) : ContDiff ℝ ∞ (parallelComponents a b) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun _ : ℝ => a)
    fun_prop
  · change ContDiff ℝ ∞ (fun s : ℝ => b - 2 * s * a)
    fun_prop

theorem parallelComponents_hasDerivAt (a b s : ℝ) :
    HasDerivAt (parallelComponents a b) ![0, -2 * a] s := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasDerivAt_const s a
  · simpa [parallelComponents] using
      (((hasDerivAt_id s).const_mul 2).mul_const a).const_sub b

/-- A genuinely varying vector field along the nonlinear path. -/
def parallelField (a b : ℝ) : AlongField (d := 1) inertialTimePath :=
  fun s => modelField (parallelComponents a b s) (inertialTimePath s)

theorem parallelField_covariantAlong (a b s : ℝ) :
    metric.covariantAlong (parallelField a b) s = 0 := by
  unfold parallelField
  rw [covariantAlong_model, (inertialTimePath_hasDerivAt s).deriv,
    (parallelComponents_hasDerivAt a b s).deriv, leviCivita_modelField]
  apply (NormedSpace.fromTangentSpace (inertialTimePath s)).injective
  ext i
  fin_cases i <;> simp [modelField, parallelComponents]

theorem parallelField_parallel (a b : ℝ) : metric.IsParallelOn Set.univ (parallelField a b) := by
  intro s _
  exact ⟨(modelAlong_contMDiffAt inertialTimePath_contDiff.contDiffAt
    (parallelComponents_contDiff a b).contDiffAt).mdifferentiableAt (by simp),
    parallelField_covariantAlong a b s⟩

/-- The coordinate parabola is an affine geodesic of the nonlinear metric. -/
theorem inertialTimePath_geodesic : metric.IsGeodesicOn Set.univ inertialTimePath := by
  have hv : curveVelocity inertialTimePath = parallelField 1 0 := by
    funext s
    rw [curveVelocity_model, (inertialTimePath_hasDerivAt s).deriv]
    simp [parallelField, parallelComponents]
  intro s _
  refine ⟨(inertialTimePath_contDiff.of_le (by simp)).contMDiff.contMDiffAt, ?_⟩
  rw [hv]
  exact parallelField_covariantAlong 1 0 s

/-- In the actual inertial chart, this varying parallel field has constant components. -/
theorem parallelField_inertial_components (a b s : ℝ) :
    alongComponents inertialChart (parallelField a b) s = ![a, b] := by
  change NormedSpace.fromTangentSpace (shear (inertialTimePath s))
    (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shear (inertialTimePath s)
      (modelField (parallelComponents a b s) (inertialTimePath s))) = _
  rw [mfderiv_shear]
  change shearLinear (2 * inertialTimePath s 0) (parallelComponents a b s) = ![a, b]
  ext i
  fin_cases i <;> simp [parallelComponents, inertialTimePath]

/-- Endpoint transport in nonlinear coordinates is the shear matrix with
lower-left coefficient `-2 (s₁-s₀)`. This evaluates the intrinsic transport
constructed from existence and uniqueness, not a separate matrix definition. -/
theorem parallelTransport_model (s₀ s₁ : ℝ) (v : Plane) :
    metric.parallelTransport (a := s₀) (b := s₁)
      (fun t _ => (inertialTimePath_contDiff.of_le (by simp)).contMDiff.contMDiffAt (x := t))
      (modelField v (inertialTimePath s₀)) =
        modelField ![v 0, v 1 - 2 * (s₁ - s₀) * v 0] (inertialTimePath s₁) := by
  have h := metric.parallelTransport_apply_eq (a := s₀) (b := s₁)
    (fun t _ => (inertialTimePath_contDiff.of_le (by simp)).contMDiff.contMDiffAt (x := t))
    ((parallelField_parallel (v 0) (v 1 + 2 * s₀ * v 0)).mono (Set.subset_univ _))
  have hinit : parallelField (v 0) (v 1 + 2 * s₀ * v 0) s₀ =
      modelField v (inertialTimePath s₀) := by
    unfold parallelField
    congr 1
    ext i
    fin_cases i <;> simp [parallelComponents]
  have hlast : parallelField (v 0) (v 1 + 2 * s₀ * v 0) s₁ =
      modelField ![v 0, v 1 - 2 * (s₁ - s₀) * v 0] (inertialTimePath s₁) := by
    unfold parallelField
    congr 1
    ext i
    fin_cases i <;> simp [parallelComponents]
    ring
  rwa [hinit, hlast] at h

end ProjectAInos.SmoothGeometry.LorentzianCharts
