/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.LorentzFrame
public import ProjectAinos.SmoothGeometry.Lorentzian.ChartDerivatives
public import ProjectAinos.SmoothGeometry.Manifold.OpenTangent
public import ProjectAinos.SmoothGeometry.Lorentzian.AlongCurveMetric
public import ProjectAinos.SmoothGeometry.Lorentzian.SpatialForm

/-!
# Lorentz metrics from coordinate coefficients

An open set `U` of the model space `MinkowskiModel d` is a manifold with the single chart
`physicalChart`, the inclusion. A `CoordinateMetric σ d U` is a family of bilinear forms on the
model space that is smooth on `U` and has the signature of `σ` at every point of `U`.

* `CoordinateMetric.toLorentzMetric`: it is a Lorentz metric on the manifold `U`.
* `toLorentzMetric_chartComponent`: its components in the chart are the coefficients
  `g(eᵢ, eⱼ)`.
* `CoordinateMetric.ofCriterion`: a symmetric smooth family that is negative on the time axis
  and positive definite on the space, after the factor `−σ.timeSign`, is a coordinate metric.
* `CoordinateMetric.minkowski`: the constant Minkowski form is an instance.
* `CoordinateMetric.spatialMetric_pos`, `LorentzMetric.spatialForm_nonneg`,
  `LorentzMetric.spatialForm_pos`: the spatial metric of the observer at rest, and the spatial
  form of a timelike observer at every event of a Lorentz manifold, are positive.
-/

@[expose] public section

noncomputable section

open Bundle ContinuousLinearMap Set TopologicalSpace
open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ}

/-! ### The chart of an open set of the model -/

namespace CoordinateMetric

/-- The chart of an open set of the model space: the inclusion. -/
def physicalChart {U : Opens (MinkowskiModel d)} (x : U) :
    OpenPartialHomeomorph U (MinkowskiModel d) :=
  chartAt (MinkowskiModel d) x

theorem physicalChart_eq {U : Opens (MinkowskiModel d)} (x y : U) :
    physicalChart x = physicalChart y := by
  simp only [physicalChart, Opens.chartAt_eq, chartAt_self_eq]

@[simp] theorem physicalChart_apply {U : Opens (MinkowskiModel d)} (x y : U) :
    physicalChart x y = (y : MinkowskiModel d) := by
  simp [physicalChart, Opens.chartAt_eq, chartAt_self_eq]

@[simp] theorem physicalChart_source {U : Opens (MinkowskiModel d)} (x : U) :
    (physicalChart x).source = univ := by
  simp [physicalChart, Opens.chartAt_eq, chartAt_self_eq]

@[simp] theorem physicalChart_target {U : Opens (MinkowskiModel d)} (x : U) :
    (physicalChart x).target = (U : Set (MinkowskiModel d)) := by
  ext y
  constructor
  · intro hy
    rw [← (physicalChart x).right_inv hy, physicalChart_apply]
    exact ((physicalChart x).symm y).property
  · intro hy
    exact (physicalChart x).map_source (x := ⟨y, hy⟩) (by simp)

theorem physicalChart_mem {U : Opens (MinkowskiModel d)} (x : U) :
    physicalChart x ∈ IsManifold.maximalAtlas 𝓘(ℝ, MinkowskiModel d) ∞ U :=
  IsManifold.chart_mem_maximalAtlas x

theorem physicalChart_symmL {U : Opens (MinkowskiModel d)} (x y : U) :
    (trivializationAt (MinkowskiModel d) (TangentSpace 𝓘(ℝ, MinkowskiModel d)) x).symmL ℝ y =
      (ContinuousLinearMap.id ℝ (MinkowskiModel d) : MinkowskiModel d →L[ℝ] MinkowskiModel d) := by
  have hy : y ∈ (chartAt (MinkowskiModel d) x).source := by
    change y ∈ (physicalChart x).source
    simp
  rw [TangentBundle.symmL_trivializationAt_eq_core hy]
  have he : achart (MinkowskiModel d) x = achart (MinkowskiModel d) y :=
    Subtype.ext (physicalChart_eq x y)
  rw [he]
  apply ContinuousLinearMap.ext
  intro v
  exact (tangentBundleCore 𝓘(ℝ, MinkowskiModel d) U).coordChange_self
    (achart (MinkowskiModel d) y) y (mem_achart_source (MinkowskiModel d) y) v

@[simp] theorem physicalChart_tangentMap {U : Opens (MinkowskiModel d)} (x y : U)
    (v : TangentSpace 𝓘(ℝ, MinkowskiModel d) y) :
    chartTangentMap (physicalChart x) y v = (v : MinkowskiModel d) := by
  have he : (physicalChart x : U → MinkowskiModel d) = Subtype.val :=
    funext (physicalChart_apply x)
  change NormedSpace.fromTangentSpace (physicalChart x y)
    (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d)
      (physicalChart x : U → MinkowskiModel d) y v) = v
  rw [he, Manifold.mfderiv_subtype_val_apply U]
  rfl

end CoordinateMetric

/-! ### Coordinate metrics -/

/-- A family of bilinear forms on the model space that is smooth on `U` and has the signature
of `σ` at every point of `U`. -/
structure CoordinateMetric (σ : LorentzConvention) (d : ℕ) (U : Opens (MinkowskiModel d)) where
  /-- The form at a point. -/
  form : MinkowskiModel d → MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ
  /-- The family is smooth on `U`. -/
  smooth : ContDiffOn ℝ ∞ form U
  /-- The form has the signature of `σ` at every point of `U`. -/
  signature : ∀ x ∈ U, ∃ e : MinkowskiModel d ≃L[ℝ] MinkowskiModel d,
    ∀ v w, form x v w = minkowskiForm σ d (e v) (e w)

namespace CoordinateMetric

variable {U : Opens (MinkowskiModel d)} (g : CoordinateMetric σ d U)

/-- The Lorentz metric on the manifold `U`. -/
def toLorentzMetric : LorentzMetric σ d U where
  form x := g.form x
  smooth := by
    have hs := g.smooth.contMDiffOn.comp_contMDiff
      (contMDiff_subtype_val (U := U)) (fun x : U => x.property)
    intro x
    refine (contMDiffAt_section x).mpr ?_
    convert hs x using 1
    funext y
    ext v w
    have hy : y ∈ (trivializationAt (MinkowskiModel d)
        (TangentSpace 𝓘(ℝ, MinkowskiModel d)) x).baseSet := by
      change y ∈ (physicalChart x).source
      simp
    rw [hom_trivializationAt_apply, inCoordinates_apply_eq₂ hy hy (by simp),
      ← Trivialization.symmL_apply (R := ℝ) _ hy, ← Trivialization.symmL_apply (R := ℝ) _ hy,
      physicalChart_symmL]
    simp
    rfl
  signature x := g.signature x x.property

@[simp] theorem toLorentzMetric_form (x : U) (v w : TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    g.toLorentzMetric.form x v w = g.form x v w := rfl

/-- The co-ordinate field of a model vector is that vector. -/
theorem physicalChart_chartField (x y : U) (v : MinkowskiModel d) :
    (chartField (physicalChart x) v y : MinkowskiModel d) = v :=
  (physicalChart_tangentMap x y _).symm.trans
    (chartTangentMap_field (physicalChart_mem x) (by simp : y ∈ (physicalChart x).source) v)

/-- The metric in the chart is the given family of forms. -/
theorem toLorentzMetric_chartMetric (x y : U) (v w : MinkowskiModel d) :
    g.toLorentzMetric.chartMetric (physicalChart x) y v w = g.form y v w := by
  rw [chartMetric_apply, toLorentzMetric_form, physicalChart_chartField,
    physicalChart_chartField]

/-- The components of the metric in the chart are the coefficients `g(eᵢ, eⱼ)`. -/
theorem toLorentzMetric_chartComponent (x y : U) (i j : Fin (d + 1)) :
    g.toLorentzMetric.chartComponent (physicalChart x) y i j =
      g.form y (Pi.single i 1) (Pi.single j 1) := by
  rw [chartComponent, toLorentzMetric_form, physicalChart_chartField, physicalChart_chartField]

/-! ### Coefficients, the inverse and the Christoffel symbols -/

/-- The matrix `g(eᵢ, eⱼ)` of the coefficients at a point. -/
def coefficient (y : MinkowskiModel d) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  Matrix.of fun i j => g.form y (Pi.single i 1) (Pi.single j 1)

theorem form_apply (y v w : MinkowskiModel d) :
    g.form y v w = ∑ i, ∑ j, g.coefficient y i j * v i * w j := by
  conv_lhs => rw [pi_eq_sum_univ' v, pi_eq_sum_univ' w]
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, coefficient, Matrix.of_apply,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem coefficient_symmetric {y : MinkowskiModel d} (hy : y ∈ U) (i j : Fin (d + 1)) :
    g.coefficient y i j = g.coefficient y j i := by
  obtain ⟨e, he⟩ := g.signature y hy
  simp only [coefficient, Matrix.of_apply, he, minkowskiForm_symmetric]

theorem coefficient_contDiffOn (i j : Fin (d + 1)) :
    ContDiffOn ℝ ∞ (fun y => g.coefficient y i j) U :=
  (g.smooth.clm_apply contDiffOn_const).clm_apply contDiffOn_const

theorem coefficient_mul_inverseComponent (x y : U) :
    g.coefficient y * Matrix.of (g.toLorentzMetric.inverseComponent y
      (chartTangentEquiv (physicalChart_mem x) (by simp))) = 1 := by
  let e := chartTangentEquiv (physicalChart_mem x) (by simp : y ∈ (physicalChart x).source)
  have he (v : TangentSpace 𝓘(ℝ, MinkowskiModel d) y) : e v = (v : MinkowskiModel d) :=
    physicalChart_tangentMap x y v
  ext k l
  let v := g.toLorentzMetric.sharp y (Tensor.coordinateCovector y e l)
  have h := congrArg
    (fun α : TangentSpace 𝓘(ℝ, MinkowskiModel d) y →L[ℝ] ℝ => α (Pi.single k 1))
    (g.toLorentzMetric.flat_sharp y (Tensor.coordinateCovector y e l))
  change g.form y v (Pi.single k 1) = e (Pi.single k 1) l at h
  replace h := ((g.form_apply y v (Pi.single k 1)).symm.trans h).trans
    (congrFun (he (Pi.single k 1)) l)
  have hs : (∑ i, g.coefficient y i k * v i) = (Pi.single k (1 : ℝ) : MinkowskiModel d) l := by
    simpa [Pi.single_apply, mul_ite] using h
  change (∑ i, g.coefficient y k i * e v i) = _
  rw [he]
  simp_rw [g.coefficient_symmetric y.property k]
  rw [hs]
  simp [Pi.single_apply, Matrix.one_apply, eq_comm]

/-- The components of the inverse metric are the entries of the inverse matrix. -/
theorem toLorentzMetric_inverseComponent (x y : U) (i j : Fin (d + 1)) :
    g.toLorentzMetric.inverseComponent y
        (chartTangentEquiv (physicalChart_mem x) (by simp)) i j =
      (g.coefficient y)⁻¹ i j := by
  have h := (Matrix.inv_eq_right_inv (g.coefficient_mul_inverseComponent x y)).symm
  exact congrFun (congrFun h i) j

theorem coefficient_mul_inv (y : U) : g.coefficient y * (g.coefficient y)⁻¹ = 1 := by
  rw [Matrix.inv_eq_right_inv (g.coefficient_mul_inverseComponent y y)]
  exact g.coefficient_mul_inverseComponent y y

/-- The derivative of a component along a co-ordinate field is the derivative of the
coefficient. -/
theorem toLorentzMetric_component_derivative (x y : U) (i j : Fin (d + 1))
    (v : MinkowskiModel d) :
    mvfderiv 𝓘(ℝ, MinkowskiModel d)
        (fun z => g.toLorentzMetric.chartComponent (physicalChart x) z i j)
        y (chartField (physicalChart x) v y) =
      fderiv ℝ (fun z => g.coefficient z i j) y v := by
  let G := fun z : U => g.toLorentzMetric.chartComponent (physicalChart x) z i j
  have hG : MDifferentiableAt 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, ℝ) G y := by
    have hs := (g.coefficient_contDiffOn i j).contMDiffOn.comp_contMDiff
      (contMDiff_subtype_val (U := U)) (fun x : U => x.property)
    have hEq : G = (fun z : U => g.coefficient z i j) :=
      funext fun z => g.toLorentzMetric_chartComponent x z i j
    rw [hEq]
    exact (hs y).mdifferentiableAt (by simp)
  change mvfderiv 𝓘(ℝ, MinkowskiModel d) G y _ = _
  rw [mvfderiv_chartField (physicalChart_mem x) (by simp) hG]
  have hEq : G ∘ (physicalChart x).symm =ᶠ[𝓝 (y : MinkowskiModel d)]
      fun z => g.coefficient z i j := by
    filter_upwards [U.isOpen.mem_nhds y.property] with z hz
    change g.toLorentzMetric.chartComponent (physicalChart x)
      ((physicalChart x).symm z) i j = _
    rw [g.toLorentzMetric_chartComponent x, ← physicalChart_apply x ((physicalChart x).symm z),
      (physicalChart x).right_inv (by simpa using hz)]
    rfl
  rw [physicalChart_apply, hEq.fderiv_eq]

/-- The Christoffel symbols in the chart, from the coefficients and their derivatives. -/
theorem toLorentzMetric_christoffel (x y : U) (k i j : Fin (d + 1)) :
    g.toLorentzMetric.chartChristoffel (physicalChart x) y k i j =
      ∑ l, (g.coefficient y)⁻¹ k l *
        (fderiv ℝ (fun z => g.coefficient z j l) y (Pi.single i 1) +
         fderiv ℝ (fun z => g.coefficient z l i) y (Pi.single j 1) -
         fderiv ℝ (fun z => g.coefficient z i j) y (Pi.single l 1)) / 2 := by
  rw [chartChristoffel_eq _ (physicalChart_mem x) (by simp)]
  simp_rw [g.toLorentzMetric_inverseComponent, g.toLorentzMetric_component_derivative]

/-! ### The criterion and an instance -/

/-- A symmetric smooth family that, after the factor `−σ.timeSign`, is negative on the time
axis and positive definite on the space at every point of `U` is a coordinate metric. -/
def ofCriterion (B : MinkowskiModel d → MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ)
    (hB : ContDiffOn ℝ ∞ B U) (hs : ∀ x ∈ U, ∀ v w, B x v w = B x w v)
    (ht : ∀ x ∈ U, -σ.timeSign *
      B x (Fin.cons 1 (0 : Fin d → ℝ)) (Fin.cons 1 (0 : Fin d → ℝ)) < 0)
    (hx : ∀ x ∈ U, ∀ v : Fin d → ℝ, v ≠ 0 →
      0 < -σ.timeSign * B x (Fin.cons 0 v) (Fin.cons 0 v)) : CoordinateMetric σ d U where
  form := B
  smooth := hB
  signature x hx' := Minkowski.exists_lorentzFrame_convention σ (B x) (hs x hx') (ht x hx')
    (hx x hx')

@[simp] theorem ofCriterion_form
    (B : MinkowskiModel d → MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ)
    (hB : ContDiffOn ℝ ∞ B U) (hs : ∀ x ∈ U, ∀ v w, B x v w = B x w v)
    (ht : ∀ x ∈ U, -σ.timeSign *
      B x (Fin.cons 1 (0 : Fin d → ℝ)) (Fin.cons 1 (0 : Fin d → ℝ)) < 0)
    (hx : ∀ x ∈ U, ∀ v : Fin d → ℝ, v ≠ 0 →
      0 < -σ.timeSign * B x (Fin.cons 0 v) (Fin.cons 0 v)) :
    (ofCriterion B hB hs ht hx).form = B := rfl

variable (σ d U) in
/-- The constant Minkowski form, on every open set. -/
def minkowski : CoordinateMetric σ d U where
  form := fun _ => minkowskiForm σ d
  smooth := contDiffOn_const
  signature _ _ := ⟨ContinuousLinearEquiv.refl ℝ _, fun _ _ => rfl⟩

theorem minkowski_chartComponent (x y : U) (i j : Fin (d + 1)) :
    (minkowski σ d U).toLorentzMetric.chartComponent (physicalChart x) y i j =
      if i = j then lorentzSign σ i else 0 := by
  rw [toLorentzMetric_chartComponent, minkowski, minkowskiForm_apply, Finset.sum_eq_single i]
  · by_cases h : i = j
    · subst h; simp
    · simp [h]
  · intro k _ hk
    simp [Pi.single_apply, hk]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-! ### The spatial metric of the observer at rest -/

/-- Where `g₀₀ < 0`, the spatial metric `γ_{ij} = g_{ij} − g_{0i} g_{0j}/g_{00}` of the observer at
rest is positive definite. -/
theorem spatialMetric_pos (g : CoordinateMetric .timeNegative d U) {x : MinkowskiModel d}
    (hx : x ∈ U) (h00 : g.form x (Pi.single 0 1) (Pi.single 0 1) < 0) {ξ : Fin d → ℝ}
    (hξ : ξ ≠ 0) : 0 < ∑ i, ∑ j, Minkowski.spatialMetric (g.form x) i j * ξ i * ξ j := by
  obtain ⟨e, he⟩ := g.signature x hx
  exact Minkowski.spatialMetric_pos he h00 hξ

end CoordinateMetric

namespace LorentzMetric

variable {M : Type} [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

/-- At every event, the spatial form of an observer with a timelike velocity `u` is positive
semidefinite. -/
theorem spatialForm_nonneg (g : LorentzMetric .timeNegative d M) (x : M)
    {u : TangentSpace 𝓘(ℝ, MinkowskiModel d) x} (hu : g.form x u u < 0)
    (v : TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    0 ≤ Minkowski.spatialForm (g.form x) u v v := by
  obtain ⟨e, he⟩ := g.signature x
  exact Minkowski.spatialForm_nonneg he hu v

/-- At every event, the spatial form of an observer with a timelike velocity `u` is positive on
every displacement whose part orthogonal to `u` is not zero. -/
theorem spatialForm_pos (g : LorentzMetric .timeNegative d M) (x : M)
    {u v : TangentSpace 𝓘(ℝ, MinkowskiModel d) x} (hu : g.form x u u < 0)
    (hv : Minkowski.orthogonalPart (g.form x) u v ≠ 0) :
    0 < Minkowski.spatialForm (g.form x) u v v := by
  obtain ⟨e, he⟩ := g.signature x
  exact Minkowski.spatialForm_pos he hu hv

end LorentzMetric

end ProjectAinos.SmoothGeometry
