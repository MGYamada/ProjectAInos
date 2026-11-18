/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.NewtonianBounds
public import ProjectAinos.GeneralRelativity.CoordinateTime
public import ProjectAinos.SmoothGeometry.Manifold.OpenTangent
public import ProjectAinos.SmoothGeometry.Lorentzian.ChartDerivatives
public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateMetric
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.QuadraticForm.Real

/-! # Native Lorentz metrics in physical time coordinates -/

@[expose] public section
noncomputable section

open Bundle ContinuousLinearMap Set TopologicalSpace
open scoped Manifold ContDiff Topology

namespace ProjectAinos.GeneralRelativity.NewtonianMetricFamily
open SmoothGeometry LorentzMetric

local notation "E" => NewtonianCoordinates
local notation "S" => NewtonianSpace
local notation "I" => 𝓘(ℝ, E)

theorem form_symmetric {U : Opens E} (f : NewtonianMetricFamily U) {c : ℝ}
    (hc : 0 < c) {q : E} (hq : q ∈ U) (v w : E) :
    f.form c q v w = f.form c q w v := by
  rw [form_apply, form_apply, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [f.coefficient_symmetric hc hq j i]
  ring

/-- Every sufficiently large member has Lorentz signature at every point. -/
theorem form_signature {U : Opens E} (f : NewtonianMetricFamily U) {c : ℝ}
    (hc : 1 ≤ c) (hlarge : 9 * f.bound < c^2) (q : U) :
    ∃ e : E ≃L[ℝ] E, ∀ v w,
      f.form c q v w = minkowskiForm .timeNegative 3 (e v) (e w) := by
  apply Minkowski.exists_lorentzFrame (d := 3) (f.form c q)
    (f.form_symmetric (by linarith) q.property)
  · exact f.form_timeVelocity_neg hc q.property (v := 0) (V := 0) (by simp) le_rfl (by
      simpa [timelikeThreshold] using (show 3 * f.bound < c^2 by linarith [f.bound_nonneg]))
  · exact fun _ hv => f.form_spatial_pos hc q.property hlarge hv

/-- The physical coordinate chart of the common open domain, with source all of
the domain and target its underlying open subset of the coordinate model: the chart
`CoordinateMetric.physicalChart` of the shared geometry. -/
def physicalChart {U : Opens E} (x : U) : OpenPartialHomeomorph U E :=
  CoordinateMetric.physicalChart (d := 3) x

theorem physicalChart_eq {U : Opens E} (x y : U) :
    physicalChart x = physicalChart y :=
  CoordinateMetric.physicalChart_eq (d := 3) x y

@[simp] theorem physicalChart_apply {U : Opens E} (x y : U) :
    physicalChart x y = (y : E) :=
  CoordinateMetric.physicalChart_apply (d := 3) x y

@[simp] theorem physicalChart_source {U : Opens E} (x : U) :
    (physicalChart x).source = univ :=
  CoordinateMetric.physicalChart_source (d := 3) x

theorem physicalChart_mem {U : Opens E} (x : U) :
    physicalChart x ∈ IsManifold.maximalAtlas I ∞ U :=
  CoordinateMetric.physicalChart_mem (d := 3) x

/-- The native metric on the common open domain for a sufficiently large
positive value of `c`. Its smoothness and signature follow from the family. -/
def lorentzMetric {U : Opens E} (f : NewtonianMetricFamily U) (c : ℝ)
    (hc : 1 ≤ c) (hlarge : 9 * f.bound < c^2) : LorentzMetric .timeNegative 3 U where
  form x := f.form c x
  smooth := by
    have hs := (f.form_contDiffOn (show 0 < c by linarith)).contMDiffOn.comp_contMDiff
      (contMDiff_subtype_val (U := U)) (fun x : U => x.property)
    intro x
    refine (contMDiffAt_section x).mpr ?_
    convert hs x using 1
    funext y
    ext v w
    have hy : y ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
      change y ∈ (physicalChart x).source
      simp
    rw [hom_trivializationAt_apply, inCoordinates_apply_eq₂ hy hy (by simp),
      ← Trivialization.symmL_apply (R := ℝ) _ hy, ← Trivialization.symmL_apply (R := ℝ) _ hy,
      CoordinateMetric.physicalChart_symmL (d := 3)]
    simp
    rfl
  signature x := f.form_signature hc hlarge x

@[simp] theorem lorentzMetric_form {U : Opens E} (f : NewtonianMetricFamily U) {c : ℝ}
    (hc : 1 ≤ c) (hlarge : 9 * f.bound < c^2) (x : U) (v w : TangentSpace I x) :
    (f.lorentzMetric c hc hlarge).form x v w = f.form c x v w := rfl

@[simp] theorem physicalChart_target {U : Opens E} (x : U) :
    (physicalChart x).target = (U : Set E) :=
  CoordinateMetric.physicalChart_target (d := 3) x

@[simp] theorem physicalChart_tangentMap {U : Opens E} (x y : U) (v : TangentSpace I y) :
    chartTangentMap (physicalChart x) y v = (v : E) :=
  CoordinateMetric.physicalChart_tangentMap (d := 3) x y v

theorem lorentzMetric_component {U : Opens E} (f : NewtonianMetricFamily U) {c : ℝ}
    (hc : 1 ≤ c) (hlarge : 9 * f.bound < c^2) (x y : U) (i j : Fin 4) :
    (f.lorentzMetric c hc hlarge).chartComponent (physicalChart x) y i j =
      f.coefficient c y i j := by
  have h (v : E) : (chartField (physicalChart x) v y : E) = v :=
    (physicalChart_tangentMap x y _).symm.trans
      (chartTangentMap_field (physicalChart_mem x) (by simp : y ∈ (physicalChart x).source) v)
  rw [chartComponent, lorentzMetric_form, h, h, form_apply]
  simp [Pi.single_apply, mul_ite]

private theorem coefficient_mul_nativeInverse {U : Opens E} (f : NewtonianMetricFamily U) {c : ℝ}
    (hc : 1 ≤ c) (hlarge : 9 * f.bound < c^2) (x y : U) :
    f.coefficient c y * Matrix.of ((f.lorentzMetric c hc hlarge).inverseComponent y
      (chartTangentEquiv (physicalChart_mem x) (by simp))) = 1 := by
  let g := f.lorentzMetric c hc hlarge
  let e := chartTangentEquiv (physicalChart_mem x) (by simp : y ∈ (physicalChart x).source)
  have he (v : TangentSpace I y) : e v = (v : E) := physicalChart_tangentMap x y v
  ext k l
  let v := g.sharp y (Tensor.coordinateCovector y e l)
  have h := congrArg (fun α : TangentSpace I y →L[ℝ] ℝ => α (Pi.single k 1))
    (g.flat_sharp y (Tensor.coordinateCovector y e l))
  change g.form y v (Pi.single k 1) = e (Pi.single k 1) l at h
  replace h := ((f.form_apply c y v (Pi.single k 1)).symm.trans h).trans
    (congrFun (he (Pi.single k 1)) l)
  have hs : (∑ i, f.coefficient c y i k * v i) = (Pi.single k (1 : ℝ) : E) l := by
    simpa [Pi.single_apply, mul_ite] using h
  change (∑ i, f.coefficient c y k i * e v i) = _
  rw [he]
  simp_rw [f.coefficient_symmetric (show 0 < c by linarith) y.property k]
  rw [hs]
  simp [Pi.single_apply, Matrix.one_apply, eq_comm]

theorem lorentzMetric_inverseComponent {U : Opens E} (f : NewtonianMetricFamily U) {c : ℝ}
    (hc : 1 ≤ c) (hlarge : 9 * f.bound < c^2) (x y : U) (i j : Fin 4) :
    (f.lorentzMetric c hc hlarge).inverseComponent y
        (chartTangentEquiv (physicalChart_mem x) (by simp)) i j =
      (f.coefficient c y)⁻¹ i j := by
  have h := (Matrix.inv_eq_right_inv (f.coefficient_mul_nativeInverse hc hlarge x y)).symm
  exact congrFun (congrFun h i) j

theorem coefficient_mul_inverse {U : Opens E} (f : NewtonianMetricFamily U) {c : ℝ}
    (hc : 1 ≤ c) (hlarge : 9 * f.bound < c^2) (q : U) :
    f.coefficient c q * (f.coefficient c q)⁻¹ = 1 := by
  rw [Matrix.inv_eq_right_inv (f.coefficient_mul_nativeInverse hc hlarge q q)]
  exact f.coefficient_mul_nativeInverse hc hlarge q q

theorem lorentzMetric_component_derivative {U : Opens E} (f : NewtonianMetricFamily U) {c : ℝ}
    (hc : 1 ≤ c) (hlarge : 9 * f.bound < c^2) (x y : U) (i j : Fin 4) (v : E) :
    mvfderiv I (fun z => (f.lorentzMetric c hc hlarge).chartComponent (physicalChart x) z i j)
        y (chartField (physicalChart x) v y) =
      fderiv ℝ (fun z => f.coefficient c z i j) y v := by
  let G := fun z : U => (f.lorentzMetric c hc hlarge).chartComponent (physicalChart x) z i j
  have hG : MDifferentiableAt I 𝓘(ℝ, ℝ) G y := by
    have hs := (f.coefficient_contDiffOn (show 0 < c by linarith) i j).contMDiffOn.comp_contMDiff
      (contMDiff_subtype_val (U := U)) (fun x : U => x.property)
    have hEq : G = (fun z : U => f.coefficient c z i j) :=
      funext fun z => f.lorentzMetric_component hc hlarge x z i j
    rw [hEq]
    exact (hs y).mdifferentiableAt (by simp)
  change mvfderiv I G y _ = _
  rw [mvfderiv_chartField (physicalChart_mem x) (by simp) hG]
  have hEq : G ∘ (physicalChart x).symm =ᶠ[𝓝 (y : E)] fun z => f.coefficient c z i j := by
    filter_upwards [U.isOpen.mem_nhds y.property] with z hz
    change (f.lorentzMetric c hc hlarge).chartComponent (physicalChart x)
      ((physicalChart x).symm z) i j = _
    rw [f.lorentzMetric_component hc hlarge x, ← physicalChart_apply x ((physicalChart x).symm z),
      (physicalChart x).right_inv (by simpa using hz)]
  rw [physicalChart_apply, hEq.fderiv_eq]

/-- The Christoffel formula for the actual native metric in physical coordinates. -/
theorem lorentzMetric_christoffel {U : Opens E} (f : NewtonianMetricFamily U) {c : ℝ}
    (hc : 1 ≤ c) (hlarge : 9 * f.bound < c^2) (x y : U) (k i j : Fin 4) :
    (f.lorentzMetric c hc hlarge).chartChristoffel (physicalChart x) y k i j =
      ∑ l, (f.coefficient c y)⁻¹ k l *
        (fderiv ℝ (fun z => f.coefficient c z j l) y (Pi.single i 1) +
         fderiv ℝ (fun z => f.coefficient c z l i) y (Pi.single j 1) -
         fderiv ℝ (fun z => f.coefficient c z i j) y (Pi.single l 1)) / 2 := by
  rw [chartChristoffel_eq _ (physicalChart_mem x) (by simp)]
  simp_rw [f.lorentzMetric_inverseComponent, f.lorentzMetric_component_derivative]

/-- A uniform large-`c` threshold for constructing the native metric. -/
def lorentzThreshold {U : Opens E} (f : NewtonianMetricFamily U) : ℝ :=
  9 * f.bound + 2

theorem one_le_of_lorentzThreshold_le {U : Opens E} (f : NewtonianMetricFamily U)
    {c : ℝ} (hc : f.lorentzThreshold ≤ c) : 1 ≤ c := by
  unfold lorentzThreshold at hc
  linarith [f.bound_nonneg]

theorem spatialBound_lt_sq_of_lorentzThreshold_le {U : Opens E} (f : NewtonianMetricFamily U)
    {c : ℝ} (hc : f.lorentzThreshold ≤ c) : 9 * f.bound < c^2 := by
  unfold lorentzThreshold at hc
  nlinarith [sq_nonneg (c - 1), f.bound_nonneg]

/-- The ordinary Christoffel coefficient calculated from the family matrix. -/
def christoffel {U : Opens E} (f : NewtonianMetricFamily U) (c : ℝ) (q : E)
    (k i j : Fin 4) : ℝ :=
  ∑ l, (f.coefficient c q)⁻¹ k l *
    (fderiv ℝ (fun z => f.coefficient c z j l) q (Pi.single i 1) +
     fderiv ℝ (fun z => f.coefficient c z l i) q (Pi.single j 1) -
     fderiv ℝ (fun z => f.coefficient c z i j) q (Pi.single l 1)) / 2

/-- The coordinate-time acceleration calculated directly on the coordinate domain. -/
def acceleration {U : Opens E} (f : NewtonianMetricFamily U) (c : ℝ) (q : E) (v : S) : S :=
  fun k => -(∑ i : Fin 4, ∑ j : Fin 4,
    f.christoffel c q k.succ i j * timeVelocity v i * timeVelocity v j) +
      v k * (∑ i : Fin 4, ∑ j : Fin 4,
        f.christoffel c q 0 i j * timeVelocity v i * timeVelocity v j)

theorem acceleration_eq_native {U : Opens E} (f : NewtonianMetricFamily U) {c : ℝ}
    (hc : 1 ≤ c) (hlarge : 9 * f.bound < c^2) (x q : U) (v : S) :
    f.acceleration c q v =
      coordinateTimeAcceleration (f.lorentzMetric c hc hlarge) (physicalChart x) q v := by
  have hq : (physicalChart x).symm (q : E) = q := by
    simpa only [physicalChart_apply] using
      (physicalChart x).left_inv (show q ∈ (physicalChart x).source by simp)
  funext k
  simp only [coordinateTimeAcceleration, hq, f.lorentzMetric_christoffel hc hlarge,
    acceleration, christoffel]

theorem acceleration_contDiffAt {U : Opens E} (f : NewtonianMetricFamily U) {c : ℝ}
    (hc : 1 ≤ c) (hlarge : 9 * f.bound < c^2) {z : E × S} (hz : z.1 ∈ U) :
    ContDiffAt ℝ ∞ (fun y : E × S => f.acceleration c y.1 y.2) z := by
  let x : U := ⟨z.1, hz⟩
  have hs := coordinateTimeAcceleration_contDiffAt (f.lorentzMetric c hc hlarge)
    (physicalChart_mem x) (show z.1 ∈ (physicalChart x).target by simpa using hz)
  apply hs.congr_of_eventuallyEq
  filter_upwards [continuous_fst.continuousAt (U.isOpen.mem_nhds hz)] with y hy
  exact f.acceleration_eq_native hc hlarge x ⟨y.1, hy⟩ y.2

/-- A bounded physical-time velocity is timelike for the constructed native metric
as soon as its explicit uniform threshold is satisfied. -/
theorem timelike_timeVelocity {U : Opens E} (f : NewtonianMetricFamily U) {c : ℝ}
    (hc : 1 ≤ c) (hlarge : 9 * f.bound < c^2) (q : U)
    {V : ℝ} (hV : 0 ≤ V) {v : S} (hv : ‖v‖ ≤ V)
    (hspeed : f.timelikeThreshold V < c^2) :
    Timelike (f.lorentzMetric c hc hlarge) (x := q) (timeVelocity v) :=
  f.form_timeVelocity_neg hc q.property hv hV hspeed

end ProjectAinos.GeneralRelativity.NewtonianMetricFamily
