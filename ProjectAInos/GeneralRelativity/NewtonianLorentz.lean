/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.GeneralRelativity.NewtonianBounds
public import ProjectAInos.GeneralRelativity.CoordinateTime
public import ProjectAInos.SmoothGeometry.Manifold.OpenTangent
public import ProjectAInos.SmoothGeometry.Lorentzian.ChartDerivatives
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.QuadraticForm.Real

/-! # Native Lorentz metrics in physical time coordinates -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Bundle ContinuousLinearMap Set TopologicalSpace
open scoped Manifold ContDiff Topology

namespace ProjectAInos.GeneralRelativity.NewtonianMetricFamily
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

private theorem positiveQuadraticCoordinates (Q : QuadraticForm ℝ S)
    (hQ : ∀ v ≠ 0, 0 < Q v) :
    ∃ e : S ≃ₗ[ℝ] S, ∀ v, Q v = ∑ i, (e v i)^2 := by
  obtain ⟨w, ⟨e⟩⟩ := Q.equivalent_weightedSumSquares
  have hdim : Module.finrank ℝ S = 3 := Module.finrank_fin_fun ℝ
  revert w e
  rw [hdim]
  intro w e
  have hw (i : Fin 3) : 0 < w i := by
    let v : S := Pi.single i 1
    have hv : v ≠ 0 := by
      intro h
      have h' := congrFun h i
      simp [v] at h'
    have hp := hQ (e.symm v) (by
      intro hz
      exact hv (by simpa using congrArg e hz))
    rw [← e.map_app, e.apply_symm_apply, QuadraticMap.weightedSumSquares_apply] at hp
    simpa [v, Pi.single_apply, ite_pow, Finset.sum_ite_eq', mul_comm] using hp
  let r := QuadraticForm.isometryEquivSignWeightedSumSquares w
  refine ⟨(e.trans r).toLinearEquiv, fun v => ?_⟩
  rw [← (e.trans r).map_app, QuadraticMap.weightedSumSquares_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp [sign_pos (hw i), smul_eq_mul, pow_two]

/-- Completing the square along the negative time line gives a positive
quadratic form on its orthogonal complement and hence an inertial frame. -/
private theorem exists_lorentzFrame (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hs : ∀ v w, B v w = B w v)
    (ht : B (Fin.cons 1 (0 : S)) (Fin.cons 1 (0 : S)) < 0)
    (hx : ∀ v : S, v ≠ 0 → 0 < B (Fin.cons 0 v) (Fin.cons 0 v)) :
    ∃ e : E ≃L[ℝ] E, ∀ v w, B v w = minkowskiForm .timeNegative 3 (e v) (e w) := by
  let z : E := Fin.cons 1 (0 : S)
  let a := B z z
  have ha : a < 0 := ht
  let J : S →L[ℝ] E := (0 : S →L[ℝ] ℝ).finCons (ContinuousLinearMap.id ℝ S)
  have hJ (v : S) : J v = Fin.cons 0 v := rfl
  let b : S →L[ℝ] ℝ := ((B.flip) z).comp J
  let P : S →L[ℝ] E := J - (a⁻¹ • b).smulRight z
  have hP (v : S) : P v = J v - (b v / a) • z := by
    simp [P, div_eq_mul_inv, mul_comm]
  have hb (v : S) : b v = B (J v) z := rfl
  let Q : QuadraticForm ℝ S := LinearMap.BilinMap.toQuadraticMap (LinearMap.mk₂ ℝ (fun u v => B (P u) (P v))
    (by intros; simp [add_apply])
    (by intros; simp [smul_apply])
    (by intros; simp)
    (by intros; simp))
  have hQ (v : S) : Q v = B (P v) (P v) := rfl
  have horth (v : S) : B (P v) z = 0 := by
    rw [hP, map_sub, map_smul]
    simp only [sub_apply, smul_apply, smul_eq_mul, ← hb]
    change b v - (b v / a) * a = 0
    field_simp [ha.ne]
    ring
  have hsplit (v : S) : B (P v) (P v) = B (J v) (J v) - (b v)^2 / a := by
    calc
      B (P v) (P v) = B (P v) (J v) := by
        conv_lhs => arg 2; rw [hP v]
        simp [horth]
      _ = _ := by
        rw [hP, map_sub, map_smul]
        simp only [sub_apply, smul_apply, smul_eq_mul, hs z (J v), ← hb]
        ring
  obtain ⟨e, he⟩ := positiveQuadraticCoordinates Q (fun v hv => by
    rw [hQ, hsplit]
    have hp := hx v hv
    rw [← hJ v] at hp
    exact sub_pos.mpr ((div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) ha.le).trans_lt hp))
  let tailMap : E →L[ℝ] S := ContinuousLinearMap.pi fun i => proj i.succ
  let timeMap : E →L[ℝ] ℝ := proj 0 + a⁻¹ • (b.comp tailMap)
  let r := Real.sqrt (-a)
  have hr : r ≠ 0 := (Real.sqrt_pos.2 (neg_pos.mpr ha)).ne'
  let L : E →L[ℝ] E := (r • timeMap).finCons (e.toContinuousLinearEquiv.toContinuousLinearMap.comp tailMap)
  have htL (v : E) : L v 0 = r * (v 0 + b (Fin.tail v) / a) := by
    change r * (v 0 + a⁻¹ * b (Fin.tail v)) = _
    rw [div_eq_mul_inv, mul_comm a⁻¹]
  have hxL (v : E) : Fin.tail (L v) = e (Fin.tail v) := rfl
  have hinj : Function.Injective L := by
    intro v w h
    have hs' := e.injective ((hxL v).symm.trans ((congrArg Fin.tail h).trans (hxL w)))
    have ht' := congrFun h 0
    rw [htL, htL, hs'] at ht'
    have h0 := add_right_cancel (mul_left_cancel₀ hr ht')
    rw [← Fin.cons_self_tail v, ← Fin.cons_self_tail w, h0, hs']
  let iso := (LinearEquiv.ofBijective L.toLinearMap
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinj⟩).toContinuousLinearEquiv
  have hdiag (v : E) : B v v = minkowskiForm .timeNegative 3 (iso v) (iso v) := by
    let u := Fin.tail v
    let t := v 0 + b u / a
    have hv : v = t • z + P u := by
      rw [hP, hJ]
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · change v 0 = t * 1 + (0 - b u / a * 1)
        dsimp [t]
        ring
      · change v j.succ = t * 0 + (u j - b u / a * 0)
        simp only [mul_zero, sub_zero, zero_add]
        rfl
    calc
      B v v = a * t^2 + Q u := by
        nth_rw 1 2 [hv]
        simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, horth,
          hs z (P u), mul_zero, zero_add, add_zero, ← hQ]
        change t * (t * a) + Q u = _
        ring
      _ = _ := by
        have hsqrt : r^2 = -a := Real.sq_sqrt (neg_nonneg.mpr ha.le)
        rw [he, minkowskiForm_apply, Fin.sum_univ_succ]
        change a * t^2 + ∑ i, (e u i)^2 =
          lorentzSign .timeNegative (0 : Fin 4) * (L v 0 * L v 0) +
            ∑ i : Fin 3, lorentzSign .timeNegative i.succ * (L v i.succ * L v i.succ)
        have htail (i : Fin 3) : L v i.succ = e u i := congrFun (hxL v) i
        have ht0 : L v 0 = r * t := htL v
        simp only [ht0, htail, lorentzSign, LorentzConvention.timeSign, Fin.succ_ne_zero,
          ite_false, ite_true, neg_mul, one_mul, mul_neg, mul_one, neg_neg]
        simp_rw [← pow_two]
        rw [mul_pow, hsqrt]
        ring
  refine ⟨iso, fun v w => ?_⟩
  have h := hdiag (v + w)
  simp only [map_add, add_apply] at h
  rw [hs w v, hdiag v, hdiag w, minkowskiForm_symmetric .timeNegative (iso w) (iso v)] at h
  linarith

/-- Every sufficiently large member has Lorentz signature at every point. -/
theorem form_signature {U : Opens E} (f : NewtonianMetricFamily U) {c : ℝ}
    (hc : 1 ≤ c) (hlarge : 9 * f.bound < c^2) (q : U) :
    ∃ e : E ≃L[ℝ] E, ∀ v w,
      f.form c q v w = minkowskiForm .timeNegative 3 (e v) (e w) := by
  apply exists_lorentzFrame (f.form c q) (f.form_symmetric (by linarith) q.property)
  · exact f.form_timeVelocity_neg hc q.property (v := 0) (V := 0) (by simp) le_rfl (by
      simpa [timelikeThreshold] using (show 3 * f.bound < c^2 by linarith [f.bound_nonneg]))
  · exact fun _ hv => f.form_spatial_pos hc q.property hlarge hv

/-- The physical coordinate chart of the common open domain, with source all of
the domain and target its underlying open subset of the coordinate model. -/
def physicalChart {U : Opens E} (x : U) : OpenPartialHomeomorph U E := chartAt E x

theorem physicalChart_eq {U : Opens E} (x y : U) :
    physicalChart x = physicalChart y := by
  simp only [physicalChart, Opens.chartAt_eq, chartAt_self_eq]

@[simp] theorem physicalChart_apply {U : Opens E} (x y : U) :
    physicalChart x y = (y : E) := by
  simp [physicalChart, Opens.chartAt_eq, chartAt_self_eq]

@[simp] theorem physicalChart_source {U : Opens E} (x : U) :
    (physicalChart x).source = univ := by
  simp [physicalChart, Opens.chartAt_eq, chartAt_self_eq]

theorem physicalChart_mem {U : Opens E} (x : U) :
    physicalChart x ∈ IsManifold.maximalAtlas I ∞ U :=
  IsManifold.chart_mem_maximalAtlas x

private theorem physicalChart_symmL {U : Opens E} (x y : U) :
    (trivializationAt E (TangentSpace I) x).symmL ℝ y =
      (ContinuousLinearMap.id ℝ E : E →L[ℝ] E) := by
  have hy : y ∈ (chartAt E x).source := by
    change y ∈ (physicalChart x).source
    simp
  rw [TangentBundle.symmL_trivializationAt_eq_core hy]
  have he : achart E x = achart E y := Subtype.ext (physicalChart_eq x y)
  rw [he]
  apply ContinuousLinearMap.ext
  intro v
  exact (tangentBundleCore I U).coordChange_self (achart E y) y (mem_achart_source E y) v

/-- The native metric on the common open domain for a sufficiently large
positive value of `c`. Its smoothness and signature follow from the family. -/
def lorentzMetric {U : Opens E} (f : NewtonianMetricFamily U) (c : ℝ)
    (hc : 1 ≤ c) (hlarge : 9 * f.bound < c^2) : LorentzMetric .timeNegative 3 U where
  form x := f.form c x
  smooth := by
    have hs := (f.form_contDiffOn (show 0 < c by linarith)).contMDiffOn.comp_contMDiff
      (contMDiff_subtype_val (U := U)) (fun x : U => x.property)
    intro x
    rw [contMDiffAt_section]
    convert hs x using 1
    funext y
    ext v w
    have hy : y ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
      change y ∈ (physicalChart x).source
      simp
    rw [hom_trivializationAt_apply, inCoordinates_apply_eq₂ hy hy (by simp),
      ← Trivialization.symmL_apply (R := ℝ) _ hy, ← Trivialization.symmL_apply (R := ℝ) _ hy,
      physicalChart_symmL]
    simp
    rfl
  signature x := f.form_signature hc hlarge x

@[simp] theorem lorentzMetric_form {U : Opens E} (f : NewtonianMetricFamily U) {c : ℝ}
    (hc : 1 ≤ c) (hlarge : 9 * f.bound < c^2) (x : U) (v w : TangentSpace I x) :
    (f.lorentzMetric c hc hlarge).form x v w = f.form c x v w := rfl

@[simp] theorem physicalChart_target {U : Opens E} (x : U) :
    (physicalChart x).target = (U : Set E) := by
  ext y
  constructor
  · intro hy
    rw [← (physicalChart x).right_inv hy, physicalChart_apply]
    exact ((physicalChart x).symm y).property
  · intro hy
    exact (physicalChart x).map_source (x := ⟨y, hy⟩) (by simp)

@[simp] theorem physicalChart_tangentMap {U : Opens E} (x y : U) (v : TangentSpace I y) :
    chartTangentMap (physicalChart x) y v = (v : E) := by
  have he : (physicalChart x : U → E) = Subtype.val :=
    funext (physicalChart_apply x)
  change NormedSpace.fromTangentSpace (physicalChart x y)
    (mfderiv I I (physicalChart x : U → E) y v) = v
  rw [he, Manifold.mfderiv_subtype_val_apply U]
  rfl

theorem lorentzMetric_component {U : Opens E} (f : NewtonianMetricFamily U) {c : ℝ}
    (hc : 1 ≤ c) (hlarge : 9 * f.bound < c^2) (x y : U) (i j : Fin 4) :
    (f.lorentzMetric c hc hlarge).chartComponent (physicalChart x) y i j =
      f.coefficient c y i j := by
  have h (v : E) : (chartField (physicalChart x) v y : E) = v := by
    simpa only [physicalChart_tangentMap] using
      chartTangentMap_field (physicalChart_mem x) (by simp : y ∈ (physicalChart x).source) v
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
  rw [he, lorentzMetric_form, form_apply] at h
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

end ProjectAInos.GeneralRelativity.NewtonianMetricFamily
