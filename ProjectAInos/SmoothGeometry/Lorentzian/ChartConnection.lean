/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.Christoffel
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! # Levi-Civita coefficients in manifold charts

Coordinate fields and coefficients are extracted from the actual tangent
derivative of a chart and the native connection. Every chart statement is
local to its source; no global frame or global coordinate map is assumed.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle FiberBundle VectorField ContinuousLinearMap
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type}
  [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)

/-- The tangent derivative of a chart, with its target tangent fibre expressed
in the coordinate model. -/
def chartTangentMap (e : OpenPartialHomeomorph M E) (x : M) :
    TangentSpace I x →L[ℝ] E :=
  (NormedSpace.fromTangentSpace (e x)).toContinuousLinearMap.comp (mfderiv I I e x)

/-- A constant coordinate vector pulled back to the actual tangent bundle.
Only its values on the chart source are used in coordinate theorems. -/
def chartField (e : OpenPartialHomeomorph M E) (v : E) : ∀ x : M, TangentSpace I x :=
  mpullback I I e (modelField v)

omit [IsManifold I ∞ M] in
theorem chart_mdifferentiable {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) : e.MDifferentiable I I :=
  ⟨(contMDiffOn_of_mem_maximalAtlas he).mdifferentiableOn (by simp),
    (contMDiffOn_symm_of_mem_maximalAtlas he).mdifferentiableOn (by simp)⟩

omit [IsManifold I ∞ M] in
theorem chart_mfderiv_isInvertible {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source) :
    (mfderiv I I e x).IsInvertible :=
  ⟨(chart_mdifferentiable he).mfderiv hx, rfl⟩

/-- The tangent coordinate map is an equivalence at a point in the chart source. -/
def chartTangentEquiv {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source) :
    TangentSpace I x ≃L[ℝ] E :=
  ((chart_mdifferentiable he).mfderiv hx).trans (NormedSpace.fromTangentSpace (e x))

omit [IsManifold I ∞ M] in
@[simp] theorem chartTangentEquiv_apply {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source)
    (v : TangentSpace I x) : chartTangentEquiv he hx v = chartTangentMap e x v := rfl

omit [IsManifold I ∞ M] in
theorem chartTangentMap_isInvertible {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source) :
    (chartTangentMap e x).IsInvertible :=
  isInvertible_equiv.comp (chart_mfderiv_isInvertible he hx)

omit [IsManifold I ∞ M] in
@[simp] theorem chartTangentMap_field {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source) (v : E) :
    chartTangentMap e x (chartField e v x) = v := by
  simp only [chartTangentMap, chartField, comp_apply, mpullback_apply,
    IsInvertible.self_apply_inverse (chart_mfderiv_isInvertible he hx), modelField,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]

omit [IsManifold I ∞ M] in
@[simp] theorem chartField_tangentMap {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source)
    (v : TangentSpace I x) : chartField e (chartTangentMap e x v) x = v := by
  simp only [chartTangentMap, chartField, comp_apply, mpullback_apply, modelField,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply,
    IsInvertible.inverse_apply_self (chart_mfderiv_isInvertible he hx)]

theorem chartField_mdifferentiableAt {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source) (v : E) :
    MDifferentiableAt I ((I).prod I) (T% (chartField e v)) x :=
  ((modelField_contMDiff v).mdifferentiableAt (by simp)).mpullback_vectorField
    (contMDiffAt_of_mem_maximalAtlas he hx) (chart_mfderiv_isInvertible he hx) (by simp)

theorem chartField_contMDiffAt {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source) (v : E) :
    ContMDiffAt I ((I).prod I) ∞ (T% (chartField e v)) x :=
  (modelField_contMDiff v (e x)).mpullback_vectorField_preimage
    (contMDiffAt_of_mem_maximalAtlas he hx) (chart_mfderiv_isInvertible he hx) (by simp)

omit [IsManifold I ∞ M] in
@[simp] theorem chartTangentEquiv_symm {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source) (v : E) :
    (chartTangentEquiv he hx).symm v = chartField e v x := by
  apply (chartTangentEquiv he hx).injective
  simp only [ContinuousLinearEquiv.apply_symm_apply, chartTangentEquiv_apply,
    chartTangentMap_field he hx]

/-- Metric components in a chart, obtained by evaluating the native metric
on the pulled-back coordinate basis. -/
def chartComponent (g : LorentzMetric σ d M) (e : OpenPartialHomeomorph M E)
    (x : M) (i j : Fin (d + 1)) : ℝ :=
  g.form x (chartField e (Pi.single i 1) x) (chartField e (Pi.single j 1) x)

/-- The coordinate components of the constructed connection in any smooth chart. -/
def chartChristoffel (g : LorentzMetric σ d M) (e : OpenPartialHomeomorph M E)
    (x : M) (k i j : Fin (d + 1)) : ℝ :=
  chartTangentMap e x
    (g.leviCivita (chartField e (Pi.single j 1)) x (chartField e (Pi.single i 1) x)) k

@[simp] theorem chartChristoffel_opposite (g : LorentzMetric σ d M)
    (e : OpenPartialHomeomorph M E) (x : M) (k i j : Fin (d + 1)) :
    g.opposite.chartChristoffel e x k i j = g.chartChristoffel e x k i j := by
  simp only [chartChristoffel, leviCivita_opposite]

/-- Coordinate fields commute on the chart source. -/
theorem chartField_bracket {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source) (v w : E) :
    mlieBracket I (chartField e v) (chartField e w) x = 0 := by
  let : IsManifold I (minSmoothness ℝ 2) M := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : IsManifold I 2 M)
  have h := mpullback_mlieBracket
    ((modelField_contMDiff v).mdifferentiableAt (x := e x) (by simp))
    ((modelField_contMDiff w).mdifferentiableAt (x := e x) (by simp))
    (contMDiffAt_of_mem_maximalAtlas he hx) (by simp)
  simpa only [chartField, modelField_bracket, mpullback_apply, map_zero] using h.symm

/-- The inverse-metric Christoffel formula in an arbitrary smooth manifold
chart. The scalar derivatives are taken in its coordinate basis directions. -/
theorem chartChristoffel_eq (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {x : M} (hx : x ∈ e.source) (k i j : Fin (d + 1)) :
    g.chartChristoffel e x k i j = ∑ l,
      g.inverseComponent x (chartTangentEquiv he hx) k l *
        (mvfderiv I (fun y => g.chartComponent e y j l) x (chartField e (Pi.single i 1) x) +
         mvfderiv I (fun y => g.chartComponent e y l i) x (chartField e (Pi.single j 1) x) -
         mvfderiv I (fun y => g.chartComponent e y i j) x (chartField e (Pi.single l 1) x)) / 2 := by
  let a := g.leviCivita (chartField e (Pi.single j 1)) x (chartField e (Pi.single i 1) x)
  change chartTangentMap e x a k = _
  rw [← g.sharp_flat x a, Tensor.covector_eq_sum x (chartTangentEquiv he hx) (g.flat x a)]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    flat_apply, chartTangentEquiv_symm, inverseComponent, chartTangentEquiv_apply]
  apply Finset.sum_congr rfl
  intro l _
  have h := g.leviCivita_pairing
    (chartField_mdifferentiableAt he hx (Pi.single i 1))
    (chartField_mdifferentiableAt he hx (Pi.single j 1))
    (chartField_mdifferentiableAt he hx (Pi.single l 1))
  change g.form x a (chartField e (Pi.single l 1) x) = _ at h
  rw [h]
  simp only [koszul, chartField_bracket he hx, map_zero, sub_zero, chartComponent]
  ring

theorem chartChristoffel_symmetric (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {x : M} (hx : x ∈ e.source) (k i j : Fin (d + 1)) :
    g.chartChristoffel e x k i j = g.chartChristoffel e x k j i := by
  have h := (CovariantDerivative.torsion_eq_zero_iff g.leviCivita).mp
    g.leviCivita_torsion
    (chartField_mdifferentiableAt he hx (Pi.single i 1))
    (chartField_mdifferentiableAt he hx (Pi.single j 1))
  rw [chartField_bracket he hx, sub_eq_zero] at h
  exact congrArg (fun v => chartTangentMap e x v k) h

/-- Smoothness of the chart coefficients follows from connection regularity
and smoothness of the chart, at every point of its source. -/
theorem chartChristoffel_contMDiffAt (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {x : M} (hx : x ∈ e.source) (k i j : Fin (d + 1)) :
    ContMDiffAt I 𝓘(ℝ) ∞ (fun y => g.chartChristoffel e y k i j) x := by
  have hV := (g.contMDiffAt_leviCivita (n := ⊤)
    (by simpa using chartField_contMDiffAt he hx (Pi.single j 1))).clm_bundle_apply
      (chartField_contMDiffAt he hx (Pi.single i 1))
  have ht := ((contMDiffAt_of_mem_maximalAtlas he hx).contMDiffAt_tangentMap
    (m := ∞) (by simp)).comp x hV
  rw [contMDiffAt_totalSpace] at ht
  have h := (proj k : E →L[ℝ] ℝ).contMDiff.contMDiffAt.comp x ht.2
  simpa [chartChristoffel, chartTangentMap, tangentMap, NormedSpace.fromTangentSpace,
    tangentSpaceCastModel, TangentBundle.trivializationAt_apply] using! h

/-- In the standard model chart the manifold coefficients recover the earlier
coordinate-model interface. -/
@[simp] theorem chartChristoffel_model (g : LorentzMetric σ d E)
    (x : E) (k i j : Fin (d + 1)) :
    g.chartChristoffel (Homeomorph.refl E).toOpenPartialHomeomorph x k i j =
      g.christoffel x k i j := by
  have hf (v : E) : chartField (Homeomorph.refl E).toOpenPartialHomeomorph v = modelField v := by
    funext y
    simp [chartField, mpullback_apply]
  simp only [chartChristoffel, hf, chartTangentMap, christoffel]
  change NormedSpace.fromTangentSpace x
    (mfderiv I I id x (g.leviCivita (modelField (Pi.single j 1)) x
      (modelField (Pi.single i 1) x))) k = _
  rw [mfderiv_id]
  rfl

omit [IsManifold I ∞ M] in
theorem chartField_eq_sum (e : OpenPartialHomeomorph M E) (x : M) (v : E) :
    chartField e v x = ∑ i, v i • chartField e (Pi.single i 1) x := by
  have h := pi_eq_sum_univ' v
  unfold chartField mpullback
  conv_lhs => rw [h]
  simp only [modelField, map_sum, map_smul]

theorem chartChristoffel_direction (g : LorentzMetric σ d M)
    (e : OpenPartialHomeomorph M E) (x : M) (v : E) (k j : Fin (d + 1)) :
    chartTangentMap e x (g.leviCivita (chartField e (Pi.single j 1)) x (chartField e v x)) k =
      ∑ i, v i * g.chartChristoffel e x k i j := by
  rw [chartField_eq_sum]
  simp [chartChristoffel]

/-- The local derivative-plus-Christoffel formula for a vector field specified
by its coordinate components on a manifold chart. -/
theorem leviCivita_chart_coordinates (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {x : M} (hx : x ∈ e.source) {V : M → E} (hV : MDifferentiableAt I I V x)
    (v : E) (k : Fin (d + 1)) :
    chartTangentMap e x
      (g.leviCivita (fun y => chartField e (V y) y) x (chartField e v x)) k =
      mvfderiv I V x (chartField e v x) k +
        ∑ i, ∑ j, g.chartChristoffel e x k i j * v i * V x j := by
  have hf (j : Fin (d + 1)) : MDifferentiableAt I 𝓘(ℝ) (fun y => V y j) x :=
    (proj j : E →L[ℝ] ℝ).mdifferentiableAt.comp x hV
  have hb (j : Fin (d + 1)) := chartField_mdifferentiableAt he hx (Pi.single j 1)
  have hW (j : Fin (d + 1)) (_ : j ∈ Finset.univ) := (hf j).smul_section (hb j)
  have hfield : (fun y => chartField e (V y) y) =
      ∑ j : Fin (d + 1), (fun y => V y j) • chartField e (Pi.single j 1) := by
    funext y
    simpa using chartField_eq_sum e y (V y)
  have hd (j : Fin (d + 1)) : mvfderiv I (fun y => V y j) x =
      (proj j : E →L[ℝ] ℝ).comp (mvfderiv I V x) := by
    change mvfderiv I ((proj j : E →L[ℝ] ℝ) ∘ V) x = _
    rw [mvfderiv_comp x (proj j : E →L[ℝ] ℝ).mdifferentiableAt hV,
      mvfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
    rfl
  rw [hfield, g.leviCivita_sum _ _ hW]
  simp only [sum_apply, map_sum, Finset.sum_apply]
  simp_rw [g.leviCivita.isCovariantDerivativeOnUniv.leibniz (hb _) (hf _)]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, smul_apply, map_add,
    map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    chartChristoffel_direction, chartTangentMap_field he hx]
  simp [hd, Finset.sum_add_distrib, Finset.mul_sum, Pi.single_apply]
  rw [add_comm, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [IsManifold I ∞ M] in
/-- The transition map between two smooth charts is smooth at every point of
their overlap, expressed in the source coordinates. -/
theorem chartTransition_contDiffAt {e e' : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas I ∞ M) {x : M}
    (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    ContDiffAt ℝ ∞ (e' ∘ e.symm) (e x) := by
  have h := (contMDiffAt_of_mem_maximalAtlas he' hx').comp_of_eq
    (contMDiffAt_symm_of_mem_maximalAtlas he (e.map_source hx)) (e.left_inv hx)
  exact h.contDiffAt

omit [IsManifold I ∞ M] in
/-- The transition Jacobian relates the actual tangent coordinate maps. -/
theorem chartTangentMap_transition {e e' : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas I ∞ M) {x : M}
    (hx : x ∈ e.source) (hx' : x ∈ e'.source) (v : TangentSpace I x) :
    chartTangentMap e' x v =
      fderiv ℝ (e' ∘ e.symm) (e x) (chartTangentMap e x v) := by
  have heq : (e' ∘ e.symm) ∘ e =ᶠ[𝓝 x] e' := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    simp only [Function.comp_apply, e.left_inv hy]
  have hc := mvfderiv_comp x
    ((chartTransition_contDiffAt he he' hx hx').contMDiffAt.mdifferentiableAt (by simp))
    ((contMDiffAt_of_mem_maximalAtlas he hx).mdifferentiableAt (by simp))
  have hd : mfderiv I I ((e' ∘ e.symm) ∘ e) x = mfderiv I I e' x := heq.mfderiv_eq
  have hv := congrArg (fun L => L v) hc
  simp only [mvfderiv_eq_fderiv] at hv
  simpa only [mvfderiv, hd, chartTangentMap, comp_apply] using! hv

omit [IsManifold I ∞ M] in
/-- Coordinate basis vectors change by the actual transition Jacobian. -/
theorem chartField_transition {e e' : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas I ∞ M) {x : M}
    (hx : x ∈ e.source) (hx' : x ∈ e'.source) (v : E) :
    chartField e' (fderiv ℝ (e' ∘ e.symm) (e x) v) x = chartField e v x := by
  have h := chartTangentMap_transition he he' hx hx' (chartField e v x)
  rw [chartTangentMap_field he hx] at h
  rw [← h, chartField_tangentMap he' hx']

/-- On a chart overlap, the connection on a constant source-coordinate field
has the transition Hessian plus the target-chart Christoffel term. -/
theorem leviCivita_chart_transition (g : LorentzMetric σ d M)
    {e e' : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas I ∞ M) {x : M}
    (hx : x ∈ e.source) (hx' : x ∈ e'.source) (v w : E) (k : Fin (d + 1)) :
    chartTangentMap e' x (g.leviCivita (chartField e w) x (chartField e v x)) k =
      fderiv ℝ (fun z => fderiv ℝ (e' ∘ e.symm) z w) (e x) v k +
        ∑ a, ∑ b, g.chartChristoffel e' x k a b *
          fderiv ℝ (e' ∘ e.symm) (e x) v a * fderiv ℝ (e' ∘ e.symm) (e x) w b := by
  let τ : E → E := e' ∘ e.symm
  let V : M → E := fun y => fderiv ℝ τ (e y) w
  have hD : DifferentiableAt ℝ (fun z => fderiv ℝ τ z w) (e x) :=
    ((chartTransition_contDiffAt he he' hx hx').fderiv_right
      (m := 1) (by simp)).differentiableAt one_ne_zero |>.clm_apply (differentiableAt_const w)
  have heD := (contMDiffAt_of_mem_maximalAtlas he hx).mdifferentiableAt (by simp)
  have hV : MDifferentiableAt I I V x := hD.mdifferentiableAt.comp x heD
  have hfield : ∀ᶠ y in 𝓝 x, chartField e' (V y) y = chartField e w y := by
    filter_upwards [e.open_source.mem_nhds hx, e'.open_source.mem_nhds hx'] with y hy hy'
    exact chartField_transition he he' hy hy' w
  have hsource := chartField_mdifferentiableAt he hx w
  have htarget : MDifferentiableAt I ((I).prod I)
      (T% (fun y => chartField e' (V y) y)) x := by
    apply hsource.congr_of_eventuallyEq
    filter_upwards [hfield] with y hy
    exact congrArg (fun v => TotalSpace.mk' E y v) hy
  have hcov := g.leviCivita.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    htarget hsource Filter.univ_mem hfield
  have hdir := chartField_transition he he' hx hx' v
  have hd : mvfderiv I V x (chartField e v x) =
      fderiv ℝ (fun z => fderiv ℝ τ z w) (e x) v := by
    have h := congrArg (fun L => L (chartField e v x))
      (mvfderiv_comp x hD.mdifferentiableAt heD)
    simp only [mvfderiv_eq_fderiv, comp_apply] at h
    change mvfderiv I V x (chartField e v x) =
      fderiv ℝ (fun z => fderiv ℝ τ z w) (e x)
        (chartTangentMap e x (chartField e v x)) at h
    simpa only [chartTangentMap_field he hx] using h
  have h := g.leviCivita_chart_coordinates he' hx' hV (fderiv ℝ τ (e x) v) k
  rw [hcov, hdir, hd] at h
  exact h

/-- The Christoffel transformation law on arbitrary smooth chart overlaps.
It includes the actual second derivative of the transition, so connection
coefficients are not asserted to transform as a tensor. -/
theorem chartChristoffel_transformation (g : LorentzMetric σ d M)
    {e e' : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas I ∞ M) {x : M}
    (hx : x ∈ e.source) (hx' : x ∈ e'.source) (k i j : Fin (d + 1)) :
    (∑ l, fderiv ℝ (e' ∘ e.symm) (e x) (Pi.single l 1) k *
      g.chartChristoffel e x l i j) =
      fderiv ℝ (fun z => fderiv ℝ (e' ∘ e.symm) z (Pi.single j 1))
        (e x) (Pi.single i 1) k +
      ∑ a, ∑ b, g.chartChristoffel e' x k a b *
        fderiv ℝ (e' ∘ e.symm) (e x) (Pi.single i 1) a *
        fderiv ℝ (e' ∘ e.symm) (e x) (Pi.single j 1) b := by
  have h := g.leviCivita_chart_transition he he' hx hx' (Pi.single i 1) (Pi.single j 1) k
  rw [chartTangentMap_transition he he' hx hx'] at h
  rw [pi_eq_sum_univ' (chartTangentMap e x
    (g.leviCivita (chartField e (Pi.single j 1)) x (chartField e (Pi.single i 1) x)))] at h
  simpa only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    chartChristoffel, mul_comm] using h

end ProjectAInos.SmoothGeometry.LorentzMetric
