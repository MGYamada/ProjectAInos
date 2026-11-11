/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.CurvatureRegularity
public import ProjectAInos.SmoothGeometry.Lorentzian.ChartConnection
public import ProjectAInos.SmoothGeometry.Lorentzian.ChartDerivatives

/-! # Curvature coefficients on arbitrary manifold charts

The index order is `Rˡᵢⱼₖ = (R(∂ᵢ,∂ⱼ)∂ₖ)ˡ`. Coefficients are extracted
from the native tensor. Their Christoffel formula and overlap law are proved
locally on the chart sources, without a global frame.
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
local notation "TM" => TangentSpace 𝓘(ℝ, MinkowskiModel d) (M := M)

/-- Taking chart components preserves a section's local finite regularity. -/
theorem chartTangentMap_contMDiffAt {n : ℕ∞} {V : ∀ x, TM x}
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {x : M} (hx : x ∈ e.source)
    (hV : ContMDiffAt I ((I).prod I) n (T% V) x) :
    ContMDiffAt I I n (fun y => chartTangentMap e y (V y)) x := by
  have h := ((contMDiffAt_of_mem_maximalAtlas he hx).contMDiffAt_tangentMap
    (m := n) (by simp)).comp x hV
  rw [contMDiffAt_totalSpace] at h
  simpa [chartTangentMap, tangentMap, NormedSpace.fromTangentSpace,
    tangentSpaceCastModel, TangentBundle.trivializationAt_apply] using! h.2

/-- Components of the actual Riemann tensor, with arguments ordered as
`R(∂ᵢ,∂ⱼ)∂ₖ` and output component `l`. -/
def chartCurvature (g : LorentzMetric σ d M) (e : OpenPartialHomeomorph M E)
    (x : M) (l i j k : Fin (d + 1)) : ℝ :=
  chartTangentMap e x (g.curvature x (chartField e (Pi.single i 1) x)
    (chartField e (Pi.single j 1) x) (chartField e (Pi.single k 1) x)) l

theorem chartCurvature_contMDiffAt (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {x : M} (hx : x ∈ e.source) (l i j k : Fin (d + 1)) :
    ContMDiffAt I 𝓘(ℝ) ∞ (fun y => g.chartCurvature e y l i j k) x := by
  have hR := (((g.curvature_smooth x).clm_bundle_apply
    (chartField_contMDiffAt he hx (Pi.single i 1))).clm_bundle_apply
    (chartField_contMDiffAt he hx (Pi.single j 1))).clm_bundle_apply
    (chartField_contMDiffAt he hx (Pi.single k 1))
  exact (proj l : E →L[ℝ] ℝ).contMDiff.contMDiffAt.comp x
    (chartTangentMap_contMDiffAt he hx hR)

private theorem chart_covariantField_twice (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {x : M} (hx : x ∈ e.source) (l i j k : Fin (d + 1)) :
    chartTangentMap e x
      (g.covariantField (chartField e (Pi.single i 1))
        (g.covariantField (chartField e (Pi.single j 1)) (chartField e (Pi.single k 1))) x) l =
      mvfderiv I (fun y => g.chartChristoffel e y l j k) x (chartField e (Pi.single i 1) x) +
        ∑ a, g.chartChristoffel e x l i a * g.chartChristoffel e x a j k := by
  let V := g.covariantField (chartField e (Pi.single j 1)) (chartField e (Pi.single k 1))
  let C : M → E := fun y => chartTangentMap e y (V y)
  have hV : ContMDiffAt I ((I).prod I) ∞ (T% V) x :=
    g.contMDiffAt_covariantField (n := ⊤) (chartField_contMDiffAt he hx (Pi.single j 1))
      (by simpa using chartField_contMDiffAt he hx (Pi.single k 1))
  have hC : MDifferentiableAt I I C x :=
    (chartTangentMap_contMDiffAt he hx hV).mdifferentiableAt (by simp)
  have heq : ∀ᶠ y in 𝓝 x, (fun y => chartField e (C y) y) y = V y := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact chartField_tangentMap he hy (V y)
  have hW : MDifferentiableAt I ((I).prod I) (T% (fun y => chartField e (C y) y)) x := by
    apply (hV.mdifferentiableAt (by simp)).congr_of_eventuallyEq
    filter_upwards [heq] with y hy
    exact congrArg (fun v => TotalSpace.mk' E y v) hy
  have hcov := g.leviCivita.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    hW (hV.mdifferentiableAt (by simp)) Filter.univ_mem heq
  have hd : mvfderiv I (fun y => g.chartChristoffel e y l j k) x =
      (proj l : E →L[ℝ] ℝ).comp (mvfderiv I C x) := by
    change mvfderiv I ((proj l : E →L[ℝ] ℝ) ∘ C) x = _
    rw [mvfderiv_comp x (proj l : E →L[ℝ] ℝ).mdifferentiableAt hC,
      mvfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
    rfl
  have h := g.leviCivita_chart_coordinates he hx hC (Pi.single i 1) l
  rw [hcov] at h
  rw [hd]
  simpa [C, V, covariantField, chartChristoffel, Pi.single_apply] using h

/-- The Christoffel formula on an arbitrary smooth chart. Partial derivatives
are the scalar manifold derivatives in the chart's basis directions. -/
theorem chartCurvature_eq (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {x : M} (hx : x ∈ e.source) (l i j k : Fin (d + 1)) :
    g.chartCurvature e x l i j k =
      mvfderiv I (fun y => g.chartChristoffel e y l j k) x (chartField e (Pi.single i 1) x) -
      mvfderiv I (fun y => g.chartChristoffel e y l i k) x (chartField e (Pi.single j 1) x) +
      ∑ a, (g.chartChristoffel e x l i a * g.chartChristoffel e x a j k -
        g.chartChristoffel e x l j a * g.chartChristoffel e x a i k) := by
  rw [chartCurvature, g.curvature_apply
    ((chartField_contMDiffAt he hx (Pi.single i 1)).of_le (by simp))
    ((chartField_contMDiffAt he hx (Pi.single j 1)).of_le (by simp))
    ((chartField_contMDiffAt he hx (Pi.single k 1)).of_le (by simp))]
  simp only [curvatureField, map_sub, Pi.sub_apply]
  rw [chart_covariantField_twice g he hx, chart_covariantField_twice g he hx]
  simp only [covariantField, chartField_bracket he hx, map_zero, Pi.zero_apply, sub_zero]
  rw [Finset.sum_sub_distrib]
  ring

/-- The same formula with ordinary partial derivatives of the coefficient
functions expressed in the chart coordinates. -/
theorem chartCurvature_eq_fderiv (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {x : M} (hx : x ∈ e.source) (l i j k : Fin (d + 1)) :
    g.chartCurvature e x l i j k =
      fderiv ℝ (fun z => g.chartChristoffel e (e.symm z) l j k) (e x) (Pi.single i 1) -
      fderiv ℝ (fun z => g.chartChristoffel e (e.symm z) l i k) (e x) (Pi.single j 1) +
      ∑ a, (g.chartChristoffel e x l i a * g.chartChristoffel e x a j k -
        g.chartChristoffel e x l j a * g.chartChristoffel e x a i k) := by
  rw [g.chartCurvature_eq he hx,
    mvfderiv_chartField he hx ((g.chartChristoffel_contMDiffAt he hx l j k).mdifferentiableAt
      (by simp)),
    mvfderiv_chartField he hx ((g.chartChristoffel_contMDiffAt he hx l i k).mdifferentiableAt
      (by simp))]
  rfl

@[simp] theorem chartCurvature_opposite (g : LorentzMetric σ d M)
    (e : OpenPartialHomeomorph M E) (x : M) (l i j k : Fin (d + 1)) :
    g.opposite.chartCurvature e x l i j k = g.chartCurvature e x l i j k := by
  simp only [chartCurvature, curvature_opposite]

/-- Tensor components on an overlap transform with three input Jacobians
and one output Jacobian. No Hessian term remains for curvature. -/
theorem chartCurvature_transformation (g : LorentzMetric σ d M)
    {e e' : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas I ∞ M) {x : M}
    (hx : x ∈ e.source) (hx' : x ∈ e'.source) (l i j k : Fin (d + 1)) :
    (∑ a, fderiv ℝ (e' ∘ e.symm) (e x) (Pi.single a 1) l *
      g.chartCurvature e x a i j k) =
      ∑ a, ∑ b, ∑ c, g.chartCurvature e' x l a b c *
        fderiv ℝ (e' ∘ e.symm) (e x) (Pi.single i 1) a *
        fderiv ℝ (e' ∘ e.symm) (e x) (Pi.single j 1) b *
        fderiv ℝ (e' ∘ e.symm) (e x) (Pi.single k 1) c := by
  let R := g.curvature x (chartField e (Pi.single i 1) x)
    (chartField e (Pi.single j 1) x) (chartField e (Pi.single k 1) x)
  have hout : chartTangentMap e' x R l = ∑ a,
      fderiv ℝ (e' ∘ e.symm) (e x) (Pi.single a 1) l * g.chartCurvature e x a i j k := by
    rw [chartTangentMap_transition he he' hx hx', pi_eq_sum_univ' (chartTangentMap e x R)]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      chartCurvature, R, mul_comm]
  rw [← hout]
  dsimp only [R]
  rw [← chartField_transition he he' hx hx' (Pi.single i 1),
    ← chartField_transition he he' hx hx' (Pi.single j 1),
    ← chartField_transition he he' hx hx' (Pi.single k 1)]
  rw [chartField_eq_sum e' x (fderiv ℝ (e' ∘ e.symm) (e x) (Pi.single i 1)),
    chartField_eq_sum e' x (fderiv ℝ (e' ∘ e.symm) (e x) (Pi.single j 1)),
    chartField_eq_sum e' x (fderiv ℝ (e' ∘ e.symm) (e x) (Pi.single k 1))]
  simp only [map_sum, map_smul, sum_apply, smul_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, chartCurvature]
  simp_rw [Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  ring

/-- Standard model coordinates recover the ordinary Christoffel formula
for components of the intrinsic curvature. -/
theorem curvature_model_coordinates (g : LorentzMetric σ d E)
    (x : E) (l i j k : Fin (d + 1)) :
    NormedSpace.fromTangentSpace x
      (g.curvature x (modelField (Pi.single i 1) x)
        (modelField (Pi.single j 1) x) (modelField (Pi.single k 1) x)) l =
      fderiv ℝ (fun y => g.christoffel y l j k) x (Pi.single i 1) -
      fderiv ℝ (fun y => g.christoffel y l i k) x (Pi.single j 1) +
      ∑ a, (g.christoffel x l i a * g.christoffel x a j k -
        g.christoffel x l j a * g.christoffel x a i k) := by
  let e := (Homeomorph.refl E).toOpenPartialHomeomorph
  have he : e ∈ IsManifold.maximalAtlas I ∞ E := IsManifold.chart_mem_maximalAtlas x
  have hf (v : E) : chartField e v = modelField v := by
    funext y
    simp [e, chartField, mpullback_apply]
  have h := g.chartCurvature_eq_fderiv he (show x ∈ e.source from Set.mem_univ x) l i j k
  have hc (y : E) (a b c : Fin (d + 1)) :
      g.chartChristoffel e y a b c = g.christoffel y a b c := g.chartChristoffel_model y a b c
  simp only [chartCurvature, hf, hc, chartTangentMap] at h
  change NormedSpace.fromTangentSpace x
    (mfderiv I I id x (g.curvature x (modelField (Pi.single i 1) x)
      (modelField (Pi.single j 1) x) (modelField (Pi.single k 1) x))) l = _ at h
  rw [mfderiv_id] at h
  exact h

end ProjectAInos.SmoothGeometry.LorentzMetric
