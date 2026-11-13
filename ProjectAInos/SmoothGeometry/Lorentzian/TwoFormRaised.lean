/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.DualDerivative
public import ProjectAInos.SmoothGeometry.Lorentzian.TwoFormDivergence
public import ProjectAInos.SmoothGeometry.Lorentzian.DensityDerivative
public import ProjectAInos.SmoothGeometry.Lorentzian.ChartCurvature

/-! # Raised two-form components in actual smooth charts -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Bundle FiberBundle ContinuousLinearMap
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.LorentzMetric
open DifferentialForm

variable {σ : LorentzConvention} {d : ℕ} {M : Type}
  [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)
local notation "TM" => TangentSpace 𝓘(ℝ, MinkowskiModel d) (M := M)

/-- The actual coordinate covector, defined wherever the chart derivative is. -/
def chartCovector (e : OpenPartialHomeomorph M E) (x : M) (i : Fin (d + 1)) : TM x →L[ℝ] ℝ :=
  (proj i).comp (chartTangentMap e x)

theorem chartCovector_contMDiffAt {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source)
    (i : Fin (d + 1)) :
    ContMDiffAt I ((I).prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) y (chartCovector e y i)) x := by
  apply Tensor.SmoothBundle.contMDiffAt_of_apply
    (Tensor.SmoothBundle.tangent I) (Tensor.SmoothBundle.scalar I)
  intro V hV
  apply contMDiffAt_totalSpace.mpr
  refine ⟨contMDiffAt_id, ?_⟩
  exact (proj i : E →L[ℝ] ℝ).contMDiff.contMDiffAt.comp x
    (chartTangentMap_contMDiffAt he hx hV)

variable (g : LorentzMetric σ d M)

theorem sharp_pairing_symm (x : M) (α β : TM x →L[ℝ] ℝ) :
    α (g.sharp x β) = β (g.sharp x α) := by
  rw [← g.form_sharp_left x α (g.sharp x β), g.form_sharp_right]

theorem inverseComponent_symmetric (x : M) (e : TM x ≃L[ℝ] E) (i j : Fin (d + 1)) :
    g.inverseComponent x e i j = g.inverseComponent x e j i :=
  g.sharp_pairing_symm x (Tensor.coordinateCovector x e i) (Tensor.coordinateCovector x e j)

/-- Inverse-metric contraction is unchanged by swapping its two covariant slots. -/
theorem contract_flip (x : M) (B : TM x →L[ℝ] TM x →L[ℝ] ℝ) :
    g.contract x B.flip = g.contract x B := by
  let e := (trivializationAt E TM x).continuousLinearEquivAt ℝ x
    (FiberBundle.mem_baseSet_trivializationAt' x)
  rw [g.contract_eq_sum_components x e, g.contract_eq_sum_components x e, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [g.inverseComponent_symmetric x e j i]
  rfl

/-- The raised divergence is a single trace in arbitrary pointwise coordinates. -/
theorem twoFormDivergence_raised_trace (F : SmoothForm I M 2) (x : M)
    (e : TM x ≃L[ℝ] E) (j : Fin (d + 1)) :
    e (g.twoFormDivergence F x) j = ∑ i,
      g.twoFormDerivative F x (g.sharp x (Tensor.coordinateCovector x e i))
        (g.sharp x (Tensor.coordinateCovector x e j)) (e.symm (Pi.single i 1)) := by
  change Tensor.coordinateCovector x e j (g.sharp x (g.twoFormDivergenceCovector F x)) = _
  rw [g.sharp_pairing_symm, g.twoFormDivergenceCovector_apply, ← g.contract_flip,
    g.contract_eq_sum x e]
  apply Finset.sum_congr rfl
  intro i _
  change Tensor.coordinateCovector x e i
    (g.sharp x (((g.twoFormDerivative F x).flip
      (g.sharp x (Tensor.coordinateCovector x e j))).flip (e.symm (Pi.single i 1)))) = _
  rw [g.sharp_pairing_symm]
  rfl

/-- Raise the actual coordinate covector, without choosing a global frame. -/
def chartRaisedCovector (e : OpenPartialHomeomorph M E) (x : M) (i : Fin (d + 1)) : TM x :=
  g.sharp x (chartCovector e x i)

theorem chartRaisedCovector_contMDiffAt {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source)
    (i : Fin (d + 1)) :
    ContMDiffAt I ((I).prod I) ∞ (T% (fun y => g.chartRaisedCovector e y i)) x :=
  (g.sharp_smooth x).clm_bundle_apply (chartCovector_contMDiffAt he hx i)

theorem chartRaisedCovector_pairing {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source)
    (i : Fin (d + 1)) (v : E) :
    g.form x (g.chartRaisedCovector e x i) (chartField e v x) = v i := by
  rw [chartRaisedCovector, g.form_sharp_left]
  exact congrFun (chartTangentMap_field he hx v) i

/-- The raised coordinate covectors have the dual Christoffel transformation. -/
theorem leviCivita_chartRaisedCovector_pairing {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source)
    (i k b : Fin (d + 1)) :
    g.form x (g.leviCivita (fun y => g.chartRaisedCovector e y i) x
      (chartField e (Pi.single k 1) x)) (chartField e (Pi.single b 1) x) =
        -g.chartChristoffel e x i k b := by
  change g.form x (g.leviCivita (fun y => g.sharp y (chartCovector e y i)) x
    (chartField e (Pi.single k 1) x)) (chartField e (Pi.single b 1) x) = _
  rw [g.leviCivita_sharp_pairing
    ((chartCovector_contMDiffAt he hx i).mdifferentiableAt (by simp))
    (chartField_mdifferentiableAt he hx _) _]
  have heq : (fun y => chartCovector e y i (chartField e (Pi.single b 1) y)) =ᶠ[𝓝 x]
      fun _ => (Pi.single b 1 : E) i := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact congrFun (chartTangentMap_field he hy (Pi.single b 1)) i
  rw [mvfderiv_congr_of_eventuallyEq heq, mvfderiv_const]
  simp only [zero_apply, zero_sub]
  rfl

theorem leviCivita_chartRaisedCovector {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source)
    (i k : Fin (d + 1)) :
    g.leviCivita (fun y => g.chartRaisedCovector e y i) x (chartField e (Pi.single k 1) x) =
      -∑ b, g.chartChristoffel e x i k b • g.chartRaisedCovector e x b := by
  apply (g.flat x).injective
  ext v
  change g.form x _ v = g.form x _ v
  rw [← chartField_tangentMap he hx v, chartField_eq_sum e x (chartTangentMap e x v)]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  rw [g.leviCivita_chartRaisedCovector_pairing he hx]
  simp only [map_neg, neg_apply, map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul,
    g.chartRaisedCovector_pairing he hx]
  simp [Pi.single_apply]

/-- Both form indices are raised by the actual inverse metric. -/
def raisedTwoFormComponent (F : SmoothForm I M 2) (e : OpenPartialHomeomorph M E)
    (x : M) (i j : Fin (d + 1)) : ℝ :=
  F x ![g.chartRaisedCovector e x i, g.chartRaisedCovector e x j]

theorem raisedTwoFormComponent_skew (F : SmoothForm I M 2)
    (e : OpenPartialHomeomorph M E) (x : M) (i j : Fin (d + 1)) :
    g.raisedTwoFormComponent F e x i j = -g.raisedTwoFormComponent F e x j i := by
  simp only [raisedTwoFormComponent, ← twoFormBilinear_apply]
  exact twoFormBilinear_skew (F x) _ _

theorem raisedTwoFormComponent_contMDiffAt (F : SmoothForm I M 2)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {x : M} (hx : x ∈ e.source) (i j : Fin (d + 1)) :
    ContMDiffAt I 𝓘(ℝ) ∞ (fun y => g.raisedTwoFormComponent F e y i j) x := by
  have h := ((smoothTwoFormBilinear F).contMDiff x).clm_bundle_apply₂
    (g.chartRaisedCovector_contMDiffAt he hx i) (g.chartRaisedCovector_contMDiffAt he hx j)
  rw [contMDiffAt_totalSpace] at h
  simpa [raisedTwoFormComponent, smoothTwoFormBilinear_apply] using h.2

/-- Metric compatibility supplies the two positive Christoffel terms for raised indices. -/
theorem raisedTwoFormComponent_derivative (F : SmoothForm I M 2)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {x : M} (hx : x ∈ e.source) (k i j : Fin (d + 1)) :
    g.twoFormDerivative F x (g.chartRaisedCovector e x i) (g.chartRaisedCovector e x j)
        (chartField e (Pi.single k 1) x) =
      mvfderiv I (fun y => g.raisedTwoFormComponent F e y i j) x (chartField e (Pi.single k 1) x) +
      ∑ b, g.chartChristoffel e x i k b * g.raisedTwoFormComponent F e x b j +
      ∑ b, g.chartChristoffel e x j k b * g.raisedTwoFormComponent F e x i b := by
  rw [g.twoFormDerivative_apply F
    ((g.chartRaisedCovector_contMDiffAt he hx i).mdifferentiableAt (by simp))
    ((g.chartRaisedCovector_contMDiffAt he hx j).mdifferentiableAt (by simp)) _,
    g.leviCivita_chartRaisedCovector he hx, g.leviCivita_chartRaisedCovector he hx]
  simp only [← twoFormBilinear_apply]
  simp only [map_neg, neg_apply, map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul,
    twoFormBilinear_apply, sub_neg_eq_add, raisedTwoFormComponent]

theorem twoFormDivergence_chart_trace (F : SmoothForm I M 2)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {x : M} (hx : x ∈ e.source) (j : Fin (d + 1)) :
    chartTangentMap e x (g.twoFormDivergence F x) j = ∑ i,
      g.twoFormDerivative F x (g.chartRaisedCovector e x i) (g.chartRaisedCovector e x j)
        (chartField e (Pi.single i 1) x) := by
  have hc (i : Fin (d + 1)) :
      Tensor.coordinateCovector x (chartTangentEquiv he hx) i = chartCovector e x i := by
    ext v
    exact congrFun (chartTangentEquiv_apply he hx v) i
  simpa only [hc, chartTangentEquiv_apply, chartTangentEquiv_symm, chartRaisedCovector] using
    g.twoFormDivergence_raised_trace F x (chartTangentEquiv he hx) j

/-- Symmetry of the connection kills its contraction with the raised two-form. -/
theorem christoffel_raisedTwoForm_sum (F : SmoothForm I M 2)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {x : M} (hx : x ∈ e.source) (j : Fin (d + 1)) :
    (∑ i, ∑ b, g.chartChristoffel e x j i b * g.raisedTwoFormComponent F e x i b) = 0 := by
  have h : (∑ i, ∑ b, g.chartChristoffel e x j i b * g.raisedTwoFormComponent F e x i b) =
      -(∑ i, ∑ b, g.chartChristoffel e x j i b * g.raisedTwoFormComponent F e x i b) := by
    conv_lhs => rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro b _
    rw [g.chartChristoffel_symmetric he hx j b i, g.raisedTwoFormComponent_skew F e x b i]
    ring
  linarith

/-- The native two-form divergence has the density-weighted coordinate formula. -/
theorem chartDensity_mul_twoFormDivergence (F : SmoothForm I M 2)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {x : M} (hx : x ∈ e.source) (j : Fin (d + 1)) :
    g.chartDensity e x * chartTangentMap e x (g.twoFormDivergence F x) j =
      ∑ i, mvfderiv I (fun y => g.chartDensity e y * g.raisedTwoFormComponent F e y i j) x
        (chartField e (Pi.single i 1) x) := by
  have hp (i : Fin (d + 1)) := mvfderiv_fun_mul
    ((g.chartDensity_contMDiffAt he hx).mdifferentiableAt (by simp))
    ((g.raisedTwoFormComponent_contMDiffAt F he hx i j).mdifferentiableAt (by simp))
  rw [g.twoFormDivergence_chart_trace F he hx]
  simp_rw [g.raisedTwoFormComponent_derivative F he hx]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    g.christoffel_raisedTwoForm_sum F he hx, add_zero]
  simp only [hp, add_apply, smul_apply, smul_eq_mul, g.chartDensity_derivative he hx,
    mul_add, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- `∇ᵢFⁱʲ = ρ⁻¹ ∂ᵢ(ρ Fⁱʲ)` in every smooth chart. -/
theorem twoFormDivergence_density (F : SmoothForm I M 2)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {x : M} (hx : x ∈ e.source) (j : Fin (d + 1)) :
    chartTangentMap e x (g.twoFormDivergence F x) j = (g.chartDensity e x)⁻¹ *
      ∑ i, mvfderiv I (fun y => g.chartDensity e y * g.raisedTwoFormComponent F e y i j) x
        (chartField e (Pi.single i 1) x) := by
  rw [← g.chartDensity_mul_twoFormDivergence F he hx,
    ← mul_assoc, inv_mul_cancel₀ (ne_of_gt (g.chartDensity_pos he hx)), one_mul]

end ProjectAInos.SmoothGeometry.LorentzMetric
