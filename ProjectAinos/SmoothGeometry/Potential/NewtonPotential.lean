/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Potential.NewtonKernel
public import ProjectAinos.SmoothGeometry.Potential.MaximumPrinciple
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Tactic

/-!
# The Newton potential of a charge of compact support

Space is `EuclideanSpace ℝ (Fin 3)` with the Euclidean norm. For a density `ρ` the Newton
potential is the convolution `newtonPotential ρ = K ⋆ ρ` with the Newton kernel
`K x = 1/(4π‖x‖)`, so `φ(x) = ∫ K(y) ρ(x − y) dy = ∫ ρ(y)/(4π‖x − y‖) dy`
(`newtonPotential_eq_integral`).

* `contDiff_newtonPotential`: the potential of a `Cⁿ` density of compact support is `Cⁿ`, and
  `fderiv_newtonPotential_apply`: its derivatives are the potentials of the derivatives.
* `laplacian_newtonPotential`: **Poisson's equation** `Δφ = −ρ` for a `C²` density of compact
  support. The derivatives fall on `ρ`, so `Δφ(x) = ∫ K(y) Δρ(x − y) dy`, which is `−ρ(x)` by the
  point-source identity `integral_newtonKernel_mul_coordLaplacian`.
* `abs_newtonPotential_le`, `norm_fderiv_newtonPotential_le`: outside a ball `‖y‖ ≤ a` that
  contains the support, `|φ(x)| ≤ (∫|ρ|)/(4π(‖x‖ − a))` and
  `‖Dφ(x)‖ ≤ (∫|ρ|)/(4π(‖x‖ − a)²)`; `tendsto_newtonPotential_cocompact`: `φ → 0` at infinity.
* `eq_newtonPotential_of_tendsto`: **uniqueness** — a `C²` solution of `−Δu = ρ` that tends to
  `0` at infinity is the Newton potential.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric Real
open scoped Topology Laplacian ContDiff Convolution

namespace ProjectAinos.SmoothGeometry.Potential

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The Newton potential `φ = K ⋆ ρ` of a density `ρ`, `φ(x) = ∫ K(y) ρ(x − y) dy`. -/
def newtonPotential (ρ : E3 → ℝ) : E3 → ℝ :=
  newtonKernel ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ

/-- The potential as an integral of the kernel against the translated density. -/
theorem newtonPotential_apply (ρ : E3 → ℝ) (x : E3) :
    newtonPotential ρ x = ∫ y, newtonKernel y * ρ (x - y) := by
  simp [newtonPotential, convolution_def]

/-- The potential `φ(x) = ∫ ρ(y)/(4π‖x − y‖) dy`. -/
theorem newtonPotential_eq_integral (ρ : E3 → ℝ) (x : E3) :
    newtonPotential ρ x = ∫ y, ρ y * newtonKernel (x - y) := by
  rw [newtonPotential_apply,
    ← integral_sub_left_eq_self (fun y => newtonKernel y * ρ (x - y)) volume x]
  simp [mul_comm]

/-- The integrand of the potential of a continuous density of compact support is integrable. -/
theorem integrable_newtonKernel_mul {ρ : E3 → ℝ} (hcρ : HasCompactSupport ρ) (hρ : Continuous ρ)
    (x : E3) : Integrable fun y => newtonKernel y * ρ (x - y) := by
  have h := hcρ.convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℝ)
    locallyIntegrable_newtonKernel hρ x
  simp only [ConvolutionExistsAt, ContinuousLinearMap.lsmul_apply, smul_eq_mul] at h
  exact h

/-! ### Smoothness and Poisson's equation -/

/-- The potential of a `Cⁿ` density of compact support is `Cⁿ`. -/
theorem contDiff_newtonPotential {ρ : E3 → ℝ} {n : ℕ∞} (hcρ : HasCompactSupport ρ)
    (hρ : ContDiff ℝ n ρ) : ContDiff ℝ n (newtonPotential ρ) :=
  hcρ.contDiff_convolution_right _ locallyIntegrable_newtonKernel hρ

/-- The potential of a `C²` density of compact support is `C²`. -/
theorem contDiff_two_newtonPotential {ρ : E3 → ℝ} (hcρ : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 2 ρ) : ContDiff ℝ 2 (newtonPotential ρ) := by
  have h := contDiff_newtonPotential (n := 2) hcρ (by exact_mod_cast hρ)
  exact_mod_cast h

/-- The derivative of the potential along `v` is the potential of the derivative along `v`. -/
theorem fderiv_newtonPotential_apply {ρ : E3 → ℝ} (hcρ : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 1 ρ) (x v : E3) :
    fderiv ℝ (newtonPotential ρ) x v = newtonPotential (fun y => fderiv ℝ ρ y v) x := by
  unfold newtonPotential
  rw [(hcρ.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    locallyIntegrable_newtonKernel hρ x).fderiv]
  exact convolution_precompR_apply _ locallyIntegrable_newtonKernel (hcρ.fderiv ℝ)
    (hρ.continuous_fderiv (by norm_num)) x v

/-- The Laplacian of the potential is the potential of the Laplacian. -/
theorem coordLaplacian_newtonPotential {ρ : E3 → ℝ} (hcρ : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 2 ρ) (x : E3) :
    coordLaplacian (newtonPotential ρ) x = newtonPotential (coordLaplacian ρ) x := by
  have h1 : ContDiff ℝ 1 ρ := hρ.of_le (by norm_num)
  have hpart (v : E3) : (fun y => fderiv ℝ (newtonPotential ρ) y v) =
      newtonPotential (fun y => fderiv ℝ ρ y v) :=
    funext fun y => fderiv_newtonPotential_apply hcρ h1 y v
  have hterm (v : E3) : fderiv ℝ (fun y => fderiv ℝ (newtonPotential ρ) y v) x v =
      newtonPotential (fun y => fderiv ℝ (fun z => fderiv ℝ ρ z v) y v) x := by
    rw [hpart]
    exact fderiv_newtonPotential_apply (hcρ.fderiv_apply (𝕜 := ℝ) v)
      ((hρ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const) x v
  have hint (v : E3) : Integrable fun y =>
      newtonKernel y * fderiv ℝ (fun z => fderiv ℝ ρ z v) (x - y) v := by
    refine integrable_newtonKernel_mul (ρ := fun y => fderiv ℝ (fun z => fderiv ℝ ρ z v) y v)
      ((hcρ.fderiv_apply (𝕜 := ℝ) v).fderiv_apply (𝕜 := ℝ) v) ?_ x
    exact (((hρ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).continuous_fderiv
      (by norm_num)).clm_apply continuous_const
  simp only [coordLaplacian, hterm, newtonPotential_apply]
  rw [← integral_finsetSum _ fun i _ => hint _]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [Finset.mul_sum]

/-- **Poisson's equation**: the potential of a `C²` density of compact support satisfies
`Δφ = −ρ`. -/
theorem laplacian_newtonPotential {ρ : E3 → ℝ} (hcρ : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ)
    (x : E3) : Δ (newtonPotential ρ) x = -ρ x := by
  rw [← coordLaplacian_eq_laplacian (contDiff_two_newtonPotential hcρ hρ).contDiffAt,
    coordLaplacian_newtonPotential hcρ hρ, newtonPotential_apply,
    ← integral_neg_eq_self (fun y => newtonKernel y * coordLaplacian ρ (x - y)) volume]
  set χ : E3 → ℝ := fun z => ρ (x + z) with hχdef
  have hχ : ContDiff ℝ 2 χ := hρ.comp (contDiff_const.add contDiff_id)
  have hcχ : HasCompactSupport χ := hcρ.comp_homeomorph (Homeomorph.addLeft x)
  have h := integral_newtonKernel_mul_coordLaplacian hχ hcχ
  simp only [hχdef, add_zero] at h
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [newtonKernel_neg, sub_neg_eq_add, coordLaplacian_comp_add_left]

/-! ### Decay -/

/-- On the support of the density, the kernel at `x − y` is at most `1/(4π(‖x‖ − a))`. -/
theorem abs_mul_newtonKernel_le {ρ : E3 → ℝ} {a : ℝ} (ha : tsupport ρ ⊆ closedBall 0 a)
    {x : E3} (hx : a < ‖x‖) (y : E3) :
    |ρ y * newtonKernel (x - y)| ≤ |ρ y| * (4 * π * (‖x‖ - a))⁻¹ := by
  by_cases hy : ρ y = 0
  · simp [hy]
  · have hya : ‖y‖ ≤ a := by simpa using ha (subset_tsupport ρ hy)
    have hxy : ‖x‖ - a ≤ ‖x - y‖ := by
      have := norm_sub_norm_le x y
      linarith
    rw [abs_mul, abs_of_nonneg (newtonKernel_nonneg _)]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    unfold newtonKernel
    exact inv_anti₀ (by nlinarith [pi_pos]) (by nlinarith [pi_pos])

/-- **Decay of the potential**: if the support of `ρ` lies in the ball `‖y‖ ≤ a`, then
`|φ(x)| ≤ (∫|ρ|)/(4π(‖x‖ − a))` for `‖x‖ > a`. -/
theorem abs_newtonPotential_le {ρ : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ)
    {a : ℝ} (ha : tsupport ρ ⊆ closedBall 0 a) {x : E3} (hx : a < ‖x‖) :
    |newtonPotential ρ x| ≤ (∫ y, |ρ y|) / (4 * π * (‖x‖ - a)) := by
  rw [newtonPotential_eq_integral, div_eq_mul_inv, ← integral_mul_const, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le ?_ (Eventually.of_forall fun y => ?_)
  · exact (hρ.abs.mul continuous_const).integrable_of_hasCompactSupport hcρ.abs.mul_right
  · rw [Real.norm_eq_abs]
    exact abs_mul_newtonKernel_le ha hx y

/-- Outside the ball `‖y‖ ≤ a` that contains the support, the derivative of the potential is the
integral of `ρ(y) DK(x − y)`. -/
theorem hasFDerivAt_newtonPotential_of_lt {ρ : E3 → ℝ} (hρ : Continuous ρ)
    (hcρ : HasCompactSupport ρ) {a : ℝ} (ha : tsupport ρ ⊆ closedBall 0 a) {x : E3}
    (hx : a < ‖x‖) :
    HasFDerivAt (newtonPotential ρ) (∫ y, ρ y • fderiv ℝ newtonKernel (x - y)) x := by
  set δ := (‖x‖ - a) / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hfun : newtonPotential ρ = fun x' => ∫ y, ρ y * newtonKernel (x' - y) :=
    funext (newtonPotential_eq_integral ρ)
  have hsep : ∀ x' ∈ ball x δ, ∀ y, ρ y ≠ 0 → δ ≤ ‖x' - y‖ := by
    intro x' hx' y hy
    have hya : ‖y‖ ≤ a := by simpa using ha (subset_tsupport ρ hy)
    have h1 : ‖x' - x‖ < δ := by rwa [mem_ball, dist_eq_norm] at hx'
    have h2 : ‖x‖ ≤ ‖x - x'‖ + ‖x' - y‖ + ‖y‖ := by
      calc ‖x‖ = ‖(x - x') + (x' - y) + y‖ := by congr 1; abel
        _ ≤ ‖(x - x') + (x' - y)‖ + ‖y‖ := norm_add_le _ _
        _ ≤ ‖x - x'‖ + ‖x' - y‖ + ‖y‖ := by gcongr; exact norm_add_le _ _
    rw [norm_sub_rev] at h2
    linarith
  have hKm : Measurable newtonKernel := (measurable_norm.const_mul _).inv
  rw [hfun]
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := volume)
    (F := fun x' y => ρ y * newtonKernel (x' - y))
    (F' := fun x' y => ρ y • fderiv ℝ newtonKernel (x' - y))
    (bound := fun y => |ρ y| * (4 * π * δ ^ 2)⁻¹) (ball_mem_nhds x hδ)
    (Eventually.of_forall fun x' => ?_) ?_ ?_ (Eventually.of_forall fun y x' hx' => ?_) ?_
    (Eventually.of_forall fun y x' hx' => ?_)
  · exact hρ.aestronglyMeasurable.mul
      (hKm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  · refine Integrable.mono' ((hρ.abs.mul (continuous_const (y := (4 * π * (‖x‖ - a))⁻¹))
      ).integrable_of_hasCompactSupport hcρ.abs.mul_right) (hρ.aestronglyMeasurable.mul
      (hKm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
      (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]
    exact abs_mul_newtonKernel_le ha hx y
  · exact hρ.aestronglyMeasurable.smul
      ((measurable_fderiv ℝ newtonKernel).comp
        (measurable_const.sub measurable_id)).aestronglyMeasurable
  · by_cases hy : ρ y = 0
    · simp [hy]
    · have h1 := hsep x' hx' y hy
      have hne : x' - y ≠ 0 := norm_pos_iff.mp (hδ.trans_le h1)
      rw [norm_smul, norm_fderiv_newtonKernel hne, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) ?_) (abs_nonneg _)
      have : δ ^ 2 ≤ ‖x' - y‖ ^ 2 := pow_le_pow_left₀ hδ.le h1 2
      nlinarith [pi_pos]
  · exact (hρ.abs.mul continuous_const).integrable_of_hasCompactSupport hcρ.abs.mul_right
  · by_cases hy : ρ y = 0
    · simp only [hy, zero_mul, zero_smul]
      exact hasFDerivAt_const 0 x'
    · have hne : x' - y ≠ 0 := norm_pos_iff.mp (hδ.trans_le (hsep x' hx' y hy))
      have h1 : HasFDerivAt (fun z => newtonKernel (z - y)) (fderiv ℝ newtonKernel (x' - y)) x' :=
        (hasFDerivAt_comp_sub y).mpr (hasFDerivAt_newtonKernel hne).differentiableAt.hasFDerivAt
      exact h1.const_mul (ρ y)

/-- **Decay of the field**: if the support of `ρ` lies in the ball `‖y‖ ≤ a`, then
`‖Dφ(x)‖ ≤ (∫|ρ|)/(4π(‖x‖ − a)²)` for `‖x‖ > a`. -/
theorem norm_fderiv_newtonPotential_le {ρ : E3 → ℝ} (hρ : Continuous ρ)
    (hcρ : HasCompactSupport ρ) {a : ℝ} (ha : tsupport ρ ⊆ closedBall 0 a) {x : E3}
    (hx : a < ‖x‖) :
    ‖fderiv ℝ (newtonPotential ρ) x‖ ≤ (∫ y, |ρ y|) / (4 * π * (‖x‖ - a) ^ 2) := by
  rw [(hasFDerivAt_newtonPotential_of_lt hρ hcρ ha hx).fderiv, div_eq_mul_inv,
    ← integral_mul_const]
  refine norm_integral_le_of_norm_le
    ((hρ.abs.mul continuous_const).integrable_of_hasCompactSupport hcρ.abs.mul_right)
    (Eventually.of_forall fun y => ?_)
  by_cases hy : ρ y = 0
  · simp [hy]
  · have hya : ‖y‖ ≤ a := by simpa using ha (subset_tsupport ρ hy)
    have hxy : ‖x‖ - a ≤ ‖x - y‖ := by
      have := norm_sub_norm_le x y
      linarith
    have hd : 0 < ‖x‖ - a := by linarith
    have hne : x - y ≠ 0 := norm_pos_iff.mp (hd.trans_le hxy)
    rw [norm_smul, norm_fderiv_newtonKernel hne, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) ?_) (abs_nonneg _)
    have : (‖x‖ - a) ^ 2 ≤ ‖x - y‖ ^ 2 := pow_le_pow_left₀ hd.le hxy 2
    nlinarith [pi_pos]

/-- The potential of a continuous density of compact support tends to `0` at infinity. -/
theorem tendsto_newtonPotential_cocompact {ρ : E3 → ℝ} (hρ : Continuous ρ)
    (hcρ : HasCompactSupport ρ) : Tendsto (newtonPotential ρ) (cocompact E3) (𝓝 0) := by
  obtain ⟨a, ha⟩ := hcρ.isCompact.isBounded.subset_closedBall 0
  have hev : ∀ᶠ x in cocompact E3, a < ‖x‖ :=
    tendsto_norm_cocompact_atTop.eventually (eventually_gt_atTop a)
  have hlim : Tendsto (fun x : E3 => (∫ y, |ρ y|) / (4 * π * (‖x‖ - a))) (cocompact E3)
      (𝓝 0) := by
    refine tendsto_const_nhds.div_atTop ?_
    refine ((tendsto_atTop_add_const_right _ (-a) tendsto_norm_cocompact_atTop).const_mul_atTop
      (by positivity : (0 : ℝ) < 4 * π)).congr fun x => ?_
    ring
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hev] with x hx
  rw [Real.norm_eq_abs]
  exact abs_newtonPotential_le hρ hcρ ha hx

/-- A ball `‖y‖ ≤ a` with `a ≥ 0` contains the support of a density of compact support. -/
theorem exists_tsupport_subset_closedBall {ρ : E3 → ℝ} (hcρ : HasCompactSupport ρ) :
    ∃ a, 0 ≤ a ∧ tsupport ρ ⊆ closedBall 0 a := by
  obtain ⟨a, ha⟩ := hcρ.isCompact.isBounded.subset_closedBall 0
  exact ⟨max a 0, le_max_right _ _, ha.trans (closedBall_subset_closedBall (le_max_left _ _))⟩

/-- A global bound `|φ(x)| ≤ A/(1 + ‖x‖)` on the potential of a continuous density of compact
support. -/
theorem exists_abs_newtonPotential_le {ρ : E3 → ℝ} (hρ : Continuous ρ)
    (hcρ : HasCompactSupport ρ) : ∃ A, ∀ x, |newtonPotential ρ x| ≤ A * (1 + ‖x‖)⁻¹ := by
  obtain ⟨a, ha0, ha⟩ := exists_tsupport_subset_closedBall hcρ
  have hφc : Continuous (newtonPotential ρ) :=
    (contDiff_newtonPotential (n := 0) hcρ (contDiff_zero.mpr hρ)).continuous
  obtain ⟨S, hS⟩ := (isCompact_closedBall (0 : E3) (2 * a + 1)).exists_bound_of_continuousOn
    hφc.continuousOn
  have hM : 0 ≤ ∫ y, |ρ y| := integral_nonneg fun y => abs_nonneg _
  refine ⟨max ((∫ y, |ρ y|) / (2 * π)) (S * (2 * a + 2)), fun x => ?_⟩
  have hx1 : 0 < 1 + ‖x‖ := by positivity
  by_cases hx : ‖x‖ ≤ 2 * a + 1
  · have h1 : |newtonPotential ρ x| ≤ S := by
      simpa using hS x (by simpa using hx)
    have hS0 : 0 ≤ S := (abs_nonneg _).trans h1
    calc |newtonPotential ρ x| ≤ S := h1
      _ = S * (1 + ‖x‖) * (1 + ‖x‖)⁻¹ := by field_simp
      _ ≤ S * (2 * a + 2) * (1 + ‖x‖)⁻¹ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hS0)
            (by positivity)
      _ ≤ _ := by gcongr; exact le_max_right _ _
  · push Not at hx
    have hxa : a < ‖x‖ := by linarith
    calc |newtonPotential ρ x| ≤ (∫ y, |ρ y|) / (4 * π * (‖x‖ - a)) :=
          abs_newtonPotential_le hρ hcρ ha hxa
      _ ≤ (∫ y, |ρ y|) / (2 * π * (1 + ‖x‖)) :=
          div_le_div_of_nonneg_left hM (by positivity) (by nlinarith [pi_pos])
      _ = (∫ y, |ρ y|) / (2 * π) * (1 + ‖x‖)⁻¹ := by field_simp
      _ ≤ _ := by gcongr; exact le_max_left _ _

/-- A global bound `‖Dφ(x)‖ ≤ B/(1 + ‖x‖)²` on the derivative of the potential of a `C¹` density
of compact support. -/
theorem exists_norm_fderiv_newtonPotential_le {ρ : E3 → ℝ} (hρ : ContDiff ℝ 1 ρ)
    (hcρ : HasCompactSupport ρ) :
    ∃ B, ∀ x, ‖fderiv ℝ (newtonPotential ρ) x‖ ≤ B * ((1 + ‖x‖) ^ 2)⁻¹ := by
  obtain ⟨a, ha0, ha⟩ := exists_tsupport_subset_closedBall hcρ
  have hφ : ContDiff ℝ 1 (newtonPotential ρ) := by
    have h := contDiff_newtonPotential (n := 1) hcρ (by exact_mod_cast hρ)
    exact_mod_cast h
  have hDc : Continuous (fderiv ℝ (newtonPotential ρ)) := hφ.continuous_fderiv (by norm_num)
  obtain ⟨S, hS⟩ := (isCompact_closedBall (0 : E3) (2 * a + 1)).exists_bound_of_continuousOn
    hDc.continuousOn
  have hM : 0 ≤ ∫ y, |ρ y| := integral_nonneg fun y => abs_nonneg _
  refine ⟨max ((∫ y, |ρ y|) / π) (S * (2 * a + 2) ^ 2), fun x => ?_⟩
  have hx1 : 0 < 1 + ‖x‖ := by positivity
  by_cases hx : ‖x‖ ≤ 2 * a + 1
  · have h1 : ‖fderiv ℝ (newtonPotential ρ) x‖ ≤ S := hS x (by simpa using hx)
    have hS0 : 0 ≤ S := (norm_nonneg _).trans h1
    calc ‖fderiv ℝ (newtonPotential ρ) x‖ ≤ S := h1
      _ = S * (1 + ‖x‖) ^ 2 * ((1 + ‖x‖) ^ 2)⁻¹ := by field_simp
      _ ≤ S * (2 * a + 2) ^ 2 * ((1 + ‖x‖) ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) (by linarith) 2) hS0) (by positivity)
      _ ≤ _ := by gcongr; exact le_max_right _ _
  · push Not at hx
    have hxa : a < ‖x‖ := by linarith
    have hd : (1 + ‖x‖) / 2 ≤ ‖x‖ - a := by linarith
    have hd2 : ((1 + ‖x‖) / 2) ^ 2 ≤ (‖x‖ - a) ^ 2 := pow_le_pow_left₀ (by positivity) hd 2
    calc ‖fderiv ℝ (newtonPotential ρ) x‖ ≤ (∫ y, |ρ y|) / (4 * π * (‖x‖ - a) ^ 2) :=
          norm_fderiv_newtonPotential_le hρ.continuous hcρ ha hxa
      _ ≤ (∫ y, |ρ y|) / (π * (1 + ‖x‖) ^ 2) :=
          div_le_div_of_nonneg_left hM (by positivity) (by nlinarith [pi_pos])
      _ = (∫ y, |ρ y|) / π * ((1 + ‖x‖) ^ 2)⁻¹ := by field_simp
      _ ≤ _ := by gcongr; exact le_max_left _ _

/-! ### Uniqueness -/

/-- **Uniqueness of the decaying solution**: a `C²` solution of `−Δu = ρ` on all of space that
tends to `0` at infinity is the Newton potential. -/
theorem eq_newtonPotential_of_tendsto {ρ u : E3 → ℝ} (hcρ : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 2 ρ) (hu : ContDiff ℝ 2 u) (hΔ : ∀ x, -Δ u x = ρ x)
    (hlim : Tendsto u (cocompact E3) (𝓝 0)) : u = newtonPotential ρ := by
  have hφ := contDiff_two_newtonPotential hcρ hρ
  have h := eq_zero_of_harmonic_of_tendsto (u := u - newtonPotential ρ) (hu.sub hφ)
    (fun x => ?_) ?_
  · exact sub_eq_zero.mp h
  · rw [ContDiffAt.laplacian_sub hu.contDiffAt hφ.contDiffAt, laplacian_newtonPotential hcρ hρ,
      ← hΔ x]
    simp
  · have := hlim.sub (tendsto_newtonPotential_cocompact hρ.continuous hcρ)
    rw [sub_zero] at this
    exact this

end ProjectAinos.SmoothGeometry.Potential
