/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.SphericalMultipole
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-! # Spherical expansion of the interaction of two extended charges

Use coordinates relative to the centre of each charge. For disjoint enclosing balls, the
ratio of the sum of the radii to the centre separation is strictly below one. A single geometric
majorant thus justifies summation under both charge integrals. Each coefficient pairs a solid
harmonic of the relative displacement with the two actual charge densities.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Metric Set MvPolynomial
open ProjectAinos.SmoothGeometry.Potential
open ProjectAinos.SpecialFunctions ProjectAinos.SpecialFunctions.SphericalHarmonics
namespace ProjectAinos.Electrodynamics.Multipole

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private abbrev joint := (volume : Measure E3).prod (volume : Measure E3)
private def weight (ρ σ : E3 → ℝ) (p : E3 × E3) := σ p.1 * ρ p.2
private def disp (p : E3 × E3) := p.2 - p.1

/-- Solid harmonic moment of the relative displacement of a pair of charge distributions. -/
def interactionMoment (ρ σ : E3 → ℝ) (n : ℕ) (i : Fin (2 * n + 1)) : ℝ :=
  ∫ p : E3 × E3, σ p.1 * ρ p.2 * eval (p.2 - p.1)
    (solidRepresentative n (realBasis n i)).val.val ∂(volume.prod volume)

private theorem compact_weight {ρ σ : E3 → ℝ} (hρ : HasCompactSupport ρ)
    (hσ : HasCompactSupport σ) :
    HasCompactSupport (weight ρ σ) := by
  apply HasCompactSupport.of_support_subset_isCompact (hσ.prod hρ)
  rintro p hp
  exact ⟨subset_tsupport _ (left_ne_zero_of_mul hp), subset_tsupport _ (right_ne_zero_of_mul hp)⟩

private theorem continuous_weight {ρ σ : E3 → ℝ} (hρ : Continuous ρ) (hσ : Continuous σ) :
    Continuous (weight ρ σ) := (hσ.comp continuous_fst).mul (hρ.comp continuous_snd)

private theorem disp_le {ρ σ : E3 → ℝ} {a b : ℝ} (hρ : tsupport ρ ⊆ closedBall 0 a)
    (hσ : tsupport σ ⊆ closedBall 0 b) {p : E3 × E3} (hp : weight ρ σ p ≠ 0) :
    ‖disp p‖ ≤ a + b :=
  (norm_sub_le _ _).trans (add_le_add (norm_le_of_ne_zero hρ (right_ne_zero_of_mul hp))
    (norm_le_of_ne_zero hσ (left_ne_zero_of_mul hp)))

private def term (R : E3) (n : ℕ) (p : E3 × E3) :=
  (n.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ n newtonKernel R (fun _ => -disp p)

private theorem sum_joint {ρ σ : E3 → ℝ} (hρ : Continuous ρ) (hσ : Continuous σ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hsa : tsupport ρ ⊆ closedBall 0 a)
    (hsb : tsupport σ ⊆ closedBall 0 b) {R : E3} (hR : a + b < ‖R‖) :
    HasSum (fun n => ∫ p, weight ρ σ p * term R n p ∂joint)
      (∫ p, weight ρ σ p * newtonKernel (R - disp p) ∂joint) := by
  let q := (a + b) / ‖R‖
  have nr : 0 < ‖R‖ := (add_nonneg ha hb).trans_lt hR
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have sq := summable_geometric_of_lt_one hq ((div_lt_one nr).mpr hR)
  have hs := compact_weight (hasCompactSupport_of_tsupport_subset hsa)
    (hasCompactSupport_of_tsupport_subset hsb)
  have hw := (continuous_weight hρ hσ).integrable_of_hasCompactSupport (μ := joint) hs
  apply hasSum_integral_of_dominated_convergence
    (fun n p => (|weight ρ σ p| * newtonKernel R) * q ^ n)
  · intro n
    exact ((continuous_weight hρ hσ).mul (continuous_const.mul
      ((continuous_apply_neg _).comp (continuous_snd.sub continuous_fst)))).aestronglyMeasurable
  · intro n
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_mul]
    by_cases hwz : weight ρ σ p = 0
    · simp [hwz]
    have hy := disp_le hsa hsb hwz
    have h := Legendre.abs_eval_le_one n (abs_real_inner_div_norm_mul_norm_le_one R (disp p))
    unfold term
    rw [newtonKernel_derivative_legendre _ (norm_pos_iff.mp nr), abs_mul, abs_mul, abs_pow,
      abs_of_nonneg (newtonKernel_nonneg _), abs_of_nonneg (by positivity : 0 ≤ ‖disp p‖ / ‖R‖)]
    rw [mul_assoc (|weight ρ σ p|)]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply mul_le_mul_of_nonneg_left _ (newtonKernel_nonneg _)
    exact (mul_le_mul_of_nonneg_right h (by positivity)).trans (by
      rw [one_mul]
      exact pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right hy nr.le) _)
  · exact ae_of_all _ fun p => sq.mul_left _
  · simp_rw [tsum_mul_left]
    exact (hw.abs.mul_const _).mul_const _
  · filter_upwards with p
    by_cases hp : weight ρ σ p = 0
    · simp [hp, hasSum_zero]
    have h := (Legendre.hasSum_newtonKernel R (disp p) ((disp_le hsa hsb hp).trans_lt hR)).mul_left
      (weight ρ σ p)
    simpa only [term, newtonKernel_derivative_legendre _ (norm_pos_iff.mp nr)] using h

private theorem double_energy {ρ σ : E3 → ℝ} (hρ : Continuous ρ) (hσ : Continuous σ)
    {a b : ℝ} (hsa : tsupport ρ ⊆ closedBall 0 a) (hsb : tsupport σ ⊆ closedBall 0 b)
    {R : E3} (hR : a + b < ‖R‖) :
    ∫ p, weight ρ σ p * newtonKernel (R - disp p) ∂joint =
      externalEnergy σ (fun z => newtonPotential ρ (R + z)) := by
  have hw := (continuous_weight hρ hσ).integrable_of_hasCompactSupport (μ := joint)
    (compact_weight (hasCompactSupport_of_tsupport_subset hsa)
      (hasCompactSupport_of_tsupport_subset hsb))
  have hgap : 0 < ‖R‖ - (a + b) := sub_pos.mpr hR
  have hi : Integrable (fun p => weight ρ σ p * newtonKernel (R - disp p)) joint := by
    apply (hw.abs.mul_const (4 * Real.pi * (‖R‖ - (a + b)))⁻¹).mono'
    · unfold newtonKernel disp
      exact ((continuous_weight hρ hσ).measurable.mul (by fun_prop)).aestronglyMeasurable
    · filter_upwards with p
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (newtonKernel_nonneg _)]
      by_cases hp : weight ρ σ p = 0
      · simp [hp]
      have hd : ‖R‖ - (a + b) ≤ ‖R - disp p‖ := by
        linarith [norm_sub_norm_le R (disp p), disp_le hsa hsb hp]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left hd (by positivity))
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards with z
  change (∫ y : E3, σ z * ρ y * newtonKernel (R - (y - z))) = σ z * newtonPotential ρ (R + z)
  rw [newtonPotential_eq_integral, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  rw [show R - (y - z) = R + z - y by abel, mul_assoc]

/-- The convergent spherical expansion of the mutual energy when the enclosing balls are
strictly separated. Both densities may change sign and have arbitrary shape inside their balls. -/
theorem hasSum_interactionEnergy {ρ σ : E3 → ℝ} (hρ : Continuous ρ) (hσ : Continuous σ)
    {a b r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hsa : tsupport ρ ⊆ closedBall 0 a)
    (hsb : tsupport σ ⊆ closedBall 0 b) (hr : a + b < r) (u : UnitSphere 3) :
    HasSum (fun n : ℕ => ((2 * (n : ℝ) + 1) * r ^ (n + 1))⁻¹ *
      ∑ i, representative 3 n (realBasis n i) u * interactionMoment ρ σ n i)
      (externalEnergy σ (fun z => newtonPotential ρ (r • u.val + z))) := by
  have hr0 := (add_nonneg ha hb).trans_lt hr
  have hR : a + b < ‖r • u.val‖ := by
    simpa [norm_smul, Real.norm_of_nonneg hr0.le, norm_eq_of_mem_sphere] using hr
  have h := sum_joint hρ hσ ha hb hsa hsb hR
  rw [double_energy hρ hσ hsa hsb hR] at h
  apply h.congr_fun
  intro n
  let Y i := representative 3 n (realBasis n i) u
  let H i (p : E3 × E3) := eval (disp p) (solidRepresentative n (realBasis n i)).val.val
  let c := ((2 * (n : ℝ) + 1) * r ^ (n + 1))⁻¹
  have hs := compact_weight (hasCompactSupport_of_tsupport_subset hsa)
    (hasCompactSupport_of_tsupport_subset hsb)
  have hi i : Integrable (fun p => weight ρ σ p * H i p) joint :=
    ((continuous_weight hρ hσ).mul ((MvPolynomial.continuous_eval _).comp
      (continuous_pi fun j => (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp
        (continuous_snd.sub continuous_fst)))).integrable_of_hasCompactSupport hs.mul_right
  symm
  change (∫ p, weight ρ σ p * term (r • u.val) n p ∂joint) =
    c * ∑ i, Y i * interactionMoment ρ σ n i
  calc
    _ = ∫ p, c * ∑ i, Y i * (weight ρ σ p * H i p) ∂joint := by
      apply integral_congr_ae
      filter_upwards with p
      change weight ρ σ p * (_ * _) = _
      rw [newtonKernel_derivative_addition (realBasis n) u hr0]
      change weight ρ σ p * (c * ∑ i, Y i * H i p) = _
      rw [mul_left_comm, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun _ _ => mul_left_comm ..
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum _ (fun i _ => (hi i).const_mul (Y i))]
      simp only [integral_const_mul, H, disp, weight, interactionMoment]

end ProjectAinos.Electrodynamics.Multipole
