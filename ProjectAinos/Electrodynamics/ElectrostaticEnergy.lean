/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.Electrostatics
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# The electrostatic energy of charges

Space is `EuclideanSpace ℝ (Fin 3)`; the units have `div E = ρ`, so the potential of a charge
density `ρ` is the Newton potential `φ = ρ ⋆ 1/(4π|x|)` and the field is `E = −∇φ`
(Landau–Lifshitz, *The Classical Theory of Fields*, §37). For a `C²` density of compact support
the three expressions of the energy are finite and equal:

* `integrable_double`, `integral_mul_newtonPotential_eq_double`: `∫ ρφ = ∬ ρ(x)ρ(y)/(4π|x − y|)`,
  with an integrable integrand on the product (Fubini);
* `integrable_gradientNormSq_newtonPotential`, `integral_mul_newtonPotential_eq_integral_sq`:
  `∫ ρφ = ∫ |∇φ|²`, with `|∇φ|² = Σᵢ (∂ᵢφ)²`. The proof inserts a cut-off `ψ(x/R)` equal to one
  on the support, integrates by parts, and lets `R → ∞` by dominated convergence: the term
  `∫ φ ∇φ · ∇ψ_R` is dominated by `C/(1 + |x|)⁴`.
* `electrostaticEnergy_eq`: the three integrands are integrable and
  `½ ∫ ρφ = ½ ∬ ρ(x)ρ(y)/(4π|x − y|) = ∫ ½|E|²` with the field `E = −∇φ` (`coulombField`).
* `bumpCharge`, `bumpCharge_instance`: a smooth bump of compact support, with `bumpCharge 0 = 1`,
  is an instance of the equations of Maxwell and of the energy identities.

For a point charge the field energy diverges at the charge:

* `integral_pointCharge_energy_outside`: the energy `∫ ½|E_q|²` of the Coulomb field
  `E_q(x) = q x/(4π|x|³)` (`pointChargeField`) outside the ball of radius `ε` is `q²/(8πε)`;
* `tendsto_pointCharge_energy`, `not_integrable_pointCharge_energy`: it tends to `∞` as
  `ε → 0⁺`, and `½|E_q|²` is not integrable, so the self-energy of a point charge is infinite.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric Real
open scoped Topology Laplacian ContDiff

namespace ProjectAinos.Electrodynamics.Electrostatics

open SmoothGeometry.Potential

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### The double integral -/

/-- For a continuous density of compact support, `ρ(x)ρ(y)/(4π|x − y|)` is integrable on the
product of two copies of space. -/
theorem integrable_double {ρ : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) :
    Integrable (fun p : E3 × E3 => ρ p.1 * ρ p.2 * newtonKernel (p.1 - p.2))
      (volume.prod volume) := by
  obtain ⟨a, ha0, ha⟩ := exists_tsupport_subset_closedBall hcρ
  set K' : E3 → ℝ := (closedBall (0 : E3) (2 * a)).indicator newtonKernel with hK'def
  have hK' : Integrable K' := (integrable_indicator_iff measurableSet_closedBall).mpr
    (locallyIntegrable_newtonKernel.integrableOn_isCompact (isCompact_closedBall 0 (2 * a)))
  have hρi : Integrable ρ := hρ.integrable_of_hasCompactSupport hcρ
  have h1 := hρi.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hK' (μ := volume)
  obtain ⟨C, hC⟩ := hρ.bounded_above_of_compact_support hcρ
  have h2 := h1.bdd_mul (f := fun p : E3 × E3 => ρ p.1) (c := C)
    (hρ.comp continuous_fst).aestronglyMeasurable (Eventually.of_forall fun p => hC p.1)
  refine h2.congr (Eventually.of_forall fun p => ?_)
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  by_cases hx : ρ p.1 = 0
  · simp [hx]
  by_cases hy : ρ p.2 = 0
  · simp [hy]
  have hxa : ‖p.1‖ ≤ a := by simpa using ha (subset_tsupport ρ hx)
  have hya : ‖p.2‖ ≤ a := by simpa using ha (subset_tsupport ρ hy)
  have hmem : p.1 - p.2 ∈ closedBall (0 : E3) (2 * a) := by
    rw [mem_closedBall, dist_zero_right]
    linarith [norm_sub_le p.1 p.2]
  rw [hK'def, indicator_of_mem hmem]
  ring

/-- **The energy as a double integral**: `∫ ρφ = ∬ ρ(x)ρ(y)/(4π|x − y|)` for a continuous density
of compact support. -/
theorem integral_mul_newtonPotential_eq_double {ρ : E3 → ℝ} (hρ : Continuous ρ)
    (hcρ : HasCompactSupport ρ) :
    ∫ x, ρ x * newtonPotential ρ x =
      ∫ p, ρ p.1 * ρ p.2 * newtonKernel (p.1 - p.2) ∂(volume.prod volume) := by
  rw [integral_prod _ (integrable_double hρ hcρ)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [newtonPotential_eq_integral, ← integral_const_mul, mul_assoc]

/-! ### The square of the gradient -/

/-- The square `|∇f|² = Σᵢ (∂ᵢf)²` of the gradient in the co-ordinates. -/
def gradientNormSq (f : E3 → ℝ) (x : E3) : ℝ :=
  ∑ i, (fderiv ℝ f x (EuclideanSpace.single i 1)) ^ 2

/-- A partial derivative is bounded by the norm of the derivative. -/
theorem abs_apply_single_le (L : E3 →L[ℝ] ℝ) (i : Fin 3) :
    |L (EuclideanSpace.single i 1)| ≤ ‖L‖ := by
  have h := L.le_opNorm (EuclideanSpace.single i 1)
  have h1 : ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := by simp
  rwa [h1, mul_one, Real.norm_eq_abs] at h

/-- The square of the gradient is at most `3‖Df‖²`. -/
theorem gradientNormSq_le (f : E3 → ℝ) (x : E3) :
    gradientNormSq f x ≤ 3 * ‖fderiv ℝ f x‖ ^ 2 := by
  have h (i : Fin 3) : (fderiv ℝ f x (EuclideanSpace.single i 1)) ^ 2 ≤ ‖fderiv ℝ f x‖ ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_apply_single_le _ i) 2
  calc gradientNormSq f x ≤ ∑ _i : Fin 3, ‖fderiv ℝ f x‖ ^ 2 := Finset.sum_le_sum fun i _ => h i
    _ = 3 * ‖fderiv ℝ f x‖ ^ 2 := by simp

/-- The square of the gradient is nonnegative. -/
theorem gradientNormSq_nonneg (f : E3 → ℝ) (x : E3) : 0 ≤ gradientNormSq f x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The function `(1 + |x|)⁻⁴` is integrable on three-dimensional space. -/
theorem integrable_inv_one_add_norm_pow_four :
    Integrable fun x : E3 => ((1 + ‖x‖) ^ 4)⁻¹ := by
  have h := integrable_one_add_norm (E := E3) (μ := volume) (r := 4) (by simp; norm_num)
  refine h.congr (Eventually.of_forall fun x => ?_)
  have hx : 0 ≤ 1 + ‖x‖ := by positivity
  simp only
  rw [Real.rpow_neg hx]
  norm_cast

/-- The square of the gradient of the potential of a `C¹` density of compact support is
integrable. -/
theorem integrable_gradientNormSq_newtonPotential {ρ : E3 → ℝ} (hρ : ContDiff ℝ 1 ρ)
    (hcρ : HasCompactSupport ρ) : Integrable (gradientNormSq (newtonPotential ρ)) := by
  obtain ⟨B, hB⟩ := exists_norm_fderiv_newtonPotential_le hρ hcρ
  have hφ : ContDiff ℝ 1 (newtonPotential ρ) := by
    have h := contDiff_newtonPotential (n := 1) hcρ (by exact_mod_cast hρ)
    exact_mod_cast h
  have hc : Continuous (gradientNormSq (newtonPotential ρ)) := by
    unfold gradientNormSq
    refine continuous_finsetSum _ fun i _ => ?_
    exact ((hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const).pow 2
  refine Integrable.mono' (integrable_inv_one_add_norm_pow_four.const_mul (3 * B ^ 2))
    hc.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (gradientNormSq_nonneg _ x)]
  have h1 := hB x
  have h2 : ‖fderiv ℝ (newtonPotential ρ) x‖ ^ 2 ≤ (B * ((1 + ‖x‖) ^ 2)⁻¹) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  calc gradientNormSq (newtonPotential ρ) x ≤ 3 * ‖fderiv ℝ (newtonPotential ρ) x‖ ^ 2 :=
        gradientNormSq_le _ x
    _ ≤ 3 * (B * ((1 + ‖x‖) ^ 2)⁻¹) ^ 2 := by linarith
    _ = 3 * B ^ 2 * ((1 + ‖x‖) ^ 4)⁻¹ := by
        rw [mul_pow, inv_pow, ← pow_mul]
        ring

/-! ### The cut-off -/

/-- A bump function on space, equal to one on the unit ball, with support in the ball of radius
`2`. -/
def unitBump : ContDiffBump (0 : E3) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The cut-off `ψ_R(x) = ψ(x/R)`, equal to one on the ball of radius `R`. -/
def cutoff (R : ℝ) (x : E3) : ℝ := unitBump (R⁻¹ • x)

/-- The cut-off is smooth. -/
theorem contDiff_cutoff (R : ℝ) {n : ℕ∞} : ContDiff ℝ n (cutoff R) :=
  unitBump.contDiff.comp (contDiff_id.const_smul R⁻¹)

/-- The cut-off is `C¹`. -/
theorem contDiff_one_cutoff (R : ℝ) : ContDiff ℝ 1 (cutoff R) := by
  exact_mod_cast contDiff_cutoff R (n := 1)

/-- The cut-off is continuous. -/
theorem continuous_cutoff (R : ℝ) : Continuous (cutoff R) :=
  (contDiff_cutoff R (n := 0)).continuous

/-- The cut-off has a compact support. -/
theorem hasCompactSupport_cutoff {R : ℝ} (hR : R ≠ 0) : HasCompactSupport (cutoff R) :=
  unitBump.hasCompactSupport.comp_homeomorph (Homeomorph.smulOfNeZero R⁻¹ (inv_ne_zero hR))

/-- The cut-off is one on the ball of radius `R`. -/
theorem cutoff_eq_one {R : ℝ} (hR : 0 < R) {x : E3} (hx : ‖x‖ ≤ R) : cutoff R x = 1 := by
  refine unitBump.one_of_mem_closedBall ?_
  rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le)]
  change R⁻¹ * ‖x‖ ≤ 1
  rw [inv_mul_le_iff₀ hR, mul_one]
  exact hx

/-- The cut-off lies between `0` and `1`. -/
theorem cutoff_mem_Icc (R : ℝ) (x : E3) : cutoff R x ∈ Icc (0 : ℝ) 1 :=
  ⟨unitBump.nonneg, unitBump.le_one⟩

/-- The derivative of the cut-off vanishes on the open ball of radius `R`. -/
theorem fderiv_cutoff_eq_zero {R : ℝ} (hR : 0 < R) {x : E3} (hx : ‖x‖ < R) :
    fderiv ℝ (cutoff R) x = 0 := by
  have h : cutoff R =ᶠ[𝓝 x] fun _ => 1 := by
    have : ∀ᶠ y in 𝓝 x, ‖y‖ < R := continuous_norm.continuousAt.eventually (gt_mem_nhds hx)
    filter_upwards [this] with y hy using cutoff_eq_one hR hy.le
  rw [h.fderiv_eq]
  exact fderiv_const_apply _

/-- The derivative of the cut-off, `Dψ_R(x) = R⁻¹ Dψ(x/R)`. -/
theorem fderiv_cutoff (R : ℝ) (x : E3) :
    fderiv ℝ (cutoff R) x = R⁻¹ • fderiv ℝ unitBump (R⁻¹ • x) := by
  have h1 : HasFDerivAt (fun y : E3 => R⁻¹ • y) (R⁻¹ • ContinuousLinearMap.id ℝ E3) x :=
    (hasFDerivAt_id x).const_smul R⁻¹
  have h2 := ((unitBump.contDiff (n := 1)).differentiable (by norm_num) (R⁻¹ • x)).hasFDerivAt
  have h3 : HasFDerivAt (cutoff R) ((fderiv ℝ unitBump (R⁻¹ • x)).comp
      (R⁻¹ • ContinuousLinearMap.id ℝ E3)) x := h2.comp x h1
  rw [h3.fderiv]
  ext v
  simp

/-- A bound `‖Dψ_R(x)‖ ≤ C/(1 + |x|)` uniform in `R ≥ 1`. -/
theorem exists_norm_fderiv_cutoff_le :
    ∃ C, ∀ R, 1 ≤ R → ∀ x, ‖fderiv ℝ (cutoff R) x‖ ≤ C * (1 + ‖x‖)⁻¹ := by
  have hc : Continuous fun z : E3 => ‖fderiv ℝ unitBump z‖ * (1 + ‖z‖) :=
    ((unitBump.contDiff (n := 1)).continuous_fderiv (by norm_num)).norm.mul (by fun_prop)
  have hs : HasCompactSupport fun z : E3 => ‖fderiv ℝ unitBump z‖ * (1 + ‖z‖) :=
    (unitBump.hasCompactSupport.fderiv ℝ).norm.mul_right
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  refine ⟨C, fun R hR x => ?_⟩
  have hR0 : 0 < R := one_pos.trans_le hR
  have hx1 : 0 < 1 + ‖x‖ := by positivity
  set z : E3 := R⁻¹ • x with hz
  have hzn : ‖z‖ = R⁻¹ * ‖x‖ := by
    rw [hz, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR0.le)]
  have h1 : ‖fderiv ℝ unitBump z‖ * (1 + ‖z‖) ≤ C := by
    have := hC z
    rwa [Real.norm_of_nonneg (by positivity)] at this
  rw [fderiv_cutoff, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR0.le), le_mul_inv_iff₀ hx1]
  have h2 : 1 + ‖x‖ ≤ R * (1 + ‖z‖) := by
    rw [hzn, mul_add, mul_one, ← mul_assoc, mul_inv_cancel₀ hR0.ne', one_mul]
    linarith
  calc R⁻¹ * ‖fderiv ℝ unitBump z‖ * (1 + ‖x‖)
      ≤ R⁻¹ * ‖fderiv ℝ unitBump z‖ * (R * (1 + ‖z‖)) := by gcongr
    _ = ‖fderiv ℝ unitBump z‖ * (1 + ‖z‖) := by field_simp
    _ ≤ C := h1

/-! ### The field energy -/

/-- **The energy as the integral of the square of the field**: `∫ ρφ = ∫ |∇φ|²` for a `C²`
density of compact support. -/
theorem integral_mul_newtonPotential_eq_integral_sq {ρ : E3 → ℝ} (hρ : ContDiff ℝ 2 ρ)
    (hcρ : HasCompactSupport ρ) :
    ∫ x, ρ x * newtonPotential ρ x = ∫ x, gradientNormSq (newtonPotential ρ) x := by
  set φ := newtonPotential ρ with hφdef
  have hφ2 : ContDiff ℝ 2 φ := contDiff_two_newtonPotential hcρ hρ
  have hρ1 : ContDiff ℝ 1 ρ := hρ.of_le (by norm_num)
  obtain ⟨a, ha0, ha⟩ := exists_tsupport_subset_closedBall hcρ
  obtain ⟨A, hA⟩ := exists_abs_newtonPotential_le hρ.continuous hcρ
  obtain ⟨B, hB⟩ := exists_norm_fderiv_newtonPotential_le hρ1 hcρ
  obtain ⟨Cψ, hCψ⟩ := exists_norm_fderiv_cutoff_le
  have hDφ (v : E3) : Continuous fun x => fderiv ℝ φ x v :=
    (hφ2.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hDψ (R : ℝ) (v : E3) : Continuous fun x => fderiv ℝ (cutoff R) x v :=
    ((contDiff_one_cutoff R).continuous_fderiv (by norm_num)).clm_apply continuous_const
  set F : ℝ → E3 → ℝ := fun R x => ∑ i, (φ x * fderiv ℝ (cutoff R) x (EuclideanSpace.single i 1)
    + cutoff R x * fderiv ℝ φ x (EuclideanSpace.single i 1)) *
      fderiv ℝ φ x (EuclideanSpace.single i 1) with hFdef
  -- the identity for every large `R`
  have hid : ∀ R, max a 1 ≤ R → ∫ x, ρ x * φ x = ∫ x, F R x := by
    intro R hR
    have hR0 : 0 < R := one_pos.trans_le ((le_max_right a 1).trans hR)
    set w : E3 → ℝ := fun x => φ x * cutoff R x with hwdef
    have hw : ContDiff ℝ 1 w := (hφ2.of_le (by norm_num)).mul (contDiff_one_cutoff R)
    have hcw : HasCompactSupport w := (hasCompactSupport_cutoff hR0.ne').mul_left
    have h1 : ∫ x, ρ x * φ x = ∫ x, -(w x * coordLaplacian φ x) := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      have hΔ : coordLaplacian φ x = -ρ x := by
        rw [coordLaplacian_eq_laplacian hφ2.contDiffAt]
        exact laplacian_newtonPotential hcρ hρ x
      simp only [hwdef, hΔ]
      by_cases hx : ρ x = 0
      · simp [hx]
      · have hxR : ‖x‖ ≤ R :=
          (by simpa using ha (subset_tsupport ρ hx) : ‖x‖ ≤ a).trans
            ((le_max_left a 1).trans hR)
        rw [cutoff_eq_one hR0 hxR]
        ring
    rw [h1, integral_neg, integral_mul_coordLaplacian_eq_neg_sum hw hcw hφ2, neg_neg]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    have hd : fderiv ℝ w x = φ x • fderiv ℝ (cutoff R) x + cutoff R x • fderiv ℝ φ x :=
      fderiv_mul ((hφ2.differentiable (by norm_num)).differentiableAt)
        (((contDiff_one_cutoff R).differentiable (by norm_num)).differentiableAt)
    rw [hd]
    simp [smul_eq_mul]
  -- the limit `R → ∞`
  have hG := integrable_gradientNormSq_newtonPotential hρ1 hcρ
  set bound : E3 → ℝ := fun x =>
    3 * (A * (1 + ‖x‖)⁻¹) * (Cψ * (1 + ‖x‖)⁻¹) * (B * ((1 + ‖x‖) ^ 2)⁻¹) +
      gradientNormSq φ x with hbound
  have hbi : Integrable bound := by
    refine Integrable.add ?_ hG
    refine (integrable_inv_one_add_norm_pow_four.const_mul (3 * A * Cψ * B)).congr
      (Eventually.of_forall fun x => ?_)
    simp only
    have hx1 : 0 < 1 + ‖x‖ := by positivity
    field_simp
  have hlim : Tendsto (fun R => ∫ x, F R x) atTop (𝓝 (∫ x, gradientNormSq φ x)) := by
    refine tendsto_integral_filter_of_dominated_convergence bound
      (Eventually.of_forall fun R => ?_) ?_ hbi (Eventually.of_forall fun x => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      simp only [hFdef]
      refine continuous_finsetSum _ fun i _ => ?_
      exact ((((hφ2.continuous).mul (hDψ R _)).add
        ((continuous_cutoff R).mul (hDφ _))).mul (hDφ _))
    · filter_upwards [eventually_ge_atTop 1] with R hR
      refine Eventually.of_forall fun x => ?_
      have hx1 : 0 < 1 + ‖x‖ := by positivity
      set X := |φ x| * ‖fderiv ℝ (cutoff R) x‖ * ‖fderiv ℝ φ x‖ with hX
      have hterm (i : Fin 3) :
          |(φ x * fderiv ℝ (cutoff R) x (EuclideanSpace.single i 1) +
            cutoff R x * fderiv ℝ φ x (EuclideanSpace.single i 1)) *
              fderiv ℝ φ x (EuclideanSpace.single i 1)| ≤
            X + (fderiv ℝ φ x (EuclideanSpace.single i 1)) ^ 2 := by
        have hψ := cutoff_mem_Icc R x
        have e1 := abs_apply_single_le (fderiv ℝ (cutoff R) x) i
        have e2 := abs_apply_single_le (fderiv ℝ φ x) i
        set p := fderiv ℝ (cutoff R) x (EuclideanSpace.single i 1)
        set q := fderiv ℝ φ x (EuclideanSpace.single i 1)
        have hq : |q| * |q| = q ^ 2 := by rw [← sq, sq_abs]
        calc |(φ x * p + cutoff R x * q) * q| = |φ x * p * q + cutoff R x * q ^ 2| := by ring_nf
          _ ≤ |φ x * p * q| + |cutoff R x * q ^ 2| := abs_add_le _ _
          _ = |φ x| * |p| * |q| + cutoff R x * q ^ 2 := by
              rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hψ.1, abs_of_nonneg (sq_nonneg q)]
          _ ≤ X + 1 * q ^ 2 := by
              gcongr
              · rw [hX]
                gcongr
              · exact hψ.2
          _ = X + q ^ 2 := by ring
      have hXle : X ≤ (A * (1 + ‖x‖)⁻¹) * (Cψ * (1 + ‖x‖)⁻¹) * (B * ((1 + ‖x‖) ^ 2)⁻¹) := by
        have b1 := hA x
        have b2 := hCψ R hR x
        have b3 := hB x
        have n1 : 0 ≤ A * (1 + ‖x‖)⁻¹ := (abs_nonneg _).trans b1
        have n2 : 0 ≤ Cψ * (1 + ‖x‖)⁻¹ := (norm_nonneg _).trans b2
        rw [hX]
        gcongr
      rw [Real.norm_eq_abs]
      calc |F R x| ≤ ∑ i : Fin 3, |(φ x * fderiv ℝ (cutoff R) x (EuclideanSpace.single i 1) +
            cutoff R x * fderiv ℝ φ x (EuclideanSpace.single i 1)) *
              fderiv ℝ φ x (EuclideanSpace.single i 1)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i : Fin 3, (X + (fderiv ℝ φ x (EuclideanSpace.single i 1)) ^ 2) :=
            Finset.sum_le_sum fun i _ => hterm i
        _ = 3 * X + gradientNormSq φ x := by
            rw [Finset.sum_add_distrib, gradientNormSq]
            simp
        _ ≤ bound x := by
            rw [hbound]
            simp only
            linarith
    · have hev : ∀ᶠ R in atTop, F R x = gradientNormSq φ x := by
        filter_upwards [eventually_gt_atTop ‖x‖, eventually_gt_atTop 0] with R hR hR0
        simp only [hFdef, gradientNormSq, fderiv_cutoff_eq_zero hR0 hR,
          cutoff_eq_one hR0 hR.le]
        simp [sq]
      exact tendsto_const_nhds.congr' (hev.mono fun R hR => hR.symm)
  have hconst : Tendsto (fun R => ∫ x, F R x) atTop (𝓝 (∫ x, ρ x * φ x)) :=
    tendsto_const_nhds.congr' ((eventually_ge_atTop (max a 1)).mono fun R hR => hid R hR)
  exact tendsto_nhds_unique hconst hlim

/-- The square of the field `E = −∇φ` is the square of the gradient of the potential. -/
theorem sum_sq_coulombField (ρ : E3 → ℝ) (x : E3) :
    ∑ i, coulombField ρ x i ^ 2 = gradientNormSq (newtonPotential ρ) x := by
  simp [coulombField, gradientNormSq]

/-- **The electrostatic energy of charges**: for a `C²` density of compact support,
`½ ∫ ρφ = ½ ∬ ρ(x)ρ(y)/(4π|x − y|) = ∫ ½|E|²`, and all three integrands are integrable. -/
theorem electrostaticEnergy_eq {ρ : E3 → ℝ} (hρ : ContDiff ℝ 2 ρ) (hcρ : HasCompactSupport ρ) :
    (Integrable (fun x => ρ x * newtonPotential ρ x) ∧
      Integrable (fun p : E3 × E3 => ρ p.1 * ρ p.2 * newtonKernel (p.1 - p.2))
        (volume.prod volume) ∧
      Integrable fun x => (∑ i, coulombField ρ x i ^ 2) / 2) ∧
    (1 / 2 * ∫ x, ρ x * newtonPotential ρ x =
      1 / 2 * ∫ p, ρ p.1 * ρ p.2 * newtonKernel (p.1 - p.2) ∂(volume.prod volume)) ∧
    1 / 2 * ∫ x, ρ x * newtonPotential ρ x = ∫ x, (∑ i, coulombField ρ x i ^ 2) / 2 := by
  have hφc : Continuous (newtonPotential ρ) := (contDiff_two_newtonPotential hcρ hρ).continuous
  have hsq : (fun x => (∑ i, coulombField ρ x i ^ 2) / 2) =
      fun x => gradientNormSq (newtonPotential ρ) x / 2 := by
    funext x
    rw [sum_sq_coulombField]
  refine ⟨⟨(hρ.continuous.mul hφc).integrable_of_hasCompactSupport hcρ.mul_right,
    integrable_double hρ.continuous hcρ, ?_⟩, ?_, ?_⟩
  · rw [hsq]
    exact (integrable_gradientNormSq_newtonPotential (hρ.of_le (by norm_num)) hcρ).div_const 2
  · rw [integral_mul_newtonPotential_eq_double hρ.continuous hcρ]
  · rw [hsq, integral_div, integral_mul_newtonPotential_eq_integral_sq hρ hcρ]
    ring

/-! ### An instance -/

/-- A smooth charge density of compact support: the bump `unitBump`, equal to one on the unit
ball and zero outside the ball of radius `2`. -/
def bumpCharge (x : E3) : ℝ := unitBump x

/-- The bump charge is `C²`. -/
theorem contDiff_bumpCharge : ContDiff ℝ 2 bumpCharge := by
  exact_mod_cast (unitBump.contDiff (n := 2))

/-- The bump charge has a compact support. -/
theorem hasCompactSupport_bumpCharge : HasCompactSupport bumpCharge :=
  unitBump.hasCompactSupport

/-- The bump charge is not zero: its density at the origin is one. -/
theorem bumpCharge_zero : bumpCharge 0 = 1 :=
  unitBump.one_of_mem_closedBall (mem_closedBall_self zero_le_one)

/-- The equations of Maxwell and the energy identities hold for the bump charge. -/
theorem bumpCharge_instance :
    (∀ y, divergence3 (electricField (fieldTensor (electrostaticPotential bumpCharge))) y =
      bumpCharge (SmoothGeometry.Minkowski.space y)) ∧
    1 / 2 * ∫ x, bumpCharge x * newtonPotential bumpCharge x =
      ∫ x, (∑ i, coulombField bumpCharge x i ^ 2) / 2 :=
  ⟨fun y => (maxwell_electrostaticPotential hasCompactSupport_bumpCharge contDiff_bumpCharge
    y).2.1, (electrostaticEnergy_eq contDiff_bumpCharge hasCompactSupport_bumpCharge).2.2⟩

/-! ### The self-energy of a point charge -/

/-- The square of the Coulomb field is `q²/(16π²|x|⁴)` away from the charge. -/
theorem norm_sq_pointChargeField (q : ℝ) {x : E3} (hx : x ≠ 0) :
    ‖pointChargeField q x‖ ^ 2 = q ^ 2 / (16 * π ^ 2 * ‖x‖ ^ 4) := by
  have hx' : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [pointChargeField, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp
  ring

/-- **The field energy outside a ball**: `∫_{|x| > ε} ½|E_q|² = q²/(8πε)`. -/
theorem integral_pointCharge_energy_outside (q : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∫ x in {x : E3 | ε < ‖x‖}, ‖pointChargeField q x‖ ^ 2 / 2 = q ^ 2 / (8 * π * ε) := by
  rw [← integral_indicator (measurableSet_lt measurable_const measurable_norm)]
  set c : ℝ := q ^ 2 / (32 * π ^ 2) with hc
  set f : ℝ → ℝ := (Ioi ε).indicator fun r => c * (r ^ 4)⁻¹ with hf
  have hfun : ({x : E3 | ε < ‖x‖}).indicator (fun x => ‖pointChargeField q x‖ ^ 2 / 2) =
      fun x => f ‖x‖ := by
    funext x
    by_cases hx : ε < ‖x‖
    · have hx0 : x ≠ 0 := norm_pos_iff.mp (hε.trans hx)
      have hxpos : 0 < ‖x‖ := hε.trans hx
      rw [indicator_of_mem (show x ∈ {x : E3 | ε < ‖x‖} from hx), hf,
        indicator_of_mem (show ‖x‖ ∈ Ioi ε from hx), norm_sq_pointChargeField q hx0, hc]
      field_simp
      ring
    · rw [indicator_of_notMem (show x ∉ {x : E3 | ε < ‖x‖} from hx), hf,
        indicator_of_notMem (show ‖x‖ ∉ Ioi ε from hx)]
  have hvol : (volume : Measure E3).real (ball 0 1) = π * 4 / 3 := by
    simp [Measure.real, ENNReal.toReal_ofReal (by positivity : 0 ≤ π * 4 / 3)]
  have hrad : ∫ y in Ioi (0 : ℝ), y ^ (3 - 1) • f y = c * ε⁻¹ := by
    have heq : EqOn (fun y : ℝ => y ^ (3 - 1) • f y)
        ((Ioi ε).indicator fun r => c * r ^ (-2 : ℝ)) (Ioi 0) := by
      intro y hy
      have hy0 : 0 < y := hy
      by_cases hyε : ε < y
      · simp only [hf, smul_eq_mul, indicator_of_mem (show y ∈ Ioi ε from hyε)]
        rw [Real.rpow_neg hy0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        field_simp
        ring
      · simp only [hf, smul_eq_mul, indicator_of_notMem (show y ∉ Ioi ε from hyε), mul_zero]
    rw [setIntegral_congr_fun measurableSet_Ioi heq, setIntegral_indicator measurableSet_Ioi,
      Ioi_inter_Ioi, sup_of_le_right hε.le, integral_const_mul,
      integral_Ioi_rpow_of_lt (by norm_num) hε, show (-2 : ℝ) + 1 = -1 by norm_num,
      Real.rpow_neg_one]
    ring
  rw [hfun, integral_fun_norm_addHaar volume f, finrank_euclideanSpace_fin, hrad, hvol, hc]
  simp only [nsmul_eq_mul, smul_eq_mul]
  field_simp
  ring

/-- The field energy outside the ball of radius `ε` tends to `∞` as `ε → 0⁺` for a charge
`q ≠ 0`. -/
theorem tendsto_pointCharge_energy {q : ℝ} (hq : q ≠ 0) :
    Tendsto (fun ε => ∫ x in {x : E3 | ε < ‖x‖}, ‖pointChargeField q x‖ ^ 2 / 2) (𝓝[>] 0)
      atTop := by
  have h : Tendsto (fun ε : ℝ => q ^ 2 / (8 * π) * ε⁻¹) (𝓝[>] 0) atTop :=
    tendsto_inv_nhdsGT_zero.const_mul_atTop (by positivity)
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [integral_pointCharge_energy_outside q hε]
  field_simp

/-- **The self-energy of a point charge is infinite**: for `q ≠ 0` the energy density `½|E_q|²` of
the Coulomb field is not integrable on space. -/
theorem not_integrable_pointCharge_energy {q : ℝ} (hq : q ≠ 0) :
    ¬ Integrable fun x : E3 => ‖pointChargeField q x‖ ^ 2 / 2 := by
  intro hint
  set T := ∫ x : E3, ‖pointChargeField q x‖ ^ 2 / 2
  have hev := (tendsto_pointCharge_energy hq).eventually (eventually_gt_atTop T)
  obtain ⟨ε, hε⟩ := hev.exists
  have hle := setIntegral_le_integral (s := {x : E3 | ε < ‖x‖}) hint
    (Eventually.of_forall fun x => by positivity)
  exact (lt_irrefl _ (hε.trans_le hle))

end ProjectAinos.Electrodynamics.Electrostatics
