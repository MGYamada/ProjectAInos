/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Potential.NewtonKernel
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic

/-!
# The Fourier transform of the Newton kernel

Space is `EuclideanSpace ℝ (Fin 3)` with the Euclidean norm and Mathlib's normalization of the
Fourier transform, `𝓕 f ξ = ∫ e^{−2πi⟨x, ξ⟩} f x dx`. The Newton kernel `K x = 1/(4π‖x‖)` is not
integrable, and its transform is the locally integrable function `newtonSymbol ξ = 1/(4π²‖ξ‖²)`,
which has no temperate growth at the origin. The identity is therefore stated in pairing form.

* `integral_newtonKernel_mul_fourier`: **the Fourier transform of the Newton kernel**,
  `∫ K(z) 𝓕χ(z) dz = ∫ χ(ξ)/(4π²‖ξ‖²) dξ` for every Schwartz function `χ`.

The proof is Gaussian subordination. For `z ≠ 0`,
`1/‖z‖ = π^{-1/2} ∫₀^∞ t^{-1/2} e^{−t‖z‖²} dt` (`kernelFourier_integral_rpow_exp`); the transform
of the Gaussian `e^{−t‖z‖²}` is `(π/t)^{3/2} e^{−π²‖ξ‖²/t}` (`fourier_gaussian_innerProductSpace`),
so Fubini's theorem twice and `∫₀^∞ t^{-2} e^{−a/t} dt = 1/a`
(`kernelFourier_integral_rpow_exp_inv`) give the symbol. The double integrals converge because
`‖z‖⁻¹` and `‖ξ‖⁻²` are locally integrable in three dimensions and bounded away from the origin
(`kernelFourier_integrable_rpow_mul`).

* `kernelFourier_integral_mul_fourier`: the multiplication formula `∫ f 𝓕g = ∫ 𝓕f g` for
  integrable `f` and `g`, and `kernelFourier_integral_comp_sub_mul_fourier`: its translate,
  `∫ f(x − y) 𝓕χ(x) dx = 𝓕(𝓕f · χ)(y)`.
* `integral_fourier_eq_apply_zero`: `∫ 𝓕χ = χ(0)`, the transform of a constant is a multiple of
  the Dirac mass at the origin.
* `exists_schwartzMap_apply_zero_eq_one`: a Schwartz function with `χ(0) = 1`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric Real
open scoped Topology FourierTransform SchwartzMap Complex ContDiff

namespace ProjectAinos.SmoothGeometry.Potential

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### The symbol -/

/-- The Fourier symbol `1/(4π²‖ξ‖²)` of the Newton kernel. Its value at the origin is `0`, because
`(0 : ℝ)⁻¹ = 0`. -/
def newtonSymbol (ξ : E3) : ℝ := (4 * π ^ 2 * ‖ξ‖ ^ 2)⁻¹

/-- The symbol is nonnegative. -/
theorem newtonSymbol_nonneg (ξ : E3) : 0 ≤ newtonSymbol ξ := by
  unfold newtonSymbol
  positivity

/-- The Newton kernel as a power of the norm, `K x = (4π)⁻¹ ‖x‖^{-1}`, also at the origin. -/
theorem kernelFourier_newtonKernel_eq_rpow (x : E3) :
    newtonKernel x = (4 * π)⁻¹ * ‖x‖ ^ (-1 : ℝ) := by
  rw [newtonKernel, Real.rpow_neg_one, mul_inv]

/-- The symbol as a power of the norm, `(4π²)⁻¹ ‖ξ‖^{-2}`, also at the origin. -/
theorem kernelFourier_newtonSymbol_eq_rpow (ξ : E3) :
    newtonSymbol ξ = (4 * π ^ 2)⁻¹ * ‖ξ‖ ^ (-2 : ℝ) := by
  rw [newtonSymbol, Real.rpow_neg (norm_nonneg _), mul_inv]
  norm_cast

/-! ### Integrability -/

/-- For `0 ≤ α < 3`, the product of `‖x‖^{-α}` with the norm of an integrable continuous function
is integrable: near the origin the power is integrable and the function is bounded, and away from
it the power is at most `1`. -/
theorem kernelFourier_integrable_rpow_mul {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 3) {f : E3 → ℂ}
    (hf : Integrable f) (hfc : Continuous f) :
    Integrable fun x : E3 => ‖x‖ ^ (-α) * ‖f x‖ := by
  have hmeas : AEStronglyMeasurable (fun x : E3 => ‖x‖ ^ (-α) * ‖f x‖) :=
    ((measurable_norm.pow_const _).mul hfc.measurable.norm).aestronglyMeasurable
  have hloc : LocallyIntegrable fun x : E3 => ‖x‖ ^ (-α) := by
    refine locallyIntegrable_of_norm_le_rpow (by simp) (C := 1) (α := α) (by simpa using hα)
      (Eventually.of_forall fun x => ?_) (measurable_norm.pow_const _).aestronglyMeasurable
    rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  have h1 : IntegrableOn (fun x : E3 => ‖x‖ ^ (-α) * ‖f x‖) (closedBall 0 1) :=
    (hloc.integrableOn_isCompact (isCompact_closedBall 0 1)).mul_continuousOn
      hfc.norm.continuousOn (isCompact_closedBall 0 1)
  have h2 : IntegrableOn (fun x : E3 => ‖x‖ ^ (-α) * ‖f x‖) (closedBall 0 1)ᶜ := by
    refine Integrable.mono' hf.norm.integrableOn hmeas.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_closedBall.compl] with x hx
    have hx1 : 1 ≤ ‖x‖ := by
      simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] at hx
      exact hx.le
    rw [Real.norm_of_nonneg (by positivity)]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith))
  simpa using h1.union h2

/-- The kernel times an integrable continuous function is integrable. -/
theorem kernelFourier_integrable_newtonKernel_mul {f : E3 → ℂ} (hf : Integrable f)
    (hfc : Continuous f) : Integrable fun x => (newtonKernel x : ℂ) * f x := by
  refine Integrable.mono' ((kernelFourier_integrable_rpow_mul zero_le_one (by norm_num) hf
    hfc).const_mul (4 * π)⁻¹) ?_ (Eventually.of_forall fun x => ?_)
  · exact ((Complex.measurable_ofReal.comp ((measurable_norm.const_mul _).inv)).mul
      hfc.measurable).aestronglyMeasurable
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (newtonKernel_nonneg x),
      kernelFourier_newtonKernel_eq_rpow, mul_assoc]

/-- The symbol times an integrable continuous function is integrable. -/
theorem kernelFourier_integrable_newtonSymbol_mul {f : E3 → ℂ} (hf : Integrable f)
    (hfc : Continuous f) : Integrable fun x => (newtonSymbol x : ℂ) * f x := by
  refine Integrable.mono' ((kernelFourier_integrable_rpow_mul zero_le_two (by norm_num) hf
    hfc).const_mul (4 * π ^ 2)⁻¹) ?_ (Eventually.of_forall fun x => ?_)
  · exact ((Complex.measurable_ofReal.comp
      (((measurable_norm.pow_const 2).const_mul _).inv)).mul hfc.measurable).aestronglyMeasurable
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (newtonSymbol_nonneg x),
      kernelFourier_newtonSymbol_eq_rpow, mul_assoc]

/-! ### One-dimensional integrals -/

/-- The subordination integral `∫₀^∞ t^{-1/2} e^{−rt} dt = √π/√r` for `r > 0`. -/
theorem kernelFourier_integral_rpow_exp {r : ℝ} (hr : 0 < r) :
    ∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2) : ℝ) * rexp (-(r * t)) = √π * (√r)⁻¹ := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1 / 2) (by norm_num) hr
  rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num, Real.Gamma_one_half_eq] at h
  rw [h, ← Real.sqrt_eq_rpow, one_div, Real.sqrt_inv, mul_comm]

/-- The integrand of the subordination integral is integrable on `(0, ∞)`. -/
theorem kernelFourier_integrableOn_rpow_exp {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t ^ (-(1 / 2) : ℝ) * rexp (-(r * t))) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (s := -(1 / 2)) (p := 1) (by norm_num)
    one_pos hr
  simpa [Real.rpow_one, neg_mul] using this

/-- The integral `∫₀^∞ t^{-2} e^{−a/t} dt = 1/a` for `a > 0`, by the substitution `t = 1/y`. -/
theorem kernelFourier_integral_rpow_exp_inv {a : ℝ} (ha : 0 < a) :
    ∫ t in Ioi (0 : ℝ), t ^ (-2 : ℝ) * rexp (-(a * t⁻¹)) = a⁻¹ := by
  have h := integral_comp_rpow_Ioi (fun y : ℝ => rexp (-(a * y))) (p := -1) (by norm_num)
  have h2 := integral_exp_mul_Ioi (a := -a) (by linarith) 0
  simp only [mul_zero, Real.exp_zero, neg_mul] at h2
  rw [h2, neg_div_neg_eq, one_div] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp only [smul_eq_mul]
  rw [Real.rpow_neg_one]
  norm_num

/-- The integrand `t^{-2} e^{−a/t}` is integrable on `(0, ∞)` for `a > 0`. -/
theorem kernelFourier_integrableOn_rpow_exp_inv {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t ^ (-2 : ℝ) * rexp (-(a * t⁻¹))) (Ioi 0) := by
  have h := (integrableOn_Ioi_comp_rpow_iff' (fun y : ℝ => rexp (-(a * y))) (p := -1)
    (by norm_num)).mpr (by simpa [neg_mul] using exp_neg_integrableOn_Ioi 0 ha)
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp only [smul_eq_mul]
  rw [Real.rpow_neg_one]
  norm_num

/-! ### The multiplication formula and the Gaussian -/

/-- The multiplication formula `∫ f 𝓕g = ∫ 𝓕f g` for integrable `f` and `g`. -/
theorem kernelFourier_integral_mul_fourier {f g : E3 → ℂ} (hf : Integrable f)
    (hg : Integrable g) : ∫ x, f x * 𝓕 g x = ∫ ξ, 𝓕 f ξ * g ξ := by
  have := VectorFourier.integral_bilin_fourierIntegral_eq_flip (ContinuousLinearMap.mul ℂ ℂ)
    (L := innerₗ E3) continuous_fourierChar continuous_inner hf hg
  simp only [ContinuousLinearMap.mul_apply', flip_innerₗ] at this
  exact this.symm

/-- The translated multiplication formula `∫ f(x − y) 𝓕χ(x) dx = 𝓕(𝓕f · χ)(y)`. -/
theorem kernelFourier_integral_comp_sub_mul_fourier {f : E3 → ℂ} (hf : Integrable f)
    (χ : 𝓢(E3, ℂ)) (y : E3) :
    ∫ x, f (x - y) * 𝓕 χ x = 𝓕 (fun ξ => 𝓕 f ξ * χ ξ) y := by
  have h := kernelFourier_integral_mul_fourier (hf.comp_sub_right y) χ.integrable
  have htr := VectorFourier.fourierIntegral_comp_add_right 𝐞 volume (innerₗ E3) f (-y)
  have htr' : 𝓕 (fun x => f (x - y)) = fun ξ => 𝐞 (-inner ℝ y ξ) • 𝓕 f ξ := by
    simp only [Function.comp_def, ← sub_eq_add_neg, innerₗ_apply_apply, inner_neg_left] at htr
    exact htr
  rw [show (fun x => f (x - y) * 𝓕 χ x) = fun x => f (x - y) * 𝓕 (χ : E3 → ℂ) x from rfl, h,
    htr', Real.fourier_eq]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [real_inner_comm ξ y, smul_mul_assoc]

/-- The transform of a Gaussian against a transform: for `t > 0`,
`∫ e^{−t‖z‖²} 𝓕χ(z) dz = ∫ (π/t)^{3/2} e^{−π²‖ξ‖²/t} χ(ξ) dξ`. -/
theorem kernelFourier_integral_gaussian_smul_fourier {t : ℝ} (ht : 0 < t) (χ : 𝓢(E3, ℂ)) :
    ∫ z, rexp (-(‖z‖ ^ 2 * t)) • 𝓕 χ z =
      ∫ ξ, ((π / t) ^ (3 / 2 : ℝ) * rexp (-(π ^ 2 * ‖ξ‖ ^ 2 * t⁻¹))) • χ ξ := by
  have hb : 0 < ((t : ℂ)).re := by simpa using ht
  have hg := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add hb 0 (0 : E3)
  simp only [zero_mul, add_zero] at hg
  have h := kernelFourier_integral_mul_fourier hg χ.integrable
  calc ∫ z, rexp (-(‖z‖ ^ 2 * t)) • 𝓕 χ z
      = ∫ z, cexp (-(t : ℂ) * ‖z‖ ^ 2) * 𝓕 (χ : E3 → ℂ) z := by
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        simp only [Complex.real_smul, Complex.ofReal_exp]
        push_cast
        ring_nf
        rfl
    _ = ∫ ξ, 𝓕 (fun v : E3 => cexp (-(t : ℂ) * ‖v‖ ^ 2)) ξ * χ ξ := h
    _ = _ := by
        refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
        simp only
        rw [fourier_gaussian_innerProductSpace hb, finrank_euclideanSpace_fin, Complex.real_smul,
          Complex.ofReal_mul, Complex.ofReal_cpow (by positivity), Complex.ofReal_exp]
        push_cast
        ring_nf

/-! ### The transform of the kernel -/

/-- **The Fourier transform of the Newton kernel** in pairing form: for every Schwartz function
`χ`, `∫ K(z) 𝓕χ(z) dz = ∫ χ(ξ)/(4π²‖ξ‖²) dξ`. In the sense of tempered distributions this is
`𝓕K = 1/(4π²‖ξ‖²)`, a locally integrable function with no part at `ξ = 0`. -/
theorem integral_newtonKernel_mul_fourier (χ : 𝓢(E3, ℂ)) :
    ∫ z, (newtonKernel z : ℂ) * 𝓕 χ z = ∫ ξ, (newtonSymbol ξ : ℂ) * χ ξ := by
  set F : E3 → ℂ := ⇑(𝓕 χ : 𝓢(E3, ℂ)) with hF
  have hFi : Integrable F := (𝓕 χ).integrable
  have hFc : Continuous F := (𝓕 χ).continuous
  set c : ℝ := (4 * π)⁻¹ * (√π)⁻¹ with hc
  have hc0 : 0 ≤ c := by positivity
  set f : E3 → ℝ → ℂ := fun z t => (c * (t ^ (-(1 / 2) : ℝ) * rexp (-(‖z‖ ^ 2 * t)))) • F z
    with hf
  set g : E3 → ℝ → ℂ := fun ξ t =>
    (c * π ^ (3 / 2 : ℝ) * (t ^ (-2 : ℝ) * rexp (-(π ^ 2 * ‖ξ‖ ^ 2 * t⁻¹)))) • χ ξ with hg
  have hne : ∀ᵐ z : E3, z ≠ 0 := compl_mem_ae_iff.mpr (measure_singleton 0)
  -- the subordination of the kernel and of the symbol
  have hK : ∀ z : E3, z ≠ 0 →
      ∫ t in Ioi 0, c * (t ^ (-(1 / 2) : ℝ) * rexp (-(‖z‖ ^ 2 * t))) = newtonKernel z := by
    intro z hz
    have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
    rw [integral_const_mul, kernelFourier_integral_rpow_exp (by positivity),
      Real.sqrt_sq hr.le, hc, newtonKernel]
    have : 0 < √π := Real.sqrt_pos.mpr pi_pos
    field_simp
  have hS : ∀ ξ : E3, ξ ≠ 0 →
      ∫ t in Ioi 0, c * π ^ (3 / 2 : ℝ) * (t ^ (-2 : ℝ) * rexp (-(π ^ 2 * ‖ξ‖ ^ 2 * t⁻¹))) =
        newtonSymbol ξ := by
    intro ξ hξ
    have hr : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    rw [integral_const_mul, kernelFourier_integral_rpow_exp_inv (by positivity), hc,
      newtonSymbol, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add pi_pos,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
    have : 0 < √π := Real.sqrt_pos.mpr pi_pos
    field_simp
  -- the two double integrals converge absolutely
  have hint1 : Integrable (Function.uncurry f) (volume.prod (volume.restrict (Ioi 0))) := by
    have hm : AEStronglyMeasurable (Function.uncurry f)
        (volume.prod (volume.restrict (Ioi 0))) := by
      apply Measurable.aestronglyMeasurable
      have := hFc.measurable
      rw [hf]
      fun_prop
    rw [integrable_prod_iff hm]
    refine ⟨?_, ?_⟩
    · filter_upwards [hne] with z hz
      have hr : 0 < ‖z‖ ^ 2 := pow_pos (norm_pos_iff.mpr hz) 2
      have := ((kernelFourier_integrableOn_rpow_exp hr).const_mul c).smul_const (F z)
      simpa only [Function.uncurry_apply_pair, hf] using this
    · refine (kernelFourier_integrable_newtonKernel_mul hFi hFc).norm.congr ?_
      filter_upwards [hne] with z hz
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (newtonKernel_nonneg z), ← hK z hz,
        ← integral_mul_const]
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      simp only [Function.uncurry_apply_pair, hf, norm_smul]
      rw [Real.norm_of_nonneg (by have := ht.out.le; positivity)]
  have hint2 : Integrable (Function.uncurry g) (volume.prod (volume.restrict (Ioi 0))) := by
    have hm : AEStronglyMeasurable (Function.uncurry g)
        (volume.prod (volume.restrict (Ioi 0))) := by
      apply Measurable.aestronglyMeasurable
      have := χ.continuous.measurable
      rw [hg]
      fun_prop
    rw [integrable_prod_iff hm]
    refine ⟨?_, ?_⟩
    · filter_upwards [hne] with ξ hξ
      have hr : 0 < π ^ 2 * ‖ξ‖ ^ 2 := by have := norm_pos_iff.mpr hξ; positivity
      have := ((kernelFourier_integrableOn_rpow_exp_inv hr).const_mul
        (c * π ^ (3 / 2 : ℝ))).smul_const (χ ξ)
      simpa only [Function.uncurry_apply_pair, hg] using this
    · refine (kernelFourier_integrable_newtonSymbol_mul χ.integrable χ.continuous).norm.congr ?_
      filter_upwards [hne] with ξ hξ
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (newtonSymbol_nonneg ξ), ← hS ξ hξ,
        ← integral_mul_const]
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      simp only [Function.uncurry_apply_pair, hg, norm_smul]
      rw [Real.norm_of_nonneg (by have := ht.out.le; positivity)]
  -- for each `t`, the transform of the Gaussian
  have h2 : ∀ t ∈ Ioi (0 : ℝ), ∫ z, f z t = ∫ ξ, g ξ t := by
    intro t ht
    have ht' : 0 < t := ht
    have hpow : t ^ (-(1 / 2) : ℝ) * (π / t) ^ (3 / 2 : ℝ) = π ^ (3 / 2 : ℝ) * t ^ (-2 : ℝ) := by
      rw [Real.div_rpow pi_pos.le ht'.le, show (-2 : ℝ) = -(1 / 2) - 3 / 2 by norm_num,
        Real.rpow_sub ht']
      ring
    calc ∫ z, f z t = ∫ z, (c * t ^ (-(1 / 2) : ℝ)) • (rexp (-(‖z‖ ^ 2 * t)) • F z) := by
          refine integral_congr_ae (Eventually.of_forall fun z => ?_)
          simp only [hf, smul_smul]
          ring_nf
      _ = (c * t ^ (-(1 / 2) : ℝ)) • ∫ z, rexp (-(‖z‖ ^ 2 * t)) • F z := integral_smul _ _
      _ = (c * t ^ (-(1 / 2) : ℝ)) •
            ∫ ξ, ((π / t) ^ (3 / 2 : ℝ) * rexp (-(π ^ 2 * ‖ξ‖ ^ 2 * t⁻¹))) • χ ξ := by
          rw [hF, kernelFourier_integral_gaussian_smul_fourier ht' χ]
      _ = ∫ ξ, g ξ t := by
          rw [← integral_smul]
          refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
          simp only [hg, smul_smul]
          congr 1
          rw [← mul_assoc, mul_assoc c, hpow]
          ring
  calc ∫ z, (newtonKernel z : ℂ) * 𝓕 χ z = ∫ z, ∫ t in Ioi 0, f z t := by
        refine integral_congr_ae ?_
        filter_upwards [hne] with z hz
        rw [hf]
        simp only
        rw [integral_smul_const, hK z hz, Complex.real_smul]
    _ = ∫ t in Ioi 0, ∫ z, f z t := integral_integral_swap hint1
    _ = ∫ t in Ioi 0, ∫ ξ, g ξ t := setIntegral_congr_fun measurableSet_Ioi h2
    _ = ∫ ξ, ∫ t in Ioi 0, g ξ t := (integral_integral_swap hint2).symm
    _ = ∫ ξ, (newtonSymbol ξ : ℂ) * χ ξ := by
        refine integral_congr_ae ?_
        filter_upwards [hne] with ξ hξ
        rw [hg]
        simp only
        rw [integral_smul_const, hS ξ hξ, Complex.real_smul]

/-! ### Constants and the origin -/

/-- **The transform of a constant** is a Dirac mass at the origin: `∫ 𝓕χ = χ(0)` for every
Schwartz function `χ`, by Fourier inversion at `0`. -/
theorem integral_fourier_eq_apply_zero (χ : 𝓢(E3, ℂ)) : ∫ x, 𝓕 χ x = χ 0 := by
  have h0 : 𝓕⁻ (𝓕 χ) = χ := FourierTransform.fourierInv_fourier_eq χ
  have h := congrArg (fun ψ : 𝓢(E3, ℂ) => ψ 0) h0
  rw [← h, SchwartzMap.fourierInv_coe, Real.fourierInv_eq]
  simp

/-- A smooth bump function, `1` on the unit ball and `0` outside the ball of radius `2`. -/
def kernelFourier_bump : ContDiffBump (0 : E3) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The bump function, as a complex function, is smooth. -/
theorem kernelFourier_contDiff_bump :
    ContDiff ℝ ∞ fun x : E3 => (kernelFourier_bump x : ℂ) :=
  Complex.ofRealCLM.contDiff.comp kernelFourier_bump.contDiff

/-- The bump function, as a complex function, has compact support. -/
theorem kernelFourier_hasCompactSupport_bump :
    HasCompactSupport fun x : E3 => (kernelFourier_bump x : ℂ) :=
  kernelFourier_bump.hasCompactSupport.comp_left Complex.ofReal_zero

/-- A Schwartz function with `χ(0) = 1`: the transform of a constant `c` is `c δ₀`, and this test
function sees it. -/
theorem exists_schwartzMap_apply_zero_eq_one : ∃ χ : 𝓢(E3, ℂ), χ 0 = 1 := by
  refine ⟨kernelFourier_hasCompactSupport_bump.toSchwartzMap kernelFourier_contDiff_bump, ?_⟩
  simp only [HasCompactSupport.toSchwartzMap_toFun]
  rw [kernelFourier_bump.one_of_mem_closedBall (mem_closedBall_self kernelFourier_bump.rIn_pos.le)]
  simp

end ProjectAinos.SmoothGeometry.Potential
