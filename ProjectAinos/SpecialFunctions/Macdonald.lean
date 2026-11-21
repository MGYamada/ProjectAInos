/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-! # Macdonald's function on the right half-plane

The bilateral Schläfli integral converges for every complex order. Its order shifts express
both differentiation in the argument and integration by parts in the real rapidity variable.
-/

@[expose] public section
noncomputable section

open Complex Filter MeasureTheory
open scoped Topology ComplexConjugate

namespace ProjectAinos.SpecialFunctions.Bessel

private def kernel (a z : ℂ) (t : ℝ) : ℂ := exp (-z * Real.cosh t + a * t)

/-- The Macdonald function of complex order, given by its bilateral Schläfli integral. -/
def macdonald (a z : ℂ) : ℂ := (∫ t : ℝ, exp (-z * Real.cosh t + a * t)) / 2

private def bound (a : ℂ) (p t : ℝ) : ℝ :=
  Real.exp (a.re ^ 2 / p) * Real.exp (-(p / 4) * t ^ 2)

private theorem integrable_bound (a : ℂ) {p : ℝ} (hp : 0 < p) : Integrable (bound a p) :=
  (integrable_exp_neg_mul_sq (by positivity : 0 < p / 4)).const_mul _

private theorem sq_le_cosh (t : ℝ) : t ^ 2 / 2 ≤ Real.cosh t := by
  have hs := (Real.hasSum_cosh t)
  have h := hs.summable.le_tsum 1 (fun n _ => by rw [pow_mul]; positivity)
  rw [hs.tsum_eq] at h
  norm_num at h ⊢
  exact h

private theorem norm_kernel (a z : ℂ) {p : ℝ} (hp : 0 < p) (hz : p ≤ z.re) (t : ℝ) :
    ‖kernel a z t‖ ≤ bound a p t := by
  rw [kernel, norm_exp, bound, ← Real.exp_add, Real.exp_le_exp]
  simp only [add_re, re_mul_ofReal, neg_re]
  have hc := mul_le_mul_of_nonneg_left (sq_le_cosh t) hp.le
  have hz' := mul_le_mul_of_nonneg_right hz (Real.cosh_pos t).le
  have h : a.re * t ≤ a.re ^ 2 / p + p * t ^ 2 / 4 := by
    apply (mul_le_mul_iff_of_pos_right hp).mp
    field_simp
    nlinarith [sq_nonneg (2 * a.re - p * t)]
  nlinarith

private theorem integrable_kernel (a z : ℂ) (hz : 0 < z.re) : Integrable (kernel a z) :=
  (integrable_bound a hz).mono' (by unfold kernel; fun_prop)
    (ae_of_all _ (norm_kernel a z hz le_rfl))

/-- Absolute convergence of the Schläfli integral throughout the right half-plane. -/
theorem integrable_macdonald (a z : ℂ) (hz : 0 < z.re) :
    Integrable (fun t : ℝ => exp (-z * Real.cosh t + a * t)) := integrable_kernel a z hz

private theorem shift_plus (a z : ℂ) (t : ℝ) :
    kernel (a + 1) z t = exp (t : ℂ) * kernel a z t := by
  unfold kernel
  rw [← exp_add]
  congr 1
  ring

private theorem shift_minus (a z : ℂ) (t : ℝ) :
    kernel (a - 1) z t = exp (-(t : ℂ)) * kernel a z t := by
  unfold kernel
  rw [← exp_add]
  congr 1
  ring

private def argumentDeriv (a z : ℂ) (t : ℝ) : ℂ :=
  -(kernel (a + 1) z t + kernel (a - 1) z t) / 2

private theorem deriv_argument (a z : ℂ) (t : ℝ) :
    HasDerivAt (fun w => kernel a w t) (argumentDeriv a z t) z := by
  have h := (((hasDerivAt_id z).neg.mul_const (Real.cosh t : ℂ)).add_const
    (a * (t : ℂ))).cexp
  convert h using 1
  · rfl
  unfold argumentDeriv
  change _ = kernel a z t * (-1 * (Real.cosh t : ℂ))
  rw [shift_plus, shift_minus, ← add_mul, Complex.ofReal_cosh, Complex.cosh]
  ring

/-- Differentiating the Macdonald function raises and lowers the order. -/
theorem hasDerivAt_macdonald (a z : ℂ) (hz : 0 < z.re) :
    HasDerivAt (macdonald a) (-(macdonald (a + 1) z + macdonald (a - 1) z) / 2) z := by
  let p := z.re / 2
  have hp : 0 < p := half_pos hz
  let s := {w : ℂ | p < w.re}
  have hs : s ∈ 𝓝 z := (isOpen_lt continuous_const continuous_re).mem_nhds (half_lt_self hz)
  let b := fun t => (bound (a + 1) p t + bound (a - 1) p t) / 2
  have hi : Integrable b := ((integrable_bound (a + 1) hp).add
    (integrable_bound (a - 1) hp)).div_const 2
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := kernel a)
    (F' := argumentDeriv a) hs (Eventually.of_forall fun w => by unfold kernel; fun_prop)
    (integrable_kernel a z hz) (by unfold argumentDeriv kernel; fun_prop)
    (bound := b) (ae_of_all _ fun t w hw => by
      change p < w.re at hw
      simp only [argumentDeriv, norm_div, norm_neg, norm_ofNat, b]
      gcongr
      exact (norm_add_le _ _).trans (add_le_add (norm_kernel _ _ hp hw.le _)
        (norm_kernel _ _ hp hw.le _))) hi
    (ae_of_all _ fun t w _ => deriv_argument a w t)
  convert hd.2.div_const 2 using 1
  · rfl
  change -((∫ t, kernel (a + 1) z t) / 2 + (∫ t, kernel (a - 1) z t) / 2) / 2 = _
  unfold argumentDeriv
  rw [integral_div, integral_neg, integral_add (integrable_kernel _ _ hz)
    (integrable_kernel _ _ hz)]
  ring

/-- Order reflection in the bilateral integral, including imaginary orders. -/
theorem macdonald_neg_order (a z : ℂ) : macdonald (-a) z = macdonald a z := by
  change (∫ t, kernel (-a) z t) / 2 = (∫ t, kernel a z t) / 2
  rw [← integral_neg_eq_self (kernel a z)]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  simp [kernel]

/-- Complex conjugation respects both parameters of the Schläfli integral. -/
theorem macdonald_conj (a z : ℂ) : conj (macdonald a z) = macdonald (conj a) (conj z) := by
  unfold macdonald
  rw [map_div₀, ← integral_conj]
  simp only [map_ofNat]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  rw [← Complex.exp_conj]
  simp only [map_add, map_mul, map_neg, conj_ofReal]

/-- At purely imaginary order and positive real argument the Macdonald integral is a real
cosine transform. -/
theorem macdonald_imaginary (b x : ℝ) (hx : 0 < x) :
    macdonald (b * I) x =
      ((∫ t : ℝ, Real.exp (-x * Real.cosh t) * Real.cos (b * t)) / 2 : ℝ) := by
  have h := macdonald_conj (b * I) x
  rw [map_mul, conj_ofReal, conj_I, conj_ofReal, mul_neg, macdonald_neg_order] at h
  apply Complex.ext
  · simp only [ofReal_re, macdonald, div_ofNat_re]
    change RCLike.re (∫ t, kernel (b * I) x t) / 2 = _
    rw [← integral_re (integrable_kernel (b * I) x hx)]
    congr 1
    apply integral_congr_ae
    filter_upwards with t
    simp [kernel, exp_re, mul_re, mul_im]
  · have hi := congrArg Complex.im h
    simp only [conj_im] at hi
    simpa only [ofReal_im] using (by linarith : (macdonald (b * I) x).im = 0)

/-- The decaying solution is strictly positive for real order and positive real argument. -/
theorem macdonald_re_pos (a x : ℝ) (hx : 0 < x) : 0 < (macdonald a x).re := by
  simp only [macdonald, div_ofNat_re]
  apply div_pos _ (by norm_num)
  change 0 < RCLike.re (∫ t, kernel a x t)
  rw [← integral_re (integrable_kernel a x hx)]
  have he (t : ℝ) : (kernel a x t).re = Real.exp (-x * Real.cosh t + a * t) := by
    simp [kernel, exp_re]
  apply integral_pos_of_integrable_nonneg_nonzero (x := 0)
  · unfold kernel
    fun_prop
  · exact (integrable_kernel a x hx).re
  · intro t
    change 0 ≤ (kernel a x t).re
    rw [he]
    exact (Real.exp_pos _).le
  · change (kernel a x 0).re ≠ 0
    rw [he]
    exact (Real.exp_pos _).ne'

private def rapidityDeriv (a z : ℂ) (t : ℝ) : ℂ :=
  a * kernel a z t - z / 2 * (kernel (a + 1) z t - kernel (a - 1) z t)

private theorem deriv_rapidity (a z : ℂ) (t : ℝ) :
    HasDerivAt (kernel a z) (rapidityDeriv a z t) t := by
  have h := (((Real.hasDerivAt_cosh t).ofReal_comp.const_mul (-z)).add
    ((hasDerivAt_id t).ofReal_comp.const_mul a)).cexp
  convert h using 1
  · rfl
  change _ = kernel a z t * (-z * (Real.sinh t : ℂ) + a * (1 : ℝ))
  rw [rapidityDeriv, shift_plus, shift_minus, ← sub_mul, Complex.ofReal_sinh, Complex.sinh]
  unfold kernel
  simp only [ofReal_one, mul_one]
  ring

/-- Integration by parts in rapidity gives the order recurrence for all complex orders. -/
theorem macdonald_recurrence (a z : ℂ) (hz : 0 < z.re) :
    z * (macdonald (a + 1) z - macdonald (a - 1) z) = 2 * a * macdonald a z := by
  have hi (b : ℂ) := integrable_kernel b z hz
  have hd : Integrable (rapidityDeriv a z) :=
    ((hi a).const_mul a).sub (((hi _).sub (hi _)).const_mul (z / 2))
  have he := integral_eq_zero_of_hasDerivAt_of_integrable (deriv_rapidity a z) hd (hi a)
  unfold rapidityDeriv at he
  have hs : Integrable (fun t => kernel (a + 1) z t - kernel (a - 1) z t) := (hi _).sub (hi _)
  rw [integral_sub ((hi a).const_mul a) (hs.const_mul (z / 2)),
    integral_const_mul, integral_const_mul, integral_sub (hi _) (hi _)] at he
  unfold macdonald
  unfold kernel at he
  linear_combination -he

private theorem deriv_next (a z : ℂ) (hz : 0 < z.re) :
    HasDerivAt (macdonald a) (a / z * macdonald a z - macdonald (a + 1) z) z := by
  convert hasDerivAt_macdonald a z hz using 1
  have h := macdonald_recurrence a z hz
  field_simp [ne_zero_of_re_pos hz]
  linear_combination -h

/-- Modified Bessel's differential equation for the Schläfli integral. -/
theorem macdonald_equation (a z : ℂ) (hz : 0 < z.re) :
    z ^ 2 * deriv (deriv (macdonald a)) z + z * deriv (macdonald a) z -
      (z ^ 2 + a ^ 2) * macdonald a z = 0 := by
  have hz0 := ne_zero_of_re_pos hz
  have hd := deriv_next a z hz
  have he := (((hasDerivAt_const z a).div (hasDerivAt_id z) hz0).mul hd).sub
    (deriv_next (a + 1) z hz)
  have hn : ∀ᶠ w in 𝓝 z, 0 < w.re := (isOpen_lt continuous_const continuous_re).mem_nhds hz
  have hf : deriv (macdonald a) =ᶠ[𝓝 z] (fun w => a / w * macdonald a w - macdonald (a + 1) w) :=
    hn.mono fun w hw => (deriv_next a w hw).deriv
  rw [(he.congr_of_eventuallyEq hf).deriv, hd.deriv]
  have hr := macdonald_recurrence (a + 1) z hz
  rw [add_sub_cancel_right] at hr
  dsimp only [id_eq, Pi.div_apply]
  field_simp [hz0]
  linear_combination z * hr

end ProjectAinos.SpecialFunctions.Bessel
