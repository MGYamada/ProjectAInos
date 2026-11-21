/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.Macdonald
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-! # The infinite rays of the Schläfli contour

In a half-plane of the argument, each ray converges absolutely for every complex order.
Integration by parts keeps the contribution at its finite endpoint.
-/

@[expose] public section
noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology

namespace ProjectAinos.SpecialFunctions.Bessel.Schlaefli

private def kernel (a z : ℂ) (t : ℝ) := exp (-z * Real.sinh t + a * t)

/-- Integral over the positive real rapidity ray of the Schläfli contour. -/
def ray (a z : ℂ) : ℂ := ∫ t : ℝ in Ioi 0, exp (-z * Real.sinh t + a * t)

private def bound (a : ℂ) (p t : ℝ) : ℝ :=
  Real.exp p * ‖exp (-(p : ℂ) * Real.cosh t + a * t)‖

private theorem integrable_bound (a : ℂ) {p : ℝ} (hp : 0 < p) : Integrable (bound a p) :=
  (integrable_macdonald a p hp).norm.const_mul _

private theorem norm_kernel (a z : ℂ) {p : ℝ} (hp : 0 < p) (hz : p ≤ z.re) {t : ℝ} (ht : 0 ≤ t) :
    ‖kernel a z t‖ ≤ bound a p t := by
  rw [kernel, bound, norm_exp, norm_exp, ← Real.exp_add, Real.exp_le_exp]
  simp only [add_re, re_mul_ofReal, neg_re, ofReal_re]
  have he := Real.cosh_sub_sinh t
  have h := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
  have hs := mul_le_mul_of_nonneg_right hz (Real.sinh_nonneg_iff.mpr ht)
  nlinarith [mul_nonneg hp.le (sub_nonneg.mpr h)]

private theorem integrable_kernel (a z : ℂ) (hz : 0 < z.re) :
    IntegrableOn (kernel a z) (Ioi 0) :=
  (integrable_bound a hz).integrableOn.mono' (by unfold kernel; fun_prop)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun _ ht => norm_kernel a z hz le_rfl ht.le)

private theorem plus (a z : ℂ) (t : ℝ) : kernel (a + 1) z t = exp (t : ℂ) * kernel a z t := by
  unfold kernel
  rw [← exp_add]
  congr 1
  ring

private theorem minus (a z : ℂ) (t : ℝ) : kernel (a - 1) z t = exp (-(t : ℂ)) * kernel a z t := by
  unfold kernel
  rw [← exp_add]
  congr 1
  ring

private def dz (a z : ℂ) (t : ℝ) := (kernel (a - 1) z t - kernel (a + 1) z t) / 2

private theorem deriv_argument (a z : ℂ) (t : ℝ) :
    HasDerivAt (fun w => kernel a w t) (dz a z t) z := by
  have h := (((hasDerivAt_id z).neg.mul_const (Real.sinh t : ℂ)).add_const (a * (t : ℂ))).cexp
  convert h using 1
  · rfl
  change _ = kernel a z t * (-1 * (Real.sinh t : ℂ))
  rw [dz, plus, minus, Complex.ofReal_sinh, Complex.sinh]
  ring

/-- Differentiation under the integral expresses the argument derivative by order shifts. -/
theorem hasDerivAt_ray (a z : ℂ) (hz : 0 < z.re) :
    HasDerivAt (ray a) ((ray (a - 1) z - ray (a + 1) z) / 2) z := by
  let p := z.re / 2
  have hp : 0 < p := half_pos hz
  let s := {w : ℂ | p < w.re}
  have hs : s ∈ 𝓝 z := (isOpen_lt continuous_const continuous_re).mem_nhds (half_lt_self hz)
  let b := fun t => (bound (a - 1) p t + bound (a + 1) p t) / 2
  have hi : Integrable b := ((integrable_bound (a - 1) hp).add
    (integrable_bound (a + 1) hp)).div_const 2
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := kernel a) (F' := dz a)
    hs (Eventually.of_forall fun w => by unfold kernel; fun_prop) (integrable_kernel a z hz)
    (by unfold dz kernel; fun_prop) (bound := b)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht w hw => by
      change p < w.re at hw
      simp only [dz, norm_div, norm_ofNat, b]
      gcongr
      exact (norm_sub_le _ _).trans (add_le_add (norm_kernel _ _ hp hw.le ht.le)
        (norm_kernel _ _ hp hw.le ht.le))) hi.integrableOn
    (ae_of_all _ fun t w _ => deriv_argument a w t)
  convert hd.2 using 1
  · rfl
  unfold dz
  rw [integral_div, integral_sub (integrable_kernel _ _ hz) (integrable_kernel _ _ hz)]
  rfl

private def dt (a z : ℂ) (t : ℝ) :=
  a * kernel a z t - z / 2 * (kernel (a + 1) z t + kernel (a - 1) z t)

private theorem deriv_rapidity (a z : ℂ) (t : ℝ) :
    HasDerivAt (kernel a z) (dt a z t) t := by
  have h := (((Real.hasDerivAt_sinh t).ofReal_comp.const_mul (-z)).add
    ((hasDerivAt_id t).ofReal_comp.const_mul a)).cexp
  convert h using 1
  · rfl
  change _ = kernel a z t * (-z * (Real.cosh t : ℂ) + a * (1 : ℝ))
  rw [dt, plus, minus, Complex.ofReal_cosh, Complex.cosh, ofReal_one]
  ring

/-- The inhomogeneous term is the value of the ray integrand at its finite endpoint. -/
theorem ray_recurrence (a z : ℂ) (hz : 0 < z.re) :
    z / 2 * (ray (a + 1) z + ray (a - 1) z) - a * ray a z = 1 := by
  have hi (b : ℂ) := integrable_kernel b z hz
  have hs : IntegrableOn (fun t => kernel (a + 1) z t + kernel (a - 1) z t) (Ioi 0) :=
    (hi _).add (hi _)
  have hd : IntegrableOn (dt a z) (Ioi 0) := ((hi _).const_mul a).sub (hs.const_mul (z / 2))
  have h := tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := 0)
    (fun t _ => deriv_rapidity a z t) hd (hi a)
  have he := integral_Ioi_of_hasDerivAt_of_tendsto' (fun t _ => deriv_rapidity a z t) hd h
  unfold dt at he
  rw [integral_sub ((hi _).const_mul a) (hs.const_mul (z / 2)), integral_const_mul,
    integral_const_mul, integral_add (hi _) (hi _)] at he
  simp only [kernel, Real.sinh_zero, ofReal_zero, mul_zero, add_zero, exp_zero, zero_sub] at he
  unfold ray
  linear_combination -he

end ProjectAinos.SpecialFunctions.Bessel.Schlaefli
