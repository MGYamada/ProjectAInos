/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.BesselIntegral
public import ProjectAinos.SpecialFunctions.Schlaefli
public import ProjectAinos.SpecialFunctions.SchlaefliArc
import Mathlib.Tactic

/-! # Cylindrical Hankel and Neumann functions

The outgoing Schläfli contour runs from negative infinity to zero, then up to iπ, and horizontally
to positive infinity. Its exponential kernel decays on both infinite rays when Re z > 0.
The contour therefore defines the second solution even at integral order. Its endpoint terms
cancel in the order recurrence.
-/

@[expose] public section
noncomputable section

open Complex Filter
open scoped Real Topology

namespace ProjectAinos.SpecialFunctions.Bessel

open Schlaefli

private def factor (a : ℂ) := exp (-(a * π) * I)

private theorem factor_add (a : ℂ) : factor (a + 1) = -factor a := by
  unfold factor
  rw [show -((a + 1) * π) * I = -(a * π) * I + -(π * I) by ring, exp_add, exp_neg_pi_mul_I]
  ring

private theorem factor_sub (a : ℂ) : factor (a - 1) = -factor a := by
  unfold factor
  rw [show -((a - 1) * π) * I = -(a * π) * I + π * I by ring, exp_add, exp_pi_mul_I]
  ring

/-- The outgoing cylindrical Hankel function, in the right-half-plane contour representation. -/
def hankelFirst (a z : ℂ) : ℂ :=
  (arc a z - I * (ray a z + exp (-(a * π) * I) * ray (-a) z)) / π

private theorem hankel_eq (a z : ℂ) :
    hankelFirst a z = (arc a z - I * (ray a z + factor a * ray (-a) z)) / π := rfl

/-- The Neumann function (second-kind cylindrical Bessel function). -/
def neumann (a z : ℂ) : ℂ := (hankelFirst a z - besselJ a z) / I

/-- The incoming cylindrical Hankel function. -/
def hankelSecond (a z : ℂ) : ℂ := 2 * besselJ a z - hankelFirst a z

/-- Differentiating the outgoing contour gives its adjacent-order relation. -/
theorem hasDerivAt_hankelFirst (a z : ℂ) (hz : 0 < z.re) : HasDerivAt (hankelFirst a)
    ((hankelFirst (a - 1) z - hankelFirst (a + 1) z) / 2) z := by
  have h := ((hasDerivAt_arc a z).sub (((hasDerivAt_ray a z hz).add
    ((hasDerivAt_ray (-a) z hz).const_mul (factor a))).const_mul I)).div_const (π : ℂ)
  convert h using 1
  · rfl
  simp only [hankel_eq]
  rw [factor_add, factor_sub, show -(a - 1) = -a + 1 by ring, show -(a + 1) = -a - 1 by ring]
  ring

/-- The endpoint contributions of the three contour segments cancel for every complex order. -/
theorem hankelFirst_recurrence (a z : ℂ) (hz : 0 < z.re) :
    z / 2 * (hankelFirst (a + 1) z + hankelFirst (a - 1) z) = a * hankelFirst a z := by
  have ha := arc_recurrence a z
  change I * _ = factor a - 1 at ha
  have har : z / 2 * (arc (a + 1) z + arc (a - 1) z) - a * arc a z = -I * (factor a - 1) := by
    rw [← ha, ← mul_assoc, neg_mul, I_mul_I, neg_neg, one_mul]
  have hp := ray_recurrence a z hz
  have hm := ray_recurrence (-a) z hz
  simp only [hankel_eq]
  rw [factor_add, factor_sub, show -(a - 1) = -a + 1 by ring, show -(a + 1) = -a - 1 by ring]
  linear_combination (har - I * hp + I * factor a * hm) / (π : ℂ)

private theorem slit {z : ℂ} (hz : 0 < z.re) : z ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl hz)

private theorem deriv_J (a z : ℂ) (hz : 0 < z.re) : HasDerivAt (besselJ a)
    ((besselJ (a - 1) z - besselJ (a + 1) z) / 2) z := by
  convert hasDerivAt_besselJ a z (slit hz) using 1
  linear_combination (recurrence a z (slit hz)) / 2

private theorem recurrence_J (a z : ℂ) (hz : 0 < z.re) :
    z / 2 * (besselJ (a + 1) z + besselJ (a - 1) z) = a * besselJ a z := by
  rw [add_comm (besselJ _ _), recurrence a z (slit hz)]
  field_simp [ne_zero_of_re_pos hz]

/-- Adjacent-order derivative of the second-kind solution, also at integer orders. -/
theorem hasDerivAt_neumann (a z : ℂ) (hz : 0 < z.re) : HasDerivAt (neumann a)
    ((neumann (a - 1) z - neumann (a + 1) z) / 2) z := by
  convert ((hasDerivAt_hankelFirst a z hz).sub (deriv_J a z hz)).div_const I using 1
  · rfl
  unfold neumann
  ring

/-- Adjacent-order derivative of the incoming cylindrical solution. -/
theorem hasDerivAt_hankelSecond (a z : ℂ) (hz : 0 < z.re) : HasDerivAt (hankelSecond a)
    ((hankelSecond (a - 1) z - hankelSecond (a + 1) z) / 2) z := by
  convert ((deriv_J a z hz).const_mul 2).sub (hasDerivAt_hankelFirst a z hz) using 1
  · rfl
  unfold hankelSecond
  ring

private theorem ode (f : ℂ → ℂ → ℂ)
    (hd : ∀ a z : ℂ, 0 < z.re → HasDerivAt (f a) ((f (a - 1) z - f (a + 1) z) / 2) z)
    (hr : ∀ a z : ℂ, 0 < z.re → z / 2 * (f (a + 1) z + f (a - 1) z) = a * f a z)
    (a z : ℂ) (hz : 0 < z.re) :
    z ^ 2 * deriv (deriv (f a)) z + z * deriv (f a) z + (z ^ 2 - a ^ 2) * f a z = 0 := by
  have h₁ := hr (a - 1) z hz
  have h₂ := hr (a + 1) z hz
  rw [sub_add_cancel] at h₁
  rw [add_sub_cancel_right] at h₂
  have hn : ∀ᶠ w in 𝓝 z, 0 < w.re := (isOpen_lt continuous_const continuous_re).mem_nhds hz
  have hf : deriv (f a) =ᶠ[𝓝 z] fun w => (f (a - 1) w - f (a + 1) w) / 2 :=
    hn.mono fun w hw => (hd a w hw).deriv
  have he := (((hd (a - 1) z hz).sub (hd (a + 1) z hz)).div_const 2).congr_of_eventuallyEq hf
  rw [he.deriv, (hd a z hz).deriv, sub_add_cancel, add_sub_cancel_right]
  linear_combination z / 2 * h₁ + z / 2 * h₂ + a * hr a z hz

/-- Cylindrical Bessel equation for the outgoing contour solution. -/
theorem hankelFirst_equation (a z : ℂ) (hz : 0 < z.re) :
    z ^ 2 * deriv (deriv (hankelFirst a)) z + z * deriv (hankelFirst a) z +
      (z ^ 2 - a ^ 2) * hankelFirst a z = 0 :=
  ode hankelFirst hasDerivAt_hankelFirst hankelFirst_recurrence a z hz

/-- Cylindrical Bessel equation for the second-kind solution. -/
theorem neumann_equation (a z : ℂ) (hz : 0 < z.re) :
    z ^ 2 * deriv (deriv (neumann a)) z + z * deriv (neumann a) z +
      (z ^ 2 - a ^ 2) * neumann a z = 0 := by
  apply ode neumann hasDerivAt_neumann _ a z hz
  intro b w hw
  unfold neumann
  linear_combination (hankelFirst_recurrence b w hw - recurrence_J b w hw) / I

/-- Cylindrical Bessel equation for the incoming solution. -/
theorem hankelSecond_equation (a z : ℂ) (hz : 0 < z.re) :
    z ^ 2 * deriv (deriv (hankelSecond a)) z + z * deriv (hankelSecond a) z +
      (z ^ 2 - a ^ 2) * hankelSecond a z = 0 := by
  apply ode hankelSecond hasDerivAt_hankelSecond _ a z hz
  intro b w hw
  unfold hankelSecond
  linear_combination 2 * recurrence_J b w hw - hankelFirst_recurrence b w hw

private theorem real_ray (a x : ℝ) : ray a x =
    ((∫ t : ℝ in Set.Ioi 0, Real.exp (-x * Real.sinh t + a * t)) : ℝ) := by
  unfold ray
  rw [← integral_complex_ofReal]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  push_cast
  rfl

/-- Integer-order Neumann integral on the positive real axis. Both the angular sine integral
and the exponentially decaying ray are included at integral order. -/
theorem neumann_integral (n : ℤ) (x : ℝ) (_hx : 0 < x) : neumann n x =
    (((∫ t in 0..π, Real.sin (x * Real.sin t - n * t)) -
      ((∫ t : ℝ in Set.Ioi 0, Real.exp (-x * Real.sinh t + n * t)) + (-1 : ℝ) ^ n *
        ∫ t : ℝ in Set.Ioi 0, Real.exp (-x * Real.sinh t - n * t))) / π : ℝ) := by
  let u (t : ℝ) := x * Real.sin t - n * t
  have har : arc n x = ((∫ t in 0..π, Real.cos (u t)) : ℝ) +
      ((∫ t in 0..π, Real.sin (u t)) : ℝ) * I := by
    unfold arc
    have he (t : ℝ) : exp (((x : ℂ) * Real.sin t - n * t) * I) =
        ↑(Real.cos (u t)) + ↑(Real.sin (u t)) * I := by
      rw [exp_mul_I, ofReal_cos, ofReal_sin]
      unfold u
      push_cast
      rfl
    simp_rw [he]
    rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by unfold u; fun_prop) ..)
      (Continuous.intervalIntegrable (by unfold u; fun_prop) ..),
      intervalIntegral.integral_mul_const,
      intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
  have hJ := integral n x
  have hc (t : ℝ) : Real.cos (n * t - x * Real.sin t) = Real.cos (u t) := by
    rw [← Real.cos_neg, neg_sub]
  simp_rw [hc] at hJ
  have hf : factor n = ((-1 : ℝ) ^ n : ℝ) := by
    unfold factor
    rw [show -((n : ℂ) * π) * I = n * -(π * I) by ring, Complex.exp_int_mul, exp_neg_pi_mul_I]
    push_cast
    rfl
  have hr := real_ray (n : ℝ) x
  have hr' := real_ray (-(n : ℝ)) x
  push_cast at hr hr'
  have he' (t : ℝ) : -x * Real.sinh t + -(n : ℝ) * t = -x * Real.sinh t - n * t := by ring
  simp_rw [he'] at hr'
  unfold neumann
  rw [hankel_eq, har, hf, hr, hr', hJ]
  push_cast
  unfold u
  field_simp [I_ne_zero, Real.pi_ne_zero]
  ring

end ProjectAinos.SpecialFunctions.Bessel
