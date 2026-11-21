/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.BesselIntegral
public import ProjectAinos.SpecialFunctions.QuadraticPhase
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! # Large positive argument of the integer-order Bessel functions

Split Bessel's cosine integral about its stationary point at π/2. On each half,
`s = 2 sin(β/2)` makes the phase exactly quadratic. The smooth amplitude at the endpoint
is one. The Fresnel limit gives the normalization and the phase shift π/4.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter Complex
open scoped Topology Real ContDiff
namespace ProjectAinos.SpecialFunctions.Bessel

private def cis (t : ℝ) := exp ((t : ℂ) * I)
private theorem re_cis (t : ℝ) : (cis t).re = Real.cos t := by
  rw [cis, exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  simp only [add_re, mul_I_re, ofReal_im, neg_zero, ofReal_re, add_zero]
private theorem im_cis (t : ℝ) : (cis t).im = Real.sin t := by
  rw [cis, exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  simp only [add_im, mul_I_im, ofReal_im, ofReal_re, zero_add]
private theorem cis_add (s t : ℝ) : cis (s+t) = cis s * cis t := by
  simp [cis, add_mul, exp_add]
private theorem cis_norm (t : ℝ) : ‖cis t‖ = 1 := by simp [cis]

private def angle (s : ℝ) := 2 * Real.arcsin (s / 2)
private def jac (s : ℝ) := 1 / √(1 - (s / 2) ^ 2)
private def weight (n : ℤ) (s : ℝ) : ℂ := ((jac s * Real.cos (n * angle s) : ℝ) : ℂ)

private theorem small {s : ℝ} (hs : s ∈ Icc 0 (√2)) : -1 < s / 2 ∧ s / 2 < 1 := by
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  constructor <;> nlinarith [hs.1, hs.2]

private theorem rad_pos {s : ℝ} (hs : s ∈ Icc 0 (√2)) : 0 < 1 - (s / 2) ^ 2 := by
  have h := small hs
  have hp := mul_pos (sub_pos.mpr h.2) (show 0 < s / 2 + 1 by linarith [h.1])
  nlinarith

private theorem smooth_jac {s : ℝ} (hs : s ∈ Icc 0 (√2)) : ContDiffAt ℝ 1 jac s := by
  have hu : ContDiff ℝ 1 (fun x : ℝ => x / 2) := by fun_prop
  exact contDiffAt_const.div
    ((contDiffAt_const.sub (hu.contDiffAt.pow 2)).sqrt (rad_pos hs).ne')
    (Real.sqrt_pos.mpr (rad_pos hs)).ne'

private theorem smooth {s : ℝ} (hs : s ∈ Icc 0 (√2)) (n : ℤ) : ContDiffAt ℝ 1 (weight n) s := by
  have h := small hs
  have hu : ContDiff ℝ 1 (fun x : ℝ => x / 2) := by fun_prop
  have har := (Real.contDiffAt_arcsin (n := 1) h.1.ne' h.2.ne).comp s
    (f := fun t : ℝ => t / 2) hu.contDiffAt
  have ha : ContDiffAt ℝ 1 angle s := contDiffAt_const.mul har
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp s
    ((smooth_jac hs).mul ((contDiffAt_const.mul ha).cos))

private theorem da {s : ℝ} (hs : s ∈ Icc 0 (√2)) :
    HasDerivAt angle (jac s) s := by
  have h := small hs
  convert (((Real.hasDerivAt_arcsin h.1.ne' h.2.ne).comp s
    ((hasDerivAt_id s).div_const 2)).const_mul 2) using 1
  · rfl
  · dsimp [jac]
    ring

private theorem quadratic (n : ℤ) (x : ℝ) :
    (∫ β in 0..π/2, (Real.cos (n * β) : ℂ) * cis (x * (1-Real.cos β))) =
    ∫ s in 0..√2, weight n s * cis (x/2*s^2) := by
  let f (β : ℝ) := (Real.cos (n * β) : ℂ) * cis (x * (1 - Real.cos β))
  have hb : (0 : ℝ) ≤ √2 := Real.sqrt_nonneg _
  have h := intervalIntegral.integral_deriv_smul_comp (a := 0) (b := √2) (g := f)
    (fun t ht => da (uIcc_of_le hb ▸ ht))
    (fun t ht => (smooth_jac (uIcc_of_le hb ▸ ht)).continuousAt.continuousWithinAt)
    (by unfold f cis; fun_prop)
  have hend : angle (√2) = π / 2 := by
    unfold angle
    rw [← Real.sin_pi_div_four,
      Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]
    ring
  rw [show angle 0 = 0 by simp [angle], hend] at h
  rw [← h]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' := small (uIcc_of_le hb ▸ hs)
  have he : 1 - Real.cos (angle s) = s ^ 2 / 2 := by
    rw [angle, Real.cos_two_mul_eq_one_sub, Real.sin_arcsin hs'.1.le hs'.2.le]
    ring
  simp only [Function.comp_apply, f, he, weight, Complex.real_smul, ofReal_mul]
  rw [show x * (s^2/2) = x/2*s^2 by ring]
  ring

private theorem halves (n : ℤ) (x : ℝ) :
    (besselJ n (x : ℂ)).re =
      2 / π * (cis (n * (π/2) - x) *
        ∫ β in 0..π/2, (Real.cos (n*β) : ℂ) * cis (x * (1 - Real.cos β))).re := by
  let f (t : ℝ) := Real.cos (n * t - x * Real.sin t)
  have hf : Continuous f := by unfold f; fun_prop
  have ha := intervalIntegral.integral_comp_sub_left (a := 0) (b := π/2) f (π/2)
  have hb := intervalIntegral.integral_comp_add_left (a := 0) (b := π/2) f (π/2)
  rw [sub_self, sub_zero] at ha
  rw [add_zero, add_halves] at hb
  have hs := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (a := 0) (b := π/2) (c := π)
    (hf.intervalIntegrable ..) (hf.intervalIntegrable ..)
  rw [← ha, ← hb, ← intervalIntegral.integral_add
    (f := fun t => f (π/2 - t)) (g := fun t => f (π/2 + t))
    (Continuous.intervalIntegrable (by fun_prop) ..)
    (Continuous.intervalIntegrable (by fun_prop) ..)] at hs
  let a := n * (π/2) - x
  let g (t : ℝ) := cis a * ((Real.cos (n*t) : ℂ) * cis (x*(1-Real.cos t)))
  have hg (t : ℝ) : f (π/2-t) + f (π/2+t) = 2 * (g t).re := by
    unfold f g a
    rw [Real.sin_pi_div_two_sub, add_comm (π/2) t, Real.sin_add_pi_div_two]
    let b := n * (π/2) - x * Real.cos t
    rw [show (n : ℝ)*(π/2-t)-x*Real.cos t = b-n*t by dsimp [b]; ring,
      show (n : ℝ)*(t+π/2)-x*Real.cos t = b+n*t by dsimp [b]; ring,
      Real.cos_sub, Real.cos_add, mul_left_comm (cis _), ← cis_add, re_ofReal_mul, re_cis,
      show n*(π/2)-x+x*(1-Real.cos t) = b by dsimp [b]; ring]
    ring
  have hreal := Complex.reCLM.intervalIntegral_comp_comm
    (a := 0) (b := π/2) (μ := volume) (f := g)
    (Continuous.intervalIntegrable (by unfold g cis; fun_prop) ..)
  rw [integral, Complex.ofReal_re, ← hs]
  simp_rw [hg, intervalIntegral.integral_const_mul]
  change _ = 2 / π * (cis a * ∫ t in 0..π/2, _).re
  rw [← intervalIntegral.integral_const_mul (cis a), ← show (∫ t in 0..π/2, (g t).re) =
    (∫ t in 0..π/2, g t).re from hreal]
  ring

private theorem scaled (n : ℤ) :
    Tendsto (fun r : ℝ => (r : ℂ) * ∫ s in 0..√2,
      weight n s * cis (π*r^2/2*s^2)) atTop (𝓝 ((1+I)/2)) := by
  have h := Oscillatory.quadratic_endpoint (b := √2) (by positivity) (A := weight n)
    (D := deriv (weight n)) (fun s hs => (smooth hs n).differentiableAt one_ne_zero |>.hasDerivAt)
    (fun s hs => ((smooth hs n).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt)
  have he r s : π*r^2/2*s^2 = π/2*(r*s)^2 := by ring
  simpa [cis, he, weight, jac, angle] using h

/-- Leading positive-real asymptotic for each integer order, including the phase shift π/4. -/
theorem tendsto_large_argument (n : ℤ) :
    Tendsto (fun x : ℝ => √x * (besselJ n (x : ℂ)).re -
      √(2 / π) * Real.cos (x - n * (π / 2) - π / 4)) atTop (𝓝 0) := by
  let r (x : ℝ) := √(x/π)
  have hr : Tendsto r atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_id.atTop_div_const Real.pi_pos)
  let A (x : ℝ) := cis (n*(π/2)-x)
  let Q (x : ℝ) := ∫ s in 0..√2, weight n s * cis (x/2*s^2)
  have hQ : Tendsto (fun x => (r x : ℂ) * Q x - (1+I)/2) atTop (𝓝 0) := by
    have he := ((scaled n).comp hr).sub_const ((1+I)/2)
    rw [sub_self] at he
    apply he.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    simp only [Function.comp_apply, r, Real.sq_sqrt (div_nonneg hx Real.pi_pos.le),
      mul_div_cancel₀ _ Real.pi_ne_zero, Q]
  have H : Tendsto (fun x => A x * ((r x : ℂ) * Q x - (1+I)/2)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [A, norm_mul, cis_norm] using (tendsto_zero_iff_norm_tendsto_zero.mp hQ)
  have H' := ((Complex.continuous_re.tendsto 0).comp H).const_mul (2 / √π)
  simp only [Complex.zero_re, mul_zero] at H'
  apply H'.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [halves, quadratic]
  have hπ := Real.sq_sqrt Real.pi_pos.le
  have h₂ := Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))
  have hroot := Real.sqrt_pos.mpr Real.pi_pos
  have hc : (A x * ((1+I)/2)).re =
      √2/2 * Real.cos (x - n * (π/2) - π/4) := by
    dsimp only [A]
    rw [show x - n*(π/2) - π/4 = -((n*(π/2)-x)+π/4) by ring, Real.cos_neg, Real.cos_add]
    simp [Complex.mul_re, re_cis, im_cis, Real.cos_pi_div_four, Real.sin_pi_div_four]
    linear_combination -(Real.cos (n * (π / 2) - x) - Real.sin (n * (π / 2) - x)) / 4 * h₂
  change 2 / √π * (A x * ((r x : ℂ) * Q x - (1+I)/2)).re = _
  rw [mul_sub, Complex.sub_re, hc, mul_left_comm (A x) (r x : ℂ), Complex.re_ofReal_mul]
  change _ = √x * (2 / π * (A x * Q x).re) - _
  dsimp only [r]
  rw [Real.sqrt_div hx, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp
  linear_combination -2 * √x * (A x * Q x).re * hπ

end ProjectAinos.SpecialFunctions.Bessel
