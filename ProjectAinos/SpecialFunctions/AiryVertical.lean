/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.AiryIntegral
import Mathlib.Tactic

/-! # Absolutely convergent vertical Airy integrals

Moving the contour one unit to the right of the imaginary axis gives a Gaussian bound in
the integration variable. The same contour then gives the derivative by differentiation
under the integral sign.
-/

@[expose] public section
noncomputable section

open Complex Filter MeasureTheory Set
open scoped Real Topology ComplexConjugate
namespace ProjectAinos.SpecialFunctions.Airy

private def line (s : ℝ) : ℂ := 1 + s*I
private def value (u s : ℝ) : ℂ := integrand u (line s)

private theorem norm_value (u s : ℝ) :
    ‖value u s‖ = Real.exp (1/3-u) * Real.exp (-s^2) := by
  rw [value, integrand, norm_exp, ← Real.exp_add]
  congr 1
  simp [line, pow_succ, Complex.mul_re, Complex.mul_im, div_ofNat_re]
  ring

private theorem conjugate (u : ℝ) (w : ℂ) : conj (primitive u w) = primitive u (conj w) := by
  have h (z : ℂ) := segment (u : ℂ) 0 z 1
  have h0 : primitive u 0 = 0 := by simp [primitive, wedgeIntegral]
  simp only [ofReal_one, mul_one, zero_add, h0, sub_zero] at h
  rw [h, h, intervalIntegral.integral_of_le zero_le_one, ← integral_conj,
    intervalIntegral.integral_of_le zero_le_one]
  apply integral_congr_ae
  filter_upwards with t
  simp only [integrand, map_mul, ← exp_conj, map_sub, map_div₀, map_pow, conj_ofReal, map_ofNat]

private theorem integrable_value (u : ℝ) : Integrable (value u) := by
  have hi := (integrable_exp_neg_mul_sq (by norm_num : 0 < (1 : ℝ))).const_mul (Real.exp (1/3-u))
  apply Integrable.mono' (g := fun t : ℝ => Real.exp (1/3-u) * Real.exp (-t^2))
    (by simpa using hi) (by unfold value integrand line; fun_prop)
  exact ae_of_all _ fun t => (norm_value u t).le

private theorem bound_line (s : ℝ) : ‖line s‖ ≤ 1 + |s| := by
  simpa [line, norm_mul] using norm_add_le (1 : ℂ) (s*I)

private theorem column (u : ℝ) : (∫ t, value u t) = 2*π*ai u := by
  have htop := shifted_vertical_limit u 1 zero_le_one
  have he (s : ℝ) : I*s + ↑(1 : ℝ) = line s := by unfold line; push_cast; ring
  simp only [he] at htop
  have hbot := (continuous_conj.tendsto _).comp (htop.comp tendsto_neg_atBot_atTop)
  change Tendsto (fun s : ℝ => conj (primitive u (line (-s)))) _ _ at hbot
  simp only [conjugate, line, ofReal_neg, map_add, map_one, map_mul, map_neg, conj_ofReal,
    conj_I, neg_mul_neg, conj_ray] at hbot
  have hd (s : ℝ) : HasDerivAt (fun t : ℝ => primitive u (line t)) (I * value u s) s := by
    have h : HasDerivAt line I s := by
      change HasDerivAt (fun t : ℝ => 1 + (t : ℂ)*I) I s
      simpa only [id_eq, ofReal_one, one_mul] using
        (((hasDerivAt_id s).ofReal_comp.mul_const I).const_add (1 : ℂ))
    exact (deriv_primitive u (line s)).scomp s h
  have h := integral_of_hasDerivAt_of_tendsto hd ((integrable_value u).const_mul I) hbot htop
  rw [integral_const_mul] at h
  rw [ai, ← h]
  field_simp [Real.pi_ne_zero, I_ne_zero]

/-- Unit-shift vertical contour for the Airy profile. -/
theorem integral_vertical (u : ℝ) :
    (∫ t : ℝ, integrand u (1+t*I)) = 2*π*ai u := column u

private theorem deriv_column (u : ℝ) : HasDerivAt (fun x => ∫ t, value x t)
    (∫ t, -line t * value u t) u := by
  let B := Real.exp (1/3+|u|+1)
  let g (t : ℝ) := B * ((1+|t|) * Real.exp (-t^2))
  have hi : Integrable g := by
    have h₁ := integrable_exp_neg_mul_sq (by norm_num : 0 < (1 : ℝ))
    have h₂ := (integrable_mul_exp_neg_mul_sq (by norm_num : 0 < (1 : ℝ))).norm
    simpa [g, add_mul, Real.norm_eq_abs, abs_mul] using (h₁.add h₂).const_mul B
  have hd (x t : ℝ) : HasDerivAt (fun y => value y t) (-line t * value x t) x := by
    have h := ((((hasDerivAt_id x).ofReal_comp.mul_const (line t)).const_sub ((line t)^3/3)).cexp)
    convert h using 1
    · rfl
    simp [value, integrand]
    ring
  have he (t x : ℝ) (hx : |x| < |u|+1) : ‖-line t * value x t‖ ≤ g t := by
    dsimp only [g]
    rw [norm_mul, norm_neg, norm_value, mul_left_comm B]
    gcongr
    · exact bound_line t
    · unfold B
      apply Real.exp_le_exp.mpr
      linarith [neg_abs_le x]
  have hn : {x : ℝ | |x| < |u|+1} ∈ 𝓝 u :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds (by simp)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := value)
    (F' := fun x t => -line t * value x t) hn
    (Eventually.of_forall fun _ => by unfold value integrand line; fun_prop)
    (integrable_value u) (by unfold value integrand line; fun_prop) (bound := g)
    (ae_of_all _ he) hi (ae_of_all _ fun t x _ => hd x t)).2

/-- The extra linear factor in the absolutely convergent vertical integral gives Ai′. -/
theorem integral_vertical_deriv (u : ℝ) :
    (∫ t : ℝ, -(1+t*I) * integrand u (1+t*I)) = 2*π*deriv ai u := by
  have h := (hasDerivAt_ai (u : ℂ)).differentiableAt.hasDerivAt.comp_ofReal.const_mul (2*π : ℂ)
  exact (deriv_column u).unique (h.congr_of_eventuallyEq (Eventually.of_forall column))

end ProjectAinos.SpecialFunctions.Airy
