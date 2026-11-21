/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-! # Entire Airy functions from their cubic contours

The three rays with ω³ = −1 give absolutely convergent moments of exp(−t³/3 − ωzt).
Their endpoint terms cancel in the outgoing and incoming contour combinations that define
Ai and Bi. This gives both the Airy equation and the gamma normalization at the origin.
-/

@[expose] public section
noncomputable section

open Complex MeasureTheory Set Filter
open scoped Real Topology ComplexConjugate

namespace ProjectAinos.SpecialFunctions.Airy

private def kernel (n : ℕ) (z : ℂ) (t : ℝ) := (t : ℂ) ^ n * exp (-(t : ℂ)^3/3 - z*t)

/-- Laplace moment on the positive cubic decay ray. -/
def moment (n : ℕ) (z : ℂ) : ℂ := ∫ t : ℝ in Ioi 0, (t : ℂ) ^ n * exp (-(t : ℂ)^3/3 - z*t)

private def bound (n : ℕ) (B t : ℝ) := Real.exp ((B^2+9)/2) * (t ^ n * Real.exp (-t^2))

private theorem integrable_bound (n : ℕ) (B : ℝ) : IntegrableOn (bound n B) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_sq (b := 1) zero_lt_one
    (s := (n : ℝ)) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  unfold bound IntegrableOn
  simpa using h.const_mul (Real.exp ((B^2+9)/2))

private theorem estimate (n : ℕ) {z : ℂ} {B t : ℝ} (hz : ‖z‖ ≤ B) (ht : 0 ≤ t) :
    ‖kernel n z t‖ ≤ bound n B t := by
  simp only [kernel, norm_mul, norm_pow, norm_real, Real.norm_eq_abs, abs_of_nonneg ht, norm_exp,
    sub_re, div_ofNat_re, neg_re, ← ofReal_pow, ofReal_re, re_mul_ofReal, bound]
  rw [mul_left_comm, ← Real.exp_add]
  gcongr
  have hr : -z.re ≤ B := (neg_le_abs _).trans ((abs_re_le_norm z).trans hz)
  nlinarith [mul_le_mul_of_nonneg_right hr ht, sq_nonneg (B-t),
    mul_nonneg (sq_nonneg (t-3)) (show 0 ≤ 2*t+3 by linarith)]

private theorem integrable_kernel (n : ℕ) (z : ℂ) : IntegrableOn (kernel n z) (Ioi 0) :=
  (integrable_bound n ‖z‖).mono' (by unfold kernel; fun_prop)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun _ ht => estimate _ le_rfl ht.le)

private theorem deriv_kernel (n : ℕ) (z : ℂ) (t : ℝ) :
    HasDerivAt (fun w => kernel n w t) (-kernel (n+1) z t) z := by
  have h := ((((hasDerivAt_id z).mul_const (t : ℂ)).const_sub (-(t : ℂ)^3/3)).cexp).const_mul
    ((t : ℂ)^n)
  convert h using 1
  · rfl
  unfold kernel
  simp only [id_eq, one_mul, pow_succ]
  ring

/-- Differentiating the cubic moment with respect to its complex argument raises its degree. -/
theorem hasDerivAt_moment (n : ℕ) (z : ℂ) : HasDerivAt (moment n) (-moment (n+1) z) z := by
  let B := ‖z‖ + 1
  have hs : {w : ℂ | ‖w‖ < B} ∈ 𝓝 z := (isOpen_lt continuous_norm continuous_const).mem_nhds
    (by dsimp [B]; linarith)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := kernel n)
    (F' := fun w t => -kernel (n+1) w t) hs
    (Eventually.of_forall fun _ => by unfold kernel; fun_prop)
    (integrable_kernel n z) (by unfold kernel; fun_prop) (bound := bound (n+1) B)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht w hw => by
      rw [norm_neg]
      exact estimate _ (le_of_lt hw) ht.le) (integrable_bound _ _)
    (ae_of_all _ fun t w _ => deriv_kernel n w t)
  convert h.2 using 1
  · rfl
  rw [integral_neg]
  rfl

private theorem deriv_t (z : ℂ) (t : ℝ) : HasDerivAt (kernel 0 z)
    (-(kernel 2 z t + z * kernel 0 z t)) t := by
  have h := (((((hasDerivAt_id t).ofReal_comp.pow 3).neg.div_const 3).sub
    ((hasDerivAt_id t).ofReal_comp.const_mul z)).cexp)
  convert h using 1
  · funext u
    simp [kernel]
  unfold kernel
  simp only [id_eq, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply, pow_zero, one_mul, ofReal_one,
    mul_one, Nat.cast_ofNat]
  ring

/-- Integration by parts supplies the endpoint value of the zeroth moment. -/
theorem moment_recurrence (z : ℂ) : moment 2 z + z * moment 0 z = 1 := by
  have hs : IntegrableOn (fun t => kernel 2 z t + z * kernel 0 z t) (Ioi 0) :=
    (integrable_kernel 2 z).add ((integrable_kernel 0 z).const_mul z)
  have hd := hs.neg
  have h := tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := 0) (fun t _ => deriv_t z t)
    hd (integrable_kernel 0 z)
  have he := integral_Ioi_of_hasDerivAt_of_tendsto' (fun t _ => deriv_t z t) hd h
  change (∫ t in Ioi 0, -(kernel 2 z t + z * kernel 0 z t)) = 0 - kernel 0 z 0 at he
  rw [integral_neg, integral_add (integrable_kernel 2 z) ((integrable_kernel 0 z).const_mul z),
    integral_const_mul] at he
  simpa [moment, kernel] using congrArg Neg.neg he

/-- At the origin the ray moments are real gamma integrals. -/
theorem moment_zero (n : ℕ) : moment n 0 =
    (((1/3 : ℝ) ^ (-((n : ℝ)+1)/3) * (1/3) * Real.Gamma (((n : ℝ)+1)/3)) : ℝ) := by
  have h := _root_.integral_rpow_mul_exp_neg_mul_rpow (p := 3) (q := (n : ℝ)) (b := 1/3)
    (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by norm_num)
  rw [← h, ← integral_complex_ofReal]
  unfold moment
  apply integral_congr_ae
  filter_upwards with t
  simp only [zero_mul, sub_zero, Real.rpow_natCast, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num]
  push_cast
  congr 2
  ring

/-- Uniform tail estimate for the zeroth moment throughout a closed disk of arguments. -/
theorem moment_tail {z : ℂ} {B R : ℝ} (hz : ‖z‖ ≤ B) (hR : 0 ≤ R) :
    ‖moment 0 z - ∫ t in 0..R, exp (-(t : ℂ)^3/3 - z*t)‖ ≤
      ∫ t : ℝ in Ioi R, Real.exp ((B^2+9)/2) * Real.exp (-t^2) := by
  have hi := intervalIntegral.integral_Ioi_sub_Ioi (integrable_kernel 0 z) hR
  have h := norm_integral_le_of_norm_le ((integrable_bound 0 B).mono_set (Ioi_subset_Ioi hR))
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => estimate 0 hz (hR.trans ht.le))
  rw [← sub_eq_of_eq_add (eq_add_of_sub_eq' hi)] at h
  simpa [moment, kernel, bound] using h

/-- The upper decay ray, directed at π/3. -/
def upper : ℂ := exp ((π / 3 : ℝ) * I)

/-- Cartesian coordinates of the upper decay ray. -/
theorem upper_eq : upper = (1 + (√3 : ℝ) * I) / 2 := by
  rw [upper, exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast
  ring

/-- The upper ray has cubic direction −1. -/
theorem upper_cube : upper ^ 3 = -1 := by
  rw [upper, ← exp_nat_mul, ← exp_pi_mul_I]
  congr 1
  push_cast
  ring

private theorem lower_cube : (starRingEnd ℂ upper) ^ 3 = -1 := by
  rw [← map_pow, upper_cube]
  simp

/-- Conjugating both the argument and the integral conjugates the cubic moment. -/
theorem conj_moment (n : ℕ) (z : ℂ) : conj (moment n z) = moment n (conj z) := by
  unfold moment
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with t
  simp only [map_mul, map_pow, conj_ofReal, ← exp_conj, map_sub, map_div₀, map_neg, map_ofNat]

/-- The finite cubic integral tends to the absolutely convergent moment. -/
theorem tendsto_moment (n : ℕ) (z : ℂ) :
    Tendsto (fun R : ℝ => ∫ t in 0..R, (t : ℂ)^n * exp (-(t : ℂ)^3/3 - z*t))
      atTop (𝓝 (moment n z)) :=
  intervalIntegral_tendsto_integral_Ioi 0 (integrable_kernel n z) tendsto_id

/-- Oriented Airy ray, with its complex line element. -/
def ray (w z : ℂ) : ℂ := w * moment 0 (w*z)

/-- Conjugating an oriented cubic contour conjugates its ray and parameter. -/
theorem conj_ray (w z : ℂ) : conj (ray w z) = ray (conj w) (conj z) := by
  simp only [ray, map_mul, conj_moment]

/-- First derivative of an oriented ray integral. -/
theorem hasDerivAt_ray (w z : ℂ) : HasDerivAt (ray w) (-w ^ 2 * moment 1 (w*z)) z := by
  convert ((hasDerivAt_moment 0 (w*z)).comp z ((hasDerivAt_id z).const_mul w)).const_mul w using 1
  · rfl
  ring

private theorem second_ray (w z : ℂ) (hw : w^3 = -1) :
    HasDerivAt (deriv (ray w)) (z * ray w z - 1) z := by
  rw [show deriv (ray w) = fun t => -w ^ 2 * moment 1 (w*t) from funext fun t =>
    (hasDerivAt_ray w t).deriv]
  convert ((hasDerivAt_moment 1 (w*z)).comp z ((hasDerivAt_id z).const_mul w)).const_mul
    (-w ^ 2) using 1
  · rfl
  simp only [mul_one, ray]
  have h := moment_recurrence (w*z)
  linear_combination h - moment 2 (w*z) * hw

/-- Ai as the difference of the two oblique cubic decay rays. -/
def ai (z : ℂ) : ℂ := (ray upper z - ray (starRingEnd ℂ upper) z) / (2 * π * I)

/-- Bi as the sum of the oblique rays and twice the reversed negative real ray. -/
def bi (z : ℂ) : ℂ := (ray upper z + ray (starRingEnd ℂ upper) z - 2 * ray (-1) z) / (2 * π)

/-- The contour defining Ai is differentiable throughout the complex plane. -/
theorem hasDerivAt_ai (z : ℂ) : HasDerivAt ai
    ((deriv (ray upper) z - deriv (ray (starRingEnd ℂ upper)) z) / (2 * π * I)) z :=
  (((hasDerivAt_ray upper z).differentiableAt.hasDerivAt).sub
    (hasDerivAt_ray (starRingEnd ℂ upper) z).differentiableAt.hasDerivAt).div_const _

/-- The contour defining Bi is differentiable throughout the complex plane. -/
theorem hasDerivAt_bi (z : ℂ) : HasDerivAt bi
    ((deriv (ray upper) z + deriv (ray (starRingEnd ℂ upper)) z - 2 * deriv (ray (-1)) z) /
      (2 * π)) z :=
  (((hasDerivAt_ray upper z).differentiableAt.hasDerivAt.add
    (hasDerivAt_ray (starRingEnd ℂ upper) z).differentiableAt.hasDerivAt).sub
      ((hasDerivAt_ray (-1) z).differentiableAt.hasDerivAt.const_mul 2)).div_const _

/-- Ai solves Airy's equation on the entire complex plane. -/
theorem ai_equation (z : ℂ) : deriv (deriv ai) z = z * ai z := by
  rw [show deriv ai = _ from funext fun w => (hasDerivAt_ai w).deriv]
  have h := (((second_ray upper z upper_cube).sub (second_ray _ z lower_cube)).div_const
    (2 * π * I : ℂ)).deriv
  simp only [Pi.sub_apply] at h
  rw [h]
  unfold ai
  ring

/-- Bi solves Airy's equation on the entire complex plane. -/
theorem bi_equation (z : ℂ) : deriv (deriv bi) z = z * bi z := by
  rw [show deriv bi = _ from funext fun w => (hasDerivAt_bi w).deriv]
  have h := ((((second_ray upper z upper_cube).add (second_ray _ z lower_cube)).sub
    ((second_ray (-1) z (by norm_num)).const_mul 2)).div_const (2 * π : ℂ)).deriv
  simp only [Pi.sub_apply, Pi.add_apply] at h
  rw [h]
  unfold bi
  ring

private theorem lower_eq : conj upper = (1 - (√3 : ℝ) * I) / 2 := by
  rw [upper_eq, map_div₀, map_add, map_mul, conj_ofReal, conj_I, map_one, map_ofNat]
  ring

private theorem sqrt_sq : ((√3 : ℝ) : ℂ) ^ 2 = 3 := by
  exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3))

/-- Initial values of both Airy solutions and their derivatives in terms of the two gamma
moments. In particular their normalizations and signs are fixed. -/
theorem initialValues :
    ai 0 = (√3 : ℝ) * moment 0 0 / (2 * π) ∧
    deriv ai 0 = -(√3 : ℝ) * moment 1 0 / (2 * π) ∧
    bi 0 = 3 * moment 0 0 / (2 * π) ∧ deriv bi 0 = 3 * moment 1 0 / (2 * π) := by
  rw [(hasDerivAt_ai 0).deriv, (hasDerivAt_bi 0).deriv]
  simp only [(hasDerivAt_ray _ _).deriv, ai, bi, ray, mul_zero]
  rw [lower_eq, upper_eq]
  refine ⟨?_,?_,?_,?_⟩
  · field_simp [I_ne_zero, Real.pi_ne_zero]
    ring
  · field_simp [I_ne_zero, Real.pi_ne_zero]
    ring
  · ring
  · ring_nf
    rw [I_sq, sqrt_sq]
    ring

private theorem gamma_product : moment 0 0 * moment 1 0 = (2 * π) / (3 * (√3 : ℝ)) := by
  rw [moment_zero, moment_zero]
  norm_num only [Nat.cast_zero, Nat.cast_one, zero_add, one_add_one_eq_two]
  have h := Real.Gamma_mul_Gamma_one_sub (1/3)
  rw [show (1 : ℝ) - 1/3 = 2/3 by norm_num, show π * (1/3) = π/3 by ring,
    Real.sin_pi_div_three] at h
  have hp : (1/3 : ℝ) ^ (-(1:ℝ)/3) * (1/3 : ℝ) ^ (-(2:ℝ)/3) = 3 := by
    rw [← Real.rpow_add (by norm_num), show -(1:ℝ)/3 + -(2:ℝ)/3 = -1 by norm_num,
      Real.rpow_neg_one]
    norm_num
  have hr : ((1/3 : ℝ)^(-(1:ℝ)/3) * (1/3) * Real.Gamma (1/3)) *
      ((1/3 : ℝ)^(-(2:ℝ)/3) * (1/3) * Real.Gamma (2/3)) = (2 * π) / (3 * √3) := by
    calc
      _ = ((1/3 : ℝ)^(-(1:ℝ)/3) * (1/3 : ℝ)^(-(2:ℝ)/3)) *
          (Real.Gamma (1/3) * Real.Gamma (2/3)) / 9 := by ring
      _ = _ := by rw [hp,h]; ring
  have hc := congrArg Complex.ofReal hr
  push_cast at hc ⊢
  simpa only [neg_div] using hc

/-- W(Ai,Bi) = 1/π at every complex argument. -/
theorem wronskian (z : ℂ) : ai z * deriv bi z - deriv ai z * bi z = 1 / π := by
  let W (w : ℂ) := ai w * deriv bi w - deriv ai w * bi w
  have da : Differentiable ℂ ai := fun w => (hasDerivAt_ai w).differentiableAt
  have db : Differentiable ℂ bi := fun w => (hasDerivAt_bi w).differentiableAt
  have hd (w : ℂ) : HasDerivAt W 0 w := by
    have ha := (da w).hasDerivAt
    have hb := (db w).hasDerivAt
    have ha' := (da.analyticAt w).deriv.differentiableAt.hasDerivAt
    have hb' := (db.analyticAt w).deriv.differentiableAt.hasDerivAt
    convert (ha.mul hb').sub (ha'.mul hb) using 1
    rw [ai_equation, bi_equation]
    ring
  have h := is_const_of_deriv_eq_zero (fun w => (hd w).differentiableAt)
    (fun w => (hd w).deriv) z 0
  change W z = _
  rw [h]
  unfold W
  obtain ⟨a,da,b,db⟩ := initialValues
  rw [a,da,b,db]
  calc
    _ = 3 * (√3 : ℝ) / (2 * π ^ 2) * (moment 0 0 * moment 1 0) := by ring
    _ = _ := by rw [gamma_product]; field_simp [Real.pi_ne_zero]

end ProjectAinos.SpecialFunctions.Airy
