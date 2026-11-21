/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.AiryIntegral
public import ProjectAinos.SpecialFunctions.Macdonald
import Mathlib.Tactic

/-! # Positive-argument Airy functions in terms of Macdonald functions

The curve w = b(ω exp(t/3) + ω̄ exp(−t/3)), with ω = exp(iπ/3), passes through the real
saddle at b. For Airy argument b², the cubic exponent on the curve is exactly
−(2b³/3) cosh(t). The two ends approach the defining rays through connecting segments
of vanishing length on which the integrand has norm at most one.
-/

@[expose] public section
noncomputable section

open Complex Filter MeasureTheory Set
open scoped Real Topology ComplexConjugate
namespace ProjectAinos.SpecialFunctions.Airy
open Bessel

private def leg (w : ℂ) (b t : ℝ) := w * ((b * Real.exp (t/3) : ℝ) : ℂ)
private def path (w : ℂ) (b t : ℝ) := leg w b t + leg (conj w) b (-t)
private def argument (b : ℝ) := 2*b^3/3
private def term (b : ℝ) (ν : ℂ) (t : ℝ) := exp (-((argument b : ℝ) : ℂ)*Real.cosh t + ν*t)

private theorem norm_upper : ‖upper‖ = 1 := by rw [upper, norm_exp]; simp

private theorem cube_conj {w : ℂ} (h : w^3 = -1) : (conj w)^3 = -1 := by rw [← map_pow, h]; simp

private theorem leg_cube {w : ℂ} (h : w^3 = -1) (b t : ℝ) :
    (leg w b t)^3 = -(((b * Real.exp (t/3))^3 : ℝ) : ℂ) := by
  rw [leg, mul_pow, h, ofReal_pow, neg_one_mul]

private theorem legs_mul {w : ℂ} (hw : ‖w‖ = 1) (b t : ℝ) :
    leg w b t * leg (conj w) b (-t) = ((b^2 : ℝ) : ℂ) := by
  have h : w * conj w = 1 := by rw [mul_conj, normSq_eq_norm_sq, hw]; norm_num
  unfold leg
  rw [mul_mul_mul_comm, h, one_mul, ← ofReal_mul]
  congr 1
  rw [mul_mul_mul_comm, ← Real.exp_add, show t/3+-t/3 = 0 by ring, Real.exp_zero]
  ring

private theorem leg_re {w : ℂ} (hw : 0 ≤ w.re) {b : ℝ} (hb : 0 ≤ b) (t : ℝ) :
    0 ≤ (leg w b t).re := by rw [leg, re_mul_ofReal]; positivity

private theorem decreasing {u v : ℂ} {B : ℝ} (hB : 0 ≤ B) (huv : u*v = B)
    (hu : (u^3).re ≤ 0) (hv : (v^3).re ≤ 0) (hu' : 0 ≤ u.re) (hv' : 0 ≤ v.re)
    {s : ℝ} (hs : s ∈ Icc 0 1) : ‖integrand B (u+v*s)‖ ≤ 1 := by
  rw [integrand, norm_exp, Real.exp_le_one_iff]
  have he : (u+v*s)^3/3 - B*(u+v*s) =
      u^3/3 + (((s^3/3 : ℝ) : ℂ) * v^3) +
        (((s-1)*B : ℝ) : ℂ)*u + (((s^2-s)*B : ℝ) : ℂ)*v := by
    push_cast
    rw [← huv]
    ring
  rw [he]
  simp only [add_re, div_ofNat_re, re_ofReal_mul]
  have hs' : s^2-s ≤ 0 := by nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr hs.2)]
  have hs0 := hs.1
  have h1 := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ s^3/3) hv
  have h2 := mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs.2) hB) hu'
  have h3 := mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hs' hB) hv'
  linarith

private theorem bridge {w : ℂ} (hw : ‖w‖ = 1) (hc : w^3 = -1) (hr : 0 ≤ w.re)
    {b : ℝ} (hb : 0 < b) (t : ℝ) :
    ‖primitive (b^2 : ℝ) (path w b t) - primitive (b^2 : ℝ) (leg w b t)‖ ≤
      b * Real.exp (-t/3) := by
  let u := leg w b t
  let v := leg (conj w) b (-t)
  have h := segment ((b^2 : ℝ) : ℂ) u v 1
  simp only [ofReal_one, mul_one] at h
  change ‖primitive _ (u+v) - primitive _ u‖ ≤ _
  rw [h]
  have H : ‖∫ s in (0 : ℝ)..1, v * integrand (b^2 : ℝ) (u+v*s)‖ ≤ ‖v‖ * |1-0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro s hs
    rw [norm_mul]
    apply mul_le_of_le_one_right (norm_nonneg _)
    rw [uIoc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] at hs
    apply decreasing (sq_nonneg b) (legs_mul hw b t) _ _ (leg_re hr hb.le _)
      (leg_re (w := conj w) (by simpa using hr) hb.le _) ⟨hs.1.le,hs.2⟩
    · rw [leg_cube hc, neg_re, ofReal_re]
      exact neg_nonpos.mpr (by positivity)
    · rw [leg_cube (cube_conj hc), neg_re, ofReal_re]
      exact neg_nonpos.mpr (by positivity)
  have hv : ‖v‖ = b * Real.exp (-t/3) := by
    change ‖conj w * ((b * Real.exp (-t/3) : ℝ) : ℂ)‖ = _
    rw [norm_mul,
      norm_conj, hw, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), one_mul]
  simpa only [hv, sub_zero, abs_one, mul_one] using H

private theorem end_limit {w : ℂ} (hw : ‖w‖ = 1) (hc : w^3 = -1) (hr : 0 ≤ w.re)
    {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t => primitive (b^2 : ℝ) (path w b t)) atTop (𝓝 (ray w (b^2 : ℝ))) := by
  have ht : Tendsto (fun t : ℝ => t/3) atTop atTop := tendsto_id.atTop_div_const (by norm_num)
  have hl := (ray_limit w ((b^2 : ℝ) : ℂ) hc).comp
    ((Real.tendsto_exp_atTop.comp ht).const_mul_atTop hb)
  have he : Tendsto (fun t : ℝ => b * Real.exp (-t/3)) atTop (𝓝 0) := by
    simpa [neg_div] using (Real.tendsto_exp_neg_atTop_nhds_zero.comp ht).const_mul b
  have hdiff := squeeze_zero_norm' (Eventually.of_forall (bridge hw hc hr hb)) he
  simpa only [Function.comp_def, sub_add_cancel, zero_add, leg] using hdiff.add hl

private theorem exponent (b t : ℝ) : (path upper b t)^3/3 - (b^2 : ℝ)*path upper b t =
    -((argument b * Real.cosh t : ℝ) : ℂ) := by
  have h := legs_mul norm_upper b t
  have h3 : (path upper b t)^3/3 - (b^2 : ℝ)*path upper b t =
      (leg upper b t)^3/3 + (leg (conj upper) b (-t))^3/3 := by
    unfold path
    rw [← h]
    ring
  rw [h3, leg_cube upper_cube, leg_cube (cube_conj upper_cube)]
  have hex (s : ℝ) : Real.exp (s/3)^3 = Real.exp s := by
    rw [← Real.exp_nat_mul]
    norm_num
    ring
  unfold argument
  simp only [mul_pow, hex, Real.cosh_eq]
  push_cast
  ring

private theorem deriv_leg (w : ℂ) (b t : ℝ) :
    HasDerivAt (leg w b) (leg w b t / 3) t := by
  have h := (((((hasDerivAt_id t).div_const 3).exp).const_mul b).ofReal_comp.const_mul w)
  convert h using 1
  · rfl
  simp [leg]
  ring

private theorem deriv_on_path (b t : ℝ) :
    HasDerivAt (fun s => primitive (b^2 : ℝ) (path upper b s))
      (b/3 * upper * term b (1/3) t - b/3 * conj upper * term b (-1/3) t) t := by
  have hd := (deriv_leg upper b t).add
    ((deriv_leg (conj upper) b (-t)).scomp t (hasDerivAt_id t).neg)
  have H := (deriv_primitive ((b^2 : ℝ) : ℂ) (path upper b t)).scomp t hd
  convert H using 1
  · rfl
  simp only [integrand, exponent, leg, neg_smul, one_smul, smul_eq_mul]
  unfold term
  rw [exp_add, exp_add,
    show (1/3 : ℂ)*t = ((t/3 : ℝ) : ℂ) by push_cast; ring,
    show (-1/3 : ℂ)*t = ((-t/3 : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_exp, ← ofReal_exp]
  simp only [ofReal_mul, neg_mul]
  ring

private theorem contour_value {b : ℝ} (hb : 0 < b) :
    ray upper (b^2 : ℝ) - ray (conj upper) (b^2 : ℝ) =
      (b/3 * (upper-conj upper)) * (2 * macdonald (1/3) (argument b)) := by
  have hr : 0 ≤ upper.re := by rw [upper_eq]; simp
  have htop := end_limit norm_upper upper_cube hr hb
  have hbot := (end_limit (w := conj upper) (by rw [norm_conj, norm_upper]) (cube_conj upper_cube)
    (by simpa using hr) hb).comp tendsto_neg_atBot_atTop
  have hsw (t : ℝ) : path (conj upper) b (-t) = path upper b t := by simp [path, add_comm]
  change Tendsto (fun t : ℝ => primitive (b^2 : ℝ) (path (conj upper) b (-t))) _ _ at hbot
  simp only [hsw] at hbot
  have hpos : 0 < argument b := by unfold argument; positivity
  have hi (ν : ℂ) : Integrable (term b ν) := integrable_macdonald ν (argument b) hpos
  have H := integral_of_hasDerivAt_of_tendsto (deriv_on_path b)
    (((hi _).const_mul _).sub ((hi _).const_mul _)) hbot htop
  rw [integral_sub ((hi _).const_mul _) ((hi _).const_mul _), integral_const_mul,
    integral_const_mul] at H
  have ht (ν : ℂ) : (∫ s, term b ν s) = 2 * macdonald ν (argument b) := by
    unfold term macdonald
    ring
  rw [ht, ht, show (-1/3 : ℂ) = -(1/3) by ring, macdonald_neg_order] at H
  rw [← H]
  ring

/-- For positive b, the positive-argument Airy profile at b² is K of order one third
at the synchrotron spectral argument 2b³/3. -/
theorem ai_sq_macdonald {b : ℝ} (hb : 0 < b) :
    ai (b^2 : ℝ) = b / ((√3 : ℝ) * π) * macdonald (1/3) (2*b^3/3 : ℝ) := by
  rw [ai, contour_value hb]
  have h : upper - conj upper = (√3 : ℝ) * I := by
    rw [upper_eq]
    simp only [map_div₀, map_add, map_mul, map_one, conj_ofReal, conj_I, map_ofNat]
    ring
  rw [h]
  unfold argument
  have hs : ((√3 : ℝ) : ℂ)^2 = 3 := by
    rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  field_simp [Real.pi_ne_zero, I_ne_zero]
  linear_combination (b : ℂ) * macdonald (1/3) (2*b^3/3 : ℝ) * hs

/-- The derivative of the Airy profile gives K of order two thirds, with the
same spectral argument and gamma normalization. -/
theorem deriv_ai_sq_macdonald {b : ℝ} (hb : 0 < b) :
    deriv ai (b^2 : ℝ) = -(b^2 : ℝ) / ((√3 : ℝ) * π) * macdonald (2/3) (2*b^3/3 : ℝ) := by
  let z := argument b
  let ν := (1/3 : ℂ)
  let c := ((√3 : ℝ) : ℂ) * π
  have hz : 0 < z := by dsimp [z, argument]; positivity
  have hc : c ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr (by positivity))
    (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have ha := (hasDerivAt_ai (b^2 : ℝ)).differentiableAt.hasDerivAt.comp_ofReal.scomp b
    ((hasDerivAt_id b).pow 2)
  have harg : HasDerivAt argument (2*b^2) b := by
    convert (((hasDerivAt_id b).pow 3).const_mul 2).div_const 3 using 1
    · rfl
    dsimp
    ring
  have hk := (hasDerivAt_macdonald ν (z : ℂ) hz).comp_ofReal.scomp b harg
  have hright := (((hasDerivAt_id b).ofReal_comp.div_const c).mul hk)
  have he : (fun x : ℝ => ai (x^2 : ℝ)) =ᶠ[𝓝 b]
      (fun x : ℝ => (x : ℂ)/c * macdonald ν (argument x)) := by
    filter_upwards [lt_mem_nhds hb] with x hx
    exact ai_sq_macdonald hx
  have H := (ha.congr_of_eventuallyEq he.symm).unique hright
  have hrec := macdonald_recurrence ν (z : ℂ) hz
  have hν : ν - 1 = -(2/3 : ℂ) := by dsimp [ν]; ring
  rw [hν, macdonald_neg_order] at hrec
  let K (μ : ℂ) := macdonald μ (z : ℂ)
  have H₁ : 2*(b : ℂ)*deriv ai (b^2 : ℝ) = 1/c*K ν +
      b/c * (2*(b : ℂ)^2) * (-(K (ν+1) + K (2/3))/2) := by
    simp only [Complex.real_smul, id_eq, ofReal_one, mul_one, Nat.cast_ofNat, hν,
      macdonald_neg_order, Function.comp_apply] at H
    push_cast at H
    simp only [K, z, ofReal_pow] at H ⊢
    convert H using 1 <;> ring
  have hez : (z : ℂ) = 2*(b : ℂ)^3/3 := by dsimp [z, argument]; push_cast; ring
  have H₂ : 2*(b : ℂ)^3*(K (ν+1)-K (2/3)) = 2*K ν := by
    change (z : ℂ) * (K (ν+1) - K (2/3)) = 2*ν*K ν at hrec
    rw [hez] at hrec
    dsimp only [ν] at hrec ⊢
    linear_combination 3 * hrec
  have hb' : (b : ℂ) ≠ 0 := ofReal_ne_zero.mpr hb.ne'
  change deriv ai (b^2 : ℝ) = -(↑(b^2) : ℂ)/c * K (2/3)
  rw [ofReal_pow, div_mul_eq_mul_div, eq_div_iff hc]
  apply mul_left_cancel₀ hb'
  field_simp [hc] at H₁
  push_cast at H₁ ⊢
  linear_combination H₁ / 2 - H₂ / 4

end ProjectAinos.SpecialFunctions.Airy
