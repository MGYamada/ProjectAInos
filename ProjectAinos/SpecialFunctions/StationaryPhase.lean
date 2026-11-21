/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.QuadraticPhase
public import ProjectAinos.SmoothAlgebra.DividedDifference
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! # Local stationary phase for a smooth real phase in one variable

Twice taking the smooth divided difference factors out the square of the distance
to a critical point. Where the second derivative is positive, its smooth square root
gives a local coordinate. Changing variables in the integral then reduces the leading
term to the Fresnel integral.
-/

@[expose] public section
noncomputable section

open Complex Filter MeasureTheory Set
open scoped Real Topology ContDiff ComplexConjugate
namespace ProjectAinos.SpecialFunctions.Oscillatory
open SmoothAlgebra

private def factor (ψ : ℝ → ℝ) (a x : ℝ) := dividedDifference₂ ψ (a,a,x)

private theorem factor_self (ψ : ℝ → ℝ) (a : ℝ) :
    factor ψ a a = deriv (deriv ψ) a / 2 := by
  simp only [factor, dividedDifference₂, sub_self, mul_zero, add_zero,
    intervalIntegral.integral_const, sub_zero, one_smul]
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_sub (g := fun t : ℝ => t)
    (continuous_const.intervalIntegrable ..) (continuous_id.intervalIntegrable ..)]
  simp [integral_id]
  ring

private theorem factor_phase {ψ : ℝ → ℝ} {a : ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (ha : deriv ψ a = 0) (x : ℝ) : ψ x - ψ a = (x-a)^2 * factor ψ a x := by
  have h := sub_eq_mul_dividedDifference (hψ.of_le (by simp)) a x
  have h' := dividedDifference_sub hψ a a x
  rw [dividedDifference_self, ha, sub_zero] at h'
  rw [h'] at h
  unfold factor
  linear_combination -h

private theorem normal_coordinate {ψ : ℝ → ℝ} {a : ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (ha : deriv ψ a = 0) (hpos : 0 < deriv (deriv ψ) a) :
    ∃ g : ℝ → ℝ, g 0 = a ∧ deriv g 0 = (√(deriv (deriv ψ) a / π))⁻¹ ∧
      ∀ᶠ t in 𝓝 0, ContDiffAt ℝ 2 g t ∧ 0 < deriv g t ∧ ψ (g t) - ψ a = π / 2 * t^2 := by
  let Q := factor ψ a
  have hQ : ContDiff ℝ ∞ Q := (contDiff_dividedDifference₂ hψ).comp
    (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))
  have hQa : Q a = deriv (deriv ψ) a / 2 := factor_self ψ a
  have hp : 0 < Q a := by rw [hQa]; positivity
  let k (x : ℝ) := √(2*Q x/π)
  have hk : ContDiffAt ℝ 2 k a := by
    have h : ContDiffAt ℝ 2 (fun t => 2*Q t/π) a :=
      ((contDiffAt_const.mul (hQ.contDiffAt.of_le (by simp))).div_const _)
    exact h.sqrt (by positivity)
  let f (x : ℝ) := (x-a)*k x
  have hf : ContDiffAt ℝ 2 f a := (contDiffAt_id.sub contDiffAt_const).mul hk
  have hfa : f a = 0 := by simp [f]
  have hka : k a = √(deriv (deriv ψ) a / π) := by unfold k; rw [hQa]; congr 1; ring
  have hkp : 0 < k a := by rw [hka]; positivity
  have hd : HasDerivAt f (k a) a := by
    simpa [f, Pi.mul_def] using (((hasDerivAt_id a).sub_const a).mul
      (hk.differentiableAt (by norm_num)).hasDerivAt)
  let e := hf.toOpenPartialHomeomorph f (hd.hasFDerivAt_equiv hkp.ne') (by norm_num)
  have hsrc : a ∈ e.source := ContDiffAt.mem_toOpenPartialHomeomorph_source ..
  have htarg : f a ∈ e.target := e.map_source hsrc
  have hei : e.symm (f a) = a := e.left_inv hsrc
  have hde : HasDerivAt e (k a) (e.symm (f a)) := hei.symm ▸ hd
  have hce : ContDiffAt ℝ 2 e (e.symm (f a)) := hei.symm ▸ hf
  have hg := e.contDiffAt_symm_deriv hkp.ne' htarg hde hce
  have hg' := e.hasDerivAt_symm htarg hkp.ne' hde
  have hg0 : e.symm 0 = a := hfa ▸ e.left_inv hsrc
  rw [hfa] at hg hg' htarg
  have hdpos := ((hg.derivWithin (m := 1) (by norm_num)).continuousAt).eventually
    (lt_mem_nhds (show 0 < deriv e.symm 0 by rw [hg'.deriv]; positivity))
  have hpos' : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < Q (e.symm t) :=
    (hQ.continuous.continuousAt.comp hg.continuousAt).eventually
      (lt_mem_nhds (by rwa [hg0] : 0 < Q (e.symm 0)))
  refine ⟨e.symm, hg0, hg'.deriv.trans (by rw [hka]), ?_⟩
  filter_upwards [hg.eventually (by norm_num), hdpos, hpos', e.open_target.mem_nhds htarg]
    with t hs hd' hq ht
  refine ⟨hs,hd',?_⟩
  have hft : f (e.symm t) = t := e.right_inv ht
  apply Eq.trans _ (congrArg (fun s : ℝ => π/2*s^2) hft)
  rw [factor_phase hψ ha]
  change (e.symm t - a)^2 * Q (e.symm t) = π/2 * ((e.symm t - a) * k (e.symm t))^2
  dsimp only [k]
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  field_simp

private def quadraticWave (r t : ℝ) := exp (((π/2*(r*t)^2 : ℝ) : ℂ) * I)

private theorem both_sides {s t : ℝ} (hs : s < 0) (ht : 0 < t) {W : ℝ → ℂ}
    (hW : ∀ x ∈ Icc s t, ContDiffAt ℝ 1 W x) :
    Tendsto (fun r : ℝ => (r : ℂ) * ∫ x in s..t, W x * quadraticWave r x)
      atTop (𝓝 (W 0 * (1 + I))) := by
  have hp : Icc 0 t ⊆ Icc s t := Icc_subset_Icc_left hs.le
  have hn : MapsTo (fun x : ℝ => -x) (Icc 0 (-s)) (Icc s t) :=
    fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hpos := quadratic_endpoint ht (A := W) (D := deriv W)
    (fun x hx => ((hW x (hp hx)).differentiableAt one_ne_zero).hasDerivAt)
    (fun x hx => ((hW x (hp hx)).derivWithin (m := 0) (by norm_num))
      |>.continuousAt.continuousWithinAt)
  let V (x : ℝ) := W (-x)
  have hv (x : ℝ) (hx : x ∈ Icc 0 (-s)) : ContDiffAt ℝ 1 V x :=
    (hW (-x) (hn hx)).comp x (by fun_prop)
  have hneg := quadratic_endpoint (neg_pos.mpr hs) (A := V) (D := deriv V)
    (fun x hx => ((hv x hx).differentiableAt one_ne_zero).hasDerivAt)
    (fun x hx => ((hv x hx).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt)
  have he (r : ℝ) : (∫ x in 0..-s, V x * quadraticWave r x) =
      ∫ x in s..0, W x * quadraticWave r x := by
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := -s)
      (fun x => W x * quadraticWave r x)
    simpa [V, quadraticWave, mul_neg] using h
  have hw (r : ℝ) : ContinuousOn (fun x => W x * quadraticWave r x) (Icc s t) :=
    (fun x hx => (hW x hx).continuousAt.continuousWithinAt.mul
      ((by unfold quadraticWave; fun_prop : Continuous (quadraticWave r)).continuousWithinAt))
  have hj (r : ℝ) := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (a := s) (b := 0) (c := t)
    ((hw r).mono (by rw [uIcc_of_le hs.le]; exact Icc_subset_Icc_right ht.le) |>.intervalIntegrable)
    ((hw r).mono (by rwa [uIcc_of_le ht.le]) |>.intervalIntegrable)
  change Tendsto (fun r : ℝ => (r : ℂ) * ∫ x in 0..-s, V x * quadraticWave r x) _ _ at hneg
  change Tendsto (fun r : ℝ => (r : ℂ) * ∫ x in 0..t, W x * quadraticWave r x) _ _ at hpos
  have H := hneg.add hpos
  simp only [he, ← mul_add, hj] at H
  convert H using 2
  simp only [V, neg_zero]
  ring

private def oscillation (ψ : ℝ → ℝ) (a r x : ℝ) :=
  exp (((r^2 * (ψ x - ψ a) : ℝ) : ℂ) * I)

/-- Every sufficiently small interval containing a nondegenerate local minimum gives the
same leading term for a smooth phase and a continuously differentiable complex amplitude.
Subtracting the critical value removes the constant phase factor. -/
theorem stationary_minimum {ψ : ℝ → ℝ} {a : ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (ha : deriv ψ a = 0) (hp : 0 < deriv (deriv ψ) a) :
    ∃ l < a, ∃ b > a, ∀ s ∈ Ico l a, ∀ t ∈ Ioc a b, ∀ A : ℝ → ℂ, ContDiff ℝ 1 A →
      Tendsto (fun r : ℝ => (r : ℂ) * ∫ x in s..t,
        A x * exp (((r^2 * (ψ x - ψ a) : ℝ) : ℂ) * I)) atTop
        (𝓝 (((√(deriv (deriv ψ) a / π))⁻¹ : ℝ) * A a * (1 + I))) := by
  obtain ⟨g,hg0,hd0,hm⟩ := normal_coordinate hψ ha hp
  obtain ⟨p,q,hpq,hpq'⟩ := hm.exists_Ioo_subset
  let l := p/2
  let b := q/2
  have hl : l < 0 := by dsimp [l]; linarith [hpq.1]
  have hb : 0 < b := by dsimp [b]; linarith [hpq.2]
  have hg (x : ℝ) (hx : x ∈ Icc l b) := hpq' (a := x)
    (show x ∈ Ioo p q from ⟨by dsimp [l] at hx; linarith [hx.1, hpq.1],
      by dsimp [b] at hx; linarith [hx.2, hpq.2]⟩)
  have hc : ContinuousOn g (Icc l b) := fun x hx => (hg x hx).1.continuousAt.continuousWithinAt
  have hmono := strictMonoOn_of_deriv_pos (D := Icc l b) (convex_Icc l b) hc
    (fun x hx => (hg x (interior_subset hx)).2.1)
  have h0 : 0 ∈ Icc l b := ⟨hl.le,hb.le⟩
  have hlb := hl.le.trans hb.le
  refine ⟨g l, hg0 ▸ hmono (left_mem_Icc.mpr hlb) h0 hl,
    g b, hg0 ▸ hmono h0 (right_mem_Icc.mpr hlb) hb, ?_⟩
  intro s hs t ht A hA
  obtain ⟨u,hu,hus⟩ := intermediate_value_Icc hl.le (hc.mono (Icc_subset_Icc_right hb.le))
    (show s ∈ Icc (g l) (g 0) by rw [hg0]; exact ⟨hs.1,hs.2.le⟩)
  obtain ⟨v,hv,hvt⟩ := intermediate_value_Icc hb.le (hc.mono (Icc_subset_Icc_left hl.le))
    (show t ∈ Icc (g 0) (g b) by rw [hg0]; exact ⟨ht.1.le,ht.2⟩)
  have hu' : u < 0 := hu.2.lt_of_ne (fun he => hs.2.ne (by rw [← hus, he, hg0]))
  have hv' : 0 < v := hv.1.lt_of_ne (fun he => ht.1.ne (by rw [← hvt, ← he, hg0]))
  have huv := hu'.le.trans hv'.le
  have hsub := Icc_subset_Icc hu.1 hv.2
  let W (x : ℝ) := ((deriv g x : ℝ) : ℂ) * A (g x)
  have hw (x : ℝ) (hx : x ∈ Icc u v) : ContDiffAt ℝ 1 W x := by
    have h := (hg x (hsub hx)).1
    exact (ofRealCLM.contDiff.contDiffAt.comp x (h.derivWithin (by norm_num))).mul
      (hA.contDiffAt.comp x (h.of_le (by norm_num)))
  have H := both_sides hu' hv' hw
  have he (r : ℝ) : (∫ x in u..v, W x * quadraticWave r x) =
      ∫ x in s..t, A x * oscillation ψ a r x := by
    have h := intervalIntegral.integral_deriv_smul_comp (a := u) (b := v)
      (g := fun x => A x * oscillation ψ a r x)
      (fun x hx => ((hg x (hsub (uIcc_of_le huv ▸ hx))).1.differentiableAt
        (by norm_num)).hasDerivAt)
      (fun x hx => ((hg x (hsub (uIcc_of_le huv ▸ hx))).1.derivWithin (m := 1) (by norm_num))
        |>.continuousAt.continuousWithinAt)
      (hA.continuous.mul (by unfold oscillation; fun_prop))
    rw [hus, hvt] at h
    rw [← h]
    apply intervalIntegral.integral_congr
    intro x hx
    change W x * quadraticWave r x = deriv g x • (A (g x) * oscillation ψ a r (g x))
    dsimp only [W]
    rw [Complex.real_smul, oscillation, (hg x (hsub (uIcc_of_le huv ▸ hx))).2.2]
    rw [quadraticWave, show r^2*(π/2*x^2) = π/2*(r*x)^2 by ring]
    ring
  simp only [he, W, hd0, hg0, oscillation] at H
  exact H

/-- The corresponding local formula at a nondegenerate maximum has the conjugate
Fresnel phase. Both signs allow arbitrary continuously differentiable complex amplitudes. -/
theorem stationary_maximum {ψ : ℝ → ℝ} {a : ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (ha : deriv ψ a = 0) (hp : deriv (deriv ψ) a < 0) :
    ∃ l < a, ∃ b > a, ∀ s ∈ Ico l a, ∀ t ∈ Ioc a b, ∀ A : ℝ → ℂ, ContDiff ℝ 1 A →
      Tendsto (fun r : ℝ => (r : ℂ) * ∫ x in s..t,
        A x * exp (((r^2 * (ψ x - ψ a) : ℝ) : ℂ) * I)) atTop
        (𝓝 (((√(-deriv (deriv ψ) a / π))⁻¹ : ℝ) * A a * (1 - I))) := by
  have hd : deriv (-ψ) = -deriv ψ := deriv.neg'
  have he : deriv (deriv (-ψ)) = -deriv (deriv ψ) := by rw [hd]; exact deriv.neg'
  obtain ⟨l,hl,b,hb,h⟩ := stationary_minimum (ψ := -ψ) hψ.neg
    (a := a) (by rw [hd]; simp [ha]) (by rw [he]; simpa)
  refine ⟨l,hl,b,hb,?_⟩
  intro s hs t ht A hA
  have H := h s hs t ht (fun x => conj (A x)) (Complex.conjCLE.contDiff.comp hA)
  have H' := (continuous_conj.tendsto _).comp H
  have hh (r : ℝ) : conj (∫ x in s..t, conj (A x) * oscillation (-ψ) a r x) =
      ∫ x in s..t, A x * oscillation ψ a r x := by
    rw [intervalIntegral.integral_of_le (hs.2.le.trans ht.1.le), ← integral_conj,
      intervalIntegral.integral_of_le (hs.2.le.trans ht.1.le)]
    apply integral_congr_ae
    filter_upwards with x
    rw [map_mul, conj_conj, oscillation, ← exp_conj, map_mul, conj_ofReal, conj_I, oscillation]
    simp only [Pi.neg_apply]
    congr 2
    push_cast
    ring
  change Tendsto (fun r : ℝ => conj (r * ∫ x in s..t, conj (A x) * oscillation (-ψ) a r x)) _ _
    at H'
  simp only [map_mul, conj_ofReal, hh, he, Pi.neg_apply, conj_conj, map_add,
    map_one, conj_I, ← sub_eq_add_neg] at H'
  exact H'

end ProjectAinos.SpecialFunctions.Oscillatory
