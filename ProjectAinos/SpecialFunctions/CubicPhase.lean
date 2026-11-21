/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.AiryIntegral
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic

/-! # Airy asymptotics at two coalescing stationary points

For a cubic phase with large parameter r³ and linear perturbation u/r², the stationary
points merge at zero. The scaled error tends to zero for every bounded moving u, including
parameters that cross zero or have no limit. The contour tail bound controls the boundary
terms uniformly; integration by parts transfers the remaining error to the amplitude derivative.
-/

@[expose] public section
noncomputable section

open Complex Filter MeasureTheory Set
open scoped Real Topology ComplexConjugate
namespace ProjectAinos.SpecialFunctions.Oscillatory
open Airy

private def wave (x t : ℝ) := exp (((t^3/3+x*t : ℝ) : ℂ) * I)
private def remainder (x R : ℝ) := cubicIntegral x R - cubicLimit x
private def bound (B R : ℝ) := 3/R^2 +
  ∫ t : ℝ in Ioi (2/√3*R), Real.exp ((B^2+9)/2) * Real.exp (-t^2)

private theorem bound_zero (B : ℝ) : Tendsto (bound B) atTop (𝓝 0) := by
  have hp : Tendsto (fun R : ℝ => R^2) atTop atTop := tendsto_pow_atTop two_ne_zero
  have hq : Tendsto (fun R : ℝ => 3/R^2) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hp
  have ht : Tendsto (fun R : ℝ => 2/√3*R) atTop atTop :=
    tendsto_id.const_mul_atTop (by positivity : 0 < 2/√(3 : ℝ))
  unfold bound
  simpa only [add_zero] using hq.add (tendsto_integral_Ioi_zero (μ := volume)
    (f := fun t : ℝ => Real.exp ((B^2+9)/2) * Real.exp (-t^2)) ht)

private theorem tail_eventually (B : ℝ) :
    ∀ᶠ R : ℝ in atTop, ∀ x : ℝ, |x| ≤ B → ‖remainder x R‖ ≤ bound B R := by
  have hp : Tendsto (fun R : ℝ => R^2) atTop atTop := tendsto_pow_atTop two_ne_zero
  filter_upwards [eventually_gt_atTop (0 : ℝ), hp.eventually_ge_atTop (3*B)] with R hR h
  exact fun _ hx => cubic_tail hx hR h

private theorem moving_tail {B : ℝ} {u v : ℝ → ℝ}
    (hu : ∀ᶠ r in atTop, |u r| ≤ B) (hv : Tendsto v atTop atTop) :
    Tendsto (fun r => remainder (u r) (v r)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ ((bound_zero B).comp hv)
  filter_upwards [hu, hv.eventually (tail_eventually B)] with r hx h
  exact h _ hx

private theorem derivative (x t : ℝ) : HasDerivAt (cubicIntegral x) (wave x t) t := by
  have hc : Continuous (wave x) := by unfold wave; fun_prop
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable ..)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

private theorem uniform_bound (B : ℝ) :
    ∃ C : ℝ, ∀ x R : ℝ, |x| ≤ B → 0 ≤ R → ‖remainder x R‖ ≤ C := by
  have hc : Continuous cubicLimit := continuous_const.mul (continuous_conj.comp
    ((continuous_iff_continuousAt.mpr fun z => (hasDerivAt_ray upper z).continuousAt).comp
      continuous_ofReal))
  obtain ⟨L,hL⟩ := (isCompact_Icc (a := -B) (b := B)).exists_bound_of_continuousOn hc.continuousOn
  obtain ⟨T,hT⟩ := eventually_atTop.mp ((tail_eventually B).and
    ((bound_zero B).eventually_lt_const zero_lt_one))
  refine ⟨max (T+L) 1, fun x R hx hR => ?_⟩
  rcases le_total T R with h | h
  · exact (((hT R h).1 _ hx).trans (hT R h).2.le).trans (le_max_right ..)
  · have hI : ‖cubicIntegral x R‖ ≤ R := by
      simpa only [cubicIntegral, wave, sub_zero, abs_of_nonneg hR, one_mul] using
        intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := R) (C := 1)
          (f := wave x) (fun t _ => by rw [wave, norm_exp, mul_I_re, ofReal_im]; simp)
    exact (norm_sub_le _ _).trans ((add_le_add (hI.trans h) (hL x (abs_le.mp hx))).trans
      (le_max_left ..))

private theorem weighted {b B : ℝ} (hb : 0 < b) {u : ℝ → ℝ}
    (hu : ∀ᶠ r in atTop, |u r| ≤ B) (D : ℝ → ℂ) (hD : ContinuousOn D (Icc 0 b)) :
    Tendsto (fun r : ℝ => ∫ t in 0..b, D t * remainder (u r) (r*t)) atTop (𝓝 0) := by
  obtain ⟨C,hC⟩ := uniform_bound B
  have hm := measurableSet_Ioc (a := (0 : ℝ)) (b := b)
  have hd := hD.mono (Ioc_subset_Icc_self (a := (0 : ℝ)) (b := b))
  have hc (x : ℝ) : Continuous (remainder x) :=
    (continuous_iff_continuousAt.mpr fun t => (derivative x t).continuousAt).sub continuous_const
  simp_rw [intervalIntegral.integral_of_le hb.le]
  rw [← integral_zero (α := ℝ) (G := ℂ) (μ := volume.restrict (Ioc 0 b))]
  apply tendsto_integral_filter_of_dominated_convergence (fun t => ‖D t‖ * C)
  · exact Eventually.of_forall fun r => (hd.mul
      ((hc _).comp (continuous_const.mul continuous_id)).continuousOn).aestronglyMeasurable hm
  · filter_upwards [eventually_ge_atTop (0 : ℝ), hu] with r hr hx
    filter_upwards [ae_restrict_mem hm] with t ht
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC _ _ hx (mul_nonneg hr ht.1.le)) (norm_nonneg _)
  · exact (hD.norm.mul continuousOn_const).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  · filter_upwards [ae_restrict_mem hm] with t ht
    simpa using (moving_tail hu (tendsto_id.atTop_mul_const ht.1)).const_mul (D t)

/-- Uniform one-sided asymptotics throughout every bounded interval of cubic unfolding
parameters. The amplitude and its continuous derivative may be complex. -/
theorem cubic_endpoint {b B : ℝ} (hb : 0 < b) {u : ℝ → ℝ} (hu : ∀ᶠ r in atTop, |u r| ≤ B)
    {A D : ℝ → ℂ} (hA : ∀ t ∈ Icc 0 b, HasDerivAt A (D t) t) (hD : ContinuousOn D (Icc 0 b)) :
    Tendsto (fun r : ℝ => (r : ℂ) * (∫ t in 0..b,
      A t * exp ((((r*t)^3/3+u r*(r*t) : ℝ) : ℂ) * I)) - A 0 * cubicLimit (u r))
      atTop (𝓝 0) := by
  have hb' := uIcc_of_le hb.le
  have h (r : ℝ) : (r : ℂ) * (∫ t in 0..b, A t * wave (u r) (r*t)) - A 0 * cubicLimit (u r) =
      A b * remainder (u r) (r*b) - ∫ t in 0..b, D t * remainder (u r) (r*t) := by
    have du (t : ℝ) : HasDerivAt (fun s => remainder (u r) (r*s)) (r * wave (u r) (r*t)) t := by
      simpa [remainder, Function.comp_def, Complex.real_smul, mul_comm (r : ℂ)] using
        (((derivative (u r) (r*t)).scomp t ((hasDerivAt_id t).const_mul r)).sub_const
          (cubicLimit (u r)))
    have hp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := b)
      (fun t ht => hA t (hb' ▸ ht)) (fun t _ => du t)
      ((hb'.symm ▸ hD).intervalIntegrable)
      (Continuous.intervalIntegrable (by unfold wave; fun_prop) ..)
    have hzero : remainder (u r) (r*0) = -cubicLimit (u r) := by simp [remainder, cubicIntegral]
    rw [hzero] at hp
    rw [← intervalIntegral.integral_const_mul]
    have he (t : ℝ) : (r : ℂ) * (A t * wave (u r) (r*t)) = A t * (r * wave (u r) (r*t)) := by ring
    simp_rw [he, hp]
    ring
  have he := (moving_tail hu (tendsto_id.atTop_mul_const hb)).const_mul (A b)
  simpa only [id_eq, ← h, wave, mul_zero, sub_zero] using he.sub (weighted hb hu D hD)

private theorem wave_neg (x t : ℝ) : wave x (-t) = conj (wave x t) := by
  rw [wave, wave, ← exp_conj, map_mul, conj_ofReal, conj_I]
  congr 1
  push_cast
  ring

/-- At a pair of coalescing critical points of the canonical cubic phase the full leading
profile is 2π Ai(u) times the value of the amplitude at the collision point. The error
tends to zero even for bounded unfolding parameters that vary with the large parameter. -/
theorem cubic_coalescence {b B : ℝ} (hb : 0 < b) {u : ℝ → ℝ}
    (hu : ∀ᶠ r in atTop, |u r| ≤ B) {A D : ℝ → ℂ}
    (hA : ∀ t ∈ Icc (-b) b, HasDerivAt A (D t) t) (hD : ContinuousOn D (Icc (-b) b)) :
    Tendsto (fun r : ℝ => (r : ℂ) * (∫ t in -b..b,
      A t * exp ((((r*t)^3/3+u r*(r*t) : ℝ) : ℂ) * I)) - A 0 * (2*π*ai (u r)))
      atTop (𝓝 0) := by
  have hs : Icc 0 b ⊆ Icc (-b) b := Icc_subset_Icc_left (by linarith)
  have hn : MapsTo (fun t : ℝ => -t) (Icc 0 b) (Icc (-b) b) :=
    fun t ht => ⟨neg_le_neg ht.2, by linarith [ht.1]⟩
  have hp := cubic_endpoint hb hu (fun t ht => hA t (hs ht)) (hD.mono hs)
  have ha (t : ℝ) (ht : t ∈ Icc 0 b) :
      HasDerivAt (fun s => conj (A (-s))) (conj (-D (-t))) t := by
    simpa [Function.comp_def] using ((hA _ (hn ht)).scomp t (hasDerivAt_id t).neg).star
  have hd : ContinuousOn (fun t => conj (-D (-t))) (Icc 0 b) :=
    continuous_conj.continuousOn.comp ((hD.comp continuous_neg.continuousOn hn).neg)
      (mapsTo_univ ..)
  have hq := (continuous_conj.tendsto (0 : ℂ)).comp (cubic_endpoint hb hu ha hd)
  have he (r : ℝ) :
      conj (∫ t in 0..b, conj (A (-t)) * wave (u r) (r*t)) =
        ∫ t in -b..0, A t * wave (u r) (r*t) := by
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := b)
      (fun t => A t * wave (u r) (r*t))
    rw [neg_zero] at h
    rw [← h, intervalIntegral.integral_of_le hb.le, intervalIntegral.integral_of_le hb.le,
      ← integral_conj]
    simp only [map_mul, conj_conj, mul_neg, wave_neg]
  have hc : ContinuousOn A (Icc (-b) b) := fun t ht => (hA t ht).continuousAt.continuousWithinAt
  have hj (r : ℝ) := (hc.mul (g := fun t => wave (u r) (r*t))
    (Continuous.continuousOn (by unfold wave; fun_prop)))
  have hi (r : ℝ) := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (a := -b) (b := 0) (c := b)
    ((hj r).mono (by rw [uIcc_of_le (by linarith : -b ≤ 0)]; exact Icc_subset_Icc_right hb.le)
      |>.intervalIntegrable)
    ((hj r).mono (by rwa [uIcc_of_le hb.le]) |>.intervalIntegrable)
  change Tendsto (fun r : ℝ => conj (r * (∫ t in 0..b, conj (A (-t)) * wave (u r) (r*t)) -
    conj (A (-0)) * cubicLimit (u r))) _ _ at hq
  simp only [map_sub, map_mul, conj_ofReal, he, neg_zero, conj_conj, map_zero] at hq
  change Tendsto (fun r : ℝ => r * (∫ t in 0..b, A t * wave (u r) (r*t)) -
    A 0 * cubicLimit (u r)) _ _ at hp
  have H := hq.add hp
  rw [add_zero] at H
  apply H.congr
  intro r
  simp only [Pi.mul_apply] at hi
  simp only [wave] at hi ⊢
  rw [← cubicLimit_add_conj, ← hi]
  ring

end ProjectAinos.SpecialFunctions.Oscillatory
