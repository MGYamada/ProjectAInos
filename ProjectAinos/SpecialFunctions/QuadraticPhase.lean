/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.Fresnel
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic

/-! # Leading term at a quadratic stationary point

Integrate the amplitude by parts against the scaled Fresnel primitive. That primitive stays
bounded and converges at every positive point. Dominated convergence cancels the far endpoint
term and leaves precisely the amplitude at the stationary endpoint.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Set Complex
open scoped Topology Real
namespace ProjectAinos.SpecialFunctions.Oscillatory

private abbrev limit : ℂ := (1 + I) / 2
private def chirp (t : ℝ) := exp (((π / 2 * t ^ 2 : ℝ) : ℂ) * I)

private theorem cont : Continuous Fresnel.integral :=
  continuous_iff_continuousAt.mpr fun x => (Fresnel.hasDerivAt_integral x).continuousAt

private theorem bounded : ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → ‖Fresnel.integral t‖ ≤ C := by
  obtain ⟨a,ha⟩ := eventually_atTop.mp (Fresnel.tendsto_integral_atTop.norm.eventually_lt_const
    (show ‖limit‖ < ‖limit‖ + 1 by linarith))
  obtain ⟨M,hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := a)).exists_bound_of_continuousOn
    cont.continuousOn
  refine ⟨max M (‖limit‖ + 1), fun t ht => ?_⟩
  rcases le_total t a with h | h
  · exact (hM t ⟨ht,h⟩).trans (le_max_left ..)
  · exact (ha t h).le.trans (le_max_right ..)

private theorem weighted_limit {b : ℝ} (hb : 0 < b) (D : ℝ → ℂ) (hD : ContinuousOn D (Icc 0 b)) :
    Tendsto (fun r : ℝ => ∫ t in 0..b, D t * Fresnel.integral (r * t)) atTop
      (𝓝 ((∫ t in 0..b, D t) * limit)) := by
  obtain ⟨C,hC⟩ := bounded
  have hm := measurableSet_Ioc (a := (0 : ℝ)) (b := b)
  have hd := hD.mono (Ioc_subset_Icc_self (a := (0 : ℝ)) (b := b))
  simp_rw [intervalIntegral.integral_of_le hb.le, ← integral_mul_const]
  apply tendsto_integral_filter_of_dominated_convergence (fun t => ‖D t‖ * C)
  · exact Eventually.of_forall fun r => (hd.mul
      (cont.comp (continuous_const.mul continuous_id)).continuousOn).aestronglyMeasurable hm
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    filter_upwards [ae_restrict_mem hm] with t ht
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC _ (mul_nonneg hr ht.1.le)) (norm_nonneg _)
  · exact (hD.norm.mul continuousOn_const).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  · filter_upwards [ae_restrict_mem hm] with t ht
    exact (Fresnel.tendsto_integral_atTop.comp (tendsto_id.atTop_mul_const ht.1)).const_mul (D t)

/-- One-sided stationary phase with quadratic phase and an arbitrary continuously differentiable
complex amplitude. The scaling parameter tends to positive infinity. -/
theorem quadratic_endpoint {b : ℝ} (hb : 0 < b) {A D : ℝ → ℂ}
    (hA : ∀ t ∈ Icc 0 b, HasDerivAt A (D t) t) (hD : ContinuousOn D (Icc 0 b)) :
    Tendsto (fun r : ℝ => (r : ℂ) * ∫ t in 0..b,
      A t * exp (((π / 2 * (r * t) ^ 2 : ℝ) : ℂ) * I)) atTop (𝓝 (A 0 * ((1 + I) / 2))) := by
  have hb' := show Set.uIcc 0 b = Icc 0 b from uIcc_of_le hb.le
  have h (r : ℝ) : (r : ℂ) * ∫ t in 0..b, A t * chirp (r * t) =
      A b * Fresnel.integral (r * b) - ∫ t in 0..b, D t * Fresnel.integral (r * t) := by
    have du (t : ℝ) : HasDerivAt (fun s => Fresnel.integral (r * s)) (r * chirp (r * t)) t := by
      simpa [chirp, Function.comp_def, Complex.real_smul, mul_comm (r : ℂ)] using
        (Fresnel.hasDerivAt_integral (r * t)).scomp t ((hasDerivAt_id t).const_mul r)
    have hp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := b)
      (fun t ht => hA t (hb' ▸ ht)) (fun t _ => du t)
      ((hb'.symm ▸ hD).intervalIntegrable)
      (Continuous.intervalIntegrable (by unfold chirp; fun_prop) ..)
    simp only [mul_zero, Fresnel.integral_zero, sub_zero] at hp
    rw [← hp, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun t _ => by ring
  have he := (Fresnel.tendsto_integral_atTop.comp
    (tendsto_id.atTop_mul_const hb)).const_mul (A b)
  have H := he.sub (weighted_limit hb D hD)
  have hd := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := b)
    (fun t ht => hA t (hb' ▸ ht)) ((hb'.symm ▸ hD).intervalIntegrable)
  simp only [hd] at H
  have heq : A b * limit - (A b - A 0) * limit = A 0 * limit := by ring
  rw [heq] at H
  apply H.congr'
  exact Eventually.of_forall fun r => (h r).symm

end ProjectAinos.SpecialFunctions.Oscillatory
