/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.ODE.Volterra
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Topology.Algebra.Order.Floor

/-! # The Volterra operator is quasi-nilpotent

The `n`-th power of the Volterra operator of a coefficient curve `A` has norm
at most `‖A‖ ^ n / n!`. Hence the integral equation operator `id - V_A` is
invertible for every coefficient curve, with no bound on its norm, and the
solution of the linear equation on the unit interval depends smoothly on the
whole coefficient curve. The statements of `Volterra` that assume `‖A‖ < 1`
are repeated here without that hypothesis.
-/

@[expose] public section
noncomputable section

open Set ContinuousLinearMap
open scoped unitInterval ContDiff Topology Nat

namespace ProjectAInos.SmoothGeometry.LinearODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The pointwise bound that gives the factorial: at time `t` the `n`-th power
is at most `‖A‖ ^ n * t ^ n / n!`. -/
theorem volterra_pow_apply_norm_le (A : Curve (E →L[ℝ] E)) (n : ℕ) (f : Curve E)
    (t : unitInterval) :
    ‖(volterra A ^ n) f t‖ ≤ ‖A‖ ^ n * (t : ℝ) ^ n / n ! * ‖f‖ := by
  induction n generalizing t with
  | zero =>
    simpa using f.norm_coe_le_norm t
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, volterra_apply]
    have hbound : ∀ s ∈ Ioc (0 : ℝ) t,
        ‖extend A s (extend ((volterra A ^ n) f) s)‖ ≤ ‖A‖ ^ (n + 1) / n ! * ‖f‖ * s ^ n := by
      intro s hs
      have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2.trans t.property.2⟩
      have hA : ‖extend A s‖ ≤ ‖A‖ := by
        change ‖extend A ((⟨s, hs'⟩ : unitInterval) : ℝ)‖ ≤ ‖A‖
        rw [extend_coe]
        exact A.norm_coe_le_norm _
      have hf : ‖extend ((volterra A ^ n) f) s‖ ≤ ‖A‖ ^ n * s ^ n / n ! * ‖f‖ := by
        change ‖extend ((volterra A ^ n) f) ((⟨s, hs'⟩ : unitInterval) : ℝ)‖ ≤ _
        rw [extend_coe]
        exact ih ⟨s, hs'⟩
      calc ‖extend A s (extend ((volterra A ^ n) f) s)‖
          ≤ ‖extend A s‖ * ‖extend ((volterra A ^ n) f) s‖ := (extend A s).le_opNorm _
        _ ≤ ‖A‖ * (‖A‖ ^ n * s ^ n / n ! * ‖f‖) :=
          mul_le_mul hA hf (norm_nonneg _) (norm_nonneg A)
        _ = ‖A‖ ^ (n + 1) / n ! * ‖f‖ * s ^ n := by ring
    have h := intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume)
      t.property.1 (Filter.Eventually.of_forall hbound)
      ((continuous_const.mul (continuous_id.pow n)).intervalIntegrable 0 (t : ℝ))
    refine h.trans (le_of_eq ?_)
    rw [intervalIntegral.integral_const_mul, integral_pow, Nat.factorial_succ]
    have hn : (n ! : ℝ) ≠ 0 := by positivity
    have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

/-- The powers of the Volterra operator decay like `‖A‖ ^ n / n!`. -/
theorem volterra_pow_norm_le (A : Curve (E →L[ℝ] E)) (n : ℕ) :
    ‖volterra A ^ n‖ ≤ ‖A‖ ^ n / n ! := by
  apply opNorm_le_bound _ (by positivity)
  intro f
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  refine (volterra_pow_apply_norm_le A n f t).trans ?_
  have ht : (t : ℝ) ^ n ≤ 1 := pow_le_one₀ t.property.1 t.property.2
  have hA : 0 ≤ ‖A‖ ^ n / n ! := by positivity
  calc ‖A‖ ^ n * (t : ℝ) ^ n / n ! * ‖f‖ = ‖A‖ ^ n / n ! * (t : ℝ) ^ n * ‖f‖ := by ring
    _ ≤ ‖A‖ ^ n / n ! * 1 * ‖f‖ := by gcongr
    _ = ‖A‖ ^ n / n ! * ‖f‖ := by ring

/-- The integral equation operator is invertible for every coefficient curve. -/
theorem isInvertible_equationOperator (A : Curve (E →L[ℝ] E)) :
    (equationOperator A).IsInvertible := by
  obtain ⟨n, hn⟩ := ((FloorSemiring.tendsto_pow_div_factorial_atTop ‖A‖).eventually
    (gt_mem_nhds (zero_lt_one' ℝ))).exists
  have hu := isUnit_one_sub_of_norm_lt_one (x := volterra A ^ n)
    ((volterra_pow_norm_le A n).trans_lt hn)
  rw [← mul_neg_geom_sum (volterra A) n] at hu
  have hc : Commute (1 - volterra A) (∑ i ∈ Finset.range n, volterra A ^ i) :=
    (Commute.one_left _).sub_left
      (Commute.sum_right _ _ _ fun i _ => (Commute.refl _).pow_right i)
  obtain ⟨u, hu'⟩ := (hc.isUnit_mul_iff.mp hu).1
  exact ⟨ContinuousLinearEquiv.ofUnit u, hu'⟩

/-- The solution satisfies the Volterra integral equation. -/
theorem solutionOperator_integral_eq (A : Curve (E →L[ℝ] E)) (y : E) (t : unitInterval) :
    solutionOperator A y t = y +
      ∫ s in 0..(t : ℝ), extend A s (extend (solutionOperator A y) s) := by
  have h := congrArg (fun f : Curve E => f t)
    ((isInvertible_equationOperator A).self_apply_inverse (ContinuousMap.const _ y))
  change solutionOperator A y t - volterra A (solutionOperator A y) t = y at h
  rw [volterra_apply] at h
  exact sub_eq_iff_eq_add.mp h

@[simp] theorem solutionOperator_zero (A : Curve (E →L[ℝ] E)) (y : E) :
    solutionOperator A y 0 = y := by
  simpa using solutionOperator_integral_eq A y 0

/-- Uniqueness among continuous curves satisfying the integral equation. -/
theorem eq_solutionOperator_of_integral_eq (A : Curve (E →L[ℝ] E)) (y : E) (f : Curve E)
    (hf : ∀ t : unitInterval, f t = y + ∫ s in 0..(t : ℝ), extend A s (extend f s)) :
    f = solutionOperator A y := by
  apply (isInvertible_equationOperator A).injective
  rw [show equationOperator A (solutionOperator A y) = ContinuousMap.const _ y from
    (isInvertible_equationOperator A).self_apply_inverse _]
  ext t
  change f t - volterra A f t = y
  rw [volterra_apply, hf t]
  abel

/-- The solution satisfies the differential equation on the unit interval,
with one-sided derivatives at the two ends. -/
theorem solutionOperator_hasDerivWithinAt (A : Curve (E →L[ℝ] E)) (y : E) (t : unitInterval) :
    HasDerivWithinAt (extend (solutionOperator A y)) (A t (solutionOperator A y t))
      (Icc (0 : ℝ) 1) t := by
  have hc := extend_continuous (pointwiseApply A (solutionOperator A y))
  have hd := (hc.integral_hasStrictDerivAt 0 (t : ℝ)).hasDerivAt.const_add y
  have heq : ∀ s ∈ Icc (0 : ℝ) 1, extend (solutionOperator A y) s =
      y + ∫ u in 0..s, extend (pointwiseApply A (solutionOperator A y)) u := by
    intro s hs
    change extend (solutionOperator A y) (⟨s, hs⟩ : unitInterval) = _
    rw [extend_coe]
    exact solutionOperator_integral_eq A y ⟨s, hs⟩
  simpa only [extend_coe, pointwiseApply, ContinuousMap.coe_mk] using
    hd.hasDerivWithinAt.congr_of_mem heq t.property

/-- Uniqueness for the differential equation: continuity at the two ends and
the equation in the interior suffice. -/
theorem eq_solutionOperator_of_hasDerivAt (A : Curve (E →L[ℝ] E)) (y : E) (f : Curve E)
    (h0 : f 0 = y)
    (hf : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt (extend f) (extend A t (extend f t)) t) :
    f = solutionOperator A y := by
  apply eq_solutionOperator_of_integral_eq A y f
  intro t
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le t.property.1
    (extend_continuous f).continuousOn
    (fun s hs => hf s ⟨hs.1, hs.2.trans_le t.property.2⟩)
    ((extend_continuous (pointwiseApply A f)).intervalIntegrable 0 (t : ℝ))
  have hzero : extend f 0 = y := by
    change extend f ((0 : unitInterval) : ℝ) = y
    rw [extend_coe, h0]
  rw [extend_coe, hzero] at h
  change f t = y + ∫ s in 0..(t : ℝ), extend A s (extend f s)
  rw [h]
  abel

/-- The solution depends smoothly on the coefficient curve, on the whole
space of coefficient curves. -/
theorem solutionOperator_contDiff : ContDiff ℝ ∞ (solutionOperator (E := E)) := by
  have hv := ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (E := Curve (E →L[ℝ] E)) (F := Curve E →L[ℝ] Curve E) (volterra (E := E))
  have he : ContDiff ℝ ∞ (equationOperator (E := E)) := contDiff_const.sub hv
  rw [contDiff_iff_contDiffAt]
  intro A
  exact ((isInvertible_equationOperator A).contDiffAt_map_inverse.comp A
    he.contDiffAt).clm_comp contDiffAt_const

/-- Joint smooth dependence on the coefficient curve and the initial value. -/
theorem solutionOperator_apply_contDiff :
    ContDiff ℝ ∞ (fun p : Curve (E →L[ℝ] E) × E => solutionOperator p.1 p.2) :=
  (solutionOperator_contDiff.comp contDiff_fst).clm_apply contDiff_snd

end ProjectAInos.SmoothGeometry.LinearODE
