/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Smooth parametric integrals

For a function `f` of a parameter `x` in a finite-dimensional space and of a
real variable `t`, the integral `F(x) = ∫ₐᵇ f(x, t) dt` is as smooth as `f`:

* `hasFDerivAt_parametric_intervalIntegral`: if `f` is `C¹`, the derivative of
  `F` is the integral of the derivative of `f` with respect to `x`;
* `contDiff_parametric_intervalIntegral`: if `f` is `Cⁿ`, so is `F`;
* `contDiff_infty_parametric_intervalIntegral`: if `f` is smooth, so is `F`;
* `contDiff_infty_parametric_intervalIntegral_limits`: if `f` is smooth, the
  integral is smooth in `x` and the limits `a`, `b` together.

This is the interface statement (I) of the manuscript. It is used for
Hadamard's lemma. The parameter space and the space of values are in one
universe, so that the induction on the order can pass to the space of linear
maps.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.SmoothAlgebra

open MeasureTheory Metric Set
open scoped Topology Interval ContDiff

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
variable {G : Type u} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The derivative of `f : E × ℝ → G` with respect to the first variable. -/
def fderivLeft (f : E × ℝ → G) (p : E × ℝ) : E →L[ℝ] G :=
  (fderiv ℝ f p).comp (ContinuousLinearMap.inl ℝ E ℝ)

omit [ProperSpace E] in
theorem contDiff_fderivLeft {f : E × ℝ → G} {n : ℕ} (hf : ContDiff ℝ (n + 1 : ℕ) f) :
    ContDiff ℝ n (fderivLeft f) := by
  have h : ContDiff ℝ n (fderiv ℝ f) := hf.fderiv_right (by norm_cast)
  exact h.clm_comp contDiff_const

omit [ProperSpace E] in
theorem hasFDerivAt_left {f : E × ℝ → G} (hf : Differentiable ℝ f) (x : E) (t : ℝ) :
    HasFDerivAt (fun y => f (y, t)) (fderivLeft f (x, t)) x :=
  (hf (x, t)).hasFDerivAt.comp x (hasFDerivAt_prodMk_left x t)

/-- Differentiation under the integral sign for a `C¹` function. -/
theorem hasFDerivAt_parametric_intervalIntegral {f : E × ℝ → G} (hf : ContDiff ℝ 1 f)
    (a b : ℝ) (x₀ : E) :
    HasFDerivAt (fun x => ∫ t in a..b, f (x, t)) (∫ t in a..b, fderivLeft f (x₀, t)) x₀ := by
  have hcont : Continuous f := hf.continuous
  have hdiff : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hf' : Continuous (fderivLeft f) := by
    have h : ContDiff ℝ 0 (fderivLeft f) := contDiff_fderivLeft (n := 0) (by simpa using hf)
    exact h.continuous
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x₀ 1).prod (isCompact_uIcc (a := a) (b := b))
    ).exists_bound_of_continuousOn hf'.continuousOn
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := closedBall x₀ 1) (bound := fun _ => C) (closedBall_mem_nhds x₀ one_pos)
    (Filter.Eventually.of_forall fun x =>
      (hcont.comp (Continuous.prodMk_right x)).aestronglyMeasurable)
    ((hcont.comp (Continuous.prodMk_right x₀)).intervalIntegrable a b)
    (hf'.comp (Continuous.prodMk_right x₀)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t ht x hx => hC (x, t) ⟨hx, uIoc_subset_uIcc ht⟩)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun t _ x _ => hasFDerivAt_left hdiff x t)

/-- A parametric integral of a `Cⁿ` function is `Cⁿ`. -/
theorem contDiff_parametric_intervalIntegral {n : ℕ} :
    ∀ {G : Type u} [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E × ℝ → G},
      ContDiff ℝ n f → ∀ a b : ℝ, ContDiff ℝ n fun x => ∫ t in a..b, f (x, t) := by
  induction n with
  | zero =>
    intro G _ _ f hf a b
    rw [Nat.cast_zero, contDiff_zero] at hf ⊢
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun x t => f (x, t)) hf a b
  | succ n ih =>
    intro G _ _ f hf a b
    have h1 : ContDiff ℝ 1 f := hf.of_le (by norm_cast; omega)
    have hderiv (x : E) := hasFDerivAt_parametric_intervalIntegral h1 a b x
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
    refine ⟨fun x => (hderiv x).differentiableAt, fun h => absurd h (by simp), ?_⟩
    have hfd : fderiv ℝ (fun x => ∫ t in a..b, f (x, t)) =
        fun x => ∫ t in a..b, fderivLeft f (x, t) :=
      funext fun x => (hderiv x).fderiv
    rw [hfd]
    exact ih (contDiff_fderivLeft hf) a b

/-- A parametric integral of a smooth function is smooth. -/
theorem contDiff_infty_parametric_intervalIntegral {f : E × ℝ → G} (hf : ContDiff ℝ ∞ f)
    (a b : ℝ) : ContDiff ℝ ∞ fun x => ∫ t in a..b, f (x, t) :=
  contDiff_infty.mpr fun n => contDiff_parametric_intervalIntegral (contDiff_infty.mp hf n) a b

/-- A parametric integral of a smooth function is smooth in the parameter and
the limits of integration together. -/
theorem contDiff_infty_parametric_intervalIntegral_limits {f : E × ℝ → G}
    (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ fun p : E × ℝ × ℝ => ∫ t in p.2.1..p.2.2, f (p.1, t) := by
  have h (p : E × ℝ × ℝ) : ∫ t in p.2.1..p.2.2, f (p.1, t) =
      (p.2.2 - p.2.1) • ∫ s in (0 : ℝ)..1, f (p.1, p.2.1 + (p.2.2 - p.2.1) * s) := by
    have h' := intervalIntegral.smul_integral_comp_add_mul (a := 0) (b := 1)
      (fun t => f (p.1, t)) (p.2.2 - p.2.1) p.2.1
    rw [h', mul_zero, add_zero, mul_one, add_sub_cancel]
  have hg : ContDiff ℝ ∞ fun q : (E × ℝ × ℝ) × ℝ =>
      f (q.1.1, q.1.2.1 + (q.1.2.2 - q.1.2.1) * q.2) := by
    fun_prop
  simp only [h]
  exact ContDiff.smul (by fun_prop) (contDiff_infty_parametric_intervalIntegral hg 0 1)

end ProjectAInos.SmoothAlgebra
