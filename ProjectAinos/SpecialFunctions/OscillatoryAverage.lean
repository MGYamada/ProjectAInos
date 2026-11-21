/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.NonstationaryPhase
import Mathlib.Tactic

/-! # The mean square of a single real oscillation

The square of the real part has a constant term and a doubled phase. Nonstationary phase
removes the latter. A continuous compactly supported amplitude of order ε does not change
the limit.
-/

@[expose] public section
noncomputable section

open Complex Set MeasureTheory Filter
open scoped Topology ContDiff

namespace ProjectAinos.SpecialFunctions.Oscillatory

private def cis (ε s : ℝ) := exp (I / ε * s)

private theorem unit (ε s : ℝ) : ‖cis ε s‖ = 1 := by simp [cis, norm_exp, div_re]

private theorem double (ε s : ℝ) : (cis ε s) ^ 2 = cis (ε / 2) s := by
  rw [cis, cis, sq, ← exp_add]
  congr 1
  push_cast
  ring

private theorem re_sq (z : ℂ) : 2 * z.re ^ 2 = ‖z‖ ^ 2 + (z ^ 2).re := by
  rw [sq z, mul_re]
  nlinarith [Complex.sq_norm_sub_sq_re z]

private theorem compact_sq {X : Type*} [TopologicalSpace X] [T2Space X] {f : X → ℂ}
    (hf : HasCompactSupport f) :
    HasCompactSupport (fun x => f x ^ 2) := by
  exact HasCompactSupport.intro hf fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx]

private theorem unperturbed {d : ℕ} {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : EuclideanSpace ℝ (Fin d) → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (hn : ∀ x ∈ tsupport g, fderiv ℝ ψ x ≠ 0) :
    Tendsto (fun ε : ℝ => ∫ x, (g x * cis ε (ψ x)).re ^ 2) (𝓝[≠] 0)
      (𝓝 ((∫ x, ‖g x‖ ^ 2) / 2)) := by
  let F (ε : ℝ) := ∫ x, g x ^ 2 * cis (ε / 2) (ψ x)
  have hs : tsupport (fun x => g x ^ 2) ⊆ tsupport g := by
    simpa only [sq] using (tsupport_mul_subset_left (f := g) (g := g))
  obtain ⟨C,_,hC⟩ := nonstationary hψ 1 (hg.pow 2) (compact_sq hc) (fun x hx => hn x (hs hx))
  have hF : Tendsto F (𝓝[≠] 0) (𝓝 0) := by
    have h : Continuous (fun ε : ℝ => C * |ε / 2|) := by fun_prop
    have hl : Tendsto (fun ε : ℝ => C * |ε / 2|) (𝓝[≠] 0) (𝓝 0) := by
      simpa using (h.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
    apply squeeze_zero_norm' _ hl
    filter_upwards [self_mem_nhdsWithin] with ε (hε : ε ≠ 0)
    simpa only [F, cis, pow_one] using hC (ε/2) (div_ne_zero hε two_ne_zero)
  have hlim := (tendsto_const_nhds (x := ∫ x, ‖g x‖ ^ 2)).add
    (continuous_re.continuousAt.tendsto.comp hF)
  have hv (ε : ℝ) : (∫ x, (g x * cis ε (ψ x)).re ^ 2) =
      ((∫ x, ‖g x‖ ^ 2) + (F ε).re) / 2 := by
    have ig : Integrable (fun x => ‖g x‖ ^ 2) :=
      (hg.continuous.norm.pow 2).integrable_of_hasCompactSupport
        (by simpa only [sq] using hc.norm.mul_right (f' := fun x => ‖g x‖))
    have ic (u : ℝ) : Continuous (fun x => cis u (ψ x)) := by unfold cis; fun_prop
    have ik : Integrable (fun x => g x ^ 2 * cis (ε / 2) (ψ x)) :=
      ((hg.continuous.pow 2).mul (ic _)).integrable_of_hasCompactSupport ((compact_sq hc).mul_right)
    change _ = ((∫ x, ‖g x‖ ^ 2) + RCLike.re (∫ x, g x ^ 2 * cis (ε / 2) (ψ x))) / 2
    rw [← integral_re ik, ← integral_add ig ik.re, ← integral_div]
    apply integral_congr_ae
    filter_upwards with x
    have h := re_sq (g x * cis ε (ψ x))
    simp only [norm_mul, unit, mul_one, mul_pow, double] at h
    change _ = (_ + (g x ^ 2 * cis (ε / 2) (ψ x)).re) / 2
    linarith
  simpa only [Function.comp_apply, ← hv, zero_re, add_zero] using hlim.div_const 2

private theorem perturb_bound (g h w : ℂ) (hw : ‖w‖ = 1) (ε : ℝ) :
    |((g + ε * h) * w).re ^ 2 - (g * w).re ^ 2| ≤
      |ε| * ‖h‖ * (2 * ‖g‖ + |ε| * ‖h‖) := by
  have hg : |(g*w).re| ≤ ‖g‖ := by simpa [hw] using abs_re_le_norm (g*w)
  have hh : |(h*w).re| ≤ ‖h‖ := by simpa [hw] using abs_re_le_norm (h*w)
  rw [add_mul, mul_assoc, add_re, re_ofReal_mul, sq_sub_sq, add_sub_cancel_left, abs_mul, abs_mul]
  rw [mul_comm |(g*w).re + ε * (h*w).re + (g*w).re|]
  apply mul_le_mul (mul_le_mul_of_nonneg_left hh (abs_nonneg ε)) _ (abs_nonneg _) (by positivity)
  calc
    _ ≤ |(g*w).re + ε * (h*w).re| + |(g*w).re| := abs_add_le _ _
    _ ≤ |(g*w).re| + |ε| * |(h*w).re| + |(g*w).re| := by
      rw [← abs_mul]
      gcongr
      exact abs_add_le _ _
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hh (abs_nonneg ε)]

/-- The single real wave with complex amplitude g + εh has mean square ½∫|g|² in the
short-wavelength limit. Noncriticality is required only on the closed support of g. -/
theorem tendsto_real_square {d : ℕ} {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    {g h : EuclideanSpace ℝ (Fin d) → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (hn : ∀ x ∈ tsupport g, fderiv ℝ ψ x ≠ 0)
    (hh : Continuous h) (hk : HasCompactSupport h) :
    Tendsto (fun ε : ℝ => ∫ x, ((g x + ε * h x) * exp (I / ε * ψ x)).re ^ 2) (𝓝[≠] 0)
      (𝓝 ((∫ x, ‖g x‖ ^ 2) / 2)) := by
  let D (ε : ℝ) (x : EuclideanSpace ℝ (Fin d)) :=
    ((g x + ε * h x) * cis ε (ψ x)).re ^ 2 - (g x * cis ε (ψ x)).re ^ 2
  have hD : Tendsto (fun ε => ∫ x, D ε x) (𝓝[≠] 0) (𝓝 0) := by
    conv_rhs => rw [← integral_zero (α := EuclideanSpace ℝ (Fin d)) (G := ℝ) (μ := volume)]
    apply tendsto_integral_filter_of_dominated_convergence
      (fun x => ‖h x‖ * (2 * ‖g x‖ + ‖h x‖))
    · exact Eventually.of_forall fun ε =>
        Continuous.aestronglyMeasurable (by unfold D cis; fun_prop)
    · have hsmall : ∀ᶠ ε : ℝ in 𝓝[≠] 0, |ε| ≤ 1 :=
        ((continuous_abs.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds).eventually_le_const
          (by norm_num)
      filter_upwards [hsmall] with ε hε
      apply ae_of_all
      intro x
      apply (perturb_bound (g x) (h x) _ (unit ε (ψ x)) ε).trans
      have hle := mul_le_mul_of_nonneg_right hε (norm_nonneg (h x))
      rw [one_mul] at hle
      gcongr
    · exact (hh.norm.mul ((continuous_const.mul hg.continuous.norm).add hh.norm))
        |>.integrable_of_hasCompactSupport hk.norm.mul_right
    · apply ae_of_all
      intro x
      apply squeeze_zero_norm' (Eventually.of_forall fun ε =>
        perturb_bound (g x) (h x) _ (unit ε (ψ x)) ε)
      have hc' : Continuous (fun ε : ℝ => |ε| * ‖h x‖ * (2 * ‖g x‖ + |ε| * ‖h x‖)) := by fun_prop
      simpa using (hc'.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
  have he (ε : ℝ) : (∫ x, D ε x) + (∫ x, (g x * cis ε (ψ x)).re ^ 2) =
      ∫ x, ((g x + ε * h x) * exp (I / ε * ψ x)).re ^ 2 := by
    have hi (f : EuclideanSpace ℝ (Fin d) → ℂ) (hf : Continuous f) (hf' : HasCompactSupport f) :
        Integrable (fun x => (f x * cis ε (ψ x)).re ^ 2) := by
      apply Continuous.integrable_of_hasCompactSupport (by unfold cis; fun_prop)
      apply HasCompactSupport.intro hf' (fun x hx => ?_)
      simp [image_eq_zero_of_notMem_tsupport hx]
    have hf : HasCompactSupport (fun x => g x + ε * h x) :=
      hc.add (hk.mul_left (f := fun _ => (ε : ℂ)))
    rw [show (∫ x, D ε x) = _ - _ from integral_sub
      (hi _ (hg.continuous.add (continuous_const.mul hh)) hf) (hi _ hg.continuous hc)]
    exact sub_add_cancel _ _
  simpa only [he, zero_add] using hD.add (unperturbed hψ hg hc hn)

end ProjectAinos.SpecialFunctions.Oscillatory
