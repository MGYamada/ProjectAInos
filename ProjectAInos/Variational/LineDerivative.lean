/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-!
# Differentiability from the derivatives along lines

`hasFDerivAt_of_hasDerivAt_line`: let `f` have, at every point `s` of an open
set and for every direction `a`, the derivative `A s a` along the line
`ε ↦ s + ε a`, where `A s` is a continuous linear map that depends
continuously on `s`. Then `A s` is the derivative of `f` at `s`.
`hasDerivAt_line` is the converse at one point.
-/

@[expose] public section
noncomputable section

open Set Filter
open scoped Topology

namespace ProjectAInos.Variational

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
  [NormedSpace ℝ G]

/-- The derivative along a line through a point of differentiability. -/
theorem hasDerivAt_line {f : E → G} {f' : E →L[ℝ] G} {s : E} (hf : HasFDerivAt f f' s)
    (a : E) : HasDerivAt (fun ε : ℝ => f (s + ε • a)) (f' a) 0 :=
  hf.hasLineDerivAt a

/-- The derivative along a line, in a parameter that is shifted by `r`. -/
theorem hasDerivAt_line_sub {f : E → G} {f' : E →L[ℝ] G} {s : E} (hf : HasFDerivAt f f' s)
    (a : E) (r : ℝ) : HasDerivAt (fun t : ℝ => f (s + (t - r) • a)) (f' a) r := by
  have h0 : HasDerivAt (fun ε : ℝ => f (s + ε • a)) (f' a) (r - r) := by
    rw [sub_self]
    exact hasDerivAt_line hf a
  have h1 := HasDerivAt.scomp r (g₁ := fun ε : ℝ => f (s + ε • a)) (h := fun t : ℝ => t - r)
    h0 ((hasDerivAt_id r).sub_const r)
  rw [one_smul] at h1
  exact h1

/-- Continuous derivatives along lines are a derivative. -/
theorem hasFDerivAt_of_hasDerivAt_line {f : E → G} {A : E → E →L[ℝ] G} {S : Set E}
    (hS : IsOpen S) (hf : ∀ s ∈ S, ∀ a, HasDerivAt (fun ε : ℝ => f (s + ε • a)) (A s a) 0)
    (hA : ContinuousOn A S) {s : E} (hs : s ∈ S) : HasFDerivAt f (A s) s := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  have hAs : ContinuousAt A s := hA.continuousAt (hS.mem_nhds hs)
  have hnear : ∀ᶠ y in 𝓝 s, y ∈ S ∧ ‖A y - A s‖ ≤ c := by
    filter_upwards [hS.mem_nhds hs, hAs.eventually (Metric.closedBall_mem_nhds (A s) hc)]
      with y hy hy'
    exact ⟨hy, by rwa [dist_eq_norm] at hy'⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  filter_upwards [Metric.ball_mem_nhds (0 : E) hδ] with h hh
  have hhn : ‖h‖ < δ := mem_ball_zero_iff.mp hh
  have hpt : ∀ t ∈ Icc (0 : ℝ) 1, s + t • h ∈ S ∧ ‖A (s + t • h) - A s‖ ≤ c := by
    intro t ht
    refine hball ?_
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg h) ht.2) hhn
  have hg : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun t : ℝ => f (s + t • h) - t • A s h)
      (A (s + t • h) h - A s h) (Icc (0 : ℝ) 1) t := by
    intro t ht
    have h0 : HasDerivAt (fun ε : ℝ => f (s + t • h + ε • h)) (A (s + t • h) h) (t - t) := by
      rw [sub_self]
      exact hf _ (hpt t ht).1 h
    have h1 : HasDerivAt (fun t' : ℝ => t' - t) 1 t := (hasDerivAt_id t).sub_const t
    have h2 := HasDerivAt.scomp t (g₁ := fun ε : ℝ => f (s + t • h + ε • h))
      (h := fun t' : ℝ => t' - t) h0 h1
    rw [one_smul] at h2
    have e : ((fun ε : ℝ => f (s + t • h + ε • h)) ∘ fun t' : ℝ => t' - t) =
        fun t' : ℝ => f (s + t' • h) := by
      funext t'
      change f (s + t • h + (t' - t) • h) = f (s + t' • h)
      rw [sub_smul]
      congr 1
      abel
    rw [e] at h2
    have h3 : HasDerivAt (fun t : ℝ => t • A s h) (A s h) t := by
      have h := (hasDerivAt_id t).smul_const (A s h)
      rwa [one_smul] at h
    exact (h2.sub h3).hasDerivWithinAt
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1, ‖A (s + t • h) h - A s h‖ ≤ c * ‖h‖ := by
    intro t ht
    have e : A (s + t • h) h - A s h = (A (s + t • h) - A s) h := rfl
    rw [e]
    exact ((A (s + t • h) - A s).le_opNorm h).trans
      (mul_le_mul_of_nonneg_right (hpt t ⟨ht.1, ht.2.le⟩).2 (norm_nonneg h))
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01' hg hbound
  have e : f (s + (1 : ℝ) • h) - (1 : ℝ) • A s h - (f (s + (0 : ℝ) • h) - (0 : ℝ) • A s h) =
      f (s + h) - f s - A s h := by
    rw [one_smul, one_smul, zero_smul, zero_smul, add_zero, sub_zero]
    abel
  rw [e] at hmv
  exact hmv

end ProjectAInos.Variational
