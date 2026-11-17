/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# From derivatives along lines to the Fréchet derivative

If a real function has, at every point near `x` and in every direction `v`, the
derivative `ℓ(y) v` along the line `s ↦ y + s v`, where `ℓ(y)` is a continuous
linear form that depends continuously on `y` at `x`, then the function is
Fréchet differentiable at `x` with the derivative `ℓ(x)`. The proof is the mean
value inequality on the segment from `x` to `x + h`.
-/

@[expose] public section
noncomputable section

open Set Filter Metric Asymptotics
open scoped Topology

namespace ProjectAinos.SmoothAlgebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Derivatives along all lines, given by a field of linear forms that is
continuous at the point, assemble to the Fréchet derivative. -/
theorem hasFDerivAt_of_hasDerivAt_line {f : E → ℝ} {ℓ : E → E →L[ℝ] ℝ} {x : E}
    (h : ∀ᶠ y in 𝓝 x, ∀ v : E, HasDerivAt (fun s : ℝ => f (y + s • v)) (ℓ y v) 0)
    (hℓ : ContinuousAt ℓ x) : HasFDerivAt f (ℓ x) x := by
  rw [hasFDerivAt_iff_isLittleO, isLittleO_iff]
  intro c hc
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem h (hℓ (ball_mem_nhds (ℓ x) hc)))
  apply Metric.eventually_nhds_iff_ball.mpr
  refine ⟨r, hr, fun y hy => ?_⟩
  -- the function along the segment from `x` to `y`, minus its linear part
  let v : E := y - x
  have hseg : ∀ s ∈ Icc (0 : ℝ) 1, x + s • v ∈ ball x r := by
    intro s hs
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.1]
    have hyr : ‖v‖ < r := by simpa [v, dist_eq_norm] using hy
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg v) hs.2) hyr
  have hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt
      (fun s : ℝ => f (x + s • v) - s * ℓ x v) (ℓ (x + s • v) v - ℓ x v) (Icc 0 1) s := by
    intro s hs
    have h1 : HasDerivAt (fun σ : ℝ => f ((x + s • v) + σ • v)) (ℓ (x + s • v) v) 0 :=
      (hball (hseg s hs)).1 v
    have h2 : HasDerivAt (fun σ : ℝ => f ((x + s • v) + (σ - s) • v)) (ℓ (x + s • v) v) s := by
      have h3 : HasDerivAt (fun σ : ℝ => f ((x + s • v) + σ • v)) (ℓ (x + s • v) v) (s - s) := by
        rwa [sub_self]
      exact h3.comp_sub_const s s
    have h4 : (fun σ : ℝ => f ((x + s • v) + (σ - s) • v)) = fun σ : ℝ => f (x + σ • v) := by
      funext σ
      congr 1
      module
    rw [h4] at h2
    have h5 : HasDerivAt (fun σ : ℝ => σ * ℓ x v) (ℓ x v) s := by
      simpa using (hasDerivAt_id s).mul_const (ℓ x v)
    exact (h2.sub h5).hasDerivWithinAt
  have hbound : ∀ s ∈ Ico (0 : ℝ) 1, ‖ℓ (x + s • v) v - ℓ x v‖ ≤ c * ‖v‖ := by
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.le⟩
    have hdist : ‖ℓ (x + s • v) - ℓ x‖ ≤ c := by
      have hmem := (hball (hseg s hs')).2
      rw [mem_preimage, mem_ball, dist_eq_norm] at hmem
      exact hmem.le
    calc ‖ℓ (x + s • v) v - ℓ x v‖ = ‖(ℓ (x + s • v) - ℓ x) v‖ := by
          rw [_root_.sub_apply]
      _ ≤ ‖ℓ (x + s • v) - ℓ x‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ c * ‖v‖ := mul_le_mul_of_nonneg_right hdist (norm_nonneg v)
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01' hd hbound
  have hval : f (x + (1 : ℝ) • v) - 1 * ℓ x v - (f (x + (0 : ℝ) • v) - 0 * ℓ x v) =
      f y - f x - ℓ x (y - x) := by
    simp [v]
    ring
  rw [hval] at hmv
  exact hmv

end ProjectAinos.SmoothAlgebra
