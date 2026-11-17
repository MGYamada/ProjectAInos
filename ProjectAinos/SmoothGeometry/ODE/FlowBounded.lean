/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.ODE.FlowComplete
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Completeness of a flow with bounded velocities

On the space of the co-ordinates `ι ⊕ κ → ℝ`, let the components `Sum.inl i` of a smooth field
be bounded, and let its components `Sum.inr k` be bounded on every set where the co-ordinates
`Sum.inl i` are bounded. Then the flow is defined for all times and points
(`flowDomain_eq_univ_of_bounded_inl`): in a finite time the first co-ordinates stay in a
bounded set, so the second co-ordinates change with a bounded speed.

The relativistic motion of a charge is of this kind. The speed is less than the speed of
light, and the force is bounded where the position is bounded.
-/

@[expose] public section
noncomputable section

open Set Metric
open scoped ContDiff

namespace ProjectAinos.SmoothGeometry.NonlinearODE

/-- A field on `ι ⊕ κ → ℝ` whose components `Sum.inl i` are bounded, and whose components
`Sum.inr k` are bounded where the co-ordinates `Sum.inl i` are bounded, has a flow defined for
all times and points. -/
theorem flowDomain_eq_univ_of_bounded_inl {ι κ : Type*} [Fintype ι] [Fintype κ]
    {X : (ι ⊕ κ → ℝ) → ι ⊕ κ → ℝ} (hX : ContDiff ℝ ∞ X) {V : ℝ}
    (hV : ∀ z i, |X z (Sum.inl i)| ≤ V)
    (hF : ∀ R : ℝ, ∃ M : ℝ, ∀ z, (∀ i, |z (Sum.inl i)| ≤ R) → ∀ k, |X z (Sum.inr k)| ≤ M) :
    flowDomain X = univ := by
  refine eq_univ_of_forall fun p => ?_
  obtain ⟨T, z₀⟩ := p
  obtain ⟨M, hM⟩ := hF (‖z₀‖ + |V| * |T|)
  refine mem_flowDomain_of_isCompact hX
    (isCompact_closedBall (0 : ι ⊕ κ → ℝ) (‖z₀‖ + (|V| + |M|) * |T|)) fun t ht h => ?_
  rw [mem_closedBall_zero_iff]
  have hmem : ∀ s ∈ uIcc 0 t, (s, z₀) ∈ flowDomain X := fun s hs =>
    mem_flowDomain_of_mem_uIcc h hs
  have hder : ∀ s ∈ uIcc 0 t, ∀ a, HasDerivWithinAt (fun r => flow X (r, z₀) a)
      (X (flow X (s, z₀)) a) (uIcc 0 t) s := fun s hs a =>
    (hasDerivAt_pi.mp (hasDerivAt_flow hX (hmem s hs)) a).hasDerivWithinAt
  have habs : ∀ s ∈ uIcc 0 t, |s| ≤ |T| := by
    intro s hs
    have h1 : |s - 0| ≤ |t - 0| := abs_sub_left_of_mem_uIcc hs
    have h2 : |t - 0| ≤ |T - 0| := abs_sub_left_of_mem_uIcc ht
    simpa using h1.trans h2
  -- a bound for a co-ordinate from a bound for its velocity on the segment
  have hcoord : ∀ (a : ι ⊕ κ) (C : ℝ), 0 ≤ C →
      (∀ r ∈ uIcc 0 t, |X (flow X (r, z₀)) a| ≤ C) →
      ∀ s ∈ uIcc 0 t, |flow X (s, z₀) a| ≤ ‖z₀‖ + C * |T| := by
    intro a C hC hbound s hs
    have hb := (convex_uIcc (0 : ℝ) t).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun r => flow X (r, z₀) a) (f' := fun r => X (flow X (r, z₀)) a) (C := C)
      (fun r hr => hder r hr a) (fun r hr => hbound r hr) left_mem_uIcc hs
    simp only [flow_zero, Real.norm_eq_abs, sub_zero] at hb
    have h0 : |z₀ a| ≤ ‖z₀‖ := norm_le_pi_norm z₀ a
    have h1 : |flow X (s, z₀) a| ≤ |z₀ a| + |flow X (s, z₀) a - z₀ a| := by
      have := abs_add_le (z₀ a) (flow X (s, z₀) a - z₀ a)
      simpa using this
    have h2 : C * |s| ≤ C * |T| := mul_le_mul_of_nonneg_left (habs s hs) hC
    linarith
  have hpos : ∀ s ∈ uIcc 0 t, ∀ i, |flow X (s, z₀) (Sum.inl i)| ≤ ‖z₀‖ + |V| * |T| :=
    fun s hs i => hcoord (Sum.inl i) |V| (abs_nonneg V)
      (fun r _ => (hV _ i).trans (le_abs_self V)) s hs
  have hmom : ∀ k, |flow X (t, z₀) (Sum.inr k)| ≤ ‖z₀‖ + |M| * |T| :=
    fun k => hcoord (Sum.inr k) |M| (abs_nonneg M)
      (fun r hr => (hM _ (hpos r hr) k).trans (le_abs_self M)) t right_mem_uIcc
  have hVT : 0 ≤ |V| * |T| := mul_nonneg (abs_nonneg V) (abs_nonneg T)
  have hMT : 0 ≤ |M| * |T| := mul_nonneg (abs_nonneg M) (abs_nonneg T)
  refine (pi_norm_le_iff_of_nonneg (by nlinarith [norm_nonneg z₀])).mpr fun a => ?_
  rw [Real.norm_eq_abs]
  rcases a with i | k
  · have := hpos t right_mem_uIcc i
    nlinarith
  · have := hmom k
    nlinarith

end ProjectAinos.SmoothGeometry.NonlinearODE
