/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# A smooth implicit function on a neighbourhood

Mathlib's implicit function theorem gives a function that is smooth at the base
point. Smoothness of infinite order at a point does not hold in a neighbourhood
of the point, so a statement on a neighbourhood needs an argument: if the
equation is smooth on an open set and its partial derivative is invertible at
every point of that set, the implicit function of the base point agrees, near
each point of its graph, with the implicit function of that point.
-/

@[expose] public section
noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace ProjectAinos.SmoothAlgebra

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [CompleteSpace E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [CompleteSpace E₂]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The implicit function theorem on a neighbourhood: a smooth equation whose
partial derivative in the second variable is invertible on an open set has,
through each point of that set, an implicit function that is smooth on an open
neighbourhood of the first co-ordinate of the point. -/
theorem exists_contDiffOn_implicitFunction {f : E₁ × E₂ → F} {W : Set (E₁ × E₂)}
    (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f W)
    (hinv : ∀ v ∈ W, (fderiv ℝ f v ∘L .inr ℝ E₁ E₂).IsInvertible) {u : E₁ × E₂}
    (hu : u ∈ W) :
    ∃ (V : Set E₁) (ψ : E₁ → E₂), IsOpen V ∧ u.1 ∈ V ∧ ψ u.1 = u.2 ∧ ContDiffOn ℝ ∞ ψ V ∧
      ∀ x ∈ V, (x, ψ x) ∈ W ∧ f (x, ψ x) = f u := by
  have hfa : ∀ v ∈ W, ContDiffAt ℝ ∞ f v := fun v hv => hf.contDiffAt (hW.mem_nhds hv)
  have hne : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  let ψ := (hfa u hu).implicitFunction hne (hinv u hu)
  have hψu : ψ u.1 = u.2 := (hfa u hu).implicitFunction_apply_self hne (hinv u hu)
  have hev : ∀ᶠ x in 𝓝 u.1, f (x, ψ x) = f u :=
    (hfa u hu).eventually_apply_implicitFunction hne (hinv u hu)
  have hψc : ContDiffAt ℝ ∞ ψ u.1 := (hfa u hu).contDiffAt_implicitFunction hne (hinv u hu)
  have hcont : ∀ᶠ x in 𝓝 u.1, ContinuousAt ψ x :=
    ((hψc.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)).eventually (by simp)).mono
      fun x hx => hx.continuousAt
  have hmem : ∀ᶠ x in 𝓝 u.1, (x, ψ x) ∈ W := by
    have htend : Tendsto (fun x => (x, ψ x)) (𝓝 u.1) (𝓝 (u.1, ψ u.1)) :=
      (continuousAt_id (x := u.1)).prodMk hψc.continuousAt
    rw [hψu] at htend
    exact htend.eventually (hW.mem_nhds hu)
  have key : ∀ᶠ x in 𝓝 u.1, ContDiffAt ℝ ∞ ψ x := by
    filter_upwards [hev.eventually_nhds, hcont, hmem] with x hx hxc hxW
    let ψ' := (hfa _ hxW).implicitFunction hne (hinv _ hxW)
    have hψ' : ContDiffAt ℝ ∞ ψ' x :=
      (hfa _ hxW).contDiffAt_implicitFunction hne (hinv _ hxW)
    have hiff := (hfa _ hxW).eventually_apply_eq_iff_implicitFunction hne (hinv _ hxW)
    have htend : Tendsto (fun y => (y, ψ y)) (𝓝 x) (𝓝 (x, ψ x)) :=
      (continuousAt_id (x := x)).prodMk hxc
    have heq : ψ =ᶠ[𝓝 x] ψ' := by
      filter_upwards [htend.eventually hiff, hx] with y hy hfy
      exact (hy.mp (hfy.trans hx.self_of_nhds.symm)).symm
    exact hψ'.congr_of_eventuallyEq heq
  obtain ⟨V, hVsub, hVopen, huV⟩ := mem_nhds_iff.mp (key.and (hev.and hmem))
  exact ⟨V, ψ, hVopen, huV, hψu, fun x hx => (hVsub hx).1.contDiffWithinAt,
    fun x hx => ⟨(hVsub hx).2.2, (hVsub hx).2.1⟩⟩

end ProjectAinos.SmoothAlgebra
