/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothAlgebra.ImplicitFunction

/-!
# The implicit function theorem for one real equation

A smooth equation `Φ(s, y) = Φ(u)` in one real unknown `y` with one real
parameter `s` is solved near a point `u` at which the derivative in `y` does not
vanish, by a function that is smooth on an open set of parameters
(`exists_contDiffOn_implicitFunction_real`). It is the case of
`exists_contDiffOn_implicitFunction` in which invertibility of the partial
derivative is the non-vanishing of a number.
-/

@[expose] public section
noncomputable section

open Set
open scoped ContDiff

namespace ProjectAinos.SmoothAlgebra

/-- The implicit function theorem for one real equation in one real unknown,
on an open set of the parameter. The derivative in the unknown is given as a
continuous function `Φ'`. -/
theorem exists_contDiffOn_implicitFunction_real {Φ Φ' : ℝ × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (hd : ∀ v : ℝ × ℝ, HasDerivAt (fun y => Φ (v.1, y)) (Φ' v) v.2) (hc : Continuous Φ')
    {u : ℝ × ℝ} (hu : Φ' u ≠ 0) :
    ∃ (J : Set ℝ) (ψ : ℝ → ℝ), IsOpen J ∧ u.1 ∈ J ∧ ψ u.1 = u.2 ∧ ContDiffOn ℝ ∞ ψ J ∧
      ∀ s ∈ J, Φ' (s, ψ s) ≠ 0 ∧ Φ (s, ψ s) = Φ u := by
  have hfd : ∀ v : ℝ × ℝ, fderiv ℝ Φ v ∘L ContinuousLinearMap.inr ℝ ℝ ℝ =
      Φ' v • ContinuousLinearMap.id ℝ ℝ := by
    intro v
    have h1 : HasFDerivAt (fun y : ℝ => Φ (v.1, y)) (fderiv ℝ Φ v ∘L
        ContinuousLinearMap.inr ℝ ℝ ℝ) v.2 :=
      HasFDerivAt.comp (g := Φ) (f := fun y : ℝ => (v.1, y)) v.2
        (hΦ.differentiable (by simp) v).hasFDerivAt (hasFDerivAt_prodMk_right v.1 v.2)
    have h3 := h1.unique (hd v).hasFDerivAt
    rw [h3]
    ext
    simp
  have hopen : IsOpen {v : ℝ × ℝ | Φ' v ≠ 0} := isOpen_ne_fun hc continuous_const
  have hinv : ∀ v ∈ {v : ℝ × ℝ | Φ' v ≠ 0},
      (fderiv ℝ Φ v ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    intro v hv
    rw [hfd v]
    refine ContinuousLinearMap.IsInvertible.of_inverse
      (g := (Φ' v)⁻¹ • ContinuousLinearMap.id ℝ ℝ) ?_ ?_
    · ext
      simp
      exact inv_mul_cancel₀ hv
    · ext
      simp
      exact mul_inv_cancel₀ hv
  obtain ⟨J, ψ, hJ, hu₁, hψ₀, hψ, hsol⟩ := exists_contDiffOn_implicitFunction (f := Φ)
    hopen hΦ.contDiffOn hinv (u := u) hu
  exact ⟨J, ψ, hJ, hu₁, hψ₀, hψ, fun s hs => hsol s hs⟩

end ProjectAinos.SmoothAlgebra
