/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.ODE.FlatFrame

/-! # Bundled curvature of coordinate connection coefficients

The coordinate curvature expression is trilinear. This supplies finite
basis tests and germ locality for the flatness condition used by radial
parallel-frame construction.
-/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open ContinuousLinearMap Set Filter
open scoped ContDiff Topology

namespace ProjectAInos.SmoothGeometry.LinearODE

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The trilinear coordinate curvature, with arguments `R(u,v)w`. -/
def coefficientCurvature (Γ : E → E →L[ℝ] E →L[ℝ] E) (x : E) :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] E :=
  let B := ((compL ℝ E (E →L[ℝ] E) (E →L[ℝ] E)).flip (Γ x)).comp
    ((compL ℝ E E E).comp (Γ x))
  fderiv ℝ Γ x - (fderiv ℝ Γ x).flip + B - B.flip

theorem coefficientCurvature_apply (Γ : E → E →L[ℝ] E →L[ℝ] E) (x u v w : E) :
    coefficientCurvature Γ x u v w =
      fderiv ℝ Γ x u v w - fderiv ℝ Γ x v u w +
        Γ x u (Γ x v w) - Γ x v (Γ x u w) := rfl

theorem isFlatConnectionOn_iff (Γ : E → E →L[ℝ] E →L[ℝ] E) (U : Set E) :
    IsFlatConnectionOn Γ U ↔ ∀ x ∈ U, coefficientCurvature Γ x = 0 := by
  constructor
  · intro h x hx
    ext u v w
    exact h x hx u v w
  · intro h x hx u v w
    have hz := congrArg (fun A : E →L[ℝ] E →L[ℝ] E →L[ℝ] E => A u v w) (h x hx)
    exact hz

theorem coefficientCurvature_congr {Γ Δ : E → E →L[ℝ] E →L[ℝ] E} {x : E}
    (h : Γ =ᶠ[𝓝 x] Δ) : coefficientCurvature Γ x = coefficientCurvature Δ x := by
  simp only [coefficientCurvature, h.fderiv_eq, h.self_of_nhds]

/-- Flatness is local in the coefficient germ, including its derivative. -/
theorem IsFlatConnectionOn.congr {Γ Δ : E → E →L[ℝ] E →L[ℝ] E} {U : Set E}
    (h : IsFlatConnectionOn Γ U) (hU : IsOpen U) (heq : EqOn Γ Δ U) :
    IsFlatConnectionOn Δ U := by
  rw [isFlatConnectionOn_iff] at h ⊢
  intro x hx
  have hg : Γ =ᶠ[𝓝 x] Δ := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact heq hy
  rw [← coefficientCurvature_congr hg]
  exact h x hx

/-- A finite coordinate basis suffices to test the whole trilinear map. -/
theorem coefficientCurvature_eq_zero_of_basis {n : ℕ}
    (Γ : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (x : Fin n → ℝ)
    (h : ∀ i j k, coefficientCurvature Γ x (Pi.single i 1) (Pi.single j 1)
      (Pi.single k 1) = 0) : coefficientCurvature Γ x = 0 := by
  ext u v w
  rw [pi_eq_sum_univ' u, pi_eq_sum_univ' v, pi_eq_sum_univ' w]
  simp only [map_sum, map_smul, sum_apply, smul_apply, h, smul_zero,
    Finset.sum_const_zero, zero_apply]

end ProjectAInos.SmoothGeometry.LinearODE
