/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.EndpointAction

/-!
# The variation of the integral of a one-form along a family of curves

Let `θ` be a continuous bilinear form, read as the one-form `w ↦ θ(z)(w)` at the
point `z`, and let `γ(ε, r)` be a family of curves. `hasDerivAt_lineIntegral`:

`d/dε ∫ θ(γ)(∂ᵣγ) dr = [θ(γ)(∂_εγ)] + ∫ (θ(∂_εγ)(∂ᵣγ) − θ(∂ᵣγ)(∂_εγ)) dr`.

The integrand of the last integral is the exterior derivative of the one-form
on the two partial derivatives. For the canonical one-form `p dq` it is the
symplectic form `ω(∂ᵣγ, ∂_εγ)`. The family is twice continuously
differentiable at the points of the reference curve.
-/

@[expose] public section
noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval

namespace ProjectAInos.Mechanics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The first variation of the integral of the one-form `θ` along a family of
curves. -/
theorem hasDerivAt_lineIntegral (θ : E →L[ℝ] E →L[ℝ] ℝ) {γ : ℝ × ℝ → E} {ε₀ a b : ℝ}
    (hγ : ∀ r ∈ uIcc a b, ContDiffAt ℝ 2 γ (ε₀, r)) :
    HasDerivAt (fun ε => ∫ r in a..b, θ (γ (ε, r)) (deriv (fun t => γ (ε, t)) r))
      (θ (γ (ε₀, b)) (fderiv ℝ γ (ε₀, b) (1, 0)) -
          θ (γ (ε₀, a)) (fderiv ℝ γ (ε₀, a) (1, 0)) +
        ∫ r in a..b, (θ (fderiv ℝ γ (ε₀, r) (1, 0)) (fderiv ℝ γ (ε₀, r) (0, 1)) -
          θ (fderiv ℝ γ (ε₀, r) (0, 1)) (fderiv ℝ γ (ε₀, r) (1, 0)))) ε₀ := by
  have hd : ∀ r ∈ uIcc a b, DifferentiableAt ℝ γ (ε₀, r) := fun r hr =>
    (hγ r hr).differentiableAt (by simp)
  have hγ1 : ∀ r ∈ uIcc a b, ContDiffAt ℝ 1 (fderiv ℝ γ) (ε₀, r) := fun r hr =>
    (hγ r hr).fderiv_right (m := 1) (by norm_num)
  have hd' : ∀ r ∈ uIcc a b, DifferentiableAt ℝ (fderiv ℝ γ) (ε₀, r) := fun r hr =>
    (hγ1 r hr).differentiableAt one_ne_zero
  -- the integrand near the reference curve
  have hG : ∀ r ∈ uIcc a b,
      ContDiffAt ℝ 1 (fun p : ℝ × ℝ => θ (γ p) (fderiv ℝ γ p (0, 1))) (ε₀, r) := fun r hr =>
    (θ.contDiff.contDiffAt.comp _ ((hγ r hr).of_le (by norm_num))).clm_apply
      ((hγ1 r hr).clm_apply contDiffAt_const)
  have hev : ∀ r ∈ uIcc a b,
      (fun p : ℝ × ℝ => θ (γ p) (deriv (fun t => γ (p.1, t)) p.2)) =ᶠ[𝓝 (ε₀, r)]
        fun p : ℝ × ℝ => θ (γ p) (fderiv ℝ γ p (0, 1)) := fun r hr => by
    filter_upwards [(hγ r hr).eventually (by simp)] with p hp
    rw [deriv_family_time (hp.differentiableAt (by simp))]
  have hF : ∀ r ∈ uIcc a b, ContDiffAt ℝ 1
      (fun p : ℝ × ℝ => θ (γ p) (deriv (fun t => γ (p.1, t)) p.2)) (ε₀, r) := fun r hr =>
    (hG r hr).congr_of_eventuallyEq (hev r hr)
  have hD : ∀ r ∈ uIcc a b,
      HasDerivAt (fun ε => θ (γ (ε, r)) (deriv (fun t => γ (ε, t)) r))
        (θ (fderiv ℝ γ (ε₀, r) (1, 0)) (fderiv ℝ γ (ε₀, r) (0, 1)) +
          θ (γ (ε₀, r)) (fderiv ℝ (fderiv ℝ γ) (ε₀, r) (1, 0) (0, 1))) ε₀ := by
    intro r hr
    have h1 : HasDerivAt (fun ε => θ (γ (ε, r))) (θ (fderiv ℝ γ (ε₀, r) (1, 0))) ε₀ :=
      θ.hasFDerivAt.comp_hasDerivAt ε₀ (hasDerivAt_family_parameter (hd r hr))
    have h2 : HasDerivAt (fun ε => fderiv ℝ γ (ε, r) (0, 1))
        (fderiv ℝ (fderiv ℝ γ) (ε₀, r) (1, 0) (0, 1)) ε₀ := by
      have h := (hasDerivAt_family_parameter (hd' r hr)).clm_apply
        (hasDerivAt_const ε₀ ((0 : ℝ), (1 : ℝ)))
      simpa using h
    have heq : (fun ε => θ (γ (ε, r)) (deriv (fun t => γ (ε, t)) r)) =ᶠ[𝓝 ε₀]
        fun ε => θ (γ (ε, r)) (fderiv ℝ γ (ε, r) (0, 1)) := by
      have hc' : Tendsto (fun ε : ℝ => (ε, r)) (𝓝 ε₀) (𝓝 (ε₀, r)) :=
        (continuous_id.prodMk continuous_const).continuousAt
      exact hc'.eventually (hev r hr)
    exact (h1.clm_apply h2).congr_of_eventuallyEq heq
  have hmain := Variational.hasDerivAt_intervalIntegral_of_contDiffAt
    (F := fun p : ℝ × ℝ => θ (γ p) (deriv (fun t => γ (p.1, t)) p.2)) hF hD
  -- integration by parts along the reference curve
  have hη : ∀ r ∈ uIcc a b, ContDiffAt ℝ 1 (fun t => fderiv ℝ γ (ε₀, t) (1, 0)) r :=
    fun r hr => (ContDiffAt.comp (g := fderiv ℝ γ) (f := fun t : ℝ => (ε₀, t)) r (hγ1 r hr)
      (contDiffAt_const.prodMk contDiffAt_id)).clm_apply contDiffAt_const
  have hγ0 : ∀ r ∈ uIcc a b, ContDiffAt ℝ 1 (fun t => γ (ε₀, t)) r := fun r hr =>
    ContDiffAt.comp (g := γ) (f := fun t : ℝ => (ε₀, t)) r ((hγ r hr).of_le (by norm_num))
      (contDiffAt_const.prodMk contDiffAt_id)
  have hP : ∀ r ∈ uIcc a b,
      ContDiffAt ℝ 1 (fun t => θ (γ (ε₀, t)) (fderiv ℝ γ (ε₀, t) (1, 0))) r := fun r hr =>
    (θ.contDiff.contDiffAt.comp r (hγ0 r hr)).clm_apply (hη r hr)
  have hDc := Variational.continuousOn_parameter_derivative
    (F := fun p : ℝ × ℝ => θ (γ p) (deriv (fun t => γ (p.1, t)) p.2)) hF hD
  have hPd : ∀ r ∈ uIcc a b,
      HasDerivAt (fun t => θ (γ (ε₀, t)) (fderiv ℝ γ (ε₀, t) (1, 0)))
        ((fun r => θ (fderiv ℝ γ (ε₀, r) (1, 0)) (fderiv ℝ γ (ε₀, r) (0, 1)) +
            θ (γ (ε₀, r)) (fderiv ℝ (fderiv ℝ γ) (ε₀, r) (1, 0) (0, 1))) r -
          (fun r => θ (fderiv ℝ γ (ε₀, r) (1, 0)) (fderiv ℝ γ (ε₀, r) (0, 1)) -
            θ (fderiv ℝ γ (ε₀, r) (0, 1)) (fderiv ℝ γ (ε₀, r) (1, 0))) r) r := by
    intro r hr
    have h1 : HasDerivAt (fun t => θ (γ (ε₀, t))) (θ (fderiv ℝ γ (ε₀, r) (0, 1))) r :=
      θ.hasFDerivAt.comp_hasDerivAt r (hasDerivAt_family_time (hd r hr))
    have h2 : HasDerivAt (fun t => fderiv ℝ γ (ε₀, t) (1, 0))
        (fderiv ℝ (fderiv ℝ γ) (ε₀, r) (0, 1) (1, 0)) r := by
      have h := (hasDerivAt_family_time (hd' r hr)).clm_apply
        (hasDerivAt_const r ((1 : ℝ), (0 : ℝ)))
      simpa using h
    have hsymm := ((hγ r hr).isSymmSndFDerivAt (by simp)) (1, 0) (0, 1)
    refine (h1.clm_apply h2).congr_deriv ?_
    beta_reduce
    rw [hsymm]
    ring
  have hint := Variational.integral_eq_boundary_add_residual hP hDc hPd
  refine hmain.congr_deriv ?_
  rw [hint]

end ProjectAInos.Mechanics
