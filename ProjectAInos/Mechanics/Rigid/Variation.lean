/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Rigid.Dynamics
public import ProjectAInos.Mechanics.EndpointAction
public import ProjectAInos.Variational.IntervalParameter

/-!
# The variation of a rotation

A curve of rotations `R(t)` has the angular velocity `Ω = vee (Rᵀ Ṙ)` in the
body frame (`curveVelocity`). For a smooth family `R(ε, t)` of orthogonal
matrices (`IsRotationFamily`) the derivative in the parameter is
`∂R/∂ε = R η̂` with `η = vee (Rᵀ ∂R/∂ε)` (`familyVariation`): every variation of
a rotation is of this form, and

`∂Ω/∂ε = ∂η/∂t + Ω × η` (`hasDerivAt_curveVelocity_family`).

For a vector `γ` fixed in space, `Γ = Rᵀ γ` varies by `∂Γ/∂ε = Γ × η`
(`hasDerivAt_bodyVector_family`).
-/

@[expose] public section
noncomputable section

open Set Matrix
open scoped ContDiff

namespace ProjectAInos.Mechanics.Rigid

/-! ### The derivative of a product of matrices, entry by entry -/

theorem hasDerivAt_transpose_mul {A B : ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    {A' B' : Matrix (Fin 3) (Fin 3) ℝ} {t : ℝ}
    (hA : ∀ a b, HasDerivAt (fun s => A s a b) (A' a b) t)
    (hB : ∀ a b, HasDerivAt (fun s => B s a b) (B' a b) t) (a b : Fin 3) :
    HasDerivAt (fun s => ((A s)ᵀ * B s) a b) ((A'ᵀ * B t + (A t)ᵀ * B') a b) t := by
  have h : HasDerivAt (fun s => ∑ k, A s k a * B s k b)
      (∑ k, (A' k a * B t k b + A t k a * B' k b)) t :=
    HasDerivAt.fun_sum fun k _ => (hA k a).mul (hB k b)
  refine h.congr_deriv ?_
  rw [Finset.sum_add_distrib]
  rfl

theorem vee_add (A B : Matrix (Fin 3) (Fin 3) ℝ) : vee (A + B) = vee A + vee B := by
  ext i
  fin_cases i <;> simp [vee]

/-- The derivative of the angular velocity of a curve of matrices. -/
theorem hasDerivAt_angularVelocityBody {A B : ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    {A' B' : Matrix (Fin 3) (Fin 3) ℝ} {t : ℝ}
    (hA : ∀ a b, HasDerivAt (fun s => A s a b) (A' a b) t)
    (hB : ∀ a b, HasDerivAt (fun s => B s a b) (B' a b) t) :
    HasDerivAt (fun s => angularVelocityBody (A s) (B s))
      (vee (A'ᵀ * B t + (A t)ᵀ * B')) t := by
  refine hasDerivAt_pi.mpr fun i => ?_
  fin_cases i
  · exact hasDerivAt_transpose_mul hA hB 2 1
  · exact hasDerivAt_transpose_mul hA hB 0 2
  · exact hasDerivAt_transpose_mul hA hB 1 0

/-- The algebraic identity behind `δΩ = η̇ + Ω × η`. -/
theorem vee_transpose_mul_hat {R : Matrix (Fin 3) (Fin 3) ℝ} (horth : Rᵀ * R = 1)
    (w η : Fin 3 → ℝ) :
    vee ((R * hat η)ᵀ * (R * hat w)) = vee ((R * hat w)ᵀ * (R * hat η)) + w ⨯₃ η := by
  have h (x y : Fin 3 → ℝ) : (R * hat x)ᵀ * (R * hat y) = -(hat x * hat y) := by
    rw [transpose_mul, transpose_hat, Matrix.mul_assoc, ← Matrix.mul_assoc Rᵀ, horth,
      Matrix.one_mul, Matrix.neg_mul]
  rw [h, h]
  ext i
  fin_cases i <;>
    simp [vee, hat, cross_apply] <;> ring

/-! ### Curves and families of rotations -/

/-- The derivative of a curve of matrices, entry by entry. -/
def curveDeriv (R : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun a b => deriv (fun s => R s a b) t

/-- The angular velocity of a curve of rotations, in the body frame. -/
def curveVelocity (R : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) : Fin 3 → ℝ :=
  angularVelocityBody (R t) (curveDeriv R t)

/-- Along a rigid motion the angular velocity of the curve of rotations is the
one of the motion. -/
theorem IsRigidMotion.curveVelocity_eq {c c' : ℝ → Fin 3 → ℝ}
    {R R' : ℝ → Matrix (Fin 3) (Fin 3) ℝ} (h : IsRigidMotion c c' R R') (t : ℝ) :
    curveVelocity R t = angularVelocityBody (R t) (R' t) := by
  have hd : curveDeriv R t = R' t := by
    ext a b
    exact (h.hasDerivAt_rotation t a b).deriv
  rw [curveVelocity, hd]

/-- A smooth family of orthogonal matrices; the parameter of the family is the
first variable and the time is the second. -/
structure IsRotationFamily (R : ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℝ) : Prop where
  contDiff : ∀ a b, ContDiff ℝ ∞ fun p => R p a b
  orthogonal : ∀ p, (R p)ᵀ * R p = 1

/-- The variation field `η = vee (Rᵀ ∂R/∂ε)` of a family, in the body frame. -/
def familyVariation (R : ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℝ) (p : ℝ × ℝ) : Fin 3 → ℝ :=
  angularVelocityBody (R p) (curveDeriv (fun e => R (e, p.2)) p.1)

/-- The derivative of a family in a direction of the plane of the parameter
and the time, entry by entry. -/
def familyDeriv (R : ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℝ) (v p : ℝ × ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun a b => fderiv ℝ (fun q => R q a b) p v

namespace IsRotationFamily

variable {R : ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℝ}

theorem differentiableAt (h : IsRotationFamily R) (a b : Fin 3) (p : ℝ × ℝ) :
    DifferentiableAt ℝ (fun q => R q a b) p :=
  (h.contDiff a b).differentiable (by simp) p

theorem contDiff_familyDeriv (h : IsRotationFamily R) (v : ℝ × ℝ) (a b : Fin 3) :
    ContDiff ℝ ∞ fun p => familyDeriv R v p a b :=
  ((h.contDiff a b).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem curveDeriv_time (h : IsRotationFamily R) (p : ℝ × ℝ) :
    curveDeriv (fun s => R (p.1, s)) p.2 = familyDeriv R (0, 1) p := by
  ext a b
  exact (hasDerivAt_family_time (g := fun q => R q a b) (h.differentiableAt a b p)).deriv

theorem curveDeriv_parameter (h : IsRotationFamily R) (p : ℝ × ℝ) :
    curveDeriv (fun e => R (e, p.2)) p.1 = familyDeriv R (1, 0) p := by
  ext a b
  exact (hasDerivAt_family_parameter (g := fun q => R q a b) (h.differentiableAt a b p)).deriv

theorem hasDerivAt_time (h : IsRotationFamily R) (ε t : ℝ) (a b : Fin 3) :
    HasDerivAt (fun s => R (ε, s) a b) (familyDeriv R (0, 1) (ε, t) a b) t :=
  hasDerivAt_family_time (g := fun q => R q a b) (h.differentiableAt a b (ε, t))

theorem hasDerivAt_parameter (h : IsRotationFamily R) (ε t : ℝ) (a b : Fin 3) :
    HasDerivAt (fun e => R (e, t) a b) (familyDeriv R (1, 0) (ε, t) a b) ε :=
  hasDerivAt_family_parameter (g := fun q => R q a b) (h.differentiableAt a b (ε, t))

/-- The mixed second derivative of a family. -/
def mixedDeriv (R : ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℝ) (p : ℝ × ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun a b => fderiv ℝ (fderiv ℝ fun q => R q a b) p (1, 0) (0, 1)

theorem hasDerivAt_familyDeriv_time_parameter (h : IsRotationFamily R) (ε t : ℝ) (a b : Fin 3) :
    HasDerivAt (fun e => familyDeriv R (0, 1) (e, t) a b) (mixedDeriv R (ε, t) a b) ε := by
  have hd : DifferentiableAt ℝ (fderiv ℝ fun q => R q a b) (ε, t) :=
    ((h.contDiff a b).fderiv_right (m := ∞) (by simp)).differentiable (by simp) _
  have h1 : HasDerivAt (fun e : ℝ => fderiv ℝ (fun q => R q a b) (e, t) (0, 1))
      (fderiv ℝ (fderiv ℝ fun q => R q a b) (ε, t) (1, 0) (0, 1)) ε := by
    have h0 := (hasDerivAt_family_parameter hd).clm_apply
      (hasDerivAt_const ε ((0 : ℝ), (1 : ℝ)))
    simpa using h0
  exact h1

theorem hasDerivAt_familyDeriv_parameter_time (h : IsRotationFamily R) (ε t : ℝ) (a b : Fin 3) :
    HasDerivAt (fun s => familyDeriv R (1, 0) (ε, s) a b) (mixedDeriv R (ε, t) a b) t := by
  have hd : DifferentiableAt ℝ (fderiv ℝ fun q => R q a b) (ε, t) :=
    ((h.contDiff a b).fderiv_right (m := ∞) (by simp)).differentiable (by simp) _
  have h1 : HasDerivAt (fun s : ℝ => fderiv ℝ (fun q => R q a b) (ε, s) (1, 0))
      (fderiv ℝ (fderiv ℝ fun q => R q a b) (ε, t) (0, 1) (1, 0)) t := by
    have h0 := (hasDerivAt_family_time hd).clm_apply
      (hasDerivAt_const t ((1 : ℝ), (0 : ℝ)))
    simpa using h0
  have hsymm := ((h.contDiff a b).contDiffAt (x := (ε, t))).isSymmSndFDerivAt (by simp)
    (1, 0) (0, 1)
  rw [mixedDeriv, Matrix.of_apply, hsymm]
  exact h1

/-- `∂R/∂t = R Ω̂`. -/
theorem familyDeriv_time (h : IsRotationFamily R) (p : ℝ × ℝ) :
    familyDeriv R (0, 1) p = R p * hat (curveVelocity (fun s => R (p.1, s)) p.2) := by
  have h1 := deriv_eq_mul_hat (R := fun s => R (p.1, s)) (R' := familyDeriv R (0, 1) p)
    (t := p.2) (h.hasDerivAt_time p.1 p.2) fun s => h.orthogonal (p.1, s)
  rw [curveVelocity, h.curveDeriv_time]
  exact h1

/-- `∂R/∂ε = R η̂`: every variation of a rotation is an infinitesimal rotation
in the body frame. -/
theorem familyDeriv_parameter (h : IsRotationFamily R) (p : ℝ × ℝ) :
    familyDeriv R (1, 0) p = R p * hat (familyVariation R p) := by
  have h1 := deriv_eq_mul_hat (R := fun e => R (e, p.2)) (R' := familyDeriv R (1, 0) p)
    (t := p.1) (h.hasDerivAt_parameter p.1 p.2) fun e => h.orthogonal (e, p.2)
  rw [familyVariation, h.curveDeriv_parameter]
  exact h1

/-- The derivative of the variation field in the time. -/
theorem hasDerivAt_familyVariation (h : IsRotationFamily R) (ε t : ℝ) :
    HasDerivAt (fun s => familyVariation R (ε, s))
      (vee ((familyDeriv R (0, 1) (ε, t))ᵀ * familyDeriv R (1, 0) (ε, t) +
        (R (ε, t))ᵀ * mixedDeriv R (ε, t))) t := by
  have h1 := hasDerivAt_angularVelocityBody (A := fun s => R (ε, s))
    (B := fun s => familyDeriv R (1, 0) (ε, s)) (h.hasDerivAt_time ε t)
    (h.hasDerivAt_familyDeriv_parameter_time ε t)
  have heq : (fun s => familyVariation R (ε, s)) =
      fun s => angularVelocityBody (R (ε, s)) (familyDeriv R (1, 0) (ε, s)) :=
    funext fun s => by rw [familyVariation, h.curveDeriv_parameter]
  rw [heq]
  exact h1

/-- `∂Ω/∂ε = ∂η/∂t + Ω × η`. -/
theorem hasDerivAt_curveVelocity_family (h : IsRotationFamily R) (ε t : ℝ) :
    HasDerivAt (fun e => curveVelocity (fun s => R (e, s)) t)
      (deriv (fun s => familyVariation R (ε, s)) t +
        curveVelocity (fun s => R (ε, s)) t ⨯₃ familyVariation R (ε, t)) ε := by
  have h1 := hasDerivAt_angularVelocityBody (A := fun e => R (e, t))
    (B := fun e => familyDeriv R (0, 1) (e, t)) (h.hasDerivAt_parameter ε t)
    (h.hasDerivAt_familyDeriv_time_parameter ε t)
  have heq : (fun e => curveVelocity (fun s => R (e, s)) t) =
      fun e => angularVelocityBody (R (e, t)) (familyDeriv R (0, 1) (e, t)) :=
    funext fun e => by rw [curveVelocity, h.curveDeriv_time (e, t)]
  rw [heq]
  refine h1.congr_deriv ?_
  rw [(h.hasDerivAt_familyVariation ε t).deriv, vee_add, vee_add, add_right_comm]
  congr 1
  have ht := h.familyDeriv_time (ε, t)
  have hp := h.familyDeriv_parameter (ε, t)
  rw [ht, hp]
  exact vee_transpose_mul_hat (h.orthogonal (ε, t)) _ _

/-- A vector fixed in space varies by `∂Γ/∂ε = Γ × η` in the body frame. -/
theorem hasDerivAt_bodyVector_family (h : IsRotationFamily R) (γ : Fin 3 → ℝ) (ε t : ℝ) :
    HasDerivAt (fun e => (R (e, t))ᵀ *ᵥ γ)
      (((R (ε, t))ᵀ *ᵥ γ) ⨯₃ familyVariation R (ε, t)) ε := by
  have h1 := hasDerivAt_transpose_mulVec (R := fun e => R (e, t))
    (h.hasDerivAt_parameter ε t) (fun e => h.orthogonal (e, t)) γ
  rw [familyVariation, h.curveDeriv_parameter]
  exact h1

end IsRotationFamily

end ProjectAInos.Mechanics.Rigid
