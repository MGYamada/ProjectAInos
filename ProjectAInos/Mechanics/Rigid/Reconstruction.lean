/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Rigid.Dynamics
public import ProjectAInos.SmoothGeometry.ODE.Propagator
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# The rotation of a body with a given angular velocity

Euler's equations determine the angular velocity `Ω(t)` in the body frame. The
rotation is then the solution of `Ṙ = R Ω̂`, a linear equation with a
continuous coefficient: the rows of `R` solve `u̇ = u × Ω`.

* `rotation Ω R₀`: the solution with `R(0) = R₀`, for every continuous `Ω` and
  all times (`hasDerivAt_rotation`, `rotation_zero`); it is the only one
  (`eq_rotation_of_hasDerivAt`).
* `rotation_transpose_mul`, `det_rotation`: it is a rotation if `R₀` is one, so
  that it is a rigid motion with the angular velocity `Ω`
  (`isRigidMotion_rotation`, `angularVelocityBody_rotation`). It is smooth
  in the time if `Ω` is (`contDiff_rotation`).
* `hasDerivAt_rotation_mulVec`: `d(R L)/dt = R (L̇ − L × Ω)`. Hence, if
  `L̇ = L × Ω`, the vector `R L` is constant (`rotation_mulVec_eq`): a solution
  of Euler's equations for the free body gives a motion with a constant
  angular momentum in space.
-/

@[expose] public section
noncomputable section

open Set Matrix
open scoped ContDiff

namespace ProjectAInos.Mechanics.Rigid

open SmoothGeometry SmoothGeometry.LinearODE

/-! ### Identities of the cross product -/

theorem cross_dotProduct_add (u v w : Fin 3 → ℝ) : (u ⨯₃ w) ⬝ᵥ v + u ⬝ᵥ (v ⨯₃ w) = 0 := by
  simp [cross_apply, dotProduct, Fin.sum_univ_three]
  ring

theorem triple_cross_eq_zero (u₀ u₁ u₂ w : Fin 3 → ℝ) :
    (u₀ ⨯₃ w) ⬝ᵥ (u₁ ⨯₃ u₂) + u₀ ⬝ᵥ ((u₁ ⨯₃ w) ⨯₃ u₂ + u₁ ⨯₃ (u₂ ⨯₃ w)) = 0 := by
  simp [cross_apply, dotProduct, Fin.sum_univ_three]
  ring

theorem det_eq_dotProduct_cross (M : Matrix (Fin 3) (Fin 3) ℝ) :
    M.det = (M 0) ⬝ᵥ ((M 1) ⨯₃ (M 2)) := by
  rw [det_fin_three]
  simp [cross_apply, dotProduct, Fin.sum_univ_three]
  ring

/-- The rows of `R Ω̂` are the cross products of the rows of `R` with `Ω`. -/
theorem mul_hat_apply (R : Matrix (Fin 3) (Fin 3) ℝ) (w : Fin 3 → ℝ) (a b : Fin 3) :
    (R * hat w) a b = ((R a) ⨯₃ w) b := by
  fin_cases b <;> simp [Matrix.mul_apply, hat, Fin.sum_univ_three, cross_apply] <;> ring

/-! ### The equation of the rows -/

/-- The operator `u ↦ u × w`, linear in `w`. -/
def crossRight : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := Fin 3 → ℝ)
    (F' := Fin 3 → ℝ)).toLinearMap ∘ₗ (crossProduct (R := ℝ)).flip

@[simp] theorem crossRight_apply (w u : Fin 3 → ℝ) : crossRight w u = u ⨯₃ w := rfl

/-- The coefficient of the equation `u̇ = u × Ω(t)` of the rows of the rotation. -/
def rowCoefficient (Ω : C(ℝ, Fin 3 → ℝ)) : C(ℝ, (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) :=
  ⟨fun t => crossRight (Ω t), crossRight.continuous_of_finiteDimensional.comp Ω.continuous⟩

@[simp] theorem rowCoefficient_apply (Ω : C(ℝ, Fin 3 → ℝ)) (t : ℝ) (u : Fin 3 → ℝ) :
    rowCoefficient Ω t u = u ⨯₃ Ω t := rfl

/-- The rotation with the angular velocity `Ω` in the body frame that is `R₀`
at the time `0`. -/
def rotation (Ω : C(ℝ, Fin 3 → ℝ)) (R₀ : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun a => propagator (rowCoefficient Ω) t 0 (R₀ a)

variable (Ω : C(ℝ, Fin 3 → ℝ)) (R₀ : Matrix (Fin 3) (Fin 3) ℝ)

@[simp] theorem rotation_zero : rotation Ω R₀ 0 = R₀ := by
  ext a b
  simp [rotation]

/-- The rows of the rotation solve `u̇ = u × Ω`. -/
theorem hasDerivAt_rotation_row (a : Fin 3) (t : ℝ) :
    HasDerivAt (fun s => rotation Ω R₀ s a) ((rotation Ω R₀ t a) ⨯₃ Ω t) t :=
  hasDerivAt_propagator_apply (rowCoefficient Ω) t 0 (R₀ a)

/-- `Ṙ = R Ω̂`, entry by entry. -/
theorem hasDerivAt_rotation (t : ℝ) (a b : Fin 3) :
    HasDerivAt (fun s => rotation Ω R₀ s a b) ((rotation Ω R₀ t * hat (Ω t)) a b) t := by
  rw [mul_hat_apply]
  exact hasDerivAt_pi.mp (hasDerivAt_rotation_row Ω R₀ a t) b

/-- The scalar products of the rows are constant. -/
theorem rotation_dotProduct (a b : Fin 3) (t : ℝ) :
    (rotation Ω R₀ t a) ⬝ᵥ (rotation Ω R₀ t b) = (R₀ a) ⬝ᵥ (R₀ b) := by
  have hd : ∀ s, HasDerivAt (fun s => (rotation Ω R₀ s a) ⬝ᵥ (rotation Ω R₀ s b)) 0 s := by
    intro s
    refine (hasDerivAt_dotProduct (hasDerivAt_rotation_row Ω R₀ a s)
      (hasDerivAt_rotation_row Ω R₀ b s)).congr_deriv ?_
    exact cross_dotProduct_add _ _ _
  have h := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  rw [h, rotation_zero]

/-- The rotation stays orthogonal. -/
theorem rotation_mul_transpose (h₀ : R₀ * R₀ᵀ = 1) (t : ℝ) :
    rotation Ω R₀ t * (rotation Ω R₀ t)ᵀ = 1 := by
  ext a b
  have h := congrFun (congrFun h₀ a) b
  rw [Matrix.mul_apply] at h ⊢
  simp only [Matrix.transpose_apply] at h ⊢
  rw [← h]
  exact rotation_dotProduct Ω R₀ a b t

theorem rotation_transpose_mul (h₀ : R₀ᵀ * R₀ = 1) (t : ℝ) :
    (rotation Ω R₀ t)ᵀ * rotation Ω R₀ t = 1 :=
  mul_eq_one_comm.mp (rotation_mul_transpose Ω R₀ (mul_eq_one_comm.mp h₀) t)

/-- The determinant of the rotation is constant. -/
theorem det_rotation (t : ℝ) : (rotation Ω R₀ t).det = R₀.det := by
  have hd : ∀ s, HasDerivAt (fun s => (rotation Ω R₀ s 0) ⬝ᵥ
      ((rotation Ω R₀ s 1) ⨯₃ (rotation Ω R₀ s 2))) 0 s := by
    intro s
    refine (hasDerivAt_dotProduct (hasDerivAt_rotation_row Ω R₀ 0 s)
      (hasDerivAt_cross (hasDerivAt_rotation_row Ω R₀ 1 s)
        (hasDerivAt_rotation_row Ω R₀ 2 s))).congr_deriv ?_
    exact triple_cross_eq_zero _ _ _ _
  have h := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  rw [det_eq_dotProduct_cross, det_eq_dotProduct_cross, h, rotation_zero]

/-- The solution of `Ṙ = R Ω̂` from a rotation is a rigid motion about a fixed
point. -/
theorem isRigidMotion_rotation (h₀ : R₀ᵀ * R₀ = 1) (hdet : R₀.det = 1) :
    IsRigidMotion (fun _ => 0) (fun _ => 0) (rotation Ω R₀)
      (fun t => rotation Ω R₀ t * hat (Ω t)) where
  hasDerivAt_origin s := hasDerivAt_const s 0
  hasDerivAt_rotation s a b := hasDerivAt_rotation Ω R₀ s a b
  orthogonal := rotation_transpose_mul Ω R₀ h₀
  det_eq_one s := (det_rotation Ω R₀ s).trans hdet

/-- The angular velocity of the reconstructed rotation is `Ω`. -/
theorem angularVelocityBody_rotation (h₀ : R₀ᵀ * R₀ = 1) (t : ℝ) :
    angularVelocityBody (rotation Ω R₀ t) (rotation Ω R₀ t * hat (Ω t)) = Ω t := by
  rw [angularVelocityBody, ← Matrix.mul_assoc, rotation_transpose_mul Ω R₀ h₀, Matrix.one_mul,
    vee_hat]

/-- Uniqueness: a curve of matrices with `Ṙ = R Ω̂` is the reconstructed
rotation from its value at the time `0`. -/
theorem eq_rotation_of_hasDerivAt {R : ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hR : ∀ t a b, HasDerivAt (fun s => R s a b) ((R t * hat (Ω t)) a b) t) (t : ℝ) :
    R t = rotation Ω (R 0) t := by
  ext a b
  have hrow : ∀ s, HasDerivAt (fun u => R u a) (rowCoefficient Ω s (R s a)) s := by
    intro s
    refine hasDerivAt_pi.mpr fun j => ?_
    have h := hR s a j
    rwa [mul_hat_apply] at h
  have h := eq_propagator_apply_of_hasDerivAt (rowCoefficient Ω) (f := fun u => R u a)
    (s := 0) (t := t)
    (continuous_iff_continuousAt.mpr fun s => (hrow s).continuousAt).continuousOn
    (fun s _ => hrow s)
  exact congrFun h b

variable {Ω R₀}

/-- For a smooth angular velocity the rotation is smooth in the time. -/
theorem contDiff_rotation (hΩ : ContDiff ℝ ∞ Ω) (R₀ : Matrix (Fin 3) (Fin 3) ℝ) (a b : Fin 3) :
    ContDiff ℝ ∞ fun t => rotation Ω R₀ t a b := by
  have hA : ContDiff ℝ ∞ (rowCoefficient Ω) :=
    ContDiff.comp (g := fun w : Fin 3 → ℝ => crossRight w) (f := fun t : ℝ => Ω t)
      (LinearMap.toContinuousLinearMap crossRight).contDiff hΩ
  have h1 : ContDiff ℝ ∞ fun t : ℝ => propagator (rowCoefficient Ω) t 0 :=
    ContDiff.comp (g := fun q : ℝ × ℝ => propagator (rowCoefficient Ω) q.1 q.2)
      (f := fun t : ℝ => (t, (0 : ℝ))) (propagator_contDiff_of_contDiff hA)
      (contDiff_id.prodMk contDiff_const)
  have h2 : ContDiff ℝ ∞ fun t : ℝ => propagator (rowCoefficient Ω) t 0 (R₀ a) :=
    h1.clm_apply contDiff_const
  exact contDiff_pi.mp h2 b

/-- `d(R L)/dt = R (L̇ − L × Ω)` for a curve `L` in the body frame. -/
theorem hasDerivAt_rotation_mulVec {L : ℝ → Fin 3 → ℝ} {L' : Fin 3 → ℝ} {t : ℝ}
    (hL : HasDerivAt L L' t) :
    HasDerivAt (fun s => rotation Ω R₀ s *ᵥ L s) (rotation Ω R₀ t *ᵥ (L' - L t ⨯₃ Ω t)) t := by
  refine (hasDerivAt_mulVec (hasDerivAt_rotation Ω R₀ t) hL).congr_deriv ?_
  rw [← mulVec_mulVec, hat_mulVec, ← mulVec_add, ← cross_anticomm, neg_add_eq_sub]

/-- If `L̇ = L × Ω`, the vector `R L` is constant: the angular momentum of the
free body is constant in space. -/
theorem rotation_mulVec_eq {L : ℝ → Fin 3 → ℝ} (hL : ∀ t, HasDerivAt L (L t ⨯₃ Ω t) t)
    (t : ℝ) : rotation Ω R₀ t *ᵥ L t = R₀ *ᵥ L 0 := by
  have hd : ∀ s, HasDerivAt (fun s => rotation Ω R₀ s *ᵥ L s) 0 s := by
    intro s
    refine (hasDerivAt_rotation_mulVec (hL s)).congr_deriv ?_
    rw [sub_self, mulVec_zero]
  have h := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  rw [h, rotation_zero]

end ProjectAInos.Mechanics.Rigid
