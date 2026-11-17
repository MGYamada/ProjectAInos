/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAinos.Mechanics.Poisson.RigidBodyEquations

/-! Typed contracts for the equations of motion of a rigid body: the balance of
the momentum and of the angular momentum for a rigid motion of point masses,
the rotation with a given angular velocity, the variation of a rotation,
Hamilton's principle on the rotations, and the Lie–Poisson equations. These
examples use default elaborator options. -/

open ProjectAinos ProjectAinos.Mechanics ProjectAinos.Mechanics.Rigid
open ProjectAinos.Mechanics.RigidBody
open ProjectAinos.SmoothAlgebra ProjectAinos.SmoothAlgebra.FreeSmoothRing
open ProjectAinos.SmoothGeometry ProjectAinos.SmoothGeometry.LinearODE
open ProjectAinos.SmoothGeometry.JacobiElliptic
open Set Matrix MeasureTheory
open scoped ContDiff

noncomputable section

section Dynamics

variable {ι : Type*} [Fintype ι] {m : ι → ℝ} {r : ι → Fin 3 → ℝ}
  {c c' : ℝ → Fin 3 → ℝ} {R R' : ℝ → Matrix (Fin 3) (Fin 3) ℝ}

example (A : Matrix (Fin 3) (Fin 3) ℝ) (x y : Fin 3 → ℝ) :
    (A *ᵥ x) ⨯₃ (A *ᵥ y) = (adjugate A)ᵀ *ᵥ (x ⨯₃ y) :=
  mulVec_cross_mulVec A x y

example {R : Matrix (Fin 3) (Fin 3) ℝ} (horth : Rᵀ * R = 1)
    (hdet : R.det = 1) :
    adjugate R = Rᵀ :=
  adjugate_eq_transpose horth hdet

example {R : Matrix (Fin 3) (Fin 3) ℝ} (horth : Rᵀ * R = 1) (hdet : R.det = 1)
    (x y : Fin 3 → ℝ) :
    (R *ᵥ x) ⨯₃ (R *ᵥ y) = R *ᵥ (x ⨯₃ y) :=
  mulVec_cross horth hdet x y

example {R : Matrix (Fin 3) (Fin 3) ℝ} (horth : Rᵀ * R = 1)
    (x : Fin 3 → ℝ) :
    Rᵀ *ᵥ (R *ᵥ x) = x :=
  transpose_mulVec_mulVec horth x

example {R : Matrix (Fin 3) (Fin 3) ℝ} (horth : Rᵀ * R = 1)
    (x : Fin 3 → ℝ) :
    R *ᵥ (Rᵀ *ᵥ x) = x :=
  mulVec_transpose_mulVec horth x

example {R : Matrix (Fin 3) (Fin 3) ℝ} (horth : Rᵀ * R = 1)
    (x y : Fin 3 → ℝ) :
    (R *ᵥ x) ⬝ᵥ (R *ᵥ y) = x ⬝ᵥ y :=
  mulVec_dotProduct_mulVec horth x y

example {R : Matrix (Fin 3) (Fin 3) ℝ} (horth : Rᵀ * R = 1)
    (hdet : R.det = 1) (x y : Fin 3 → ℝ) :
    Rᵀ *ᵥ ((R *ᵥ x) ⨯₃ y) = x ⨯₃ (Rᵀ *ᵥ y) :=
  transpose_mulVec_cross horth hdet x y

example {x y : ℝ → Fin 3 → ℝ} {x' y' : Fin 3 → ℝ} {t : ℝ}
    (hx : HasDerivAt x x' t) (hy : HasDerivAt y y' t) :
    HasDerivAt (fun s => x s ⬝ᵥ y s) (x' ⬝ᵥ y t + x t ⬝ᵥ y') t :=
  hasDerivAt_dotProduct hx hy

example {x y : ℝ → Fin 3 → ℝ} {x' y' : Fin 3 → ℝ} {t : ℝ}
    (hx : HasDerivAt x x' t) (hy : HasDerivAt y y' t) :
    HasDerivAt (fun s => x s ⨯₃ y s) (x' ⨯₃ y t + x t ⨯₃ y') t :=
  hasDerivAt_cross hx hy

example {R : ℝ → Matrix (Fin 3) (Fin 3) ℝ} {R' : Matrix (Fin 3) (Fin 3) ℝ}
    {x : ℝ → Fin 3 → ℝ} {x' : Fin 3 → ℝ} {t : ℝ}
    (hR : ∀ a b, HasDerivAt (fun s => R s a b) (R' a b) t) (hx : HasDerivAt x x' t) :
    HasDerivAt (fun s => R s *ᵥ x s) (R' *ᵥ x t + R t *ᵥ x') t :=
  hasDerivAt_mulVec hR hx

example {R : ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    {R' : Matrix (Fin 3) (Fin 3) ℝ} {t : ℝ}
    (hR : ∀ a b, HasDerivAt (fun s => R s a b) (R' a b) t)
    (horth : ∀ s, (R s)ᵀ * R s = 1) :
    ((R t)ᵀ * R')ᵀ = -((R t)ᵀ * R') :=
  transpose_mul_deriv_transpose hR horth

example (R R' : Matrix (Fin 3) (Fin 3) ℝ) :
    angularVelocityBody R R' =
      vee (Rᵀ * R') := rfl

example {R : ℝ → Matrix (Fin 3) (Fin 3) ℝ} {R' : Matrix (Fin 3) (Fin 3) ℝ}
    {t : ℝ} (hR : ∀ a b, HasDerivAt (fun s => R s a b) (R' a b) t)
    (horth : ∀ s, (R s)ᵀ * R s = 1) :
    R' = R t * hat (angularVelocityBody (R t) R') :=
  deriv_eq_mul_hat hR horth

example {R : ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    {R' : Matrix (Fin 3) (Fin 3) ℝ} {t : ℝ}
    (hR : ∀ a b, HasDerivAt (fun s => R s a b) (R' a b) t)
    (horth : ∀ s, (R s)ᵀ * R s = 1) (e : Fin 3 → ℝ) :
    HasDerivAt (fun u => (R u)ᵀ *ᵥ e) (((R t)ᵀ *ᵥ e) ⨯₃ angularVelocityBody (R t) R') t :=
  hasDerivAt_transpose_mulVec hR horth e

example (A : Matrix (Fin 3) (Fin 3) ℝ) (x : ι → Fin 3 → ℝ) :
    A *ᵥ ∑ a, x a = ∑ a, A *ᵥ x a :=
  mulVec_sum A x

example (x : ι → Fin 3 → ℝ) (y : Fin 3 → ℝ) :
    (∑ a, x a) ⨯₃ y = ∑ a, x a ⨯₃ y :=
  sum_cross x y

example (x : Fin 3 → ℝ) (y : ι → Fin 3 → ℝ) :
    x ⨯₃ ∑ a, y a = ∑ a, x ⨯₃ y a :=
  cross_sum x y

example {f : ι → ι → Fin 3 → ℝ} (hf : ∀ a b, f a b = -f b a) :
    ∑ a, ∑ b, f a b = 0 :=
  sum_internal_force hf

example {f : ι → ι → Fin 3 → ℝ} (hf : ∀ a b, f a b = -f b a)
    {q : ι → Fin 3 → ℝ} (hq : ∀ a b, (q a - q b) ⨯₃ f a b = 0) (c : Fin 3 → ℝ) :
    ∑ a, (q a - c) ⨯₃ ∑ b, f a b = 0 :=
  sum_cross_internal_force hf hq c

example {R : Matrix (Fin 3) (Fin 3) ℝ} (horth : Rᵀ * R = 1)
    (hdet : R.det = 1) (m : ι → ℝ) (r : ι → Fin 3 → ℝ) (g : ℝ) (e : Fin 3 → ℝ) :
    Rᵀ *ᵥ ∑ a, (R *ᵥ r a) ⨯₃ (-(m a * g) • e) = (Rᵀ *ᵥ e) ⨯₃ (g • ∑ a, m a • r a) :=
  transpose_mulVec_sum_cross_weight horth hdet m r g e

example (h : IsRigidMotion c c' R R') (s : ℝ) : HasDerivAt c (c' s) s :=
  h.hasDerivAt_origin s

example (h : IsRigidMotion c c' R R') (s : ℝ) (a b : Fin 3) :
    HasDerivAt (fun u => R u a b) (R' s a b) s :=
  h.hasDerivAt_rotation s a b

example (h : IsRigidMotion c c' R R') (s : ℝ) : (R s)ᵀ * R s = 1 :=
  h.orthogonal s

example (h : IsRigidMotion c c' R R') (s : ℝ) : (R s).det = 1 :=
  h.det_eq_one s

example (h : IsRigidMotion c c' R R') (s : ℝ) :
    R' s = R s * hat (angularVelocityBody (R s) (R' s)) :=
  IsRigidMotion.rotation_deriv h s

example (h : IsRigidMotion c c' R R') (r₀ : Fin 3 → ℝ) (s : ℝ) :
    HasDerivAt (fun u => c u + R u *ᵥ r₀) (c' s + R' s *ᵥ r₀) s :=
  IsRigidMotion.hasDerivAt_position h r₀ s

example (h : IsRigidMotion c c' R R') (r₀ : Fin 3 → ℝ) (s : ℝ) :
    R' s *ᵥ r₀ = R s *ᵥ (angularVelocityBody (R s) (R' s) ⨯₃ r₀) :=
  IsRigidMotion.deriv_mulVec h r₀ s

example (h : IsRigidMotion c c' R R') (e : Fin 3 → ℝ) (t : ℝ) :
    HasDerivAt (fun u => (R u)ᵀ *ᵥ e)
      (((R t)ᵀ *ᵥ e) ⨯₃ angularVelocityBody (R t) (R' t)) t :=
  IsRigidMotion.hasDerivAt_bodyVector h e t

example (hcm : ∑ a, m a • r a = 0) (v : Fin 3 → ℝ)
    (A : Matrix (Fin 3) (Fin 3) ℝ) :
    ∑ a, m a • (v + A *ᵥ r a) = (∑ a, m a) • v :=
  IsRigidMotion.sum_smul_velocity hcm v A

example (hcm : ∑ a, m a • r a = 0) {F : ι → Fin 3 → ℝ} {t : ℝ}
    (hF : ∀ a, HasDerivAt (fun u => m a • (c' u + R' u *ᵥ r a)) (F a) t) :
    HasDerivAt (fun u => (∑ a, m a) • c' u) (∑ a, F a) t :=
  IsRigidMotion.hasDerivAt_momentum hcm hF

example (h : IsRigidMotion c c' R R') (m : ι → ℝ)
    (r : ι → Fin 3 → ℝ) (s : ℝ) :
    ∑ a, m a • ((R s *ᵥ r a) ⨯₃ (R' s *ᵥ r a)) =
      R s *ᵥ (inertia m r *ᵥ angularVelocityBody (R s) (R' s)) :=
  IsRigidMotion.sum_smul_cross_velocity h m r s

example (h : IsRigidMotion c c' R R') (m : ι → ℝ)
    (r : ι → Fin 3 → ℝ) (s : ℝ) :
    ∑ a, (R s *ᵥ r a) ⨯₃ (m a • (c' s + R' s *ᵥ r a)) =
      R s *ᵥ (inertia m r *ᵥ angularVelocityBody (R s) (R' s)) +
        (R s *ᵥ ∑ a, m a • r a) ⨯₃ c' s :=
  IsRigidMotion.sum_cross_smul_velocity h m r s

example (h : IsRigidMotion c c' R R')
    (hpt : ∑ a, m a • r a = 0 ∨ ∀ s, c' s = 0) {F : ι → Fin 3 → ℝ} {t : ℝ}
    (hF : ∀ a, HasDerivAt (fun u => m a • (c' u + R' u *ᵥ r a)) (F a) t) :
    HasDerivAt (fun u => R u *ᵥ (inertia m r *ᵥ angularVelocityBody (R u) (R' u)))
      (∑ a, (R t *ᵥ r a) ⨯₃ F a) t :=
  IsRigidMotion.hasDerivAt_angularMomentum h hpt hF

example (h : IsRigidMotion c c' R R')
    (hpt : ∑ a, m a • r a = 0 ∨ ∀ s, c' s = 0) {F : ι → Fin 3 → ℝ} {t : ℝ}
    (hF : ∀ a, HasDerivAt (fun u => m a • (c' u + R' u *ᵥ r a)) (F a) t) :
    HasDerivAt (fun u => inertia m r *ᵥ angularVelocityBody (R u) (R' u))
      ((inertia m r *ᵥ angularVelocityBody (R t) (R' t)) ⨯₃ angularVelocityBody (R t) (R' t) +
        (R t)ᵀ *ᵥ ∑ a, (R t *ᵥ r a) ⨯₃ F a) t :=
  IsRigidMotion.hasDerivAt_bodyAngularMomentum h hpt hF

example (h : IsRigidMotion c c' R R') {s : ℝ}
    (hpt : ∑ a, m a • r a = 0 ∨ c' s = 0) :
    ∑ a, m a * ((c' s + R' s *ᵥ r a) ⬝ᵥ (c' s + R' s *ᵥ r a)) =
      (∑ a, m a) * (c' s ⬝ᵥ c' s) +
        angularVelocityBody (R s) (R' s) ⬝ᵥ
          (inertia m r *ᵥ angularVelocityBody (R s) (R' s)) :=
  IsRigidMotion.sum_mul_velocity_sq h hpt

end Dynamics

section Reconstruction

variable (Ω : C(ℝ, Fin 3 → ℝ)) (R₀ : Matrix (Fin 3) (Fin 3) ℝ)

example (u v w : Fin 3 → ℝ) :
    (u ⨯₃ w) ⬝ᵥ v + u ⬝ᵥ (v ⨯₃ w) = 0 :=
  cross_dotProduct_add u v w

example (u₀ u₁ u₂ w : Fin 3 → ℝ) :
    (u₀ ⨯₃ w) ⬝ᵥ (u₁ ⨯₃ u₂) + u₀ ⬝ᵥ ((u₁ ⨯₃ w) ⨯₃ u₂ + u₁ ⨯₃ (u₂ ⨯₃ w)) = 0 :=
  triple_cross_eq_zero u₀ u₁ u₂ w

example (M : Matrix (Fin 3) (Fin 3) ℝ) :
    M.det = (M 0) ⬝ᵥ ((M 1) ⨯₃ (M 2)) :=
  det_eq_dotProduct_cross M

example (R : Matrix (Fin 3) (Fin 3) ℝ) (w : Fin 3 → ℝ) (a b : Fin 3) :
    (R * hat w) a b = ((R a) ⨯₃ w) b :=
  mul_hat_apply R w a b

example :
    crossRight =
      (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := Fin 3 → ℝ)
      (F' := Fin 3 → ℝ)).toLinearMap ∘ₗ (crossProduct (R := ℝ)).flip := rfl

example (w u : Fin 3 → ℝ) :
    crossRight w u = u ⨯₃ w :=
  crossRight_apply w u

example (Ω : C(ℝ, Fin 3 → ℝ)) (t : ℝ) :
    rowCoefficient Ω t = crossRight (Ω t) := rfl

example (Ω : C(ℝ, Fin 3 → ℝ)) (t : ℝ) (u : Fin 3 → ℝ) :
    rowCoefficient Ω t u = u ⨯₃ Ω t :=
  rowCoefficient_apply Ω t u

example (Ω : C(ℝ, Fin 3 → ℝ)) (R₀ : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) :
    rotation Ω R₀ t =
      Matrix.of fun a => propagator (rowCoefficient Ω) t 0 (R₀ a) := rfl

example :
    rotation Ω R₀ 0 = R₀ :=
  rotation_zero Ω R₀

example (a : Fin 3) (t : ℝ) :
    HasDerivAt (fun s => rotation Ω R₀ s a) ((rotation Ω R₀ t a) ⨯₃ Ω t) t :=
  hasDerivAt_rotation_row Ω R₀ a t

example (t : ℝ) (a b : Fin 3) :
    HasDerivAt (fun s => rotation Ω R₀ s a b) ((rotation Ω R₀ t * hat (Ω t)) a b) t :=
  hasDerivAt_rotation Ω R₀ t a b

example (a b : Fin 3) (t : ℝ) :
    (rotation Ω R₀ t a) ⬝ᵥ (rotation Ω R₀ t b) = (R₀ a) ⬝ᵥ (R₀ b) :=
  rotation_dotProduct Ω R₀ a b t

example (h₀ : R₀ * R₀ᵀ = 1) (t : ℝ) :
    rotation Ω R₀ t * (rotation Ω R₀ t)ᵀ = 1 :=
  rotation_mul_transpose Ω R₀ h₀ t

example (h₀ : R₀ᵀ * R₀ = 1) (t : ℝ) :
    (rotation Ω R₀ t)ᵀ * rotation Ω R₀ t = 1 :=
  rotation_transpose_mul Ω R₀ h₀ t

example (t : ℝ) :
    (rotation Ω R₀ t).det = R₀.det :=
  det_rotation Ω R₀ t

example (h₀ : R₀ᵀ * R₀ = 1) (hdet : R₀.det = 1) :
    IsRigidMotion (fun _ => 0) (fun _ => 0) (rotation Ω R₀)
      (fun t => rotation Ω R₀ t * hat (Ω t)) :=
  isRigidMotion_rotation Ω R₀ h₀ hdet

example (h₀ : R₀ᵀ * R₀ = 1) (t : ℝ) :
    angularVelocityBody (rotation Ω R₀ t) (rotation Ω R₀ t * hat (Ω t)) = Ω t :=
  angularVelocityBody_rotation Ω R₀ h₀ t

example {R : ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hR : ∀ t a b, HasDerivAt (fun s => R s a b) ((R t * hat (Ω t)) a b) t) (t : ℝ) :
    R t = rotation Ω (R 0) t :=
  eq_rotation_of_hasDerivAt Ω hR t

example (hΩ : ContDiff ℝ ∞ Ω) (R₀ : Matrix (Fin 3) (Fin 3) ℝ) (a b : Fin 3) :
    ContDiff ℝ ∞ fun t => rotation Ω R₀ t a b :=
  contDiff_rotation hΩ R₀ a b

example {L : ℝ → Fin 3 → ℝ} {L' : Fin 3 → ℝ} {t : ℝ}
    (hL : HasDerivAt L L' t) :
    HasDerivAt (fun s => rotation Ω R₀ s *ᵥ L s) (rotation Ω R₀ t *ᵥ (L' - L t ⨯₃ Ω t)) t :=
  hasDerivAt_rotation_mulVec hL

example {L : ℝ → Fin 3 → ℝ} (hL : ∀ t, HasDerivAt L (L t ⨯₃ Ω t) t)
    (t : ℝ) :
    rotation Ω R₀ t *ᵥ L t = R₀ *ᵥ L 0 :=
  rotation_mulVec_eq hL t

end Reconstruction

section Variation

variable {R : ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℝ}

example {A B : ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    {A' B' : Matrix (Fin 3) (Fin 3) ℝ} {t : ℝ}
    (hA : ∀ a b, HasDerivAt (fun s => A s a b) (A' a b) t)
    (hB : ∀ a b, HasDerivAt (fun s => B s a b) (B' a b) t) (a b : Fin 3) :
    HasDerivAt (fun s => ((A s)ᵀ * B s) a b) ((A'ᵀ * B t + (A t)ᵀ * B') a b) t :=
  hasDerivAt_transpose_mul hA hB a b

example (A B : Matrix (Fin 3) (Fin 3) ℝ) :
    vee (A + B) = vee A + vee B :=
  vee_add A B

example {A B : ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    {A' B' : Matrix (Fin 3) (Fin 3) ℝ} {t : ℝ}
    (hA : ∀ a b, HasDerivAt (fun s => A s a b) (A' a b) t)
    (hB : ∀ a b, HasDerivAt (fun s => B s a b) (B' a b) t) :
    HasDerivAt (fun s => angularVelocityBody (A s) (B s))
      (vee (A'ᵀ * B t + (A t)ᵀ * B')) t :=
  hasDerivAt_angularVelocityBody hA hB

example {R : Matrix (Fin 3) (Fin 3) ℝ} (horth : Rᵀ * R = 1)
    (w η : Fin 3 → ℝ) :
    vee ((R * hat η)ᵀ * (R * hat w)) = vee ((R * hat w)ᵀ * (R * hat η)) + w ⨯₃ η :=
  vee_transpose_mul_hat horth w η

example (R : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) :
    curveDeriv R t =
      Matrix.of fun a b => deriv (fun s => R s a b) t := rfl

example (R : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) :
    curveVelocity R t =
      angularVelocityBody (R t) (curveDeriv R t) := rfl

example {c c' : ℝ → Fin 3 → ℝ}
    {R R' : ℝ → Matrix (Fin 3) (Fin 3) ℝ} (h : IsRigidMotion c c' R R') (t : ℝ) :
    curveVelocity R t = angularVelocityBody (R t) (R' t) :=
  IsRigidMotion.curveVelocity_eq h t

example {R : ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℝ} (h : IsRotationFamily R) (a b : Fin 3) :
    ContDiff ℝ ∞ fun p => R p a b :=
  h.contDiff a b

example {R : ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℝ} (h : IsRotationFamily R) (p : ℝ × ℝ) :
    (R p)ᵀ * R p = 1 :=
  h.orthogonal p

example (R : ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℝ) (p : ℝ × ℝ) :
    familyVariation R p =
      angularVelocityBody (R p) (curveDeriv (fun e => R (e, p.2)) p.1) := rfl

example (R : ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℝ) (v p : ℝ × ℝ) :
    familyDeriv R v p =
      Matrix.of fun a b => fderiv ℝ (fun q => R q a b) p v := rfl

example (h : IsRotationFamily R) (a b : Fin 3) (p : ℝ × ℝ) :
    DifferentiableAt ℝ (fun q => R q a b) p :=
  IsRotationFamily.differentiableAt h a b p

example (h : IsRotationFamily R) (v : ℝ × ℝ) (a b : Fin 3) :
    ContDiff ℝ ∞ fun p => familyDeriv R v p a b :=
  IsRotationFamily.contDiff_familyDeriv h v a b

example (h : IsRotationFamily R) (p : ℝ × ℝ) :
    curveDeriv (fun s => R (p.1, s)) p.2 = familyDeriv R (0, 1) p :=
  IsRotationFamily.curveDeriv_time h p

example (h : IsRotationFamily R) (p : ℝ × ℝ) :
    curveDeriv (fun e => R (e, p.2)) p.1 = familyDeriv R (1, 0) p :=
  IsRotationFamily.curveDeriv_parameter h p

example (h : IsRotationFamily R) (ε t : ℝ) (a b : Fin 3) :
    HasDerivAt (fun s => R (ε, s) a b) (familyDeriv R (0, 1) (ε, t) a b) t :=
  IsRotationFamily.hasDerivAt_time h ε t a b

example (h : IsRotationFamily R) (ε t : ℝ) (a b : Fin 3) :
    HasDerivAt (fun e => R (e, t) a b) (familyDeriv R (1, 0) (ε, t) a b) ε :=
  IsRotationFamily.hasDerivAt_parameter h ε t a b

example (R : ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℝ) (p : ℝ × ℝ) :
    IsRotationFamily.mixedDeriv R p =
      Matrix.of fun a b => fderiv ℝ (fderiv ℝ fun q => R q a b) p (1, 0) (0, 1) := rfl

example (h : IsRotationFamily R) (ε t : ℝ) (a b : Fin 3) :
    HasDerivAt (fun e => familyDeriv R (0, 1) (e, t) a b)
      (IsRotationFamily.mixedDeriv R (ε, t) a b) ε :=
  IsRotationFamily.hasDerivAt_familyDeriv_time_parameter h ε t a b

example (h : IsRotationFamily R) (ε t : ℝ) (a b : Fin 3) :
    HasDerivAt (fun s => familyDeriv R (1, 0) (ε, s) a b)
      (IsRotationFamily.mixedDeriv R (ε, t) a b) t :=
  IsRotationFamily.hasDerivAt_familyDeriv_parameter_time h ε t a b

example (h : IsRotationFamily R) (p : ℝ × ℝ) :
    familyDeriv R (0, 1) p = R p * hat (curveVelocity (fun s => R (p.1, s)) p.2) :=
  IsRotationFamily.familyDeriv_time h p

example (h : IsRotationFamily R) (p : ℝ × ℝ) :
    familyDeriv R (1, 0) p = R p * hat (familyVariation R p) :=
  IsRotationFamily.familyDeriv_parameter h p

example (h : IsRotationFamily R) (ε t : ℝ) :
    HasDerivAt (fun s => familyVariation R (ε, s))
      (vee ((familyDeriv R (0, 1) (ε, t))ᵀ * familyDeriv R (1, 0) (ε, t) +
        (R (ε, t))ᵀ * IsRotationFamily.mixedDeriv R (ε, t))) t :=
  IsRotationFamily.hasDerivAt_familyVariation h ε t

example (h : IsRotationFamily R) (ε t : ℝ) :
    HasDerivAt (fun e => curveVelocity (fun s => R (e, s)) t)
      (deriv (fun s => familyVariation R (ε, s)) t +
        curveVelocity (fun s => R (ε, s)) t ⨯₃ familyVariation R (ε, t)) ε :=
  IsRotationFamily.hasDerivAt_curveVelocity_family h ε t

example (h : IsRotationFamily R) (γ : Fin 3 → ℝ) (ε t : ℝ) :
    HasDerivAt (fun e => (R (e, t))ᵀ *ᵥ γ)
      (((R (ε, t))ᵀ *ᵥ γ) ⨯₃ familyVariation R (ε, t)) ε :=
  IsRotationFamily.hasDerivAt_bodyVector_family h γ ε t

end Variation

section RotationAction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {R : ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℝ} {J : Matrix (Fin 3) (Fin 3) ℝ}
  {V : (Fin 3 → ℝ) → ℝ} {R₀ : ℝ → Matrix (Fin 3) (Fin 3) ℝ}

example {x y : E → Fin 3 → ℝ} (hx : ContDiff ℝ ∞ x)
    (hy : ContDiff ℝ ∞ y) :
    ContDiff ℝ ∞ fun p => x p ⬝ᵥ y p :=
  contDiff_dotProduct hx hy

example (J : Matrix (Fin 3) (Fin 3) ℝ) {x : E → Fin 3 → ℝ}
    (hx : ContDiff ℝ ∞ x) :
    ContDiff ℝ ∞ fun p => J *ᵥ x p :=
  contDiff_mulVec J hx

example {A : E → Matrix (Fin 3) (Fin 3) ℝ}
    (hA : ∀ a b, ContDiff ℝ ∞ fun p => A p a b) (γ : Fin 3 → ℝ) :
    ContDiff ℝ ∞ fun p => (A p)ᵀ *ᵥ γ :=
  contDiff_transpose_mulVec hA γ

example {A B : E → Matrix (Fin 3) (Fin 3) ℝ}
    (hA : ∀ a b, ContDiff ℝ ∞ fun p => A p a b) (hB : ∀ a b, ContDiff ℝ ∞ fun p => B p a b) :
    ContDiff ℝ ∞ fun p => angularVelocityBody (A p) (B p) :=
  contDiff_angularVelocityBody hA hB

example {x y : ℝ → Fin 3 → ℝ} (hx : Continuous x) (hy : Continuous y) :
    Continuous fun t => x t ⨯₃ y t :=
  continuous_cross hx hy

example {R : ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hR : ∀ a b, ContDiff ℝ ∞ fun t => R t a b) :
    ContDiff ℝ ∞ (curveVelocity R) :=
  contDiff_curveVelocity hR

example (h : IsRotationFamily R) :
    ContDiff ℝ ∞ fun p : ℝ × ℝ => curveVelocity (fun s => R (p.1, s)) p.2 :=
  IsRotationFamily.contDiff_curveVelocity h

example (h : IsRotationFamily R) :
    ContDiff ℝ ∞ (familyVariation R) :=
  IsRotationFamily.contDiff_familyVariation h

example {p : ℝ × ℝ} (hconst : ∀ e, R (e, p.2) = R p) :
    familyVariation R p = 0 :=
  IsRotationFamily.familyVariation_eq_zero hconst

example (J : Matrix (Fin 3) (Fin 3) ℝ) (V : (Fin 3 → ℝ) → ℝ) (w Γ : Fin 3 → ℝ) :
    bodyLagrangian J V w Γ =
      w ⬝ᵥ (J *ᵥ w) / 2 - V Γ := rfl

example (J : Matrix (Fin 3) (Fin 3) ℝ) (V : (Fin 3 → ℝ) → ℝ) (γ : Fin 3 → ℝ)
    (R : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (t₀ t₁ : ℝ) :
    rotationAction J V γ R t₀ t₁ =
      ∫ t in t₀..t₁, bodyLagrangian J V (curveVelocity R t) ((R t)ᵀ *ᵥ γ) := rfl

example (V : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) :
    bodyGradient V x =
      fun i => fderiv ℝ V x (Pi.single i 1) := rfl

example (V : (Fin 3 → ℝ) → ℝ) (x y : Fin 3 → ℝ) :
    fderiv ℝ V x y = bodyGradient V x ⬝ᵥ y :=
  fderiv_eq_bodyGradient_dotProduct V x y

example (w x : Fin 3 → ℝ) :
    bodyGradient (fun Γ : Fin 3 → ℝ => Γ ⬝ᵥ w) x = w :=
  bodyGradient_dotProduct_const w x

example (J : Matrix (Fin 3) (Fin 3) ℝ) (V : (Fin 3 → ℝ) → ℝ) (γ : Fin 3 → ℝ)
    (R : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) :
    eulerPoissonResidual J V γ R t =
      deriv (fun s => J *ᵥ curveVelocity R s) t - (J *ᵥ curveVelocity R t) ⨯₃ curveVelocity R t -
      ((R t)ᵀ *ᵥ γ) ⨯₃ bodyGradient V ((R t)ᵀ *ᵥ γ) := rfl

example (hJ : Jᵀ = J) (hV : ContDiff ℝ ∞ V)
    {w Γ : ℝ → Fin 3 → ℝ} {w' Γ' : Fin 3 → ℝ} {ε : ℝ}
    (hw : HasDerivAt w w' ε) (hΓ : HasDerivAt Γ Γ' ε) :
    HasDerivAt (fun e => bodyLagrangian J V (w e) (Γ e))
      ((J *ᵥ w ε) ⬝ᵥ w' - bodyGradient V (Γ ε) ⬝ᵥ Γ') ε :=
  hasDerivAt_bodyLagrangian hJ hV hw hΓ

example (a a' η η' w Γ G : Fin 3 → ℝ) :
    a' ⬝ᵥ η + a ⬝ᵥ η' =
      a ⬝ᵥ (η' + w ⨯₃ η) - G ⬝ᵥ (Γ ⨯₃ η) - -((a' - a ⨯₃ w - Γ ⨯₃ G) ⬝ᵥ η) :=
  variation_identity a a' η η' w Γ G

example (J : Matrix (Fin 3) (Fin 3) ℝ) (V : (Fin 3 → ℝ) → ℝ) (γ : Fin 3 → ℝ)
    (R : ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℝ) (p : ℝ × ℝ) :
    familyLagrangian J V γ R p =
      bodyLagrangian J V (curveVelocity (fun s => R (p.1, s)) p.2) ((R p)ᵀ *ᵥ γ) := rfl

example (J : Matrix (Fin 3) (Fin 3) ℝ) (V : (Fin 3 → ℝ) → ℝ) (γ : Fin 3 → ℝ)
    (R : ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℝ) (p : ℝ × ℝ) :
    variationDensity J V γ R p =
      (J *ᵥ curveVelocity (fun s => R (p.1, s)) p.2) ⬝ᵥ
      (deriv (fun s => familyVariation R (p.1, s)) p.2 +
      curveVelocity (fun s => R (p.1, s)) p.2 ⨯₃ familyVariation R p) -
      bodyGradient V ((R p)ᵀ *ᵥ γ) ⬝ᵥ (((R p)ᵀ *ᵥ γ) ⨯₃ familyVariation R p) := rfl

example (J : Matrix (Fin 3) (Fin 3) ℝ) (R : ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℝ) (p : ℝ × ℝ) :
    variationMomentum J R p =
      (J *ᵥ curveVelocity (fun s => R (p.1, s)) p.2) ⬝ᵥ familyVariation R p := rfl

example (h : IsRotationFamily R) (hV : ContDiff ℝ ∞ V)
    (γ : Fin 3 → ℝ) :
    ContDiff ℝ ∞ (familyLagrangian J V γ R) :=
  contDiff_familyLagrangian h hV γ

example (h : IsRotationFamily R) (hJ : Jᵀ = J)
    (hV : ContDiff ℝ ∞ V) (γ : Fin 3 → ℝ) (ε t : ℝ) :
    HasDerivAt (fun e => familyLagrangian J V γ R (e, t)) (variationDensity J V γ R (ε, t)) ε :=
  hasDerivAt_familyLagrangian h hJ hV γ ε t

example (h : IsRotationFamily R) :
    ContDiff ℝ ∞ (variationMomentum J R) :=
  contDiff_variationMomentum h

example (h : IsRotationFamily R) (γ : Fin 3 → ℝ) (ε t : ℝ) :
    HasDerivAt (fun s => variationMomentum J R (ε, s))
      (variationDensity J V γ R (ε, t) -
        -(eulerPoissonResidual J V γ (fun s => R (ε, s)) t ⬝ᵥ familyVariation R (ε, t))) t :=
  hasDerivAt_variationMomentum h γ ε t

example (h : IsRotationFamily R) (hJ : Jᵀ = J)
    (hV : ContDiff ℝ ∞ V) (γ : Fin 3 → ℝ) (t₀ t₁ ε : ℝ) :
    HasDerivAt (fun e => rotationAction J V γ (fun s => R (e, s)) t₀ t₁)
      ((J *ᵥ curveVelocity (fun s => R (ε, s)) t₁) ⬝ᵥ familyVariation R (ε, t₁) -
        (J *ᵥ curveVelocity (fun s => R (ε, s)) t₀) ⬝ᵥ familyVariation R (ε, t₀) -
        ∫ t in t₀..t₁, eulerPoissonResidual J V γ (fun s => R (ε, s)) t ⬝ᵥ
          familyVariation R (ε, t)) ε :=
  hasDerivAt_rotationAction h hJ hV γ t₀ t₁ ε

example (ξ : Fin 3 → ℝ) :
    cayley ξ =
      1 + (1 + ξ ⬝ᵥ ξ / 4)⁻¹ • (hat ξ + (1 / 2 : ℝ) • (hat ξ * hat ξ)) := rfl

example :
    cayley 0 = 1 :=
  cayley_zero

example (ξ : Fin 3 → ℝ) :
    (cayley ξ)ᵀ * cayley ξ = 1 :=
  cayley_transpose_mul ξ

example (x : ℝ) (w : Fin 3 → ℝ) (k b : Fin 3) :
    cayley (x • w) k b = (1 : Matrix (Fin 3) (Fin 3) ℝ) k b +
      (1 + x ^ 2 * (w ⬝ᵥ w) / 4)⁻¹ * (x * hat w k b + x ^ 2 / 2 * (hat w * hat w) k b) :=
  cayley_smul_apply x w k b

example (w : Fin 3 → ℝ) (k b : Fin 3) :
    HasDerivAt (fun x : ℝ => cayley (x • w) k b) (hat w k b) 0 :=
  hasDerivAt_cayley_smul w k b

example (k b : Fin 3) :
    ContDiff ℝ ∞ fun ξ : Fin 3 → ℝ => hat ξ k b :=
  contDiff_hat_apply k b

example (k b : Fin 3) :
    ContDiff ℝ ∞ fun ξ : Fin 3 → ℝ => cayley ξ k b :=
  contDiff_cayley_apply k b

example (M : Matrix (Fin 3) (Fin 3) ℝ) (w : Fin 3 → ℝ) :
    curveDeriv (fun e => M * cayley (e • w)) 0 = M * hat w :=
  curveDeriv_mul_cayley M w

example (hR₀ : ∀ a b, ContDiff ℝ ∞ fun t => R₀ t a b)
    (horth : ∀ t, (R₀ t)ᵀ * R₀ t = 1) {ξ : ℝ × ℝ → Fin 3 → ℝ} (hξ : ContDiff ℝ ∞ ξ) :
    IsRotationFamily fun p => R₀ p.2 * cayley (ξ p) :=
  isRotationFamily_mul_cayley hR₀ horth hξ

example (horth : ∀ t, (R₀ t)ᵀ * R₀ t = 1) (η : ℝ → Fin 3 → ℝ)
    (t : ℝ) :
    familyVariation (fun p : ℝ × ℝ => R₀ p.2 * cayley (p.1 • η p.2)) (0, t) = η t :=
  familyVariation_mul_cayley horth η t

example (hV : ContDiff ℝ ∞ V) (γ : Fin 3 → ℝ)
    {R₀ : ℝ → Matrix (Fin 3) (Fin 3) ℝ} (hR₀ : ∀ a b, ContDiff ℝ ∞ fun t => R₀ t a b) :
    Continuous (eulerPoissonResidual J V γ R₀) :=
  continuous_eulerPoissonResidual hV γ hR₀

example (γ : Fin 3 → ℝ)
    {R₀ : ℝ → Matrix (Fin 3) (Fin 3) ℝ} (hR₀ : ∀ a b, ContDiff ℝ ∞ fun t => R₀ t a b) (t : ℝ) :
    eulerPoissonResidual J V γ R₀ t = 0 ↔
      HasDerivAt (fun s => J *ᵥ curveVelocity R₀ s)
        ((J *ᵥ curveVelocity R₀ t) ⨯₃ curveVelocity R₀ t +
          ((R₀ t)ᵀ *ᵥ γ) ⨯₃ bodyGradient V ((R₀ t)ᵀ *ᵥ γ)) t :=
  eulerPoissonResidual_eq_zero_iff γ hR₀ t

example {t₀ t₁ : ℝ} (hab : t₀ < t₁) (hJ : Jᵀ = J)
    (hV : ContDiff ℝ ∞ V) (γ : Fin 3 → ℝ) {R₀ : ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hR₀ : ∀ a b, ContDiff ℝ ∞ fun t => R₀ t a b) (horth : ∀ t, (R₀ t)ᵀ * R₀ t = 1) :
    (∀ R : ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℝ, IsRotationFamily R → (∀ t, R (0, t) = R₀ t) →
        (∀ e, R (e, t₀) = R₀ t₀) → (∀ e, R (e, t₁) = R₀ t₁) →
        HasDerivAt (fun e => rotationAction J V γ (fun s => R (e, s)) t₀ t₁) 0 0) ↔
      ∀ t ∈ Ioo t₀ t₁, eulerPoissonResidual J V γ R₀ t = 0 :=
  stationary_rotationAction_iff hab hJ hV γ hR₀ horth

end RotationAction

section LiePoisson

variable {ι : Type*} [Fintype ι] {m : ι → ℝ} {r : ι → Fin 3 → ℝ}
  {c c' : ℝ → Fin 3 → ℝ} {R R' : ℝ → Matrix (Fin 3) (Fin 3) ℝ} {I : Fin 3 → ℝ}
  {y : ℝ → Fin 3 → ℝ}

example (I : Fin 3 → ℝ) (k : ℝ) (χ : Fin 3 → ℝ) :
    HeavyTop.field I k χ =
      realField (HeavyTop.poisson.hamiltonian (HeavyTop.hamiltonian I k χ)) := rfl

example (I : Fin 3 → ℝ) (k : ℝ) (χ : Fin 3 → ℝ) :
    ContDiff ℝ ∞ (HeavyTop.field I k χ) :=
  HeavyTop.contDiff_field I k χ

example (I : Fin 3 → ℝ) (k : ℝ) (χ : Fin 3 → ℝ) (z : Fin 3 ⊕ Fin 3 → ℝ)
    (a : Fin 3) :
    HeavyTop.field I k χ z (Sum.inl a) =
      ((fun i => z (Sum.inl i)) ⨯₃ (fun i => (I i)⁻¹ * z (Sum.inl i)) +
        (fun i => z (Sum.inr i)) ⨯₃ (k • χ)) a :=
  HeavyTop.field_inl I k χ z a

example (I : Fin 3 → ℝ) (k : ℝ) (χ : Fin 3 → ℝ) (z : Fin 3 ⊕ Fin 3 → ℝ)
    (a : Fin 3) :
    HeavyTop.field I k χ z (Sum.inr a) =
      ((fun i => z (Sum.inr i)) ⨯₃ (fun i => (I i)⁻¹ * z (Sum.inl i))) a :=
  HeavyTop.field_inr I k χ z a

example {I : Fin 3 → ℝ} (hI : ∀ i, I i ≠ 0) (w : Fin 3 → ℝ) :
    (diagonal I *ᵥ w) ⨯₃ w = eulerField I (diagonal I *ᵥ w) :=
  Rigid.cross_eq_eulerField hI w

example (I : Fin 3 → ℝ) (L : Fin 3 → ℝ) :
    eulerField I L = L ⨯₃ fun i => (I i)⁻¹ * L i :=
  Rigid.eulerField_eq_cross I L

example {I : Fin 3 → ℝ} (hI : ∀ i, I i ≠ 0) {k : ℝ}
    {χ : Fin 3 → ℝ} {L Γ : ℝ → Fin 3 → ℝ} {w : Fin 3 → ℝ} {t : ℝ}
    (hw : L t = diagonal I *ᵥ w)
    (hL : HasDerivAt L (L t ⨯₃ w + Γ t ⨯₃ (k • χ)) t) (hΓ : HasDerivAt Γ (Γ t ⨯₃ w) t) :
    HasDerivAt (fun u => Sum.elim (L u) (Γ u))
      (HeavyTop.field I k χ (Sum.elim (L t) (Γ t))) t :=
  Rigid.hasDerivAt_heavyTopField_of_equations hI hw hL hΓ

example (h : IsRigidMotion c c' R R')
    (hpt : ∑ a, m a • r a = 0 ∨ ∀ s, c' s = 0) (hI : ∀ i, I i ≠ 0)
    (hin : inertia m r = diagonal I) {F : ι → Fin 3 → ℝ} {t : ℝ}
    (hF : ∀ a, HasDerivAt (fun u => m a • (c' u + R' u *ᵥ r a)) (F a) t)
    (hK : ∑ a, (R t *ᵥ r a) ⨯₃ F a = 0) :
    HasDerivAt (fun u => inertia m r *ᵥ angularVelocityBody (R u) (R' u))
      (eulerField I (inertia m r *ᵥ angularVelocityBody (R t) (R' t))) t :=
  Rigid.IsRigidMotion.hasDerivAt_eulerField h hpt hI hin hF hK

example (h : IsRigidMotion c c' R R')
    (hrest : ∀ s, c' s = 0) (hI : ∀ i, I i ≠ 0) (hin : inertia m r = diagonal I)
    {N : ι → Fin 3 → ℝ} {g : ℝ} {e : Fin 3 → ℝ} {t : ℝ}
    (hF : ∀ a, HasDerivAt (fun u => m a • (c' u + R' u *ᵥ r a)) (-(m a * g) • e + N a) t)
    (hN : ∑ a, (R t *ᵥ r a) ⨯₃ N a = 0) :
    HasDerivAt (fun u => Sum.elim (inertia m r *ᵥ angularVelocityBody (R u) (R' u))
        ((R u)ᵀ *ᵥ e))
      (HeavyTop.field I g (∑ a, m a • r a)
        (Sum.elim (inertia m r *ᵥ angularVelocityBody (R t) (R' t)) ((R t)ᵀ *ᵥ e))) t :=
  Rigid.IsRigidMotion.hasDerivAt_heavyTopField h hrest hI hin hF hN

example {I : Fin 3 → ℝ} (hI : ∀ i, I i ≠ 0) {k : ℝ}
    {χ γ : Fin 3 → ℝ} {R₀ : ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hR₀ : ∀ a b, ContDiff ℝ ∞ fun t => R₀ t a b) (horth : ∀ t, (R₀ t)ᵀ * R₀ t = 1) {t : ℝ}
    (hres : eulerPoissonResidual (diagonal I) (fun Γ : Fin 3 → ℝ => Γ ⬝ᵥ (k • χ)) γ R₀ t = 0) :
    HasDerivAt (fun u => Sum.elim (diagonal I *ᵥ curveVelocity R₀ u) ((R₀ u)ᵀ *ᵥ γ))
      (HeavyTop.field I k χ
        (Sum.elim (diagonal I *ᵥ curveVelocity R₀ t) ((R₀ t)ᵀ *ᵥ γ))) t :=
  Rigid.hasDerivAt_heavyTopField_of_residual hI hR₀ horth hres

example {I : Fin 3 → ℝ} (hI : ∀ i, I i ≠ 0) {k : ℝ}
    {χ γ : Fin 3 → ℝ} {R₀ : ℝ → Matrix (Fin 3) (Fin 3) ℝ} {t₀ t₁ : ℝ} (hab : t₀ < t₁)
    (hR₀ : ∀ a b, ContDiff ℝ ∞ fun t => R₀ t a b) (horth : ∀ t, (R₀ t)ᵀ * R₀ t = 1)
    (hs : ∀ R : ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℝ, IsRotationFamily R → (∀ t, R (0, t) = R₀ t) →
      (∀ e, R (e, t₀) = R₀ t₀) → (∀ e, R (e, t₁) = R₀ t₁) →
      HasDerivAt (fun e => rotationAction (diagonal I) (fun Γ : Fin 3 → ℝ => Γ ⬝ᵥ (k • χ)) γ
        (fun s => R (e, s)) t₀ t₁) 0 0) {t : ℝ} (ht : t ∈ Ioo t₀ t₁) :
    HasDerivAt (fun u => Sum.elim (diagonal I *ᵥ curveVelocity R₀ u) ((R₀ u)ᵀ *ᵥ γ))
      (HeavyTop.field I k χ
        (Sum.elim (diagonal I *ᵥ curveVelocity R₀ t) ((R₀ t)ᵀ *ᵥ γ))) t :=
  Rigid.hasDerivAt_heavyTopField_of_stationary hI hab hR₀ horth hs ht

example (hy : ∀ t, HasDerivAt y (eulerField I (y t)) t) (t : ℝ) (i : Fin 3) :
    Rigid.eulerVelocity I y hy t i = (I i)⁻¹ * y t i := rfl

example (hy : ∀ t, HasDerivAt y (eulerField I (y t)) t)
    (R₀ : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) :
    rotation (eulerVelocity I y hy) R₀ t *ᵥ y t = R₀ *ᵥ y 0 :=
  Rigid.rotation_mulVec_eulerSolution hy R₀ t

example (h0 : (I 2)⁻¹ - (I 1)⁻¹ < 0)
    (h1 : 0 < (I 0)⁻¹ - (I 2)⁻¹) (h2 : (I 1)⁻¹ - (I 0)⁻¹ ≤ 0) {A C : ℝ} (hC : C ≠ 0)
    (hk : topModulus I A C ^ 2 < 1) (R₀ : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) :
    rotation (eulerVelocity I (ellipticMotion I A C)
        (hasDerivAt_ellipticMotion h0 h1 h2 hC hk)) R₀ t *ᵥ ellipticMotion I A C t =
      R₀ *ᵥ ![A, 0, C] :=
  Rigid.rotation_mulVec_ellipticMotion h0 h1 h2 hC hk R₀ t

example {Ω : C(ℝ, Fin 3 → ℝ)} {R₀ : Matrix (Fin 3) (Fin 3) ℝ}
    (h₀ : R₀ᵀ * R₀ = 1) (t : ℝ) :
    curveVelocity (rotation Ω R₀) t = Ω t :=
  Rigid.curveVelocity_rotation h₀ t

example {J : Matrix (Fin 3) (Fin 3) ℝ} {Ω : C(ℝ, Fin 3 → ℝ)}
    {R₀ : Matrix (Fin 3) (Fin 3) ℝ} (h₀ : R₀ᵀ * R₀ = 1) (γ : Fin 3 → ℝ) {t : ℝ}
    (hL : HasDerivAt (fun s => J *ᵥ Ω s) ((J *ᵥ Ω t) ⨯₃ Ω t) t) :
    eulerPoissonResidual J (fun _ => 0) γ (rotation Ω R₀) t = 0 :=
  Rigid.eulerPoissonResidual_rotation h₀ γ hL

example {J : Matrix (Fin 3) (Fin 3) ℝ} (hJ : Jᵀ = J)
    {Ω : C(ℝ, Fin 3 → ℝ)} (hΩ : ContDiff ℝ ∞ Ω)
    (hL : ∀ t, HasDerivAt (fun s => J *ᵥ Ω s) ((J *ᵥ Ω t) ⨯₃ Ω t) t)
    {R₀ : Matrix (Fin 3) (Fin 3) ℝ} (h₀ : R₀ᵀ * R₀ = 1) (γ : Fin 3 → ℝ) {t₀ t₁ : ℝ}
    (hab : t₀ < t₁) {R : ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℝ} (hR : IsRotationFamily R)
    (h0 : ∀ t, R (0, t) = rotation Ω R₀ t) (hend₀ : ∀ e, R (e, t₀) = rotation Ω R₀ t₀)
    (hend₁ : ∀ e, R (e, t₁) = rotation Ω R₀ t₁) :
    HasDerivAt (fun e => rotationAction J (fun _ => 0) γ (fun s => R (e, s)) t₀ t₁) 0 0 :=
  Rigid.stationary_rotationAction_rotation hJ hΩ hL h₀ γ hab hR h0 hend₀ hend₁

end LiePoisson
