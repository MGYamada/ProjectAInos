/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Rigid.AngularVelocity
public import ProjectAInos.Mechanics.Rigid.InertiaTensor
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# The equations of motion of a rigid body

Point masses `mₐ` at the body positions `rₐ` move rigidly:
`qₐ(t) = c(t) + R(t) rₐ` with `R(t)` a rotation (`IsRigidMotion`). The
velocities are `vₐ = ċ + Ṙ rₐ = ċ + R (Ω × rₐ)`, where `Ω` is the angular
velocity in the body frame, the vector of the skew-symmetric matrix `Rᵀ Ṙ`
(`angularVelocityBody`). Newton's equations `d(mₐ vₐ)/dt = Fₐ` are assumed for
each particle, with `Fₐ` the total force on it (Landau–Lifshitz §34).

* `IsRigidMotion.hasDerivAt_momentum`: `Ṗ = F` with `P = μ ċ`, when the origin
  of the body is its centre of mass.
* `IsRigidMotion.sum_smul_cross_velocity`: the angular momentum about the
  origin of the body is `R (I Ω)`.
* `IsRigidMotion.hasDerivAt_angularMomentum`: `Ṁ = K`, the moment of the
  forces about the origin of the body, when this origin is the centre of mass
  or is at rest.
* `IsRigidMotion.hasDerivAt_bodyAngularMomentum`: in the body frame,
  `d(I Ω)/dt = (I Ω) × Ω + Rᵀ K`. `IsRigidMotion.hasDerivAt_bodyVector`: a
  vector fixed in space satisfies `Γ̇ = Γ × Ω` in the body frame.
* `sum_internal_force`, `sum_cross_internal_force`: forces between the
  particles that are opposite and directed along the line joining them cancel
  in the total force and in the total moment.
* `transpose_mulVec_sum_cross_weight`: the moment of a uniform field about a
  fixed point is `Γ × (g Σ mₐ rₐ)` in the body frame.
* `IsRigidMotion.sum_mul_velocity_sq`: the kinetic energy is
  `μ |ċ|²/2 + Ω · I Ω/2`.
-/

@[expose] public section

namespace ProjectAInos.Mechanics.Rigid

open Matrix

/-! ### Rotations and the cross product -/

/-- `(A x) × (A y) = (adj A)ᵀ (x × y)` for every `3 × 3` matrix. -/
theorem mulVec_cross_mulVec (A : Matrix (Fin 3) (Fin 3) ℝ) (x y : Fin 3 → ℝ) :
    (A *ᵥ x) ⨯₃ (A *ᵥ y) = (adjugate A)ᵀ *ᵥ (x ⨯₃ y) := by
  rw [adjugate_fin_three]
  ext i
  fin_cases i <;>
    simp [cross_apply, mulVec, dotProduct, Fin.sum_univ_three] <;> ring

/-- The adjugate of a rotation is its transpose. -/
theorem adjugate_eq_transpose {R : Matrix (Fin 3) (Fin 3) ℝ} (horth : Rᵀ * R = 1)
    (hdet : R.det = 1) : adjugate R = Rᵀ := by
  have h : R * adjugate R = 1 := by rw [mul_adjugate, hdet, one_smul]
  calc adjugate R = Rᵀ * R * adjugate R := by rw [horth, Matrix.one_mul]
    _ = Rᵀ := by rw [Matrix.mul_assoc, h, Matrix.mul_one]

/-- A rotation maps the cross product to the cross product. -/
theorem mulVec_cross {R : Matrix (Fin 3) (Fin 3) ℝ} (horth : Rᵀ * R = 1) (hdet : R.det = 1)
    (x y : Fin 3 → ℝ) : (R *ᵥ x) ⨯₃ (R *ᵥ y) = R *ᵥ (x ⨯₃ y) := by
  rw [mulVec_cross_mulVec, adjugate_eq_transpose horth hdet, transpose_transpose]

theorem transpose_mulVec_mulVec {R : Matrix (Fin 3) (Fin 3) ℝ} (horth : Rᵀ * R = 1)
    (x : Fin 3 → ℝ) : Rᵀ *ᵥ (R *ᵥ x) = x := by
  rw [mulVec_mulVec, horth, one_mulVec]

theorem mulVec_transpose_mulVec {R : Matrix (Fin 3) (Fin 3) ℝ} (horth : Rᵀ * R = 1)
    (x : Fin 3 → ℝ) : R *ᵥ (Rᵀ *ᵥ x) = x := by
  rw [mulVec_mulVec, mul_eq_one_comm.mp horth, one_mulVec]

/-- An orthogonal matrix preserves the scalar product. -/
theorem mulVec_dotProduct_mulVec {R : Matrix (Fin 3) (Fin 3) ℝ} (horth : Rᵀ * R = 1)
    (x y : Fin 3 → ℝ) : (R *ᵥ x) ⬝ᵥ (R *ᵥ y) = x ⬝ᵥ y := by
  rw [dotProduct_mulVec, ← mulVec_transpose, transpose_mulVec_mulVec horth]

/-- The moment of a force in the body frame: `Rᵀ ((R x) × y) = x × (Rᵀ y)`. -/
theorem transpose_mulVec_cross {R : Matrix (Fin 3) (Fin 3) ℝ} (horth : Rᵀ * R = 1)
    (hdet : R.det = 1) (x y : Fin 3 → ℝ) : Rᵀ *ᵥ ((R *ᵥ x) ⨯₃ y) = x ⨯₃ (Rᵀ *ᵥ y) := by
  have h := mulVec_cross horth hdet x (Rᵀ *ᵥ y)
  rw [mulVec_transpose_mulVec horth] at h
  rw [h, transpose_mulVec_mulVec horth]

/-! ### Derivatives of curves of vectors and matrices -/

theorem hasDerivAt_dotProduct {x y : ℝ → Fin 3 → ℝ} {x' y' : Fin 3 → ℝ} {t : ℝ}
    (hx : HasDerivAt x x' t) (hy : HasDerivAt y y' t) :
    HasDerivAt (fun s => x s ⬝ᵥ y s) (x' ⬝ᵥ y t + x t ⬝ᵥ y') t := by
  have h : HasDerivAt (fun s => ∑ i, x s i * y s i) (∑ i, (x' i * y t i + x t i * y' i)) t :=
    HasDerivAt.fun_sum fun i _ => (hasDerivAt_pi.mp hx i).mul (hasDerivAt_pi.mp hy i)
  refine h.congr_deriv ?_
  rw [Finset.sum_add_distrib]
  rfl

theorem hasDerivAt_cross {x y : ℝ → Fin 3 → ℝ} {x' y' : Fin 3 → ℝ} {t : ℝ}
    (hx : HasDerivAt x x' t) (hy : HasDerivAt y y' t) :
    HasDerivAt (fun s => x s ⨯₃ y s) (x' ⨯₃ y t + x t ⨯₃ y') t := by
  have hx' := hasDerivAt_pi.mp hx
  have hy' := hasDerivAt_pi.mp hy
  refine hasDerivAt_pi.mpr fun i => ?_
  fin_cases i
  · refine (((hx' 1).mul (hy' 2)).sub ((hx' 2).mul (hy' 1))).congr_deriv ?_
    simp [cross_apply]
    ring
  · refine (((hx' 2).mul (hy' 0)).sub ((hx' 0).mul (hy' 2))).congr_deriv ?_
    simp [cross_apply]
    ring
  · refine (((hx' 0).mul (hy' 1)).sub ((hx' 1).mul (hy' 0))).congr_deriv ?_
    simp [cross_apply]
    ring

/-- The derivative of a curve of matrices applied to a curve of vectors. The
derivative of the matrix is taken entry by entry. -/
theorem hasDerivAt_mulVec {R : ℝ → Matrix (Fin 3) (Fin 3) ℝ} {R' : Matrix (Fin 3) (Fin 3) ℝ}
    {x : ℝ → Fin 3 → ℝ} {x' : Fin 3 → ℝ} {t : ℝ}
    (hR : ∀ a b, HasDerivAt (fun s => R s a b) (R' a b) t) (hx : HasDerivAt x x' t) :
    HasDerivAt (fun s => R s *ᵥ x s) (R' *ᵥ x t + R t *ᵥ x') t := by
  refine hasDerivAt_pi.mpr fun a => ?_
  have h : HasDerivAt (fun s => ∑ b, R s a b * x s b)
      (∑ b, (R' a b * x t b + R t a b * x' b)) t :=
    HasDerivAt.fun_sum fun b _ => (hR a b).mul (hasDerivAt_pi.mp hx b)
  refine h.congr_deriv ?_
  rw [Finset.sum_add_distrib]
  rfl

/-- For a differentiable family of orthogonal matrices, `Rᵀ Ṙ` is
skew-symmetric. -/
theorem transpose_mul_deriv_transpose {R : ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    {R' : Matrix (Fin 3) (Fin 3) ℝ} {t : ℝ}
    (hR : ∀ a b, HasDerivAt (fun s => R s a b) (R' a b) t)
    (horth : ∀ s, (R s)ᵀ * R s = 1) : ((R t)ᵀ * R')ᵀ = -((R t)ᵀ * R') := by
  have h := transpose_deriv_mul_transpose (R := fun s => (R s)ᵀ) (R' := R'ᵀ) (t := t)
    (fun a b => hR b a) (fun s => by rw [transpose_transpose]; exact horth s)
  simp only [transpose_mul, transpose_transpose] at h ⊢
  rw [h, neg_neg]

/-- The angular velocity in the body frame: the vector of the skew-symmetric
matrix `Rᵀ Ṙ`. -/
def angularVelocityBody (R R' : Matrix (Fin 3) (Fin 3) ℝ) : Fin 3 → ℝ := vee (Rᵀ * R')

/-- `Ṙ = R Ω̂` with `Ω` the angular velocity in the body frame. -/
theorem deriv_eq_mul_hat {R : ℝ → Matrix (Fin 3) (Fin 3) ℝ} {R' : Matrix (Fin 3) (Fin 3) ℝ}
    {t : ℝ} (hR : ∀ a b, HasDerivAt (fun s => R s a b) (R' a b) t)
    (horth : ∀ s, (R s)ᵀ * R s = 1) : R' = R t * hat (angularVelocityBody (R t) R') := by
  rw [angularVelocityBody, hat_vee (transpose_mul_deriv_transpose hR horth), ← Matrix.mul_assoc,
    mul_eq_one_comm.mp (horth t), Matrix.one_mul]

/-- A vector fixed in space, seen from a rotating frame: `Γ̇ = Γ × Ω` for
`Γ = Rᵀ e`. -/
theorem hasDerivAt_transpose_mulVec {R : ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    {R' : Matrix (Fin 3) (Fin 3) ℝ} {t : ℝ}
    (hR : ∀ a b, HasDerivAt (fun s => R s a b) (R' a b) t)
    (horth : ∀ s, (R s)ᵀ * R s = 1) (e : Fin 3 → ℝ) :
    HasDerivAt (fun u => (R u)ᵀ *ᵥ e) (((R t)ᵀ *ᵥ e) ⨯₃ angularVelocityBody (R t) R') t := by
  have h1 := hasDerivAt_mulVec (R := fun u => (R u)ᵀ) (R' := R'ᵀ)
    (fun a b => hR b a) (hasDerivAt_const t e)
  rw [mulVec_zero, add_zero] at h1
  refine h1.congr_deriv ?_
  conv_lhs => rw [deriv_eq_mul_hat hR horth]
  rw [transpose_mul, transpose_hat, ← mulVec_mulVec, neg_mulVec, hat_mulVec, cross_anticomm]

/-! ### Sums over the particles -/

section Sums

variable {ι : Type*} [Fintype ι]

theorem mulVec_sum (A : Matrix (Fin 3) (Fin 3) ℝ) (x : ι → Fin 3 → ℝ) :
    A *ᵥ ∑ a, x a = ∑ a, A *ᵥ x a :=
  map_sum A.mulVecLin x Finset.univ

theorem sum_cross (x : ι → Fin 3 → ℝ) (y : Fin 3 → ℝ) : (∑ a, x a) ⨯₃ y = ∑ a, x a ⨯₃ y := by
  rw [map_sum, LinearMap.sum_apply]

theorem cross_sum (x : Fin 3 → ℝ) (y : ι → Fin 3 → ℝ) : x ⨯₃ ∑ a, y a = ∑ a, x ⨯₃ y a :=
  map_sum (crossProduct x) y Finset.univ

/-- Opposite forces between the particles cancel in the total force. -/
theorem sum_internal_force {f : ι → ι → Fin 3 → ℝ} (hf : ∀ a b, f a b = -f b a) :
    ∑ a, ∑ b, f a b = 0 := by
  have h : ∑ a, ∑ b, f a b = -∑ a, ∑ b, f a b := by
    rw [← Finset.sum_neg_distrib]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun b _ => hf b a
  exact self_eq_neg.mp h

/-- Opposite forces along the lines joining the particles cancel in the total
moment, about every point `c`. -/
theorem sum_cross_internal_force {f : ι → ι → Fin 3 → ℝ} (hf : ∀ a b, f a b = -f b a)
    {q : ι → Fin 3 → ℝ} (hq : ∀ a b, (q a - q b) ⨯₃ f a b = 0) (c : Fin 3 → ℝ) :
    ∑ a, (q a - c) ⨯₃ ∑ b, f a b = 0 := by
  have hsum : ∑ a, ∑ b, q a ⨯₃ f a b = 0 := by
    have h : ∑ a, ∑ b, q a ⨯₃ f a b = -∑ a, ∑ b, q a ⨯₃ f a b := by
      rw [← Finset.sum_neg_distrib]
      conv_lhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      have h1 := hq a b
      rw [LinearMap.map_sub₂, sub_eq_zero] at h1
      rw [hf b a, map_neg, h1]
    exact self_eq_neg.mp h
  have hc : ∑ a, c ⨯₃ ∑ b, f a b = 0 := by
    rw [← cross_sum, sum_internal_force hf, map_zero]
  calc ∑ a, (q a - c) ⨯₃ ∑ b, f a b
      = ∑ a, ∑ b, q a ⨯₃ f a b - ∑ a, c ⨯₃ ∑ b, f a b := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [LinearMap.map_sub₂, cross_sum]
    _ = 0 := by rw [hsum, hc, sub_zero]

/-- The moment of a uniform field `−g e` about the origin of the body, in the
body frame: `Γ × (g Σ mₐ rₐ)` with `Γ = Rᵀ e`. -/
theorem transpose_mulVec_sum_cross_weight {R : Matrix (Fin 3) (Fin 3) ℝ} (horth : Rᵀ * R = 1)
    (hdet : R.det = 1) (m : ι → ℝ) (r : ι → Fin 3 → ℝ) (g : ℝ) (e : Fin 3 → ℝ) :
    Rᵀ *ᵥ ∑ a, (R *ᵥ r a) ⨯₃ (-(m a * g) • e) = (Rᵀ *ᵥ e) ⨯₃ (g • ∑ a, m a • r a) := by
  rw [mulVec_sum, Finset.smul_sum, cross_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h1 : (Rᵀ *ᵥ e) ⨯₃ (g • m a • r a) = -(g • m a • (r a ⨯₃ (Rᵀ *ᵥ e))) := by
    rw [map_smul, map_smul, ← cross_anticomm, smul_neg, smul_neg]
  rw [transpose_mulVec_cross horth hdet, mulVec_smul, map_smul, h1]
  module

end Sums

/-! ### Rigid motions -/

/-- A rigid motion: the origin of the body `c` with its velocity `c'`, and the
rotation `R` with its derivative `R'`, taken entry by entry. -/
structure IsRigidMotion (c c' : ℝ → Fin 3 → ℝ) (R R' : ℝ → Matrix (Fin 3) (Fin 3) ℝ) :
    Prop where
  hasDerivAt_origin : ∀ s, HasDerivAt c (c' s) s
  hasDerivAt_rotation : ∀ s a b, HasDerivAt (fun u => R u a b) (R' s a b) s
  orthogonal : ∀ s, (R s)ᵀ * R s = 1
  det_eq_one : ∀ s, (R s).det = 1

namespace IsRigidMotion

variable {c c' : ℝ → Fin 3 → ℝ} {R R' : ℝ → Matrix (Fin 3) (Fin 3) ℝ}

/-- `Ṙ = R Ω̂`. -/
theorem rotation_deriv (h : IsRigidMotion c c' R R') (s : ℝ) :
    R' s = R s * hat (angularVelocityBody (R s) (R' s)) :=
  deriv_eq_mul_hat (h.hasDerivAt_rotation s) h.orthogonal

/-- The velocity of the point of the body at `r₀`. -/
theorem hasDerivAt_position (h : IsRigidMotion c c' R R') (r₀ : Fin 3 → ℝ) (s : ℝ) :
    HasDerivAt (fun u => c u + R u *ᵥ r₀) (c' s + R' s *ᵥ r₀) s := by
  have h1 := hasDerivAt_mulVec (h.hasDerivAt_rotation s) (hasDerivAt_const s r₀)
  rw [mulVec_zero, add_zero] at h1
  exact (h.hasDerivAt_origin s).add h1

/-- `Ṙ r₀ = R (Ω × r₀)`. -/
theorem deriv_mulVec (h : IsRigidMotion c c' R R') (r₀ : Fin 3 → ℝ) (s : ℝ) :
    R' s *ᵥ r₀ = R s *ᵥ (angularVelocityBody (R s) (R' s) ⨯₃ r₀) := by
  conv_lhs => rw [h.rotation_deriv s]
  rw [← mulVec_mulVec, hat_mulVec]

/-- A vector fixed in space satisfies `Γ̇ = Γ × Ω` in the body frame. -/
theorem hasDerivAt_bodyVector (h : IsRigidMotion c c' R R') (e : Fin 3 → ℝ) (t : ℝ) :
    HasDerivAt (fun u => (R u)ᵀ *ᵥ e)
      (((R t)ᵀ *ᵥ e) ⨯₃ angularVelocityBody (R t) (R' t)) t :=
  hasDerivAt_transpose_mulVec (h.hasDerivAt_rotation t) h.orthogonal e

section Particles

variable {ι : Type*} [Fintype ι] {m : ι → ℝ} {r : ι → Fin 3 → ℝ}

/-- The momentum of a body whose origin is its centre of mass is `μ ċ`. -/
theorem sum_smul_velocity (hcm : ∑ a, m a • r a = 0) (v : Fin 3 → ℝ)
    (A : Matrix (Fin 3) (Fin 3) ℝ) : ∑ a, m a • (v + A *ᵥ r a) = (∑ a, m a) • v := by
  have h : ∑ a, m a • (A *ᵥ r a) = 0 := by
    simp_rw [← mulVec_smul]
    rw [← mulVec_sum, hcm, mulVec_zero]
  simp_rw [smul_add]
  rw [Finset.sum_add_distrib, h, add_zero, Finset.sum_smul]

/-- `Ṗ = F`: the centre of mass moves as a particle of the total mass under
the sum of the forces. -/
theorem hasDerivAt_momentum (hcm : ∑ a, m a • r a = 0) {F : ι → Fin 3 → ℝ} {t : ℝ}
    (hF : ∀ a, HasDerivAt (fun u => m a • (c' u + R' u *ᵥ r a)) (F a) t) :
    HasDerivAt (fun u => (∑ a, m a) • c' u) (∑ a, F a) t := by
  have h : HasDerivAt (fun u => ∑ a, m a • (c' u + R' u *ᵥ r a)) (∑ a, F a) t :=
    HasDerivAt.fun_sum fun a _ => hF a
  have heq : (fun u => ∑ a, m a • (c' u + R' u *ᵥ r a)) = fun u => (∑ a, m a) • c' u :=
    funext fun u => sum_smul_velocity hcm (c' u) (R' u)
  rwa [heq] at h

/-- The angular momentum about the origin of the body is `R (I Ω)`. -/
theorem sum_smul_cross_velocity (h : IsRigidMotion c c' R R') (m : ι → ℝ)
    (r : ι → Fin 3 → ℝ) (s : ℝ) :
    ∑ a, m a • ((R s *ᵥ r a) ⨯₃ (R' s *ᵥ r a)) =
      R s *ᵥ (inertia m r *ᵥ angularVelocityBody (R s) (R' s)) := by
  rw [inertia_mulVec, mulVec_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [h.deriv_mulVec, mulVec_cross (h.orthogonal s) (h.det_eq_one s), mulVec_smul]

/-- The moment of the momenta about the origin of the body: the angular
momentum `R (I Ω)` and the moment of the momentum of the origin. -/
theorem sum_cross_smul_velocity (h : IsRigidMotion c c' R R') (m : ι → ℝ)
    (r : ι → Fin 3 → ℝ) (s : ℝ) :
    ∑ a, (R s *ᵥ r a) ⨯₃ (m a • (c' s + R' s *ᵥ r a)) =
      R s *ᵥ (inertia m r *ᵥ angularVelocityBody (R s) (R' s)) +
        (R s *ᵥ ∑ a, m a • r a) ⨯₃ c' s := by
  rw [← h.sum_smul_cross_velocity, mulVec_sum, sum_cross, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_add, map_add, map_smul, map_smul, mulVec_smul, LinearMap.map_smul₂, add_comm]

/-- `Ṁ = K`: the derivative of the angular momentum `R (I Ω)` is the moment of
the forces about the origin of the body, when this origin is the centre of
mass or is at rest. -/
theorem hasDerivAt_angularMomentum (h : IsRigidMotion c c' R R')
    (hpt : ∑ a, m a • r a = 0 ∨ ∀ s, c' s = 0) {F : ι → Fin 3 → ℝ} {t : ℝ}
    (hF : ∀ a, HasDerivAt (fun u => m a • (c' u + R' u *ᵥ r a)) (F a) t) :
    HasDerivAt (fun u => R u *ᵥ (inertia m r *ᵥ angularVelocityBody (R u) (R' u)))
      (∑ a, (R t *ᵥ r a) ⨯₃ F a) t := by
  have hzero : ∀ (A : Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ), (A *ᵥ ∑ a, m a • r a) ⨯₃ c' s = 0 := by
    intro A s
    rcases hpt with hcm | hrest
    · rw [hcm, mulVec_zero, LinearMap.map_zero₂]
    · rw [hrest s, map_zero]
  have hG : HasDerivAt (fun u => ∑ a, (R u *ᵥ r a) ⨯₃ (m a • (c' u + R' u *ᵥ r a)))
      (∑ a, ((R' t *ᵥ r a) ⨯₃ (m a • (c' t + R' t *ᵥ r a)) + (R t *ᵥ r a) ⨯₃ F a)) t :=
    HasDerivAt.fun_sum fun a _ => by
      have h1 := hasDerivAt_mulVec (h.hasDerivAt_rotation t) (hasDerivAt_const t (r a))
      rw [mulVec_zero, add_zero] at h1
      exact hasDerivAt_cross h1 (hF a)
  have heq : (fun u => ∑ a, (R u *ᵥ r a) ⨯₃ (m a • (c' u + R' u *ᵥ r a))) =
      fun u => R u *ᵥ (inertia m r *ᵥ angularVelocityBody (R u) (R' u)) := by
    funext u
    rw [h.sum_cross_smul_velocity, hzero, add_zero]
  rw [heq] at hG
  refine hG.congr_deriv ?_
  rw [Finset.sum_add_distrib, add_eq_right]
  have hterm : ∀ a, (R' t *ᵥ r a) ⨯₃ (m a • (c' t + R' t *ᵥ r a)) =
      (R' t *ᵥ (m a • r a)) ⨯₃ c' t := by
    intro a
    rw [smul_add, map_add, map_smul, map_smul, cross_self, smul_zero, add_zero, mulVec_smul,
      LinearMap.map_smul₂]
  simp_rw [hterm]
  rw [← sum_cross, ← mulVec_sum, hzero]

/-- Euler's equations with a moment of forces: in the body frame,
`d(I Ω)/dt = (I Ω) × Ω + Rᵀ K`. -/
theorem hasDerivAt_bodyAngularMomentum (h : IsRigidMotion c c' R R')
    (hpt : ∑ a, m a • r a = 0 ∨ ∀ s, c' s = 0) {F : ι → Fin 3 → ℝ} {t : ℝ}
    (hF : ∀ a, HasDerivAt (fun u => m a • (c' u + R' u *ᵥ r a)) (F a) t) :
    HasDerivAt (fun u => inertia m r *ᵥ angularVelocityBody (R u) (R' u))
      ((inertia m r *ᵥ angularVelocityBody (R t) (R' t)) ⨯₃ angularVelocityBody (R t) (R' t) +
        (R t)ᵀ *ᵥ ∑ a, (R t *ᵥ r a) ⨯₃ F a) t := by
  have h1 := hasDerivAt_mulVec (R := fun u => (R u)ᵀ) (R' := (R' t)ᵀ)
    (fun a b => h.hasDerivAt_rotation t b a) (h.hasDerivAt_angularMomentum hpt hF)
  have heq : (fun u => (R u)ᵀ *ᵥ
      (R u *ᵥ (inertia m r *ᵥ angularVelocityBody (R u) (R' u)))) =
      fun u => inertia m r *ᵥ angularVelocityBody (R u) (R' u) :=
    funext fun u => transpose_mulVec_mulVec (h.orthogonal u) _
  rw [heq] at h1
  refine h1.congr_deriv ?_
  congr 1
  have hT : (R' t)ᵀ = -(hat (angularVelocityBody (R t) (R' t)) * (R t)ᵀ) := by
    conv_lhs => rw [h.rotation_deriv t]
    rw [transpose_mul, transpose_hat, Matrix.neg_mul]
  rw [hT, neg_mulVec, ← mulVec_mulVec, transpose_mulVec_mulVec (h.orthogonal t), hat_mulVec,
    cross_anticomm]

/-- The kinetic energy of a body whose origin is its centre of mass or is at
rest: `Σ mₐ |vₐ|² = μ |ċ|² + Ω · I Ω`. -/
theorem sum_mul_velocity_sq (h : IsRigidMotion c c' R R') {s : ℝ}
    (hpt : ∑ a, m a • r a = 0 ∨ c' s = 0) :
    ∑ a, m a * ((c' s + R' s *ᵥ r a) ⬝ᵥ (c' s + R' s *ᵥ r a)) =
      (∑ a, m a) * (c' s ⬝ᵥ c' s) +
        angularVelocityBody (R s) (R' s) ⬝ᵥ
          (inertia m r *ᵥ angularVelocityBody (R s) (R' s)) := by
  have hcross : ∑ a, m a * (c' s ⬝ᵥ (R' s *ᵥ r a)) = 0 := by
    have h1 : ∑ a, m a * (c' s ⬝ᵥ (R' s *ᵥ r a)) = c' s ⬝ᵥ (R' s *ᵥ ∑ a, m a • r a) := by
      rw [mulVec_sum, dotProduct_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [mulVec_smul, dotProduct_smul, smul_eq_mul]
    rcases hpt with hcm | hrest
    · rw [h1, hcm, mulVec_zero, dotProduct_zero]
    · rw [h1, hrest, zero_dotProduct]
  have hrot : ∀ a, (R' s *ᵥ r a) ⬝ᵥ (R' s *ᵥ r a) =
      (angularVelocityBody (R s) (R' s) ⨯₃ r a) ⬝ᵥ (angularVelocityBody (R s) (R' s) ⨯₃ r a) :=
    fun a => by rw [h.deriv_mulVec, mulVec_dotProduct_mulVec (h.orthogonal s)]
  rw [dotProduct_inertia_mulVec, Finset.sum_mul, ← Finset.sum_add_distrib]
  have hsplit : ∀ a, m a * ((c' s + R' s *ᵥ r a) ⬝ᵥ (c' s + R' s *ᵥ r a)) =
      m a * (c' s ⬝ᵥ c' s) + m a * ((R' s *ᵥ r a) ⬝ᵥ (R' s *ᵥ r a)) +
        2 * (m a * (c' s ⬝ᵥ (R' s *ᵥ r a))) := by
    intro a
    rw [add_dotProduct, dotProduct_add, dotProduct_add, dotProduct_comm (R' s *ᵥ r a) (c' s)]
    ring
  simp_rw [hsplit, hrot]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hcross, mul_zero, add_zero]

end Particles

end IsRigidMotion

end ProjectAInos.Mechanics.Rigid
