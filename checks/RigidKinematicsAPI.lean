/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAInos

/-! Public consumers of the rigid-body kinematics API. Default elaborator
options are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/
noncomputable section
open ProjectAInos.Mechanics ProjectAInos.Mechanics.Rigid
open Matrix

section AngularVelocity

/-- `hat Ω` acts as the cross product with `Ω`. -/
example (Ω r : Fin 3 → ℝ) : hat Ω *ᵥ r = Ω ⨯₃ r := hat_mulVec Ω r

example (Ω : Fin 3 → ℝ) : (hat Ω)ᵀ = -hat Ω := transpose_hat Ω

example (Ω : Fin 3 → ℝ) : vee (hat Ω) = Ω := vee_hat Ω

example {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : Aᵀ = -A) : hat (vee A) = A := hat_vee hA

/-- The cross product corresponds to the commutator. -/
example (Ω Ω' : Fin 3 → ℝ) : hat (Ω ⨯₃ Ω') = hat Ω * hat Ω' - hat Ω' * hat Ω :=
  hat_cross Ω Ω'

/-- `so(3) ≅ ℝ³` as Lie algebras. -/
example (Ω Ω' : Fin 3 → ℝ) : hatEquiv (Ω ⨯₃ Ω') = ⁅hatEquiv Ω, hatEquiv Ω'⁆ :=
  hatEquiv_cross Ω Ω'

example (Ω : Fin 3 → ℝ) :
    ((hatEquiv Ω : LieAlgebra.Orthogonal.so (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) = hat Ω :=
  rfl

example (V Ω r : Fin 3 → ℝ) : velocityField V Ω r = V + Ω ⨯₃ r := rfl

/-- The angular velocity is independent of the origin. -/
example {V V' Ω Ω' a : Fin 3 → ℝ}
    (h : ∀ r, velocityField V Ω (r + a) = velocityField V' Ω' r) :
    V' = V + Ω ⨯₃ a ∧ Ω' = Ω :=
  velocityField_change_of_origin h

example {V V' Ω Ω' : Fin 3 → ℝ} (h : ∀ r, velocityField V Ω r = velocityField V' Ω' r) :
    V = V' ∧ Ω = Ω' :=
  velocityField_injective h

/-- For orthogonal matrices, `Ṙ Rᵀ` is skew-symmetric. -/
example {R : ℝ → Matrix (Fin 3) (Fin 3) ℝ} {R' : Matrix (Fin 3) (Fin 3) ℝ} {t : ℝ}
    (hR : ∀ a b, HasDerivAt (fun s => R s a b) (R' a b) t)
    (horth : ∀ s, R s * (R s)ᵀ = 1) : (R' * (R t)ᵀ)ᵀ = -(R' * (R t)ᵀ) :=
  transpose_deriv_mul_transpose hR horth

/-- The velocity of a body point is `ċ + Ω × (x − c)`. -/
example {R : ℝ → Matrix (Fin 3) (Fin 3) ℝ} {R' : Matrix (Fin 3) (Fin 3) ℝ}
    {c : ℝ → Fin 3 → ℝ} {c' : Fin 3 → ℝ} {t : ℝ}
    (hR : ∀ a b, HasDerivAt (fun s => R s a b) (R' a b) t)
    (horth : ∀ s, R s * (R s)ᵀ = 1) (hc : ∀ a, HasDerivAt (fun s => c s a) (c' a) t)
    (r₀ : Fin 3 → ℝ) (a : Fin 3) :
    HasDerivAt (fun s => (c s + R s *ᵥ r₀) a)
      ((c' + vee (R' * (R t)ᵀ) ⨯₃ (R t *ᵥ r₀)) a) t :=
  hasDerivAt_rigidMotion hR horth hc r₀ a

end AngularVelocity

section InertiaTensor

variable {ι : Type*} [Fintype ι]

example (m : ι → ℝ) (r : ι → Fin 3 → ℝ) (i k : Fin 3) :
    inertia m r i k =
      ∑ a, m a * ((r a ⬝ᵥ r a) * (if i = k then 1 else 0) - r a i * r a k) := rfl

example (m : ι → ℝ) (r : ι → Fin 3 → ℝ) : (inertia m r)ᵀ = inertia m r :=
  transpose_inertia m r

/-- `M = I Ω`. -/
example (m : ι → ℝ) (r : ι → Fin 3 → ℝ) (Ω : Fin 3 → ℝ) :
    inertia m r *ᵥ Ω = ∑ a, m a • (r a ⨯₃ (Ω ⨯₃ r a)) :=
  inertia_mulVec m r Ω

/-- Twice the kinetic energy. -/
example (m : ι → ℝ) (r : ι → Fin 3 → ℝ) (Ω : Fin 3 → ℝ) :
    Ω ⬝ᵥ (inertia m r *ᵥ Ω) = ∑ a, m a * ((Ω ⨯₃ r a) ⬝ᵥ (Ω ⨯₃ r a)) :=
  dotProduct_inertia_mulVec m r Ω

example {m : ι → ℝ} (hm : ∀ a, 0 ≤ m a) (r : ι → Fin 3 → ℝ) (x : Fin 3 → ℝ) :
    0 ≤ x ⬝ᵥ (inertia m r *ᵥ x) :=
  dotProduct_inertia_mulVec_nonneg hm r x

/-- The parallel-axis theorem. -/
example (m : ι → ℝ) (r : ι → Fin 3 → ℝ) (hcm : ∑ b, m b • r b = 0) (a : Fin 3 → ℝ)
    (i k : Fin 3) :
    inertia m (fun b => r b + a) i k =
      inertia m r i k + (∑ b, m b) * ((a ⬝ᵥ a) * (if i = k then 1 else 0) - a i * a k) :=
  inertia_add_apply m r hcm a i k

/-- Principal axes and principal moments. -/
example (m : ι → ℝ) (r : ι → Fin 3 → ℝ) (c : Fin 3) :
    inertia m r *ᵥ ⇑(principalAxes m r c) = principalMoments m r c • ⇑(principalAxes m r c) :=
  inertia_mulVec_principalAxes m r c

example (m : ι → ℝ) (r : ι → Fin 3 → ℝ) (c : Fin 3) :
    ⇑(principalAxes m r c) ⬝ᵥ ⇑(principalAxes m r c) = 1 :=
  dotProduct_principalAxes_self m r c

example {m : ι → ℝ} (hm : ∀ a, 0 ≤ m a) (r : ι → Fin 3 → ℝ) (c : Fin 3) :
    0 ≤ principalMoments m r c :=
  principalMoments_nonneg hm r c

/-- The triangle inequality `I₂ ≤ I₀ + I₁` for the principal moments. -/
example {m : ι → ℝ} (hm : ∀ a, 0 ≤ m a) (r : ι → Fin 3 → ℝ) :
    principalMoments m r 2 ≤ principalMoments m r 0 + principalMoments m r 1 :=
  principalMoments_two_le hm r

example {m : ι → ℝ} (hm : ∀ a, 0 ≤ m a) (r : ι → Fin 3 → ℝ) :
    principalMoments m r 0 ≤ principalMoments m r 1 + principalMoments m r 2 :=
  principalMoments_zero_le hm r

end InertiaTensor
