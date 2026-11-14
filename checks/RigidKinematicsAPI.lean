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

section EulerAngles

variable {K : Type*} [CommRing K] {c1 s1 c2 s2 c3 s3 w1 w2 w3 : K}

example (c1 s1 c2 s2 c3 s3 : K) :
    eulerMatrix c1 s1 c2 s2 c3 s3 = rotZ c1 s1 * rotX c2 s2 * rotZ c3 s3 := rfl

example (c s : K) : rotZ c s = !![c, -s, 0; s, c, 0; 0, 0, 1] := rfl

example (c s : K) : rotX c s = !![1, 0, 0; 0, c, -s; 0, s, c] := rfl

example (c2 s2 c3 s3 w1 w2 w3 : K) :
    bodyAngularVelocity c2 s2 c3 s3 w1 w2 w3 =
      ![w1 * s2 * s3 + w2 * c3, w1 * s2 * c3 - w2 * s3, w1 * c2 + w3] := rfl

/-- The rotation is orthogonal with determinant one. -/
example (h1 : c1 ^ 2 + s1 ^ 2 = 1) (h2 : c2 ^ 2 + s2 ^ 2 = 1) (h3 : c3 ^ 2 + s3 ^ 2 = 1) :
    eulerMatrix c1 s1 c2 s2 c3 s3 * (eulerMatrix c1 s1 c2 s2 c3 s3)ᵀ = 1 ∧
      (eulerMatrix c1 s1 c2 s2 c3 s3).det = 1 :=
  ⟨eulerMatrix_mul_transpose h1 h2 h3, det_eulerMatrix h1 h2 h3⟩

/-- The angular velocity in the body frame. -/
example (h1 : c1 ^ 2 + s1 ^ 2 = 1) (h2 : c2 ^ 2 + s2 ^ 2 = 1) (h3 : c3 ^ 2 + s3 ^ 2 = 1) :
    (eulerMatrix c1 s1 c2 s2 c3 s3)ᵀ * eulerMatrixDeriv c1 s1 c2 s2 c3 s3 w1 w2 w3 =
      hat (bodyAngularVelocity c2 s2 c3 s3 w1 w2 w3) :=
  transpose_mul_eulerMatrixDeriv h1 h2 h3

/-- The angular velocity in the space frame, and the relation `ω = R Ω`. -/
example (h1 : c1 ^ 2 + s1 ^ 2 = 1) (h2 : c2 ^ 2 + s2 ^ 2 = 1) (h3 : c3 ^ 2 + s3 ^ 2 = 1) :
    eulerMatrixDeriv c1 s1 c2 s2 c3 s3 w1 w2 w3 * (eulerMatrix c1 s1 c2 s2 c3 s3)ᵀ =
        hat (spaceAngularVelocity c1 s1 c2 s2 w1 w2 w3) ∧
      eulerMatrix c1 s1 c2 s2 c3 s3 *ᵥ bodyAngularVelocity c2 s2 c3 s3 w1 w2 w3 =
        spaceAngularVelocity c1 s1 c2 s2 w1 w2 w3 :=
  ⟨eulerMatrixDeriv_mul_transpose h1 h2 h3, eulerMatrix_mulVec_bodyAngularVelocity h2 h3⟩

/-- The kinetic energy of the symmetric top in Eulerian angles. -/
example (I1 I3 : K) (h3 : c3 ^ 2 + s3 ^ 2 = 1) :
    I1 * (bodyAngularVelocity c2 s2 c3 s3 w1 w2 w3 0 ^ 2 +
          bodyAngularVelocity c2 s2 c3 s3 w1 w2 w3 1 ^ 2) +
        I3 * bodyAngularVelocity c2 s2 c3 s3 w1 w2 w3 2 ^ 2 =
      I1 * (w2 ^ 2 + w1 ^ 2 * s2 ^ 2) + I3 * (w1 * c2 + w3) ^ 2 :=
  symmetricTop_energy I1 I3 h3

/-- The angles are non-degenerate co-ordinates where `sin θ` is invertible. -/
example (c2 : K) (h3 : c3 ^ 2 + s3 ^ 2 = 1) : (eulerJacobian c2 s2 c3 s3).det = -s2 :=
  det_eulerJacobian c2 h3

example (c2 s2 c3 s3 w1 w2 w3 : K) :
    eulerJacobian c2 s2 c3 s3 *ᵥ ![w1, w2, w3] = bodyAngularVelocity c2 s2 c3 s3 w1 w2 w3 :=
  eulerJacobian_mulVec c2 s2 c3 s3 w1 w2 w3

/-- The rotation with real Eulerian angles is in `SO(3)`. -/
example (φ θ ψ : ℝ) : eulerRotation φ θ ψ ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  eulerRotation_mem_specialOrthogonalGroup φ θ ψ

/-- The derivative of the rotation for time-dependent angles. -/
example {φ θ ψ : ℝ → ℝ} {φ' θ' ψ' t : ℝ} (hφ : HasDerivAt φ φ' t) (hθ : HasDerivAt θ θ' t)
    (hψ : HasDerivAt ψ ψ' t) (i j : Fin 3) :
    HasDerivAt (fun s => eulerRotation (φ s) (θ s) (ψ s) i j)
      (eulerMatrixDeriv (Real.cos (φ t)) (Real.sin (φ t)) (Real.cos (θ t)) (Real.sin (θ t))
        (Real.cos (ψ t)) (Real.sin (ψ t)) φ' θ' ψ' i j) t :=
  hasDerivAt_eulerRotation hφ hθ hψ i j

/-- The body-frame angular velocity of Landau–Lifshitz (35.1). -/
example (φ θ ψ φ' θ' ψ' : ℝ) :
    vee ((eulerRotation φ θ ψ)ᵀ *
        eulerMatrixDeriv (Real.cos φ) (Real.sin φ) (Real.cos θ) (Real.sin θ) (Real.cos ψ)
          (Real.sin ψ) φ' θ' ψ') =
      ![φ' * Real.sin θ * Real.sin ψ + θ' * Real.cos ψ,
        φ' * Real.sin θ * Real.cos ψ - θ' * Real.sin ψ, φ' * Real.cos θ + ψ'] :=
  vee_transpose_mul_eulerMatrixDeriv φ θ ψ φ' θ' ψ'

end EulerAngles

section RegularPrecession

example (I1 I3 : ℝ) (Ω : Fin 3 → ℝ) :
    symmetricTopMomentum I1 I3 Ω = ![I1 * Ω 0, I1 * Ω 1, I3 * Ω 2] := rfl

/-- The fixed axis in the body frame is the third row of the rotation. -/
example (c1 s1 c2 s2 c3 s3 : ℝ) :
    (eulerMatrix c1 s1 c2 s2 c3 s3)ᵀ *ᵥ ![0, 0, 1] = ![s2 * s3, s2 * c3, c2] :=
  transpose_eulerMatrix_mulVec c1 s1 c2 s2 c3 s3

/-- Regular precession of the free symmetric top (Landau–Lifshitz §33, (35.4)). -/
example {c1 s1 c2 s2 c3 s3 : ℝ} (h1 : c1 ^ 2 + s1 ^ 2 = 1) (h2 : c2 ^ 2 + s2 ^ 2 = 1)
    (h3 : c3 ^ 2 + s3 ^ 2 = 1) {I1 : ℝ} (hI1 : I1 ≠ 0) (hs2 : s2 ≠ 0) (I3 M w1 w2 w3 : ℝ) :
    eulerMatrix c1 s1 c2 s2 c3 s3 *ᵥ
          symmetricTopMomentum I1 I3 (bodyAngularVelocity c2 s2 c3 s3 w1 w2 w3) =
        ![0, 0, M] ↔
      w2 = 0 ∧ I1 * w1 = M ∧ I3 * (w1 * c2 + w3) = M * c2 :=
  eulerMatrix_mulVec_symmetricTopMomentum_iff h1 h2 h3 hI1 hs2 I3 M w1 w2 w3

example {I1 I3 M c2 w1 w3 : ℝ} (hI1 : I1 ≠ 0) (hI3 : I3 ≠ 0) (hw1 : I1 * w1 = M)
    (hw3 : I3 * (w1 * c2 + w3) = M * c2) : w3 = M * c2 * (I3⁻¹ - I1⁻¹) :=
  regularPrecession_psi_rate hI1 hI3 hw1 hw3

/-- The regular precession as a motion with uniform rates. -/
example {I1 I3 : ℝ} (hI1 : I1 ≠ 0) (hI3 : I3 ≠ 0) (M φ₀ θ₀ ψ₀ t : ℝ) :
    eulerRotation (φ₀ + M / I1 * t) θ₀ (ψ₀ + M * Real.cos θ₀ * (I3⁻¹ - I1⁻¹) * t) *ᵥ
        symmetricTopMomentum I1 I3
          (bodyAngularVelocity (Real.cos θ₀) (Real.sin θ₀)
            (Real.cos (ψ₀ + M * Real.cos θ₀ * (I3⁻¹ - I1⁻¹) * t))
            (Real.sin (ψ₀ + M * Real.cos θ₀ * (I3⁻¹ - I1⁻¹) * t)) (M / I1) 0
            (M * Real.cos θ₀ * (I3⁻¹ - I1⁻¹))) =
      ![0, 0, M] :=
  eulerRotation_mulVec_symmetricTopMomentum hI1 hI3 M φ₀ θ₀ ψ₀ t

end RegularPrecession
