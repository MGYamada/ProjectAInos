/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Rigid.EulerAngles
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Regular precession of the free symmetric top

A symmetric top has the principal moments `I₁ = I₂` and `I₃`. In Eulerian
angles its angular momentum in the body frame is `(I₁ Ω₁, I₁ Ω₂, I₃ Ω₃)`, and
the angular momentum in the space frame is the rotation applied to it.

The angular momentum in the space frame is `M` along the fixed axis `Z`
exactly when `θ̇ = 0`, `I₁ φ̇ = M` and `I₃ (φ̇ cos θ + ψ̇) = M cos θ`
(Landau–Lifshitz §33 and (35.4)): the axis of the top keeps a constant angle
with `M` and turns about it uniformly, and the top turns uniformly about its
axis.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics.Rigid

open Matrix

section Algebra

variable {K : Type*} [CommRing K] {c1 s1 c2 s2 c3 s3 : K}

/-- The angular momentum of a symmetric top in the body frame. -/
def symmetricTopMomentum (I1 I3 : K) (Ω : Fin 3 → K) : Fin 3 → K :=
  ![I1 * Ω 0, I1 * Ω 1, I3 * Ω 2]

/-- The fixed axis `Z` in the body frame: `(sin θ sin ψ, sin θ cos ψ, cos θ)`. -/
def verticalAxis (c2 s2 c3 s3 : K) : Fin 3 → K := ![s2 * s3, s2 * c3, c2]

/-- The rotation takes the body components of the fixed axis to `(0, 0, 1)`. -/
theorem eulerMatrix_mulVec_verticalAxis (c1 s1 : K) (h2 : c2 ^ 2 + s2 ^ 2 = 1)
    (h3 : c3 ^ 2 + s3 ^ 2 = 1) :
    eulerMatrix c1 s1 c2 s2 c3 s3 *ᵥ verticalAxis c2 s2 c3 s3 = ![0, 0, 1] := by
  ext i
  fin_cases i <;>
    simp [eulerMatrix, rotZ, rotX, verticalAxis, Matrix.mulVec, dotProduct, Matrix.mul_apply,
      Fin.sum_univ_three]
  · linear_combination (-(s1 * s2 * c2)) * h3
  · linear_combination (c1 * s2 * c2) * h3
  · linear_combination (s2 ^ 2) * h3 + h2

/-- The components of the fixed axis in the body frame are the third row of
the rotation. -/
theorem transpose_eulerMatrix_mulVec (c1 s1 c2 s2 c3 s3 : K) :
    (eulerMatrix c1 s1 c2 s2 c3 s3)ᵀ *ᵥ ![0, 0, 1] = verticalAxis c2 s2 c3 s3 := by
  ext i
  fin_cases i <;>
    simp [eulerMatrix, rotZ, rotX, verticalAxis, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- Regular precession: with `θ̇ = 0`, `I₁ φ̇ = M` and
`I₃ (φ̇ cos θ + ψ̇) = M cos θ`, the angular momentum of the symmetric top in the
space frame is `M` along the fixed axis. -/
theorem eulerMatrix_mulVec_symmetricTopMomentum (c1 s1 : K)
    (h2 : c2 ^ 2 + s2 ^ 2 = 1) (h3 : c3 ^ 2 + s3 ^ 2 = 1) {I1 I3 M w1 w3 : K}
    (hw1 : I1 * w1 = M) (hw3 : I3 * (w1 * c2 + w3) = M * c2) :
    eulerMatrix c1 s1 c2 s2 c3 s3 *ᵥ
        symmetricTopMomentum I1 I3 (bodyAngularVelocity c2 s2 c3 s3 w1 0 w3) =
      ![0, 0, M] := by
  have hL : symmetricTopMomentum I1 I3 (bodyAngularVelocity c2 s2 c3 s3 w1 0 w3) =
      M • verticalAxis c2 s2 c3 s3 := by
    ext i
    fin_cases i
    · simp only [symmetricTopMomentum, bodyAngularVelocity, verticalAxis, Fin.zero_eta,
        Matrix.cons_val_zero, Pi.smul_apply, smul_eq_mul]
      linear_combination (s2 * s3) * hw1
    · simp only [symmetricTopMomentum, bodyAngularVelocity, verticalAxis, Fin.mk_one,
        Matrix.cons_val_one, Matrix.cons_val_zero, Pi.smul_apply, smul_eq_mul]
      linear_combination (s2 * c3) * hw1
    · simp only [symmetricTopMomentum, bodyAngularVelocity, verticalAxis, Fin.reduceFinMk,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Pi.smul_apply, smul_eq_mul]
      linear_combination hw3
  rw [hL, Matrix.mulVec_smul, eulerMatrix_mulVec_verticalAxis c1 s1 h2 h3]
  ext i
  fin_cases i <;> simp

end Algebra

/-- Regular precession of the free symmetric top (Landau–Lifshitz §33,
(35.4)): for real angles with `sin θ ≠ 0`, the angular momentum in the space
frame is `M` along the fixed axis exactly when `θ̇ = 0`, `I₁ φ̇ = M` and
`I₃ (φ̇ cos θ + ψ̇) = M cos θ`. -/
theorem eulerMatrix_mulVec_symmetricTopMomentum_iff {c1 s1 c2 s2 c3 s3 : ℝ}
    (h1 : c1 ^ 2 + s1 ^ 2 = 1) (h2 : c2 ^ 2 + s2 ^ 2 = 1) (h3 : c3 ^ 2 + s3 ^ 2 = 1) {I1 : ℝ}
    (hI1 : I1 ≠ 0) (hs2 : s2 ≠ 0) (I3 M w1 w2 w3 : ℝ) :
    eulerMatrix c1 s1 c2 s2 c3 s3 *ᵥ
          symmetricTopMomentum I1 I3 (bodyAngularVelocity c2 s2 c3 s3 w1 w2 w3) =
        ![0, 0, M] ↔
      w2 = 0 ∧ I1 * w1 = M ∧ I3 * (w1 * c2 + w3) = M * c2 := by
  constructor
  · intro h
    have hR : (eulerMatrix c1 s1 c2 s2 c3 s3)ᵀ * eulerMatrix c1 s1 c2 s2 c3 s3 = 1 :=
      mul_eq_one_comm.mp (eulerMatrix_mul_transpose h1 h2 h3)
    have hL := congrArg (fun v => (eulerMatrix c1 s1 c2 s2 c3 s3)ᵀ *ᵥ v) h
    simp only [Matrix.mulVec_mulVec, hR, Matrix.one_mulVec] at hL
    have hax : (eulerMatrix c1 s1 c2 s2 c3 s3)ᵀ *ᵥ ![0, 0, M] =
        M • verticalAxis c2 s2 c3 s3 := by
      have hM : (![0, 0, M] : Fin 3 → ℝ) = M • ![0, 0, 1] := by
        ext i
        fin_cases i <;> simp
      rw [hM, Matrix.mulVec_smul, transpose_eulerMatrix_mulVec]
    rw [hax] at hL
    have e0 := congrFun hL 0
    have e1 := congrFun hL 1
    have e2 := congrFun hL 2
    simp only [symmetricTopMomentum, bodyAngularVelocity, verticalAxis, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
      Pi.smul_apply, smul_eq_mul] at e0 e1 e2
    have hw2 : I1 * w2 = 0 := by
      linear_combination c3 * e0 - s3 * e1 - (I1 * w2) * h3
    have hw2' : w2 = 0 := (mul_eq_zero.mp hw2).resolve_left hI1
    have hw1 : (I1 * w1 - M) * s2 = 0 := by
      linear_combination s3 * e0 + c3 * e1 - (I1 * w1 * s2 - M * s2) * h3
    have hw1' : I1 * w1 = M := sub_eq_zero.mp ((mul_eq_zero.mp hw1).resolve_right hs2)
    exact ⟨hw2', hw1', e2⟩
  · rintro ⟨rfl, hw1, hw3⟩
    exact eulerMatrix_mulVec_symmetricTopMomentum c1 s1 h2 h3 hw1 hw3

/-- The rate of the proper rotation in a regular precession
(Landau–Lifshitz (35.4)): `ψ̇ = M cos θ (1/I₃ − 1/I₁)`. -/
theorem regularPrecession_psi_rate {I1 I3 M c2 w1 w3 : ℝ} (hI1 : I1 ≠ 0) (hI3 : I3 ≠ 0)
    (hw1 : I1 * w1 = M) (hw3 : I3 * (w1 * c2 + w3) = M * c2) :
    w3 = M * c2 * (I3⁻¹ - I1⁻¹) := by
  have h1 : w1 = M / I1 := by
    rw [eq_div_iff hI1, mul_comm]
    exact hw1
  have h3 : w1 * c2 + w3 = M * c2 / I3 := by
    rw [eq_div_iff hI3, mul_comm]
    exact hw3
  rw [h1] at h3
  field_simp
  field_simp at h3
  linarith

/-- The regular precession as a motion: for the angles
`φ(t) = φ₀ + (M/I₁) t`, `θ(t) = θ₀` and
`ψ(t) = ψ₀ + M cos θ₀ (1/I₃ − 1/I₁) t`, whose rates are `M/I₁`, `0` and
`M cos θ₀ (1/I₃ − 1/I₁)`, the angular momentum in the space frame is
`(0, 0, M)` at every time. -/
theorem eulerRotation_mulVec_symmetricTopMomentum {I1 I3 : ℝ} (hI1 : I1 ≠ 0) (hI3 : I3 ≠ 0)
    (M φ₀ θ₀ ψ₀ t : ℝ) :
    eulerRotation (φ₀ + M / I1 * t) θ₀ (ψ₀ + M * Real.cos θ₀ * (I3⁻¹ - I1⁻¹) * t) *ᵥ
        symmetricTopMomentum I1 I3
          (bodyAngularVelocity (Real.cos θ₀) (Real.sin θ₀)
            (Real.cos (ψ₀ + M * Real.cos θ₀ * (I3⁻¹ - I1⁻¹) * t))
            (Real.sin (ψ₀ + M * Real.cos θ₀ * (I3⁻¹ - I1⁻¹) * t)) (M / I1) 0
            (M * Real.cos θ₀ * (I3⁻¹ - I1⁻¹))) =
      ![0, 0, M] := by
  refine eulerMatrix_mulVec_symmetricTopMomentum _ _ (Real.cos_sq_add_sin_sq θ₀)
    (Real.cos_sq_add_sin_sq _) ?_ ?_
  · field_simp
  · field_simp
    ring

end ProjectAInos.Mechanics.Rigid
