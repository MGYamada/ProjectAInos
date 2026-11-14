/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Rigid.AngularVelocity
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Eulerian angles

The rotation with Eulerian angles `φ`, `θ`, `ψ` is the product
`R = R_z(φ) R_x(θ) R_z(ψ)` (Landau–Lifshitz §35). The statements are algebraic:
the cosines and sines of the three angles are elements `cₖ`, `sₖ` of a
commutative ring with `cₖ² + sₖ² = 1`, and the rates of the angles are elements
`wₖ`. The derivative of `R` is the matrix `eulerMatrixDeriv` given by the product
rule.

* `R` is orthogonal and has determinant one.
* `Rᵀ Ṙ = hat Ω` with the angular velocity in the body frame
  `Ω = (φ̇ sin θ sin ψ + θ̇ cos ψ, φ̇ sin θ cos ψ − θ̇ sin ψ, φ̇ cos θ + ψ̇)`.
* `Ṙ Rᵀ = hat ω` with the angular velocity in the space frame, and `ω = R Ω`.
-/

@[expose] public section

namespace ProjectAInos.Mechanics.Rigid

open Matrix

variable {K : Type*} [CommRing K]

/-- The rotation about the third axis with cosine `c` and sine `s`. -/
def rotZ (c s : K) : Matrix (Fin 3) (Fin 3) K := !![c, -s, 0; s, c, 0; 0, 0, 1]

/-- The rotation about the first axis with cosine `c` and sine `s`. -/
def rotX (c s : K) : Matrix (Fin 3) (Fin 3) K := !![1, 0, 0; 0, c, -s; 0, s, c]

/-- The derivative of `rotZ` with respect to its angle. -/
def dRotZ (c s : K) : Matrix (Fin 3) (Fin 3) K := !![-s, -c, 0; c, -s, 0; 0, 0, 0]

/-- The derivative of `rotX` with respect to its angle. -/
def dRotX (c s : K) : Matrix (Fin 3) (Fin 3) K := !![0, 0, 0; 0, -s, -c; 0, c, -s]

/-- The rotation `R_z(φ) R_x(θ) R_z(ψ)` with Eulerian angles `φ`, `θ`, `ψ`. -/
def eulerMatrix (c1 s1 c2 s2 c3 s3 : K) : Matrix (Fin 3) (Fin 3) K :=
  rotZ c1 s1 * rotX c2 s2 * rotZ c3 s3

/-- The derivative of the rotation, by the product rule, for rates `w1`, `w2`,
`w3` of the three angles. -/
def eulerMatrixDeriv (c1 s1 c2 s2 c3 s3 w1 w2 w3 : K) : Matrix (Fin 3) (Fin 3) K :=
  w1 • (dRotZ c1 s1 * rotX c2 s2 * rotZ c3 s3) + w2 • (rotZ c1 s1 * dRotX c2 s2 * rotZ c3 s3) +
    w3 • (rotZ c1 s1 * rotX c2 s2 * dRotZ c3 s3)

/-- The angular velocity in the body frame:
`(φ̇ sin θ sin ψ + θ̇ cos ψ, φ̇ sin θ cos ψ − θ̇ sin ψ, φ̇ cos θ + ψ̇)`. -/
def bodyAngularVelocity (c2 s2 c3 s3 w1 w2 w3 : K) : Fin 3 → K :=
  ![w1 * s2 * s3 + w2 * c3, w1 * s2 * c3 - w2 * s3, w1 * c2 + w3]

/-- The angular velocity in the space frame:
`(θ̇ cos φ + ψ̇ sin θ sin φ, θ̇ sin φ − ψ̇ sin θ cos φ, φ̇ + ψ̇ cos θ)`. -/
def spaceAngularVelocity (c1 s1 c2 s2 w1 w2 w3 : K) : Fin 3 → K :=
  ![w2 * c1 + w3 * s1 * s2, w2 * s1 - w3 * c1 * s2, w1 + w3 * c2]

variable {c1 s1 c2 s2 c3 s3 : K}

/-- The rotation with Eulerian angles is orthogonal. -/
theorem eulerMatrix_mul_transpose (h1 : c1 ^ 2 + s1 ^ 2 = 1) (h2 : c2 ^ 2 + s2 ^ 2 = 1)
    (h3 : c3 ^ 2 + s3 ^ 2 = 1) :
    eulerMatrix c1 s1 c2 s2 c3 s3 * (eulerMatrix c1 s1 c2 s2 c3 s3)ᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eulerMatrix, rotZ, rotX, Matrix.mul_apply, Fin.sum_univ_three]
  · linear_combination (c3 ^ 2 + s3 ^ 2) * h1 + (c3 ^ 2 * s1 ^ 2 + s1 ^ 2 * s3 ^ 2) * h2 + (-s1
      ^ 2 * s2 ^ 2 + 1) * h3
  · linear_combination (-c1 * c3 ^ 2 * s1 - c1 * s1 * s3 ^ 2) * h2 + (c1 * s1 * s2 ^ 2) * h3
  · linear_combination (-c2 * s1 * s2) * h3
  · linear_combination (-c1 * c3 ^ 2 * s1 - c1 * s1 * s3 ^ 2) * h2 + (c1 * s1 * s2 ^ 2) * h3
  · linear_combination (c2 ^ 2 * c3 ^ 2 + c2 ^ 2 * s3 ^ 2 + s2 ^ 2) * h1 + (-c3 ^ 2 * s1 ^ 2 +
      c3 ^ 2 - s1 ^ 2 * s3 ^ 2 + s3 ^ 2) * h2 + (s1 ^ 2 * s2 ^ 2 - s2 ^ 2 + 1) * h3
  · linear_combination (c1 * c2 * s2) * h3
  · linear_combination (-c2 * s1 * s2) * h3
  · linear_combination (c1 * c2 * s2) * h3
  · linear_combination (1) * h2 + (s2 ^ 2) * h3

/-- The rotation with Eulerian angles has determinant one. -/
theorem det_eulerMatrix (h1 : c1 ^ 2 + s1 ^ 2 = 1) (h2 : c2 ^ 2 + s2 ^ 2 = 1)
    (h3 : c3 ^ 2 + s3 ^ 2 = 1) : (eulerMatrix c1 s1 c2 s2 c3 s3).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [eulerMatrix, rotZ, rotX, Matrix.mul_apply, Fin.sum_univ_three]
  · linear_combination (c2 ^ 2 * c3 ^ 2 + c2 ^ 2 * s3 ^ 2 + c3 ^ 2 * s2 ^ 2 + s2 ^ 2 * s3 ^ 2)
      * h1 + (c3 ^ 2 + s3 ^ 2) * h2 + (1) * h3

variable {w1 w2 w3 : K}

/-- The angular velocity in the body frame (Landau–Lifshitz §35):
`Rᵀ Ṙ = hat Ω` with
`Ω = (φ̇ sin θ sin ψ + θ̇ cos ψ, φ̇ sin θ cos ψ − θ̇ sin ψ, φ̇ cos θ + ψ̇)`. -/
theorem transpose_mul_eulerMatrixDeriv (h1 : c1 ^ 2 + s1 ^ 2 = 1) (h2 : c2 ^ 2 + s2 ^ 2 = 1)
    (h3 : c3 ^ 2 + s3 ^ 2 = 1) :
    (eulerMatrix c1 s1 c2 s2 c3 s3)ᵀ * eulerMatrixDeriv c1 s1 c2 s2 c3 s3 w1 w2 w3 =
      hat (bodyAngularVelocity c2 s2 c3 s3 w1 w2 w3) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eulerMatrix, eulerMatrixDeriv, rotZ, rotX, dRotZ, dRotX, hat, bodyAngularVelocity,
      Matrix.mul_apply, Fin.sum_univ_three]
  · linear_combination (c2 ^ 2 * c3 * s3 * w3 - c2 * s2 * s3 ^ 2 * w2 - c3 * s3 * w3) * h1 +
      (c3 * s3 * w3) * h2
  · linear_combination (-c2 ^ 2 * s3 ^ 2 * w3 - c2 * c3 ^ 2 * w1 - c2 * c3 * s2 * s3 * w2 - c2
      * s3 ^ 2 * w1 - c3 ^ 2 * w3) * h1 + (-s3 ^ 2 * w3) * h2 + (-c2 * w1 - w3) * h3
  · linear_combination (-c2 ^ 2 * s3 * w2 + c3 * s2 * w1) * h1 + (-s3 * w2) * h2
  · linear_combination (c2 ^ 2 * c3 ^ 2 * w3 + c2 * c3 ^ 2 * w1 - c2 * c3 * s2 * s3 * w2 + c2 *
      s3 ^ 2 * w1 + s3 ^ 2 * w3) * h1 + (c3 ^ 2 * w3) * h2 + (c2 * w1 + w3) * h3
  · linear_combination (-c2 ^ 2 * c3 * s3 * w3 - c2 * c3 ^ 2 * s2 * w2 + c3 * s3 * w3) * h1 +
      (-c3 * s3 * w3) * h2
  · linear_combination (-c2 ^ 2 * c3 * w2 - s2 * s3 * w1) * h1 + (-c3 * w2) * h2
  · linear_combination (-c2 * c3 * s2 * w3 - c3 * s2 * w1 + s2 ^ 2 * s3 * w2) * h1 + (s3 * w2)
      * h2
  · linear_combination (c2 * s2 * s3 * w3 + c3 * s2 ^ 2 * w2 + s2 * s3 * w1) * h1 + (c3 * w2) *
      h2
  · linear_combination (c2 * s2 * w2) * h1

/-- The angular velocity in the space frame: `Ṙ Rᵀ = hat ω` with
`ω = (θ̇ cos φ + ψ̇ sin θ sin φ, θ̇ sin φ − ψ̇ sin θ cos φ, φ̇ + ψ̇ cos θ)`. -/
theorem eulerMatrixDeriv_mul_transpose (h1 : c1 ^ 2 + s1 ^ 2 = 1) (h2 : c2 ^ 2 + s2 ^ 2 = 1)
    (h3 : c3 ^ 2 + s3 ^ 2 = 1) :
    eulerMatrixDeriv c1 s1 c2 s2 c3 s3 w1 w2 w3 * (eulerMatrix c1 s1 c2 s2 c3 s3)ᵀ =
      hat (spaceAngularVelocity c1 s1 c2 s2 w1 w2 w3) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eulerMatrix, eulerMatrixDeriv, rotZ, rotX, dRotZ, dRotX, hat, spaceAngularVelocity,
      Matrix.mul_apply, Fin.sum_univ_three]
  · linear_combination (c1 * c3 ^ 2 * s1 * w1 + c1 * s1 * s3 ^ 2 * w1) * h2 + (-c1 * s1 * s2 ^
      2 * w1 - c2 * s1 ^ 2 * s2 * w2) * h3
  · linear_combination (-c2 ^ 2 * c3 ^ 2 * w1 - c2 ^ 2 * s3 ^ 2 * w1 - c2 * c3 ^ 2 * w3 - c2 *
      s3 ^ 2 * w3 - s2 ^ 2 * w1) * h1 + (c3 ^ 2 * s1 ^ 2 * w1 - c3 ^ 2 * w1 + s1 ^ 2 * s3 ^ 2 *
      w1 - s3 ^ 2 * w1) * h2 + (c1 * c2 * s1 * s2 * w2 - c2 * w3 - s1 ^ 2 * s2 ^ 2 * w1 + s2 ^
      2 * w1 - w1) * h3
  · linear_combination (s1 * w2) * h2 + (-c1 * c2 * s2 * w1 - c1 * s2 * w3 + s1 * s2 ^ 2 * w2)
      * h3
  · linear_combination (c2 * c3 ^ 2 * w3 + c2 * s3 ^ 2 * w3 + c3 ^ 2 * w1 + s3 ^ 2 * w1) * h1 +
      (c3 ^ 2 * s1 ^ 2 * w1 + s1 ^ 2 * s3 ^ 2 * w1) * h2 + (c1 * c2 * s1 * s2 * w2 + c2 * w3 -
      s1 ^ 2 * s2 ^ 2 * w1 + w1) * h3
  · linear_combination (-c2 * c3 ^ 2 * s2 * w2 - c2 * s2 * s3 ^ 2 * w2 + c2 * s2 * w2) * h1 +
      (-c1 * c3 ^ 2 * s1 * w1 - c1 * s1 * s3 ^ 2 * w1) * h2 + (c1 * s1 * s2 ^ 2 * w1 + c2 * s1
      ^ 2 * s2 * w2 - c2 * s2 * w2) * h3
  · linear_combination (-c1 * w2) * h2 + (-c1 * s2 ^ 2 * w2 - c2 * s1 * s2 * w1 - s1 * s2 * w3)
      * h3
  · linear_combination (-c3 ^ 2 * s1 * w2 - s1 * s3 ^ 2 * w2) * h2 + (c1 * s2 * w3 + s1 * s2 ^
      2 * w2 - s1 * w2) * h3
  · linear_combination (c1 * c3 ^ 2 * w2 + c1 * s3 ^ 2 * w2) * h2 + (-c1 * s2 ^ 2 * w2 + c1 *
      w2 + s1 * s2 * w3) * h3
  · linear_combination (c2 * s2 * w2) * h3

/-- The two angular velocities are related by the rotation: `ω = R Ω`. -/
theorem eulerMatrix_mulVec_bodyAngularVelocity (h2 : c2 ^ 2 + s2 ^ 2 = 1)
    (h3 : c3 ^ 2 + s3 ^ 2 = 1) :
    eulerMatrix c1 s1 c2 s2 c3 s3 *ᵥ bodyAngularVelocity c2 s2 c3 s3 w1 w2 w3 =
      spaceAngularVelocity c1 s1 c2 s2 w1 w2 w3 := by
  ext i
  fin_cases i <;>
    simp [eulerMatrix, rotZ, rotX, bodyAngularVelocity, spaceAngularVelocity, Matrix.mulVec,
      dotProduct, Matrix.mul_apply, Fin.sum_univ_three]
  · linear_combination (c1 * w2 - c2 * s1 * s2 * w1) * h3
  · linear_combination (c1 * c2 * s2 * w1 + s1 * w2) * h3
  · linear_combination (w1) * h2 + (s2 ^ 2 * w1) * h3

/-- `Ω₁² + Ω₂² = φ̇² sin² θ + θ̇²`. -/
theorem bodyAngularVelocity_sq_add_sq (h3 : c3 ^ 2 + s3 ^ 2 = 1) :
    bodyAngularVelocity c2 s2 c3 s3 w1 w2 w3 0 ^ 2 +
        bodyAngularVelocity c2 s2 c3 s3 w1 w2 w3 1 ^ 2 =
      w1 ^ 2 * s2 ^ 2 + w2 ^ 2 := by
  simp only [bodyAngularVelocity, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination (s2 ^ 2 * w1 ^ 2 + w2 ^ 2) * h3

/-- Twice the kinetic energy of a symmetric top in Eulerian angles
(Landau–Lifshitz §35):
`I₁ (Ω₁² + Ω₂²) + I₃ Ω₃² = I₁ (θ̇² + φ̇² sin² θ) + I₃ (φ̇ cos θ + ψ̇)²`. -/
theorem symmetricTop_energy (I1 I3 : K) (h3 : c3 ^ 2 + s3 ^ 2 = 1) :
    I1 * (bodyAngularVelocity c2 s2 c3 s3 w1 w2 w3 0 ^ 2 +
          bodyAngularVelocity c2 s2 c3 s3 w1 w2 w3 1 ^ 2) +
        I3 * bodyAngularVelocity c2 s2 c3 s3 w1 w2 w3 2 ^ 2 =
      I1 * (w2 ^ 2 + w1 ^ 2 * s2 ^ 2) + I3 * (w1 * c2 + w3) ^ 2 := by
  rw [bodyAngularVelocity_sq_add_sq h3]
  simp only [bodyAngularVelocity, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  ring

/-- The matrix of the linear map from the rates of the angles to the angular
velocity in the body frame. -/
def eulerJacobian (c2 s2 c3 s3 : K) : Matrix (Fin 3) (Fin 3) K :=
  !![s2 * s3, c3, 0; s2 * c3, -s3, 0; c2, 0, 1]

theorem eulerJacobian_mulVec (c2 s2 c3 s3 w1 w2 w3 : K) :
    eulerJacobian c2 s2 c3 s3 *ᵥ ![w1, w2, w3] = bodyAngularVelocity c2 s2 c3 s3 w1 w2 w3 := by
  ext i
  fin_cases i <;>
    simp [eulerJacobian, bodyAngularVelocity, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
    ring

/-- The rates of the angles are determined by the angular velocity exactly
where `sin θ` is invertible: the determinant of the Jacobian is `−sin θ`. -/
theorem det_eulerJacobian (c2 : K) {s2 c3 s3 : K} (h3 : c3 ^ 2 + s3 ^ 2 = 1) :
    (eulerJacobian c2 s2 c3 s3).det = -s2 := by
  rw [Matrix.det_fin_three]
  simp [eulerJacobian]
  linear_combination (-s2) * h3

/-! ### Real angles -/

/-- The rotation with real Eulerian angles `φ`, `θ`, `ψ`. -/
noncomputable def eulerRotation (φ θ ψ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  eulerMatrix (Real.cos φ) (Real.sin φ) (Real.cos θ) (Real.sin θ) (Real.cos ψ) (Real.sin ψ)

/-- The rotation with Eulerian angles is an element of `SO(3)`. -/
theorem eulerRotation_mem_specialOrthogonalGroup (φ θ ψ : ℝ) :
    eulerRotation φ θ ψ ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
  exact ⟨eulerMatrix_mul_transpose (Real.cos_sq_add_sin_sq φ) (Real.cos_sq_add_sin_sq θ)
    (Real.cos_sq_add_sin_sq ψ), det_eulerMatrix (Real.cos_sq_add_sin_sq φ)
    (Real.cos_sq_add_sin_sq θ) (Real.cos_sq_add_sin_sq ψ)⟩

/-- The product rule for matrices, entry by entry. -/
theorem hasDerivAt_matrix_mul {A B : ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    {A' B' : Matrix (Fin 3) (Fin 3) ℝ} {t : ℝ}
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t)
    (hB : ∀ i j, HasDerivAt (fun s => B s i j) (B' i j) t) (i j : Fin 3) :
    HasDerivAt (fun s => (A s * B s) i j) ((A' * B t + A t * B') i j) t := by
  have h : HasDerivAt (fun s => ∑ k, A s i k * B s k j)
      (∑ k, (A' i k * B t k j + A t i k * B' k j)) t :=
    HasDerivAt.fun_sum fun k _ => (hA i k).mul (hB k j)
  have he : (A' * B t + A t * B') i j = ∑ k, (A' i k * B t k j + A t i k * B' k j) := by
    rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, Finset.sum_add_distrib]
  rw [he]
  exact h

theorem hasDerivAt_rotZ {φ : ℝ → ℝ} {φ' t : ℝ} (h : HasDerivAt φ φ' t) (i j : Fin 3) :
    HasDerivAt (fun s => rotZ (Real.cos (φ s)) (Real.sin (φ s)) i j)
      ((φ' • dRotZ (Real.cos (φ t)) (Real.sin (φ t))) i j) t := by
  have hc := h.cos
  have hs := h.sin
  fin_cases i <;> fin_cases j
  · simpa [rotZ, dRotZ, mul_comm] using hc
  · simpa [rotZ, dRotZ, mul_comm] using hs.fun_neg
  · simpa [rotZ, dRotZ] using hasDerivAt_const t (0 : ℝ)
  · simpa [rotZ, dRotZ, mul_comm] using hs
  · simpa [rotZ, dRotZ, mul_comm] using hc
  · simpa [rotZ, dRotZ] using hasDerivAt_const t (0 : ℝ)
  · simpa [rotZ, dRotZ] using hasDerivAt_const t (0 : ℝ)
  · simpa [rotZ, dRotZ] using hasDerivAt_const t (0 : ℝ)
  · simpa [rotZ, dRotZ] using hasDerivAt_const t (1 : ℝ)

theorem hasDerivAt_rotX {θ : ℝ → ℝ} {θ' t : ℝ} (h : HasDerivAt θ θ' t) (i j : Fin 3) :
    HasDerivAt (fun s => rotX (Real.cos (θ s)) (Real.sin (θ s)) i j)
      ((θ' • dRotX (Real.cos (θ t)) (Real.sin (θ t))) i j) t := by
  have hc := h.cos
  have hs := h.sin
  fin_cases i <;> fin_cases j
  · simpa [rotX, dRotX] using hasDerivAt_const t (1 : ℝ)
  · simpa [rotX, dRotX] using hasDerivAt_const t (0 : ℝ)
  · simpa [rotX, dRotX] using hasDerivAt_const t (0 : ℝ)
  · simpa [rotX, dRotX] using hasDerivAt_const t (0 : ℝ)
  · simpa [rotX, dRotX, mul_comm] using hc
  · simpa [rotX, dRotX, mul_comm] using hs.fun_neg
  · simpa [rotX, dRotX] using hasDerivAt_const t (0 : ℝ)
  · simpa [rotX, dRotX, mul_comm] using hs
  · simpa [rotX, dRotX, mul_comm] using hc

/-- The derivative of the rotation with time-dependent Eulerian angles is
`eulerMatrixDeriv` with the rates of the angles, entry by entry. -/
theorem hasDerivAt_eulerRotation {φ θ ψ : ℝ → ℝ} {φ' θ' ψ' t : ℝ} (hφ : HasDerivAt φ φ' t)
    (hθ : HasDerivAt θ θ' t) (hψ : HasDerivAt ψ ψ' t) (i j : Fin 3) :
    HasDerivAt (fun s => eulerRotation (φ s) (θ s) (ψ s) i j)
      (eulerMatrixDeriv (Real.cos (φ t)) (Real.sin (φ t)) (Real.cos (θ t)) (Real.sin (θ t))
        (Real.cos (ψ t)) (Real.sin (ψ t)) φ' θ' ψ' i j) t := by
  have h := hasDerivAt_matrix_mul
    (hasDerivAt_matrix_mul (hasDerivAt_rotZ hφ) (hasDerivAt_rotX hθ)) (hasDerivAt_rotZ hψ) i j
  have he : eulerMatrixDeriv (Real.cos (φ t)) (Real.sin (φ t)) (Real.cos (θ t)) (Real.sin (θ t))
      (Real.cos (ψ t)) (Real.sin (ψ t)) φ' θ' ψ' =
      (φ' • dRotZ (Real.cos (φ t)) (Real.sin (φ t)) * rotX (Real.cos (θ t)) (Real.sin (θ t)) +
          rotZ (Real.cos (φ t)) (Real.sin (φ t)) *
            θ' • dRotX (Real.cos (θ t)) (Real.sin (θ t))) *
        rotZ (Real.cos (ψ t)) (Real.sin (ψ t)) +
      rotZ (Real.cos (φ t)) (Real.sin (φ t)) * rotX (Real.cos (θ t)) (Real.sin (θ t)) *
        ψ' • dRotZ (Real.cos (ψ t)) (Real.sin (ψ t)) := by
    simp only [eulerMatrixDeriv, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul]
  rw [he]
  exact h

/-- The angular velocity of the rotation with time-dependent Eulerian angles,
in the space frame. -/
theorem angularVelocity_eulerRotation (φ θ ψ φ' θ' ψ' : ℝ) :
    angularVelocity (eulerRotation φ θ ψ)
        (eulerMatrixDeriv (Real.cos φ) (Real.sin φ) (Real.cos θ) (Real.sin θ) (Real.cos ψ)
          (Real.sin ψ) φ' θ' ψ') =
      spaceAngularVelocity (Real.cos φ) (Real.sin φ) (Real.cos θ) (Real.sin θ) φ' θ' ψ' := by
  rw [angularVelocity, eulerRotation,
    eulerMatrixDeriv_mul_transpose (Real.cos_sq_add_sin_sq φ) (Real.cos_sq_add_sin_sq θ)
      (Real.cos_sq_add_sin_sq ψ), vee_hat]

/-- The angular velocity in the body frame: the vector of `Rᵀ Ṙ`. -/
theorem vee_transpose_mul_eulerMatrixDeriv (φ θ ψ φ' θ' ψ' : ℝ) :
    vee ((eulerRotation φ θ ψ)ᵀ *
        eulerMatrixDeriv (Real.cos φ) (Real.sin φ) (Real.cos θ) (Real.sin θ) (Real.cos ψ)
          (Real.sin ψ) φ' θ' ψ') =
      bodyAngularVelocity (Real.cos θ) (Real.sin θ) (Real.cos ψ) (Real.sin ψ) φ' θ' ψ' := by
  rw [eulerRotation,
    transpose_mul_eulerMatrixDeriv (Real.cos_sq_add_sin_sq φ) (Real.cos_sq_add_sin_sq θ)
      (Real.cos_sq_add_sin_sq ψ), vee_hat]

end ProjectAInos.Mechanics.Rigid
