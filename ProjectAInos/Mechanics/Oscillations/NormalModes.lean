/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Oscillations.Harmonic
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Oscillations of systems with more than one degree of freedom

The equations `Σₖ (mᵢₖ ẍₖ + kᵢₖ xₖ) = 0` of Landau–Lifshitz §23, for a positive
definite matrix `M = (mᵢₖ)` and a symmetric matrix `K = (kᵢₖ)`.

The two quadratic forms are diagonalized together: there is a matrix `S` with
`Sᵀ M S = 1` and `Sᵀ K S = diag λ`. Its columns are the normal modes,
`K S = M S diag λ`, and the `λₐ` are the roots of `det (K − λ M) = 0`. They are
positive when `K` is positive definite.

The normal co-ordinates `Θ = Sᵀ M x` separate the equations: `x` is a solution
exactly when `Θ̈ₐ = −λₐ Θₐ` for every `a`, and `x = S Θ`.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics.NormalModes

open Matrix SmoothAlgebra SmoothRing

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Simultaneous diagonalization -/

/-- A real symmetric matrix is diagonalized by an orthogonal matrix. -/
theorem exists_orthogonal_diagonalization {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    ∃ U : Matrix n n ℝ, Uᵀ * U = 1 ∧ Uᵀ * A * U = diagonal hA.eigenvalues := by
  refine ⟨(hA.eigenvectorUnitary : Matrix n n ℝ), ?_, ?_⟩
  · have h := Unitary.coe_star_mul_self hA.eigenvectorUnitary
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h
  · have h := hA.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply, star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial] at h
    rw [h]
    rfl

/-- A positive definite quadratic form is the unit form in suitable
co-ordinates: there is a matrix `B` with `Bᵀ M B = 1`. -/
theorem exists_transpose_mul_mul_eq_one {M : Matrix n n ℝ} (hM : M.PosDef) :
    ∃ B : Matrix n n ℝ, Bᵀ * M * B = 1 := by
  obtain ⟨U, -, hUM⟩ := exists_orthogonal_diagonalization hM.isHermitian
  have hμ := hM.eigenvalues_pos
  refine ⟨U * diagonal fun i => (Real.sqrt (hM.isHermitian.eigenvalues i))⁻¹, ?_⟩
  calc (U * diagonal fun i => (Real.sqrt (hM.isHermitian.eigenvalues i))⁻¹)ᵀ * M *
        (U * diagonal fun i => (Real.sqrt (hM.isHermitian.eigenvalues i))⁻¹)
      = (diagonal fun i => (Real.sqrt (hM.isHermitian.eigenvalues i))⁻¹) * (Uᵀ * M * U) *
          diagonal fun i => (Real.sqrt (hM.isHermitian.eigenvalues i))⁻¹ := by
        simp only [transpose_mul, diagonal_transpose, Matrix.mul_assoc]
    _ = 1 := by
        rw [hUM, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
        congr 1
        funext i
        have hs : Real.sqrt (hM.isHermitian.eigenvalues i) ≠ 0 :=
          (Real.sqrt_pos.mpr (hμ i)).ne'
        have hsq := Real.mul_self_sqrt (hμ i).le
        field_simp
        linarith

/-- Simultaneous diagonalization of a positive definite and a symmetric
quadratic form (Landau–Lifshitz (23.12)): there is a matrix `S` with
`Sᵀ M S = 1` and `Sᵀ K S` diagonal. -/
theorem exists_simultaneous_diagonalization {M K : Matrix n n ℝ} (hM : M.PosDef)
    (hK : K.IsSymm) :
    ∃ (S : Matrix n n ℝ) (lam : n → ℝ), Sᵀ * M * S = 1 ∧ Sᵀ * K * S = diagonal lam := by
  obtain ⟨B, hB⟩ := exists_transpose_mul_mul_eq_one hM
  have hKh : K.IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
    exact hK
  have hsymm : (Bᵀ * K * B).IsHermitian := by
    have h := isHermitian_conjTranspose_mul_mul B hKh
    rwa [conjTranspose_eq_transpose_of_trivial] at h
  obtain ⟨V, hV, hVK⟩ := exists_orthogonal_diagonalization hsymm
  refine ⟨B * V, hsymm.eigenvalues, ?_, ?_⟩
  · have e : (B * V)ᵀ * M * (B * V) = Vᵀ * (Bᵀ * M * B) * V := by
      simp only [transpose_mul, Matrix.mul_assoc]
    rw [e, hB, Matrix.mul_one, hV]
  · have e : (B * V)ᵀ * K * (B * V) = Vᵀ * (Bᵀ * K * B) * V := by
      simp only [transpose_mul, Matrix.mul_assoc]
    rw [e, hVK]

section Consequences

variable {M K S : Matrix n n ℝ} {lam : n → ℝ}

/-- `Sᵀ M` is the inverse of `S`. -/
theorem mul_transpose_mul_eq_one (hSM : Sᵀ * M * S = 1) : S * (Sᵀ * M) = 1 :=
  mul_eq_one_comm.mp hSM

/-- `M S` is the inverse of `Sᵀ`. -/
theorem mul_mul_transpose_eq_one (hSM : Sᵀ * M * S = 1) : M * S * Sᵀ = 1 := by
  rw [Matrix.mul_assoc] at hSM
  exact mul_eq_one_comm.mp hSM

/-- `Sᵀ K = diag λ · Sᵀ M`. -/
theorem transpose_mul_eq_diagonal_mul (hSM : Sᵀ * M * S = 1) (hSK : Sᵀ * K * S = diagonal lam) :
    Sᵀ * K = diagonal lam * (Sᵀ * M) := by
  rw [← hSK, Matrix.mul_assoc (Sᵀ * K), mul_transpose_mul_eq_one hSM, Matrix.mul_one]

/-- The columns of `S` are the normal modes: `K S = M S diag λ`
(Landau–Lifshitz (23.7)). -/
theorem mul_eq_mul_mul_diagonal (hSM : Sᵀ * M * S = 1) (hSK : Sᵀ * K * S = diagonal lam) :
    K * S = M * S * diagonal lam := by
  rw [← hSK, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_mul_transpose_eq_one hSM,
    Matrix.one_mul]

/-- The matrix `S` is invertible. -/
theorem det_ne_zero (hSM : Sᵀ * M * S = 1) : S.det ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det hSM
  rw [det_mul, det_mul, h, mul_zero, det_one] at h1
  exact zero_ne_one h1

/-- The characteristic equation (Landau–Lifshitz (23.8)): the roots of
`det (K − c M) = 0` are the `λₐ`. -/
theorem det_sub_smul_eq_zero_iff (hSM : Sᵀ * M * S = 1) (hSK : Sᵀ * K * S = diagonal lam)
    (c : ℝ) : (K - c • M).det = 0 ↔ ∃ a, c = lam a := by
  have hS : S.det ≠ 0 := det_ne_zero hSM
  have hdet : Sᵀ.det * (K - c • M).det * S.det = ∏ a, (lam a - c) := by
    rw [← det_mul, ← det_mul, Matrix.mul_sub, Matrix.sub_mul, hSK, Matrix.mul_smul,
      Matrix.smul_mul, hSM, ← diagonal_one, ← diagonal_smul, diagonal_sub, det_diagonal]
    simp
  rw [det_transpose] at hdet
  constructor
  · intro h
    rw [h, mul_zero, zero_mul] at hdet
    obtain ⟨a, -, ha⟩ := Finset.prod_eq_zero_iff.mp hdet.symm
    exact ⟨a, (sub_eq_zero.mp ha).symm⟩
  · rintro ⟨a, rfl⟩
    have h0 : ∏ b, (lam b - lam a) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ a) (sub_self _)
    rw [h0] at hdet
    rcases mul_eq_zero.mp hdet with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hS
      · exact h'
    · exact absurd h hS

/-- If the potential energy is positive definite, the `λₐ` are positive, so
the frequencies `√λₐ` are real. -/
theorem lam_pos (hSM : Sᵀ * M * S = 1) (hSK : Sᵀ * K * S = diagonal lam) (hK : K.PosDef)
    (a : n) : 0 < lam a := by
  have hinj : Function.Injective S.mulVec :=
    Matrix.mulVec_injective_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det S).mpr (isUnit_iff_ne_zero.mpr (det_ne_zero hSM)))
  have h := hK.conjTranspose_mul_mul_same hinj
  rw [conjTranspose_eq_transpose_of_trivial, hSK] at h
  exact posDef_diagonal_iff.mp h a

end Consequences

/-! ### The equations of motion -/

/-- `x` is a small oscillation of the system with the matrices `M` and `K`:
`Σₖ (mᵢₖ ẍₖ + kᵢₖ xₖ) = 0` for every `i` (Landau–Lifshitz (23.5)). -/
def IsSmallOscillation (M K : Matrix n n ℝ) (x : n → TimeFunction) : Prop :=
  M.map (algebraMap ℝ TimeFunction) *ᵥ (fun k => timeDerivative (timeDerivative (x k))) +
    K.map (algebraMap ℝ TimeFunction) *ᵥ x = 0

/-- The normal co-ordinates `Θ = Sᵀ M x`. -/
def normalCoordinates (S M : Matrix n n ℝ) (x : n → TimeFunction) : n → TimeFunction :=
  (Sᵀ * M).map (algebraMap ℝ TimeFunction) *ᵥ x

omit [Fintype n] [DecidableEq n] in
/-- A finite sum of functions of time is evaluated termwise. -/
theorem _root_.ProjectAInos.Mechanics.TimeFunction.sum_apply (s : Finset n)
    (f : n → TimeFunction) (x : Fin 1 → ℝ) : (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x :=
  (SmoothOperation.eval x).map_sum s f

omit [DecidableEq n] in
/-- A matrix of constants commutes with the time derivative. -/
theorem timeDerivative_map_mulVec (A : Matrix n n ℝ) (x : n → TimeFunction) (i : n) :
    timeDerivative ((A.map (algebraMap ℝ TimeFunction) *ᵥ x) i) =
      (A.map (algebraMap ℝ TimeFunction) *ᵥ fun k => timeDerivative (x k)) i := by
  simp only [mulVec, dotProduct, map_apply, map_sum, SmoothDerivation.map_algebraMap_mul,
    smul_eq_mul]

section Dynamics

variable {M K S : Matrix n n ℝ} {lam : n → ℝ}

/-- The positions are recovered from the normal co-ordinates: `x = S Θ`. -/
theorem map_mulVec_normalCoordinates (hSM : Sᵀ * M * S = 1) (x : n → TimeFunction) :
    S.map (algebraMap ℝ TimeFunction) *ᵥ normalCoordinates S M x = x := by
  rw [normalCoordinates, mulVec_mulVec, ← Matrix.map_mul, mul_transpose_mul_eq_one hSM,
    Matrix.map_one _ (map_zero _) (map_one _), one_mulVec]

/-- The normal co-ordinates of `S Θ` are `Θ`. -/
theorem normalCoordinates_map_mulVec (hSM : Sᵀ * M * S = 1) (Θ : n → TimeFunction) :
    normalCoordinates S M (S.map (algebraMap ℝ TimeFunction) *ᵥ Θ) = Θ := by
  rw [normalCoordinates, mulVec_mulVec, ← Matrix.map_mul, hSM,
    Matrix.map_one _ (map_zero _) (map_one _), one_mulVec]

/-- The equations in normal co-ordinates: `Sᵀ (M ẍ + K x)` has the components
`Θ̈ₐ + λₐ Θₐ`. -/
theorem transpose_map_mulVec_eq (hSM : Sᵀ * M * S = 1) (hSK : Sᵀ * K * S = diagonal lam)
    (x : n → TimeFunction) (a : n) :
    (Sᵀ.map (algebraMap ℝ TimeFunction) *ᵥ
        (M.map (algebraMap ℝ TimeFunction) *ᵥ
            (fun k => timeDerivative (timeDerivative (x k))) +
          K.map (algebraMap ℝ TimeFunction) *ᵥ x)) a =
      timeDerivative (timeDerivative (normalCoordinates S M x a)) +
        algebraMap ℝ TimeFunction (lam a) * normalCoordinates S M x a := by
  have h1 : timeDerivative (timeDerivative (normalCoordinates S M x a)) =
      ((Sᵀ * M).map (algebraMap ℝ TimeFunction) *ᵥ
        fun k => timeDerivative (timeDerivative (x k))) a := by
    rw [normalCoordinates, timeDerivative_map_mulVec, timeDerivative_map_mulVec]
  have h2 : algebraMap ℝ TimeFunction (lam a) * normalCoordinates S M x a =
      ((Sᵀ * K).map (algebraMap ℝ TimeFunction) *ᵥ x) a := by
    rw [transpose_mul_eq_diagonal_mul hSM hSK, Matrix.map_mul, ← mulVec_mulVec,
      diagonal_map (map_zero _), mulVec_diagonal]
    rfl
  rw [h1, h2, mulVec_add, mulVec_mulVec, mulVec_mulVec, ← Matrix.map_mul, ← Matrix.map_mul]
  rfl

/-- The normal co-ordinates separate the equations (Landau–Lifshitz (23.12)):
`x` is a small oscillation exactly when `Θ̈ₐ = −λₐ Θₐ` for every `a`. -/
theorem isSmallOscillation_iff (hSM : Sᵀ * M * S = 1) (hSK : Sᵀ * K * S = diagonal lam)
    (x : n → TimeFunction) :
    IsSmallOscillation M K x ↔
      ∀ a, timeDerivative (timeDerivative (normalCoordinates S M x a)) =
        -(algebraMap ℝ TimeFunction (lam a) * normalCoordinates S M x a) := by
  constructor
  · intro h a
    have ha := transpose_map_mulVec_eq hSM hSK x a
    unfold IsSmallOscillation at h
    rw [h, mulVec_zero] at ha
    exact eq_neg_of_add_eq_zero_left ha.symm
  · intro h
    have h0 : Sᵀ.map (algebraMap ℝ TimeFunction) *ᵥ
        (M.map (algebraMap ℝ TimeFunction) *ᵥ
            (fun k => timeDerivative (timeDerivative (x k))) +
          K.map (algebraMap ℝ TimeFunction) *ᵥ x) = 0 := by
      funext a
      rw [transpose_map_mulVec_eq hSM hSK x a, h a]
      exact neg_add_cancel _
    have h1 := congrArg (fun w => (M * S).map (algebraMap ℝ TimeFunction) *ᵥ w) h0
    simp only [mulVec_mulVec, ← Matrix.map_mul, mul_mul_transpose_eq_one hSM,
      Matrix.map_one _ (map_zero _) (map_one _), one_mulVec, mulVec_zero] at h1
    exact h1

/-- In a small oscillation every normal co-ordinate is a free oscillation of
frequency `ωₐ`, `ωₐ² = λₐ`. -/
theorem IsSmallOscillation.isHarmonic_normalCoordinates (hSM : Sᵀ * M * S = 1)
    (hSK : Sᵀ * K * S = diagonal lam) {ω : n → ℝ} (hω : ∀ a, ω a ^ 2 = lam a)
    {x : n → TimeFunction} (h : IsSmallOscillation M K x) (a : n) :
    IsHarmonic (ω a) (normalCoordinates S M x a) := by
  unfold IsHarmonic
  rw [hω a]
  exact (isSmallOscillation_iff hSM hSK x).mp h a

/-- A superposition of normal modes is a small oscillation
(Landau–Lifshitz (23.9)): if every `Θₐ` is a free oscillation of frequency
`ωₐ`, then `x = S Θ` is a small oscillation. -/
theorem isSmallOscillation_map_mulVec (hSM : Sᵀ * M * S = 1)
    (hSK : Sᵀ * K * S = diagonal lam) {ω : n → ℝ} (hω : ∀ a, ω a ^ 2 = lam a)
    {Θ : n → TimeFunction} (hΘ : ∀ a, IsHarmonic (ω a) (Θ a)) :
    IsSmallOscillation M K (S.map (algebraMap ℝ TimeFunction) *ᵥ Θ) := by
  rw [isSmallOscillation_iff hSM hSK, normalCoordinates_map_mulVec hSM]
  intro a
  have h := hΘ a
  unfold IsHarmonic at h
  rwa [hω a] at h

/-- The general small oscillation (Landau–Lifshitz (23.9), (23.10)): with
`ωₐ² = λₐ` and `ωₐ ≠ 0`, each co-ordinate is a superposition of the normal
oscillations `Θₐ(0) cos ωₐt + (Θ̇ₐ(0)/ωₐ) sin ωₐt` with the coefficients `Sₖₐ`. -/
theorem IsSmallOscillation.apply_eq (hSM : Sᵀ * M * S = 1) (hSK : Sᵀ * K * S = diagonal lam)
    {ω : n → ℝ} (hω : ∀ a, ω a ^ 2 = lam a) (hω0 : ∀ a, ω a ≠ 0) {x : n → TimeFunction}
    (h : IsSmallOscillation M K x) (k : n) (t : ℝ) :
    x k (fun _ => t) =
      ∑ a, S k a * (normalCoordinates S M x a (fun _ => 0) * Real.cos (ω a * t) +
        timeDerivative (normalCoordinates S M x a) (fun _ => 0) / ω a *
          Real.sin (ω a * t)) := by
  have hx := congrFun (map_mulVec_normalCoordinates hSM x) k
  have hsum : x k (fun _ => t) =
      ∑ a, S k a * normalCoordinates S M x a (fun _ => t) := by
    conv_lhs => rw [← hx]
    simp only [mulVec, dotProduct, map_apply, TimeFunction.sum_apply, TimeFunction.mul_apply,
      TimeFunction.algebraMap_apply]
  rw [hsum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [(h.isHarmonic_normalCoordinates hSM hSK hω a).apply_eq (hω0 a) t]

end Dynamics

end ProjectAInos.Mechanics.NormalModes
