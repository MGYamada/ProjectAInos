/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Oscillations.NormalModes
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Symmetry of the normal modes and the number of vibrations

Landau–Lifshitz §24. A symmetry of a system of small oscillations is a matrix
`P` that commutes with the matrices `M` and `K`. It takes solutions to
solutions, and it preserves the space of the modes of each frequency, so that
space carries a representation of the group of symmetries.

The number of non-zero frequencies is the rank of `K`: the modes with zero
frequency are the vectors annihilated by `K`, such as the translations and
the rotations of a molecule.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics.NormalModes

open SmoothAlgebra Matrix

variable {n : Type*} [Fintype n]

/-- The space of the modes with `K v = c M v`. -/
def modeSpace (M K : Matrix n n ℝ) (c : ℝ) : Submodule ℝ (n → ℝ) where
  carrier := {v | K *ᵥ v = c • (M *ᵥ v)}
  add_mem' {v w} hv hw := by
    change K *ᵥ (v + w) = c • (M *ᵥ (v + w))
    rw [Matrix.mulVec_add, Matrix.mulVec_add, smul_add, hv, hw]
  zero_mem' := by
    change K *ᵥ (0 : n → ℝ) = c • (M *ᵥ (0 : n → ℝ))
    rw [Matrix.mulVec_zero, Matrix.mulVec_zero, smul_zero]
  smul_mem' r v hv := by
    change K *ᵥ (r • v) = c • (M *ᵥ (r • v))
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, hv, smul_comm]

theorem mem_modeSpace {M K : Matrix n n ℝ} {c : ℝ} {v : n → ℝ} :
    v ∈ modeSpace M K c ↔ K *ᵥ v = c • (M *ᵥ v) :=
  Iff.rfl

/-- A symmetry preserves the space of the modes of each frequency. -/
theorem mulVec_mem_modeSpace {M K P : Matrix n n ℝ} (hM : P * M = M * P) (hK : P * K = K * P)
    {c : ℝ} {v : n → ℝ} (hv : v ∈ modeSpace M K c) : P *ᵥ v ∈ modeSpace M K c := by
  rw [mem_modeSpace] at hv ⊢
  rw [Matrix.mulVec_mulVec, ← hK, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec, hM, ← Matrix.mulVec_mulVec]

/-- A symmetry takes small oscillations to small oscillations. -/
theorem isSmallOscillation_symmetry {M K P : Matrix n n ℝ} (hM : P * M = M * P)
    (hK : P * K = K * P) {x : n → TimeFunction} (h : IsSmallOscillation M K x) :
    IsSmallOscillation M K (P.map (algebraMap ℝ TimeFunction) *ᵥ x) := by
  have hD : (fun k => timeDerivative (timeDerivative
      ((P.map (algebraMap ℝ TimeFunction) *ᵥ x) k))) =
      P.map (algebraMap ℝ TimeFunction) *ᵥ
        fun k => timeDerivative (timeDerivative (x k)) := by
    funext k
    rw [timeDerivative_map_mulVec, timeDerivative_map_mulVec]
  unfold IsSmallOscillation at h ⊢
  rw [hD, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.map_mul, ← Matrix.map_mul,
    ← hM, ← hK, Matrix.map_mul, Matrix.map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_add, h, Matrix.mulVec_zero]

variable [DecidableEq n]

/-- The number of non-zero frequencies is the rank of `K`. -/
theorem card_ne_zero_eq_rank {M K S : Matrix n n ℝ} {lam : n → ℝ} (hSM : Sᵀ * M * S = 1)
    (hSK : Sᵀ * K * S = diagonal lam) : Fintype.card {a // lam a ≠ 0} = K.rank := by
  have hS : IsUnit S.det := isUnit_iff_ne_zero.mpr (det_ne_zero hSM)
  have hSt : IsUnit Sᵀ.det := by rwa [Matrix.det_transpose]
  rw [← Matrix.rank_diagonal, ← hSK, Matrix.rank_mul_eq_left_of_isUnit_det S _ hS,
    Matrix.rank_mul_eq_right_of_isUnit_det Sᵀ _ hSt]

end ProjectAInos.Mechanics.NormalModes
