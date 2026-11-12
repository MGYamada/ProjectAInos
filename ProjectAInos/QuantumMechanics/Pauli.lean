/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.QuantumMechanics.Qubit

/-! # Pauli projective measurements

Probabilities are obtained by evaluating an independently defined positive
normalized functional on spectral projections. Both outcomes of all three
Pauli measurements are checked, including their probability bounds.
-/

@[expose] public section
noncomputable section

open Matrix
open scoped ComplexOrder

namespace ProjectAInos.QuantumMechanics.Qubit

def IsProjection (P : Operator) : Prop := P.IsHermitian ∧ P * P = P

theorem IsProjection.posSemidef {P : Operator} (h : IsProjection P) : P.PosSemidef := by
  simpa only [h.1.eq, h.2] using posSemidef_conjTranspose_mul_self P

theorem IsProjection.complement {P : Operator} (h : IsProjection P) : IsProjection (1 - P) := by
  refine ⟨isHermitian_one.sub h.1, ?_⟩
  simp [mul_sub, sub_mul, h.2]

def probability (s : State) (P : Operator) : ℝ := (s.functional P).re

theorem probability_nonneg (s : State) {P : Operator} (h : IsProjection P) :
    0 ≤ probability s P := (Complex.nonneg_iff.mp (s.positive P h.posSemidef)).1

theorem probability_im_zero (s : State) {P : Operator} (h : IsProjection P) :
    (s.functional P).im = 0 := (Complex.nonneg_iff.mp (s.positive P h.posSemidef)).2.symm

theorem probability_complement (s : State) (P : Operator) :
    probability s (1 - P) = 1 - probability s P := by
  simp [probability, map_sub, s.normalized]

theorem probability_le_one (s : State) {P : Operator} (h : IsProjection P) :
    probability s P ≤ 1 := by
  have hp := probability_nonneg s h.complement
  rw [probability_complement] at hp
  linarith

/-- x, y, z in that order; σ_y uses the standard upper-right entry -i. -/
def pauli : Fin 3 → Operator :=
  ![!![0, 1; 1, 0], !![0, -Complex.I; Complex.I, 0], !![1, 0; 0, -1]]

/-- `true` is eigenvalue +1 and `false` is eigenvalue -1. -/
def outcomeSign (plus : Bool) : ℂ := if plus then 1 else -1

def pauliProjection (axis : Fin 3) (plus : Bool) : Operator :=
  (2 : ℂ)⁻¹ • (1 + outcomeSign plus • pauli axis)

theorem pauli_isHermitian (axis : Fin 3) : (pauli axis).IsHermitian := by
  fin_cases axis <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauli, conjTranspose_apply]

theorem pauli_square (axis : Fin 3) : pauli axis * pauli axis = 1 := by
  fin_cases axis <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [pauli, mul_apply, Fin.sum_univ_two, Matrix.one_apply]

theorem pauliProjection_isProjection (axis : Fin 3) (plus : Bool) :
    IsProjection (pauliProjection axis plus) := by
  constructor
  · fin_cases axis <;> cases plus <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [pauliProjection, outcomeSign, pauli, conjTranspose_apply,
        Matrix.one_apply]
  · fin_cases axis <;> cases plus <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [pauliProjection, outcomeSign, pauli, mul_apply, Fin.sum_univ_two,
        Matrix.one_apply] <;> ring_nf <;> norm_num

theorem pauliProjection_complement (axis : Fin 3) :
    pauliProjection axis false = 1 - pauliProjection axis true := by
  ext i j
  simp [pauliProjection, outcomeSign]
  ring

theorem pauli_probability (s : State) (axis : Fin 3) (plus : Bool) :
    probability s (pauliProjection axis plus) =
      (1 + (if plus then 1 else -1) * (s.functional (pauli axis)).re) / 2 := by
  cases plus <;>
    simp [probability, pauliProjection, outcomeSign, map_add, map_smul, s.normalized,
      Complex.mul_re, Complex.inv_re, Complex.inv_im, Complex.normSq]
  <;> ring

theorem pauli_born (v : NonzeroKet) (axis : Fin 3) (plus : Bool) :
    probability (vectorState v) (pauliProjection axis plus) =
      (1 + (if plus then 1 else -1) * (expectation v (pauli axis)).re) / 2 := by
  rw [pauli_probability, vectorState_expectation]

theorem pauli_probabilities_sum (s : State) (axis : Fin 3) :
    probability s (pauliProjection axis true) +
      probability s (pauliProjection axis false) = 1 := by
  rw [pauliProjection_complement, probability_complement]
  ring

theorem pauli_probability_mem_Icc (s : State) (axis : Fin 3) (plus : Bool) :
    probability s (pauliProjection axis plus) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨probability_nonneg s (pauliProjection_isProjection axis plus),
    probability_le_one s (pauliProjection_isProjection axis plus)⟩

theorem pauli_xy_commutator :
    pauli 0 * pauli 1 - pauli 1 * pauli 0 = (2 * Complex.I) • pauli 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauli, mul_apply, Fin.sum_univ_two] <;> ring

theorem pauli_expectation_x (v : NonzeroKet) :
    expectation v (pauli 0) = (weight v)⁻¹ *
      (star (v.val 0) * v.val 1 + star (v.val 1) * v.val 0) := by
  simp [expectation, pairing, pauli, mulVec, dotProduct, Fin.sum_univ_two]

theorem pauli_expectation_y (v : NonzeroKet) :
    expectation v (pauli 1) = (weight v)⁻¹ *
      (-Complex.I * star (v.val 0) * v.val 1 + Complex.I * star (v.val 1) * v.val 0) := by
  simp only [expectation, pairing, pauli, mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Matrix.of_apply, Pi.star_apply]
  ring

theorem pauli_expectation_z (v : NonzeroKet) :
    expectation v (pauli 2) = (weight v)⁻¹ *
      (star (v.val 0) * v.val 0 - star (v.val 1) * v.val 1) := by
  simp [expectation, pairing, pauli, mulVec, dotProduct, Fin.sum_univ_two, sub_eq_add_neg]

/-- A regression example that detects the sign of σ_y. -/
def yPlusKet : NonzeroKet := ⟨![1, Complex.I], by
  intro h
  have := congrFun h 0
  simp at this⟩

theorem yPlus_expectation : expectation yPlusKet (pauli 1) = 1 := by
  norm_num [expectation, weight, pairing, yPlusKet, pauli, mulVec, dotProduct,
    Fin.sum_univ_two]

theorem yPlus_probabilities :
    probability (vectorState yPlusKet) (pauliProjection 1 true) = 1 ∧
    probability (vectorState yPlusKet) (pauliProjection 1 false) = 0 := by
  simp [pauli_born, yPlus_expectation]

end ProjectAInos.QuantumMechanics.Qubit
