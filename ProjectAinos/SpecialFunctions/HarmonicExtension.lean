/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.HarmonicPolynomial
import Mathlib.Tactic

/-! # Polynomial harmonic extension from the coordinate plane

For homogeneous planar data `p`, multiply by the desired normal power and cancel the planar
Laplacian by corrections of successively higher normal order. The recursion terminates because
each planar Laplacian lowers degree by two. Normal powers zero and one give the two independent
Cauchy data of a harmonic polynomial.
-/

@[expose] public section
noncomputable section

open MvPolynomial
namespace ProjectAinos.SpecialFunctions.HarmonicPolynomial

private abbrev P (d : ℕ) := MvPolynomial (Fin d) ℝ

/-- Finite harmonic extension recursion. The parameters are the planar degree and the initial
power of the normal coordinate `X 0`. The planar variables become `X 1` and `X 2`. -/
def extension : ℕ → ℕ → MvPolynomial (Fin 2) ℝ → MvPolynomial (Fin 3) ℝ
  | 0, b, p | 1, b, p => X 0 ^ b * rename Fin.succ p
  | n + 2, b, p => X 0 ^ b * rename Fin.succ p -
      (((b + 2 : ℝ) * (b + 1))⁻¹) • extension n (b + 2) (laplacian 2 p)

private theorem lap_hom {n : ℕ} {p : P 2} (hp : p.IsHomogeneous (n + 2)) :
    (laplacian 2 p).IsHomogeneous n := by
  change (∑ i, pderiv i (pderiv i p)).IsHomogeneous n
  exact IsHomogeneous.sum _ _ _ (fun _ _ => hp.pderiv.pderiv)

/-- The extension has the sum of the planar and normal degrees. -/
theorem homogeneous_extension (n b : ℕ) {p : MvPolynomial (Fin 2) ℝ} (hp : p.IsHomogeneous n) :
    (extension n b p).IsHomogeneous (b + n) := by
  have term {m e : ℕ} {q : P 2} (hq : q.IsHomogeneous m) :
      ((X 0 : P 3) ^ e * rename Fin.succ q).IsHomogeneous (e + m) :=
    (isHomogeneous_X_pow _ _).mul hq.rename_isHomogeneous
  induction n using Nat.twoStepInduction generalizing b p with
  | zero => exact term hp
  | one => exact term hp
  | more n ih _ =>
    rw [extension, smul_eq_C_mul]
    apply (term hp).sub
    apply IsHomogeneous.C_mul
    convert ih (b + 2) (lap_hom hp) using 1
    omega

private theorem normal_rename (p : P 2) : pderiv 0 (rename Fin.succ p) = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  intro h
  obtain ⟨i, _, hi⟩ := mem_vars_rename Fin.succ p h
  exact Fin.succ_ne_zero i hi

private theorem diff_zpow (b : ℕ) :
    pderiv 0 (X (0 : Fin 3) ^ b : P 3) = (b : P 3) * X 0 ^ (b - 1) := by
  rw [pderiv_pow, pderiv_X_self, mul_one]

private theorem diff_zpow_twice (b : ℕ) :
    pderiv 0 (pderiv 0 (X (0 : Fin 3) ^ b : P 3)) =
      C ((b : ℝ) * (b - 1 : ℕ)) * X 0 ^ (b - 2) := by
  rw [diff_zpow, ← map_natCast (C (σ := Fin 3) (R := ℝ)), pderiv_C_mul, diff_zpow]
  simp only [map_mul, map_natCast, Nat.sub_sub]
  ring

private theorem lap_zpow (b : ℕ) (p : P 2) :
    laplacian 3 (X 0 ^ b * rename Fin.succ p) =
      ((b : ℝ) * (b - 1 : ℕ)) • (X 0 ^ (b - 2) * rename Fin.succ p) +
        X 0 ^ b * rename Fin.succ (laplacian 2 p) := by
  have hz (q : P 2) (j : ℕ) : pderiv (0 : Fin 3) (X 0 ^ j * rename Fin.succ q) =
      pderiv 0 (X 0 ^ j) * rename Fin.succ q := by
    rw [pderiv_mul, normal_rename, mul_zero, add_zero]
  have ht (i : Fin 2) (q : P 2) :
      pderiv i.succ (X 0 ^ b * rename Fin.succ q) = X 0 ^ b * rename Fin.succ (pderiv i q) := by
    rw [pderiv_mul, pderiv_rename (Fin.succ_injective 2)]
    simp [Fin.succ_ne_zero]
  change ∑ i : Fin 3, pderiv i (pderiv i _) = _ + X 0 ^ b * rename Fin.succ
    (∑ i : Fin 2, pderiv i (pderiv i p))
  rw [Fin.sum_univ_succ, hz, pderiv_mul, normal_rename, diff_zpow_twice]
  simp only [ht, map_sum, Finset.mul_sum, smul_eq_C_mul, mul_zero, add_zero, mul_assoc]

private theorem lap_extension (n b : ℕ) {p : P 2} (hp : p.IsHomogeneous n) :
    laplacian 3 (extension n b p) =
      ((b : ℝ) * (b - 1 : ℕ)) • (X 0 ^ (b - 2) * rename Fin.succ p) := by
  induction n using Nat.twoStepInduction generalizing b p with
  | zero => rw [extension, lap_zpow, laplacian_eq_zero_of_degree_le_one hp (by decide), map_zero,
      mul_zero, add_zero]
  | one => rw [extension, lap_zpow, laplacian_eq_zero_of_degree_le_one hp (by decide), map_zero,
      mul_zero, add_zero]
  | more n ih _ =>
    rw [extension, map_sub, map_smul, lap_zpow, ih (b + 2) (lap_hom hp), smul_smul]
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_ofNat]
    have hh : (b + 2 - 1 : ℕ) = b + 1 := by omega
    simp [hh, show (b : ℝ) + 1 ≠ 0 by positivity, show (b : ℝ) + 2 ≠ 0 by positivity,
      mul_comm, mul_left_comm]

/-- Either planar Cauchy datum extends to a harmonic polynomial. -/
theorem harmonic_extension (n : ℕ) {b : ℕ} (hb : b ≤ 1) {p : MvPolynomial (Fin 2) ℝ}
    (hp : p.IsHomogeneous n) :
    laplacian 3 (extension n b p) = 0 := by
  interval_cases b <;> simp [lap_extension n _ hp]

/-- The coefficient of the normal variable raised to power `j`, as a planar polynomial. -/
def normalCoeff (j : ℕ) : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] MvPolynomial (Fin 2) ℝ :=
  ((Polynomial.lcoeff (MvPolynomial (Fin 2) ℝ) j).restrictScalars ℝ).comp
    (finSuccEquiv ℝ 2).toLinearMap

private theorem split_rename (p : P 2) :
    finSuccEquiv ℝ 2 (rename Fin.succ p) = Polynomial.C p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [finSuccEquiv_apply]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp, finSuccEquiv_X_succ]

private theorem normalCoeff_term (j b : ℕ) (p : P 2) :
    normalCoeff j (X 0 ^ b * rename Fin.succ p) = if b = j then p else 0 := by
  change (finSuccEquiv ℝ 2 _).coeff j = _
  rw [map_mul, map_pow, finSuccEquiv_X_zero, split_rename, mul_comm, Polynomial.coeff_C_mul_X_pow]
  by_cases h : j = b <;> simp_all [eq_comm]

/-- Higher corrections start at order `b+2`. In particular the zeroth and first coefficients
recover both pieces of Cauchy data. -/
theorem normalCoeff_extension (n b j : ℕ) (p : MvPolynomial (Fin 2) ℝ) (hj : j < b + 2) :
    normalCoeff j (extension n b p) = if b = j then p else 0 := by
  induction n using Nat.twoStepInduction generalizing b p with
  | zero => exact normalCoeff_term j b p
  | one => exact normalCoeff_term j b p
  | more n ih _ =>
    rw [extension, map_sub, map_smul, normalCoeff_term, ih (b + 2) _ (by omega)]
    simp [hj.ne']

end ProjectAinos.SpecialFunctions.HarmonicPolynomial
