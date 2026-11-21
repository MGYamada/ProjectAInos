/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.Bessel
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic

/-! # The bilateral generating series for integer-order Bessel functions

Multiply the exponential series in `zw/2` and `−z/(2w)`. Absolute convergence permits
grouping by the difference of the two indices. Each diagonal is exactly Mathlib's Bessel
series, also for negative order by the reflection formula.
-/

@[expose] public section
noncomputable section

open Complex FormalMultilinearSeries
namespace ProjectAinos.SpecialFunctions.Bessel

/-- The factorial series at nonnegative integral order. -/
theorem hasSum_nat (n : ℕ) (z : ℂ) :
    HasSum (fun j : ℕ => (z / 2) ^ n * (-(z / 2) ^ 2) ^ j /
      ((j.factorial : ℂ) * (n + j).factorial)) (besselJ n z) := by
  let p := regularizedHGFunSeries 0 {(n : ℂ) + 1}
  have h := (p.hasFPowerSeriesOnBall (by simp [p])).hasSum (y := -(z / 2) ^ 2) (by simp [p])
  have hs := h.mul_left ((z / 2) ^ n)
  simp only [besselJ, cpow_natCast, regularizedHGFun, zero_add, p] at hs ⊢
  apply hs.congr_fun
  intro j
  rw [apply_eq_pow_smul_coeff, regularizedHGFunSeries_coeff]
  have hg : Gamma ((n : ℂ) + 1 + j) = (n + j).factorial := by
    convert Gamma_nat_eq_factorial (n + j) using 2; push_cast; ring
  simp [regularizedHGFunCoeff, hg, div_eq_mul_inv, mul_assoc]

private def diag : ℤ × ℕ ≃ ℕ × ℕ where
  toFun p := (p.2 + p.1.toNat, p.2 + (-p.1).toNat)
  invFun p := ((p.1 : ℤ) - p.2, min p.1 p.2)
  left_inv := by rintro ⟨k,j⟩; apply Prod.ext <;> dsimp <;> omega
  right_inv := by rintro ⟨p,q⟩; apply Prod.ext <;> dsimp <;> omega

private def expTerm (a : ℂ) (n : ℕ) : ℂ := a ^ n / n.factorial

private theorem pos_diag (n : ℕ) (z w : ℂ) (hw : w ≠ 0) :
    HasSum (fun j : ℕ => expTerm (z / 2 * w) (j + n) * expTerm (-(z / 2) / w) j)
      (besselJ n z * w ^ n) := by
  apply ((hasSum_nat n z).mul_right (w ^ n)).congr_fun
  intro j
  rw [show -(z / 2) ^ 2 = z / 2 * -(z / 2) by ring]
  simp only [expTerm, pow_add, mul_pow, div_pow, Nat.add_comm j n]
  field_simp

private theorem neg_diag (n : ℕ) (z w : ℂ) (hw : w ≠ 0) :
    HasSum (fun j : ℕ => expTerm (z / 2 * w) j * expTerm (-(z / 2) / w) (j + n))
      (besselJ (-(n : ℂ)) z * w ^ (-(n : ℤ))) := by
  have he := besselJ_neg_int (n : ℤ) z
  simp only [Int.cast_natCast, zpow_natCast] at he
  rw [he, zpow_neg, zpow_natCast]
  apply (((hasSum_nat n z).mul_left ((-1 : ℂ) ^ n)).mul_right (w ^ n)⁻¹).congr_fun
  intro j
  unfold expTerm
  generalize z / 2 = t
  rw [show -t ^ 2 = t * -t by ring]
  simp only [pow_add, mul_pow, div_pow, Nat.add_comm j n]
  rw [show (-t) ^ n = (-1 : ℂ) ^ n * t ^ n by rw [← mul_pow, neg_one_mul]]
  field_simp

/-- Bessel's generating series, absolutely convergent for every complex `z` and `w ≠ 0`. -/
theorem hasSum_generating (z : ℂ) {w : ℂ} (hw : w ≠ 0) :
    HasSum (fun k : ℤ => besselJ k z * w ^ k) (exp (z / 2 * (w - w⁻¹))) := by
  have expSum (x : ℂ) : HasSum (expTerm x) (exp x) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp x
  let x := z / 2 * w
  let y := -(z / 2) / w
  have hh := (expSum x).mul (expSum y)
    (summable_mul_of_summable_norm (expSum x).summable.norm (expSum y).summable.norm)
  rw [← Complex.exp_add, show x + y = z / 2 * (w - w⁻¹) by dsimp [x,y]; ring] at hh
  apply (diag.hasSum_iff.mpr hh).prod_fiberwise
  intro k
  cases k with
  | ofNat n => simpa [diag, x, y] using pos_diag n z w hw
  | negSucc n =>
    have ht : (-1 + -(n : ℤ)).toNat = 0 := by omega
    simpa [diag, x, y, Int.negSucc_eq, ht] using neg_diag (n + 1) z w hw

end ProjectAinos.SpecialFunctions.Bessel
