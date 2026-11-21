/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.LegendreGenerating
public import ProjectAinos.SpecialFunctions.LegendreOrthogonality
import Mathlib.Tactic

/-! # Legendre expansions of monomials

Multiplication by the coordinate sends each normalized Legendre polynomial to a convex
combination of its two neighbors. Iteration expands every monomial with nonnegative
coefficients summing to one. This controls the double series for the plane-wave expansion.
-/

@[expose] public section
noncomputable section

open Polynomial
namespace ProjectAinos.SpecialFunctions.Legendre

/-- Legendre coefficients of `X Pₙ` from Bonnet’s three-term recurrence. -/
def mulXWeights (n : ℕ) : ℕ →₀ ℝ :=
  Finsupp.single (n + 1) ((n + 1 : ℝ) / (2 * n + 1)) +
    Finsupp.single (n - 1) (n / (2 * n + 1 : ℝ))

/-- Coefficients of the monomial of degree `k` in the normalized Legendre basis. -/
def monomialWeights : ℕ → ℕ →₀ ℝ
  | 0 => Finsupp.single 0 1
  | k + 1 => (monomialWeights k).sum fun n c =>
      c • mulXWeights n

private theorem neighbors_nonneg (n i : ℕ) : 0 ≤ mulXWeights n i := by
  simp only [mulXWeights, Finsupp.add_apply, Finsupp.single_apply]
  split_ifs <;> positivity

theorem monomialWeights_nonneg (k i : ℕ) : 0 ≤ monomialWeights k i := by
  induction k generalizing i with
  | zero => simp [monomialWeights, Finsupp.single_apply]; split <;> norm_num
  | succ k ih =>
    change 0 ≤ ((monomialWeights k).sum fun n c => c • mulXWeights n) i
    rw [Finsupp.sum, Finsupp.finsetSum_apply]
    exact Finset.sum_nonneg fun n _ => mul_nonneg (ih n) (neighbors_nonneg n i)

private abbrev value (x : ℝ) := Finsupp.linearCombination ℝ (fun n => (polynomial n).eval x)

private theorem value_neighbors (n : ℕ) (x : ℝ) :
    value x (mulXWeights n) = x * (polynomial n).eval x := by
  cases n with
  | zero => simp [mulXWeights, value]
  | succ n =>
    have h := congrArg (Polynomial.eval x) (recurrence n)
    simp only [eval_mul, eval_sub, eval_add, eval_natCast, eval_ofNat, eval_X, eval_one] at h
    simp [value, mulXWeights, Nat.cast_succ, smul_eq_mul]
    field_simp
    linear_combination h

private theorem value_weights (k : ℕ) (x : ℝ) : value x (monomialWeights k) = x ^ k := by
  induction k with
  | zero => simp [monomialWeights, value]
  | succ k ih =>
    change value x ((monomialWeights k).sum fun n c => c • mulXWeights n) = _
    rw [Finsupp.sum, map_sum]
    simp only [map_smul, value_neighbors, smul_eq_mul]
    rw [pow_succ, ← ih, Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => by simp [smul_eq_mul]; ring

/-- The Legendre expansion of `x^k` is finite. -/
theorem hasSum_monomial (k : ℕ) (x : ℝ) :
    HasSum (fun n => monomialWeights k n * (polynomial n).eval x) (x ^ k) := by
  rw [← value_weights, Finsupp.linearCombination_apply, Finsupp.sum]
  exact hasSum_sum_of_ne_finset_zero fun i hi => by simp [Finsupp.notMem_support_iff.mp hi]

theorem hasSum_monomialWeights (k : ℕ) : HasSum (monomialWeights k) 1 := by
  simpa using hasSum_monomial k 1

/-- Projection of a monomial onto the degree-`n` Legendre polynomial. -/
theorem integral_pow_mul (k n : ℕ) :
    ∫ x in (-1 : ℝ)..1, x ^ k * (polynomial n).eval x =
      monomialWeights k n * (2 / (2 * (n : ℝ) + 1)) := by
  let w := monomialWeights k
  have he x : x ^ k = ∑ j ∈ w.support, w j * (polynomial j).eval x :=
    (value_weights k x).symm
  simp_rw [he, Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum fun _ _ =>
    Continuous.intervalIntegrable (by fun_prop) ..]
  simp_rw [mul_assoc, intervalIntegral.integral_const_mul, integral_mul]
  by_cases hz : monomialWeights k n = 0 <;> simp [w, mul_ite, hz]

end ProjectAinos.SpecialFunctions.Legendre
