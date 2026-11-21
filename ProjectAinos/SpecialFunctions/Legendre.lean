/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Polynomial.ShiftedLegendre
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! # Legendre polynomials on the symmetric interval

Mathlib's shifted polynomial of degree one is `1 - 2X`. The substitution
`(1 - X)/2` gives the normalization `Pₙ(1) = 1`.
-/

@[expose] public section
noncomputable section

open Polynomial
namespace ProjectAinos.SpecialFunctions.Legendre

private abbrev shift : ℝ[X] := C (1 / 2 : ℝ) * (1 - X)

/-- The degree-`n` Legendre polynomial normalized at the right endpoint. -/
def polynomial (n : ℕ) : ℝ[X] :=
  ((shiftedLegendre n).map (Int.castRingHom ℝ)).comp (C (1 / 2 : ℝ) * (1 - X))

@[simp] theorem polynomial_zero : polynomial 0 = 1 := by
  simp [polynomial, shiftedLegendre]

@[simp] theorem polynomial_eval_one (n : ℕ) : (polynomial n).eval 1 = 1 := by
  simp [polynomial, eval_comp, ← coeff_zero_eq_eval_zero, coeff_shiftedLegendre]

theorem natDegree_polynomial (n : ℕ) : (polynomial n).natDegree = n := by
  rw [polynomial, natDegree_comp, natDegree_map_eq_of_injective (Int.cast_injective),
    natDegree_shiftedLegendre, natDegree_C_mul (by norm_num),
    natDegree_sub_eq_right_of_natDegree_lt (by simp), natDegree_X, mul_one]

theorem polynomial_eval_neg (n : ℕ) (x : ℝ) :
    (polynomial n).eval (-x) = (-1) ^ n * (polynomial n).eval x := by
  have h := shiftedLegendre_eval_symm n ((1 + x) / 2)
  simp only [aeval_def, eval₂_eq_eval_map] at h
  simp only [polynomial, eval_comp, eval_mul, eval_sub, eval_one, eval_X, eval_C]
  rwa [show (1 + x) / 2 = 1 / 2 * (1 - -x) by ring,
    show 1 - 1 / 2 * (1 - -x) = 1 / 2 * (1 - x) by ring] at h

private theorem shift_derivative (p : ℝ[X]) (n : ℕ) :
    (derivative^[n] p).comp shift = C ((-2 : ℝ) ^ n) * derivative^[n] (p.comp shift) := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih, Function.iterate_succ_apply]
    have h : p.derivative.comp shift = C (-2 : ℝ) * (p.comp shift).derivative := by
      have hs : derivative shift = C (-1 / 2 : ℝ) := by simp [shift, neg_div]
      rw [derivative_comp, hs, ← mul_assoc, ← C_mul]
      norm_num
    rw [h, iterate_derivative_C_mul, ← mul_assoc, ← C_mul, pow_succ]

/-- Rodrigues' identity, with denominators cleared. -/
theorem rodrigues (n : ℕ) :
    C (2 ^ n * (n.factorial : ℝ)) * polynomial n = derivative^[n] ((X ^ 2 - 1 : ℝ[X]) ^ n) := by
  have h := congrArg (fun p : ℤ[X] => (p.map (Int.castRingHom ℝ)).comp shift)
    (factorial_mul_shiftedLegendre_eq n)
  simp only [Polynomial.map_mul, Polynomial.map_natCast, mul_comp, natCast_comp,
    ← iterate_derivative_map, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_one,
    map_X, shift_derivative] at h
  have hs : ((X ^ n * (1 - X) ^ n : ℝ[X]).comp shift) =
      C ((-1 / 4 : ℝ) ^ n) * (X ^ 2 - 1) ^ n := by
    rw [← mul_pow, pow_comp, mul_comp, sub_comp, one_comp, X_comp, C_pow, ← mul_pow]
    congr 1
    apply Polynomial.funext
    intro x
    simp [shift]
    ring
  rw [← mul_comp, hs, iterate_derivative_C_mul, ← mul_assoc, ← C_mul, ← mul_pow] at h
  have h' := congrArg (fun p : ℝ[X] => C ((2 : ℝ) ^ n) * p) h
  simp only [← mul_assoc, ← C_mul, ← mul_pow] at h'
  norm_num at h'
  simpa [polynomial, shift, map_mul, C_eq_natCast, mul_assoc] using h'

private abbrev q : ℝ[X] := X ^ 2 - 1

private theorem derivative_q : derivative q = 2 * X := by simp [q, derivative_pow, map_ofNat]

private theorem scaled (n : ℕ) :
    (2 ^ n * (n.factorial : ℝ[X])) * polynomial n = derivative^[n] (q ^ n) := by
  simpa [q, map_mul, C_eq_natCast, map_ofNat] using rodrigues n

/-- Differentiating Rodrigues' formula gives a ladder identity at consecutive degrees. -/
theorem derivative_succ (n : ℕ) :
    derivative (polynomial (n + 1)) =
      X * derivative (polynomial n) + (n + 1 : ℝ[X]) * polynomial n := by
  let a : ℝ[X] := 2 ^ n * n.factorial
  have ha : a ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast n.factorial_ne_zero)
  have hdn : derivative^[n + 1] (q ^ n) = a * derivative (polynomial n) := by
    rw [Function.iterate_succ_apply', ← scaled]
    simp [derivative_mul, a]
  have he : derivative (q ^ (n + 1)) = (2 * (n + 1 : ℝ[X])) * (q ^ n * X) := by
    rw [derivative_pow, derivative_q]
    simp [Nat.cast_succ]
    ring
  have h := congrArg derivative (scaled (n + 1))
  have hd (p : ℝ[X]) : derivative (derivative^[n + 1] p) =
      derivative^[n + 1] (derivative p) :=
    ((Function.Commute.refl derivative).iterate_right (n + 1)) p
  rw [hd, he] at h
  have hC : (2 * (n + 1 : ℝ[X])) = C (2 * ((n : ℝ) + 1)) := by simp [map_ofNat]
  rw [hC, iterate_derivative_C_mul, ← hC, iterate_derivative_mul_X, hdn,
    Nat.add_one_sub_one, ← scaled] at h
  simp only [derivative_mul, derivative_natCast, derivative_pow, derivative_ofNat,
    mul_zero, zero_mul, zero_add, add_zero, derivative_add, derivative_one, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_succ, pow_succ, nsmul_eq_mul] at h
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℝ[X]) ≠ 0)
    (by exact_mod_cast Nat.succ_ne_zero n : (n + 1 : ℝ[X]) ≠ 0)) ha)
  dsimp [a] at *
  linear_combination h

private theorem eq_of_derivative_of_eval_one {p r : ℝ[X]}
    (hd : derivative p = derivative r) (he : p.eval 1 = r.eval 1) : p = r := by
  have h := eq_C_of_derivative_eq_zero (p := p - r) (by simp [hd])
  have hv := congrArg (eval 1) h
  simp [he] at hv
  rw [← sub_eq_zero, h, coeff_sub, ← hv, map_zero]

@[simp] theorem polynomial_one : polynomial 1 = X := by
  apply eq_of_derivative_of_eval_one
  · simpa using derivative_succ 0
  · simp

private theorem raising (n : ℕ)
    (ode : derivative (q * derivative (polynomial n)) =
      (n : ℝ[X]) * (n + 1 : ℝ[X]) * polynomial n) :
    (n + 1 : ℝ[X]) * polynomial (n + 1) =
      (n + 1 : ℝ[X]) * X * polynomial n + q * derivative (polynomial n) := by
  apply eq_of_derivative_of_eval_one
  · rw [derivative_add, ode, derivative_mul, derivative_succ]
    simp [derivative_mul, derivative_add]
    ring
  · simp [q]

/-- Legendre's equation in divergence form, as an identity of real polynomials. -/
theorem equation (n : ℕ) :
    derivative ((X ^ 2 - 1) * derivative (polynomial n)) =
      (n : ℝ[X]) * (n + 1 : ℝ[X]) * polynomial n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hr := raising n ih
    change derivative (q * derivative (polynomial (n + 1))) = _
    rw [derivative_succ, show q * (X * derivative (polynomial n) +
      (n + 1 : ℝ[X]) * polynomial n) = X * (q * derivative (polynomial n)) +
        (n + 1 : ℝ[X]) * (q * polynomial n) by ring]
    rw [derivative_add, derivative_mul, ih, derivative_mul, derivative_mul, derivative_q]
    simp only [derivative_X, one_mul, derivative_add, derivative_natCast, derivative_one,
      add_zero, zero_mul, zero_add, Nat.cast_succ]
    linear_combination -(n + 2 : ℝ[X]) * hr

/-- Bonnet's three-term recurrence. -/
theorem recurrence (n : ℕ) :
    (n + 2 : ℝ[X]) * polynomial (n + 2) =
      (2 * n + 3 : ℝ[X]) * X * polynomial (n + 1) - (n + 1 : ℝ[X]) * polynomial n := by
  have h := raising (n + 1) (equation (n + 1))
  rw [derivative_succ] at h
  push_cast at h
  have g := raising n (equation n)
  dsimp [q] at h g
  linear_combination h - X * g

/-- The difference of degrees `n+2` and `n` is an antiderivative of `(2n+3) Pₙ₊₁`. -/
theorem derivative_sub_two (n : ℕ) :
    derivative (polynomial (n + 2) - polynomial n) =
      C (2 * (n : ℝ) + 3) * polynomial (n + 1) := by
  rw [derivative_sub, derivative_succ (n + 1), derivative_succ n]
  have h := raising n (equation n)
  simp only [q] at h
  simp only [map_add, map_mul, map_ofNat, C_eq_natCast, Nat.cast_succ]
  linear_combination -h

end ProjectAinos.SpecialFunctions.Legendre
