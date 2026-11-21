/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAinos.SpecialFunctions.LegendreAssociated
import ProjectAinos.SpecialFunctions.LegendreNewton
import ProjectAinos.SpecialFunctions.LegendreOrthogonality
import Mathlib.Tactic

/-! Typed contracts for the normalization, spectrum and expansions of Legendre polynomials. -/

open Polynomial ProjectAinos.SpecialFunctions.Legendre
open ProjectAinos.SmoothGeometry.Potential

noncomputable section

example (n : ℕ) : polynomial n =
    ((shiftedLegendre n).map (Int.castRingHom ℝ)).comp (C (1 / 2 : ℝ) * (1 - X)) := rfl

example : polynomial 0 = 1 := polynomial_zero
example : polynomial 1 = X := polynomial_one
example (n : ℕ) : (polynomial n).eval 1 = 1 := polynomial_eval_one n
example (n : ℕ) : (polynomial n).natDegree = n := natDegree_polynomial n

example (n : ℕ) (x : ℝ) : (polynomial n).eval (-x) = (-1) ^ n * (polynomial n).eval x :=
  polynomial_eval_neg n x

example (n : ℕ) : C (2 ^ n * (n.factorial : ℝ)) * polynomial n =
    derivative^[n] ((X ^ 2 - 1 : ℝ[X]) ^ n) := rodrigues n

example (n : ℕ) : derivative (polynomial (n + 1)) =
    X * derivative (polynomial n) + (n + 1 : ℝ[X]) * polynomial n := derivative_succ n

example (n : ℕ) : derivative ((X ^ 2 - 1) * derivative (polynomial n)) =
    (n : ℝ[X]) * (n + 1 : ℝ[X]) * polynomial n := equation n

example (n : ℕ) : (n + 2 : ℝ[X]) * polynomial (n + 2) =
    (2 * n + 3 : ℝ[X]) * X * polynomial (n + 1) - (n + 1 : ℝ[X]) * polynomial n :=
  recurrence n

example : polynomial 2 = C (1 / 2 : ℝ) * (3 * X ^ 2 - 1) := by
  have h := recurrence 0
  norm_num [polynomial_one] at h
  apply Polynomial.funext
  intro x
  have he := congrArg (eval x) h
  simp at he ⊢
  linarith

example (n m : ℕ) : (∫ x in (-1 : ℝ)..1, (polynomial n).eval x * (polynomial m).eval x) =
    if n = m then 2 / (2 * (n : ℝ) + 1) else 0 := integral_mul n m

example : (∫ x in (-1 : ℝ)..1, ((polynomial 1).eval x) ^ 2) = 2 / 3 := by
  have h := integral_mul 1 1
  norm_num [pow_two] at h ⊢
  exact h

example (n : ℕ) {x : ℝ} (hx : |x| ≤ 1) : |(polynomial n).eval x| ≤ 1 := abs_eval_le_one n hx

example {x t : ℝ} (hx : |x| ≤ 1) (ht : |t| < 1) :
    HasSum (fun n => (polynomial n).eval x * t ^ n) (√(1 - 2 * x * t + t ^ 2))⁻¹ :=
  hasSum_generating hx ht

example (x y : EuclideanSpace ℝ (Fin 3)) (hy : ‖y‖ < ‖x‖) :
    HasSum (fun n => newtonKernel x * ((polynomial n).eval (inner ℝ x y / (‖x‖ * ‖y‖)) *
      (‖y‖ / ‖x‖) ^ n)) (newtonKernel (x - y)) := hasSum_newtonKernel x y hy

example (n m : ℕ) (x : ℝ) : associated n m x =
    (-1) ^ m * (√(1 - x ^ 2)) ^ m * (derivative^[m] (polynomial n)).eval x := rfl

example (n : ℕ) (x : ℝ) : associated n 0 x = (polynomial n).eval x := associated_zero n x

example {n m : ℕ} (h : n < m) (x : ℝ) : associated n m x = 0 := associated_eq_zero_of_lt h x

example (n m : ℕ) :
    let p := derivative^[m] (polynomial n)
    (1 - X ^ 2) * p.derivative.derivative - 2 * (m + 1 : ℝ[X]) * X * p.derivative +
      ((n : ℝ[X]) * (n + 1 : ℝ[X]) - (m : ℝ[X]) * (m + 1 : ℝ[X])) * p = 0 :=
  equation_iterate_derivative n m

example (n m : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    deriv (fun y => (1 - y ^ 2) * deriv (associated n m) y) x =
      ((m : ℝ) ^ 2 / (1 - x ^ 2) - (n : ℝ) * (n + 1)) * associated n m x :=
  associated_equation n m hx
