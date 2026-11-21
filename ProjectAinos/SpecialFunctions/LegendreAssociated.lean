/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.Legendre
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic

/-! # Associated Legendre functions of integral degree and nonnegative order -/

@[expose] public section
noncomputable section

open Polynomial Set Filter
open scoped Topology
namespace ProjectAinos.SpecialFunctions.Legendre

/-- The real Ferrers function on the cut, with the Condon–Shortley phase. -/
def associated (n m : ℕ) (x : ℝ) : ℝ :=
  (-1) ^ m * (√(1 - x ^ 2)) ^ m * (derivative^[m] (polynomial n)).eval x

@[simp] theorem associated_zero (n : ℕ) (x : ℝ) :
    associated n 0 x = (polynomial n).eval x := by simp [associated]

theorem associated_eq_zero_of_lt {n m : ℕ} (h : n < m) (x : ℝ) : associated n m x = 0 := by
  have hd := iterate_derivative_eq_zero (p := polynomial n) ((natDegree_polynomial n).symm ▸ h)
  simp [associated, hd]

/-- The polynomial factor in the order-`m` function satisfies the differentiated
Legendre equation, including at the singular endpoints. -/
theorem equation_iterate_derivative (n m : ℕ) :
    let p := derivative^[m] (polynomial n)
    (1 - X ^ 2) * p.derivative.derivative - 2 * (m + 1 : ℝ[X]) * X * p.derivative +
      ((n : ℝ[X]) * (n + 1 : ℝ[X]) - (m : ℝ[X]) * (m + 1 : ℝ[X])) * p = 0 := by
  induction m with
  | zero =>
    have h := equation n
    rw [derivative_mul] at h
    simp [derivative_sq, map_ofNat] at h ⊢
    linear_combination -h
  | succ m ih =>
    have h := congrArg derivative ih
    simp only [derivative_add, derivative_sub, derivative_mul, derivative_ofNat,
      derivative_natCast, derivative_one, derivative_sq, derivative_X, map_ofNat,
      derivative_zero, zero_mul, add_zero, zero_add, mul_zero, mul_one, sub_zero] at h
    simp only [Function.iterate_succ_apply', Nat.cast_succ]
    linear_combination h

private def weight (m : ℕ) (x : ℝ) := (-1 : ℝ) ^ m * (√(1 - x ^ 2)) ^ m

private theorem weight_deriv (m : ℕ) {x : ℝ} (hx : 0 < 1 - x ^ 2) :
    HasDerivAt (weight m) (-(m : ℝ) * x * weight m x / (1 - x ^ 2)) x := by
  have hq : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * x) x := by
    convert ((hasDerivAt_pow 2 x).const_sub 1) using 1
    simp
  have hr := hq.sqrt hx.ne'
  induction m with
  | zero =>
    change HasDerivAt (fun y => weight 0 y) _ x
    simpa [weight] using (hasDerivAt_const x (1 : ℝ))
  | succ m ih =>
    have h := (ih.mul hr).neg
    have hw : weight (m + 1) = fun y => -(weight m y * √(1 - y ^ 2)) := by
      funext y
      simp [weight, pow_succ, mul_assoc]
    rw [hw]
    apply h.congr_deriv
    push_cast
    field_simp [hx.ne', (Real.sqrt_pos.mpr hx).ne']
    linear_combination -(x * weight m x) * (Real.sq_sqrt hx.le)

/-- The associated Legendre equation in divergence form on the open interval. -/
theorem associated_equation (n m : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    deriv (fun y => (1 - y ^ 2) * deriv (associated n m) y) x =
      ((m : ℝ) ^ 2 / (1 - x ^ 2) - (n : ℝ) * (n + 1 : ℝ)) * associated n m x := by
  let p := derivative^[m] (polynomial n)
  let r : ℝ[X] := (1 - X ^ 2) * p.derivative - (m : ℝ[X]) * X * p
  have pos {y : ℝ} (hy : y ∈ Set.Ioo (-1 : ℝ) 1) : 0 < 1 - y ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hy.2) (sub_pos.mpr hy.1)]
  have hflux {y : ℝ} (hy : y ∈ Set.Ioo (-1 : ℝ) 1) :
      (1 - y ^ 2) * deriv (associated n m) y = weight m y * r.eval y := by
    have h := ((weight_deriv m (pos hy)).mul (p.hasDerivAt y)).deriv
    change deriv (associated n m) y = _ at h
    rw [h]
    simp only [r, eval_sub, eval_mul, eval_one, eval_pow, eval_X, eval_natCast]
    field_simp [(pos hy).ne']
    ring
  have hd := ((weight_deriv m (pos hx)).mul (r.hasDerivAt x)).deriv
  have he : (fun y => (1 - y ^ 2) * deriv (associated n m) y) =ᶠ[nhds x]
      (fun y => weight m y * r.eval y) :=
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hx) (fun _ hy => hflux hy)
  rw [he.deriv_eq]
  refine hd.trans ?_
  have ode := congrArg (eval x) (equation_iterate_derivative n m)
  change eval x ((1 - X ^ 2) * p.derivative.derivative -
    2 * (m + 1 : ℝ[X]) * X * p.derivative +
    ((n : ℝ[X]) * (n + 1 : ℝ[X]) - (m : ℝ[X]) * (m + 1 : ℝ[X])) * p) = _ at ode
  simp only [eval_add, eval_sub, eval_mul, eval_natCast, eval_X, eval_pow, eval_ofNat,
    eval_one, eval_zero] at ode
  change _ = _ * (weight m x * p.eval x)
  simp [r, derivative_mul, derivative_sq, map_ofNat]
  field_simp [(pos hx).ne']
  linear_combination (1 - x ^ 2) * weight m x * ode

end ProjectAinos.SpecialFunctions.Legendre
