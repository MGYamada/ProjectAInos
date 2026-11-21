/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.Legendre
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-! # The Legendre generating function on the open interval of real parameters

The differential equation bounds each coefficient by one on the closed interval.
For the partial sum `Sₙ(t)`, the recurrence cancels all but the last term in
`(1 - 2xt + t²) Sₙ′(t) + (t - x) Sₙ(t)`. Integrating the resulting derivative bound
for `√(1 - 2xt + t²) Sₙ(t)` gives its limit at every real `|t| < 1`.
-/

@[expose] public section
noncomputable section

open Polynomial Set Filter
open scoped Topology
namespace ProjectAinos.SpecialFunctions.Legendre

/-- The Sonin energy increases on the positive half interval, giving the sharp bound. -/
theorem abs_eval_le_one (n : ℕ) {x : ℝ} (hx : |x| ≤ 1) : |(polynomial n).eval x| ≤ 1 := by
  suffices pos : ∀ y ∈ Icc (0 : ℝ) 1, |(polynomial n).eval y| ≤ 1 by
    rcases le_or_gt 0 x with h | h
    · exact pos x ⟨h, (abs_le.mp hx).2⟩
    · simpa [polynomial_eval_neg, abs_mul] using
        pos (-x) ⟨by linarith, by linarith [(abs_le.mp hx).1]⟩
  cases n with
  | zero => simp
  | succ n =>
    let p := polynomial (n + 1)
    let a : ℝ := (n + 1 : ℝ) * (n + 2 : ℝ)
    let E : ℝ[X] := C a * p ^ 2 + (1 - X ^ 2) * p.derivative ^ 2
    have ode := equation (n + 1)
    change derivative ((X ^ 2 - 1) * p.derivative) = _ * _ * p at ode
    rw [derivative_mul] at ode
    simp [derivative_sq, map_ofNat] at ode
    have dE : E.derivative = 2 * X * p.derivative ^ 2 := by
      dsimp only [E, a]
      simp [derivative_mul, derivative_sq, map_ofNat]
      linear_combination -2 * p.derivative * ode
    have mono : MonotoneOn (fun t => E.eval t) (Icc 0 1) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc ..) E.continuous.continuousOn
        (fun t _ => (E.differentiableAt (x := t)).differentiableWithinAt)
      intro t ht
      rw [E.deriv, dE]
      simp only [eval_mul, eval_ofNat, eval_X, eval_pow]
      have ht' := interior_subset ht
      exact mul_nonneg (mul_nonneg (by norm_num) ht'.1) (sq_nonneg _)
    intro y hy
    have he := mono hy (right_mem_Icc.mpr zero_le_one) hy.2
    simp [E, p] at he
    have ha : 0 < a := by dsimp [a]; positivity
    have hn : 0 ≤ (1 - y ^ 2) * (p.derivative.eval y) ^ 2 :=
      mul_nonneg (by nlinarith [hy.1, hy.2, mul_nonneg hy.1 (sub_nonneg.mpr hy.2)]) (sq_nonneg _)
    have hsq : a * (p.eval y) ^ 2 ≤ a * 1 := by linarith
    have := (mul_le_mul_iff_right₀ ha).mp hsq
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

private def partialSum (x : ℝ) (n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1), C ((polynomial k).eval x) * X ^ k

private theorem partialSum_succ (x : ℝ) (n : ℕ) :
    partialSum x (n + 1) = partialSum x n + C ((polynomial (n + 1)).eval x) * X ^ (n + 1) :=
  Finset.sum_range_succ ..

private theorem residual (x t : ℝ) (n : ℕ) :
    (1 - 2 * x * t + t ^ 2) * (partialSum x n).derivative.eval t +
      (t - x) * (partialSum x n).eval t =
      (n + 1 : ℝ) * t ^ n * (t * (polynomial n).eval x - (polynomial (n + 1)).eval x) := by
  induction n with
  | zero => simp [partialSum]
  | succ n ih =>
    have h := congrArg (eval x) (recurrence n)
    simp only [eval_mul, eval_sub, eval_add, eval_X, eval_natCast, eval_one, eval_ofNat] at h
    rw [partialSum_succ, derivative_add, derivative_C_mul, derivative_X_pow]
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X, Nat.add_one_sub_one, Nat.cast_succ]
    linear_combination ih + t ^ (n + 1) * h

private theorem sqrt_lower {x t : ℝ} (hx : |x| ≤ 1) :
    1 - |t| ≤ √(1 - 2 * x * t + t ^ 2) := by
  have hxt : x * t ≤ |t| := (le_abs_self _).trans (by
    rw [abs_mul]; simpa using mul_le_mul_of_nonneg_right hx (abs_nonneg t))
  apply Real.le_sqrt_of_sq_le
  nlinarith [sq_abs t]

private theorem partialSum_error {x t : ℝ} (hx : |x| ≤ 1) (ht : |t| < 1) (n : ℕ) :
    |√(1 - 2 * x * t + t ^ 2) * (partialSum x n).eval t - 1| ≤
      ((n + 1 : ℝ) * |t| ^ n) * ((|t| + 1) / (1 - |t|) * |t|) := by
  have hzero : (partialSum x n).eval 0 = 1 := by
    induction n with
    | zero => simp [partialSum]
    | succ n ih => simp [partialSum_succ, ih]
  let f (s : ℝ) := √(1 - 2 * x * s + s ^ 2) * (partialSum x n).eval s
  let g (s : ℝ) := ((n + 1 : ℝ) * s ^ n *
    (s * (polynomial n).eval x - (polynomial (n + 1)).eval x)) / √(1 - 2 * x * s + s ^ 2)
  let U := Icc (-|t|) |t|
  have hrad {s : ℝ} (hs : s ∈ U) : 0 < √(1 - 2 * x * s + s ^ 2) :=
    lt_of_lt_of_le (by linarith [(abs_le.mpr hs).trans_lt ht]) (sqrt_lower hx)
  have df (s : ℝ) (hs : s ∈ U) : HasDerivWithinAt f (g s) U s := by
    have hQ : HasDerivAt (fun y : ℝ => 1 - 2 * x * y + y ^ 2) (2 * (s - x)) s := by
      convert ((hasDerivAt_id s).const_mul (2 * x) |>.const_sub 1).add ((hasDerivAt_id s).pow 2)
        using 1
      · rfl
      · simp; ring
    have hpos := Real.sqrt_pos.mp (hrad hs)
    apply HasDerivAt.hasDerivWithinAt
    apply ((hQ.sqrt hpos.ne').mul ((partialSum x n).hasDerivAt s)).congr_deriv
    dsimp only [g]
    rw [← residual x s n]
    apply (eq_div_iff (hrad hs).ne').2
    rw [add_mul, mul_right_comm _ ((partialSum x n).eval s),
      div_mul_eq_mul_div, mul_div_mul_right _ _ (hrad hs).ne', mul_right_comm _ _,
      ← sq, Real.sq_sqrt hpos.le]
    ring
  have bound (s : ℝ) (hs : s ∈ U) :
      ‖g s‖ ≤ (n + 1 : ℝ) * |t| ^ n * (|t| + 1) / (1 - |t|) := by
    have hst := abs_le.mpr hs
    have hnum : |s * (polynomial n).eval x - (polynomial (n + 1)).eval x| ≤ |t| + 1 := by
      apply (abs_sub _ _).trans
      rw [abs_mul]
      exact add_le_add ((mul_le_mul hst (abs_eval_le_one n hx) (abs_nonneg _) (abs_nonneg _)).trans
        (mul_one _).le) (abs_eval_le_one _ hx)
    dsimp only [g]
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hrad hs), abs_mul, abs_mul, abs_pow,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 1)]
    apply div_le_div₀ (by positivity) _ (by linarith : 0 < 1 - |t|) _
    · gcongr
    · exact (sub_le_sub_left hst 1).trans (sqrt_lower hx)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le df bound (convex_Icc ..)
    (show (0 : ℝ) ∈ U from ⟨neg_nonpos.mpr (abs_nonneg _), abs_nonneg _⟩)
    (show t ∈ U from abs_le.mp le_rfl)
  simpa [f, hzero, Real.norm_eq_abs, div_eq_mul_inv, mul_assoc] using h

/-- The generating series converges to the positive inverse square root for `|t| < 1`. -/
theorem hasSum_generating {x t : ℝ} (hx : |x| ≤ 1) (ht : |t| < 1) :
    HasSum (fun n => (polynomial n).eval x * t ^ n) (√(1 - 2 * x * t + t ^ 2))⁻¹ := by
  have hS : Summable fun n => (polynomial n).eval x * t ^ n :=
    Summable.of_norm_bounded (summable_geometric_of_lt_one (abs_nonneg t) ht) fun n => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      simpa using mul_le_mul_of_nonneg_right (abs_eval_le_one n hx) (pow_nonneg (abs_nonneg t) n)
  have hval (n : ℕ) : (partialSum x n).eval t =
      ∑ k ∈ Finset.range (n + 1), (polynomial k).eval x * t ^ k := by
    simp [partialSum, eval_finsetSum]
  have hlim : Tendsto (fun n => (partialSum x n).eval t) atTop
      (𝓝 (∑' n, (polynomial n).eval x * t ^ n)) := by
    simp_rw [hval]
    exact (tendsto_add_atTop_iff_nat 1).mpr hS.hasSum.tendsto_sum_nat
  have hz : Tendsto (fun n : ℕ => (n + 1 : ℝ) * |t| ^ n) atTop (𝓝 0) := by
    simpa [add_mul] using (tendsto_self_mul_const_pow_of_lt_one (abs_nonneg t) ht).add
      (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg t) ht)
  have he := squeeze_zero (fun n => abs_nonneg _) (partialSum_error hx ht)
    (by simpa using hz.mul_const ((|t| + 1) / (1 - |t|) * |t|))
  have heq := tendsto_nhds_unique (((hlim.const_mul _).sub_const 1).abs) he
  rw [abs_eq_zero, sub_eq_zero] at heq
  have hp : 0 < √(1 - 2 * x * t + t ^ 2) := lt_of_lt_of_le (by linarith) (sqrt_lower hx)
  rw [← one_div, ← (eq_div_iff hp.ne').mpr ((mul_comm ..).trans heq)]
  exact hS.hasSum

end ProjectAinos.SpecialFunctions.Legendre
