/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothAlgebra.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Divided differences of a smooth function of one variable

For a smooth `U : ℝ → ℝ` the first divided difference
`(U(x) − U(y)) / (x − y)` and the second divided difference are smooth
functions of all their arguments, also where the arguments coincide
(Hadamard's lemma, applied twice):

* `sub_eq_mul_dividedDifference`: `U(x) − U(y) = (x − y) U[x, y]`;
* `dividedDifference_sub`: `U[b, x] − U[b, a] = (x − a) U[a, b, x]`;
* `sub_eq_mul_mul_dividedDifference₂`: if `a ≠ b` and `U(a) = U(b) = E`, then
  `E − U(x) = (x − a)(b − x) U[a, b, x]`.

The last identity is the factorization of `E − U` between two points of the
level `E`, with a factor that is smooth in the two points and in `x`.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace ProjectAInos.SmoothAlgebra

variable {U : ℝ → ℝ}

/-- The first divided difference `U[x, y] = ∫₀¹ U′(y + t (x − y)) dt`. -/
def dividedDifference (U : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, deriv U (p.2 + t * (p.1 - p.2))

/-- Hadamard's lemma in one variable. -/
theorem sub_eq_mul_dividedDifference (hU : ContDiff ℝ 1 U) (x y : ℝ) :
    U x - U y = (x - y) * dividedDifference U (x, y) := by
  have hd : ∀ t : ℝ, HasDerivAt (fun s : ℝ => U (y + s * (x - y)))
      (deriv U (y + t * (x - y)) * (x - y)) t := by
    intro t
    have hin : HasDerivAt (fun s : ℝ => y + s * (x - y)) (x - y) t := by
      simpa using ((hasDerivAt_id t).mul_const (x - y)).const_add y
    exact ((hU.differentiable one_ne_zero _).hasDerivAt).comp t hin
  have hc : Continuous fun t : ℝ => deriv U (y + t * (x - y)) * (x - y) :=
    ((hU.continuous_deriv le_rfl).comp (by fun_prop)).mul continuous_const
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
    (fun t _ => hd t) (hc.intervalIntegrable _ _)
  rw [intervalIntegral.integral_mul_const] at h
  simp only [one_mul, zero_mul, add_zero, add_sub_cancel] at h
  rw [dividedDifference, ← h]
  ring

theorem contDiff_dividedDifference (hU : ContDiff ℝ ∞ U) :
    ContDiff ℝ ∞ (dividedDifference U) := by
  have hF : ContDiff ℝ ∞ fun q : (ℝ × ℝ) × ℝ => deriv U (q.1.2 + q.2 * (q.1.1 - q.1.2)) :=
    (hU.deriv' (n := ∞)).comp (by fun_prop)
  exact contDiff_infty_parametric_intervalIntegral hF 0 1

theorem dividedDifference_self (U : ℝ → ℝ) (x : ℝ) :
    dividedDifference U (x, x) = deriv U x := by
  simp [dividedDifference]

/-- The second divided difference `U[a, b, x]`, as an integral of the second
derivative. -/
def dividedDifference₂ (U : ℝ → ℝ) (q : ℝ × ℝ × ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, (1 - t) * ∫ s in (0 : ℝ)..1,
    deriv (deriv U) (q.1 + t * (q.2.1 - q.1) + s * ((1 - t) * (q.2.2 - q.1)))

theorem contDiff_dividedDifference₂ (hU : ContDiff ℝ ∞ U) :
    ContDiff ℝ ∞ (dividedDifference₂ U) := by
  have hU2 : ContDiff ℝ ∞ (deriv (deriv U)) := (hU.deriv' (n := ∞)).deriv' (n := ∞)
  have hF : ContDiff ℝ ∞ fun r : ((ℝ × ℝ × ℝ) × ℝ) × ℝ =>
      deriv (deriv U) (r.1.1.1 + r.1.2 * (r.1.1.2.1 - r.1.1.1) +
        r.2 * ((1 - r.1.2) * (r.1.1.2.2 - r.1.1.1))) :=
    hU2.comp (by fun_prop)
  have hinner : ContDiff ℝ ∞ fun r : (ℝ × ℝ × ℝ) × ℝ => ∫ s in (0 : ℝ)..1,
      deriv (deriv U) (r.1.1 + r.2 * (r.1.2.1 - r.1.1) +
        s * ((1 - r.2) * (r.1.2.2 - r.1.1))) :=
    contDiff_infty_parametric_intervalIntegral hF 0 1
  have hG : ContDiff ℝ ∞ fun r : (ℝ × ℝ × ℝ) × ℝ => (1 - r.2) * ∫ s in (0 : ℝ)..1,
      deriv (deriv U) (r.1.1 + r.2 * (r.1.2.1 - r.1.1) +
        s * ((1 - r.2) * (r.1.2.2 - r.1.1))) :=
    (contDiff_const.sub contDiff_snd).mul hinner
  exact contDiff_infty_parametric_intervalIntegral hG 0 1

/-- The first divided difference in its second argument, divided again. -/
theorem dividedDifference_sub (hU : ContDiff ℝ ∞ U) (a b x : ℝ) :
    dividedDifference U (b, x) - dividedDifference U (b, a) =
      (x - a) * dividedDifference₂ U (a, b, x) := by
  have hU1 : ContDiff ℝ 1 (deriv U) := (hU.deriv' (n := ∞)).of_le (by simp)
  have hc1 : Continuous fun t : ℝ => deriv U (x + t * (b - x)) :=
    hU1.continuous.comp (by fun_prop)
  have hc2 : Continuous fun t : ℝ => deriv U (a + t * (b - a)) :=
    hU1.continuous.comp (by fun_prop)
  have hpt : ∀ t : ℝ, deriv U (x + t * (b - x)) - deriv U (a + t * (b - a)) =
      (x - a) * ((1 - t) * ∫ s in (0 : ℝ)..1,
        deriv (deriv U) (a + t * (b - a) + s * ((1 - t) * (x - a)))) := by
    intro t
    have h := sub_eq_mul_dividedDifference hU1 (x + t * (b - x)) (a + t * (b - a))
    rw [h, dividedDifference]
    have harg : x + t * (b - x) - (a + t * (b - a)) = (1 - t) * (x - a) := by ring
    simp only [harg]
    ring
  rw [dividedDifference, dividedDifference, ← intervalIntegral.integral_sub
    (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _), dividedDifference₂,
    ← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr fun t _ => hpt t

/-- Between two distinct points of a level the difference from the level is the
product of the distances to the two points and the second divided difference. -/
theorem sub_eq_mul_mul_dividedDifference₂ (hU : ContDiff ℝ ∞ U) {a b E : ℝ} (hab : a ≠ b)
    (ha : U a = E) (hb : U b = E) (x : ℝ) :
    E - U x = (x - a) * (b - x) * dividedDifference₂ U (a, b, x) := by
  have hU1 : ContDiff ℝ 1 U := hU.of_le (by simp)
  have h1 := sub_eq_mul_dividedDifference hU1 b x
  have h2 := sub_eq_mul_dividedDifference hU1 b a
  have h3 := dividedDifference_sub hU a b x
  rw [hb] at h1
  rw [hb, ha, sub_self] at h2
  have h0 : dividedDifference U (b, a) = 0 := by
    rcases mul_eq_zero.mp h2.symm with h | h
    · exact absurd (sub_eq_zero.mp h).symm hab
    · exact h
  rw [h0, sub_zero] at h3
  rw [h1, h3]
  ring

end ProjectAInos.SmoothAlgebra
