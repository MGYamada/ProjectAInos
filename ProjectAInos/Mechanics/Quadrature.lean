/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Quadrature on an interval of monotone motion

Let `r` be a function of time with a continuous positive derivative `r'` on
an interval, and suppose that the conservation of the energy gives
`r'(t)² = F(r(t))`. Then time can be exchanged for the co-ordinate:
`∫ w(r(t)) dt = ∫ w(u) / √F(u) du`. With `w = 1` this is the time as a
function of the co-ordinate (Landau–Lifshitz (11.3) and (14.6)).

The interval contains no turning point, because the velocity is positive on
it. The integrals up to a turning point are improper and are not treated.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics

open Set

/-- Quadrature: if `r` has a continuous positive derivative `r'` on `[t₀, t₁]`
and `r'(t)² = F(r(t))`, then `∫ w(r(t)) dt = ∫ w(u) / √F(u) du`. -/
theorem integral_comp_eq_integral_div_sqrt {r r' F w : ℝ → ℝ} {t₀ t₁ : ℝ}
    (hr : ∀ t ∈ uIcc t₀ t₁, HasDerivAt r (r' t) t) (hr' : ContinuousOn r' (uIcc t₀ t₁))
    (hpos : ∀ t ∈ uIcc t₀ t₁, 0 < r' t) (hF : ∀ t ∈ uIcc t₀ t₁, r' t ^ 2 = F (r t))
    (hFc : ContinuousOn F (r '' uIcc t₀ t₁)) (hw : ContinuousOn w (r '' uIcc t₀ t₁)) :
    ∫ t in t₀..t₁, w (r t) = ∫ u in r t₀..r t₁, w u / √(F u) := by
  have hsqrt : ∀ t ∈ uIcc t₀ t₁, √(F (r t)) = r' t := fun t ht => by
    rw [← hF t ht, Real.sqrt_sq (hpos t ht).le]
  have hg : ContinuousOn (fun u => w u / √(F u)) (r '' uIcc t₀ t₁) := by
    refine hw.div (Real.continuous_sqrt.comp_continuousOn hFc) ?_
    rintro _ ⟨t, ht, rfl⟩
    rw [hsqrt t ht]
    exact (hpos t ht).ne'
  rw [← intervalIntegral.integral_comp_mul_deriv' hr hr' hg]
  refine intervalIntegral.integral_congr fun t ht => ?_
  simp only [Function.comp_apply]
  rw [hsqrt t ht, div_mul_cancel₀ _ (hpos t ht).ne']

/-- The time as a function of the co-ordinate: if `r` has a continuous positive
derivative `r'` on `[t₀, t₁]` and `r'(t)² = F(r(t))`, then
`t₁ − t₀ = ∫ du / √F(u)`. -/
theorem sub_eq_integral_one_div_sqrt {r r' F : ℝ → ℝ} {t₀ t₁ : ℝ}
    (hr : ∀ t ∈ uIcc t₀ t₁, HasDerivAt r (r' t) t) (hr' : ContinuousOn r' (uIcc t₀ t₁))
    (hpos : ∀ t ∈ uIcc t₀ t₁, 0 < r' t) (hF : ∀ t ∈ uIcc t₀ t₁, r' t ^ 2 = F (r t))
    (hFc : ContinuousOn F (r '' uIcc t₀ t₁)) :
    t₁ - t₀ = ∫ u in r t₀..r t₁, 1 / √(F u) := by
  rw [← integral_comp_eq_integral_div_sqrt (w := fun _ => 1) hr hr' hpos hF hFc
    continuousOn_const, intervalIntegral.integral_const, smul_eq_mul, mul_one]

/-- Motion in one dimension (Landau–Lifshitz (11.3)): if `m ẋ²/2 + U(x) = E`
on an interval where `ẋ > 0`, then `t₁ − t₀ = √(m/2) ∫ dx / √(E − U(x))`. -/
theorem sub_eq_sqrt_mul_integral_of_energy {x x' U : ℝ → ℝ} {m E t₀ t₁ : ℝ} (hm : 0 < m)
    (hx : ∀ t ∈ uIcc t₀ t₁, HasDerivAt x (x' t) t) (hx' : ContinuousOn x' (uIcc t₀ t₁))
    (hpos : ∀ t ∈ uIcc t₀ t₁, 0 < x' t)
    (hE : ∀ t ∈ uIcc t₀ t₁, m / 2 * x' t ^ 2 + U (x t) = E)
    (hU : ContinuousOn U (x '' uIcc t₀ t₁)) :
    t₁ - t₀ = √(m / 2) * ∫ u in x t₀..x t₁, 1 / √(E - U u) := by
  have hm2 : 0 < m / 2 := by positivity
  have hF : ∀ t ∈ uIcc t₀ t₁, x' t ^ 2 = (E - U (x t)) / (m / 2) := fun t ht => by
    rw [eq_div_iff hm2.ne', ← hE t ht]
    ring
  have hFc : ContinuousOn (fun u => (E - U u) / (m / 2)) (x '' uIcc t₀ t₁) :=
    (continuousOn_const.sub hU).div_const _
  rw [sub_eq_integral_one_div_sqrt hx hx' hpos hF hFc, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun u _ => ?_
  change 1 / √((E - U u) / (m / 2)) = √(m / 2) * (1 / √(E - U u))
  rw [Real.sqrt_div' _ hm2.le, one_div_div, mul_one_div]

end ProjectAInos.Mechanics
