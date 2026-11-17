/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Mechanics.OneDimension.Well
public import ProjectAinos.Mechanics.TurningPoint
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The level curve of a well, parametrized by an angle

For a well `IsWell U E a b` and a mass `m > 0` the level curve
`p²/2m + U(x) = E` between the turning points is the image of the closed curve

`x(θ) = (a + b)/2 − (b − a)/2 · cos θ`,
`p(θ) = √(2m) · (b − a)/2 · sin θ · √W(x(θ))`,

with `W` the factor of `E − U = (x − a)(b − x) W`. Both functions are smooth and
`2π`-periodic, and the curve is tangent to the Hamiltonian field
`(p/m, −U′(x))` with the positive factor `λ(θ) = √(m/2) / √W(x(θ))`
(`hasDerivAt_orbitPosition`, `hasDerivAt_orbitMomentum`): `λ` is `dt/dθ` along
the motion. No point of the curve is singular, so the turning points need no
separate treatment.

The period is `orbitPeriod = ∫₀^{2π} λ dθ`, which is
`√(2m) ∫ₐᵇ dx / √(E − U(x))` (`IsWell.orbitPeriod_eq`, Landau–Lifshitz (11.5)).
-/

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped Real ContDiff

namespace ProjectAinos.Mechanics.OneDim

variable {U : ℝ → ℝ} {E a b m : ℝ}

/-- The position on the level curve at the angle `θ`: `a` at `θ = 0` and `b` at
`θ = π`. -/
def orbitPosition (a b θ : ℝ) : ℝ := (a + b) / 2 - (b - a) / 2 * Real.cos θ

/-- The momentum on the level curve at the angle `θ`. -/
def orbitMomentum (m : ℝ) (U : ℝ → ℝ) (a b θ : ℝ) : ℝ :=
  √(2 * m) * ((b - a) / 2 * Real.sin θ) * √(wellFactor U a b (orbitPosition a b θ))

/-- The rate `dt/dθ` of the time along the level curve. -/
def orbitRate (m : ℝ) (U : ℝ → ℝ) (a b θ : ℝ) : ℝ :=
  √(m / 2) / √(wellFactor U a b (orbitPosition a b θ))

/-- The period of the motion on the level curve. -/
def orbitPeriod (m : ℝ) (U : ℝ → ℝ) (a b : ℝ) : ℝ := ∫ θ in (0 : ℝ)..2 * π, orbitRate m U a b θ

theorem orbitPosition_zero (a b : ℝ) : orbitPosition a b 0 = a := by
  simp [orbitPosition]
  ring

theorem orbitPosition_pi (a b : ℝ) : orbitPosition a b π = b := by
  simp [orbitPosition]
  ring

theorem orbitPosition_add_two_pi (a b θ : ℝ) :
    orbitPosition a b (θ + 2 * π) = orbitPosition a b θ := by
  simp [orbitPosition]

theorem orbitPosition_neg (a b θ : ℝ) : orbitPosition a b (-θ) = orbitPosition a b θ := by
  simp [orbitPosition]

theorem orbitPosition_mem_Icc (hab : a ≤ b) (θ : ℝ) : orbitPosition a b θ ∈ Icc a b := by
  have h1 := Real.neg_one_le_cos θ
  have h2 := Real.cos_le_one θ
  have hr : 0 ≤ (b - a) / 2 := by linarith
  constructor
  · rw [orbitPosition]
    nlinarith
  · rw [orbitPosition]
    nlinarith

theorem orbitPosition_sub_mul_sub (a b θ : ℝ) :
    (orbitPosition a b θ - a) * (b - orbitPosition a b θ) = ((b - a) / 2 * Real.sin θ) ^ 2 := by
  simp only [orbitPosition]
  linear_combination (-(((b - a) / 2) ^ 2)) * Real.sin_sq_add_cos_sq θ

theorem hasDerivAt_orbitPosition (a b θ : ℝ) :
    HasDerivAt (orbitPosition a b) ((b - a) / 2 * Real.sin θ) θ := by
  have h := ((Real.hasDerivAt_cos θ).const_mul ((b - a) / 2)).const_sub ((a + b) / 2)
  refine h.congr_deriv ?_
  ring

theorem contDiff_orbitPosition (a b : ℝ) : ContDiff ℝ ∞ (orbitPosition a b) :=
  contDiff_const.sub (contDiff_const.mul Real.contDiff_cos)

theorem orbitMomentum_zero (m : ℝ) (U : ℝ → ℝ) (a b : ℝ) : orbitMomentum m U a b 0 = 0 := by
  simp [orbitMomentum]

theorem orbitMomentum_add_two_pi (m : ℝ) (U : ℝ → ℝ) (a b θ : ℝ) :
    orbitMomentum m U a b (θ + 2 * π) = orbitMomentum m U a b θ := by
  simp [orbitMomentum, orbitPosition_add_two_pi]

theorem orbitMomentum_neg (m : ℝ) (U : ℝ → ℝ) (a b θ : ℝ) :
    orbitMomentum m U a b (-θ) = -orbitMomentum m U a b θ := by
  simp [orbitMomentum, orbitPosition_neg]

theorem orbitRate_add_two_pi (m : ℝ) (U : ℝ → ℝ) (a b θ : ℝ) :
    orbitRate m U a b (θ + 2 * π) = orbitRate m U a b θ := by
  simp [orbitRate, orbitPosition_add_two_pi]

theorem orbitRate_neg (m : ℝ) (U : ℝ → ℝ) (a b θ : ℝ) :
    orbitRate m U a b (-θ) = orbitRate m U a b θ := by
  simp [orbitRate, orbitPosition_neg]

namespace IsWell

/-- The factor is positive along the level curve. -/
theorem wellFactor_orbitPosition_pos (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (θ : ℝ) :
    0 < wellFactor U a b (orbitPosition a b θ) :=
  h.wellFactor_pos hU (orbitPosition_mem_Icc h.lt.le θ)

theorem orbitRate_pos (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m) (θ : ℝ) :
    0 < orbitRate m U a b θ :=
  div_pos (Real.sqrt_pos.mpr (by positivity))
    (Real.sqrt_pos.mpr (h.wellFactor_orbitPosition_pos hU θ))

/-- The curve lies on the level `E` of the Hamiltonian. -/
theorem orbit_energy (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m) (θ : ℝ) :
    orbitMomentum m U a b θ ^ 2 / (2 * m) + U (orbitPosition a b θ) = E := by
  have hW := (h.wellFactor_orbitPosition_pos hU θ).le
  have hfac := h.sub_eq hU (orbitPosition a b θ)
  rw [orbitPosition_sub_mul_sub] at hfac
  have hm2 : (0 : ℝ) ≤ 2 * m := by positivity
  rw [orbitMomentum, mul_pow, mul_pow, Real.sq_sqrt hm2, Real.sq_sqrt hW]
  have hne : (2 * m) ≠ 0 := by positivity
  field_simp
  linarith

/-- The square of the momentum on the curve. -/
theorem orbitMomentum_sq (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m) (θ : ℝ) :
    orbitMomentum m U a b θ ^ 2 = 2 * m * (E - U (orbitPosition a b θ)) := by
  have he := h.orbit_energy hU hm θ
  have hne : (2 * m) ≠ 0 := by positivity
  field_simp at he
  linarith

/-- The first component of the tangent of the curve: `dx/dθ = λ p/m`. -/
theorem orbitRate_mul_orbitMomentum (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m)
    (θ : ℝ) :
    orbitRate m U a b θ * (orbitMomentum m U a b θ / m) = (b - a) / 2 * Real.sin θ := by
  have hW := h.wellFactor_orbitPosition_pos hU θ
  have hs : √(wellFactor U a b (orbitPosition a b θ)) ≠ 0 := (Real.sqrt_pos.mpr hW).ne'
  have h2m : √(2 * m) = 2 * √(m / 2) := by
    have h4 : (2 * m) = 2 ^ 2 * (m / 2) := by ring
    rw [h4, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  have hc2 : √(m / 2) ^ 2 = m / 2 := Real.sq_sqrt (by positivity)
  have key : ∀ c s R : ℝ, s ≠ 0 → c ^ 2 = m / 2 → c / s * (2 * c * R * s / m) = R := by
    intro c s R hs0 hc
    have : c / s * (2 * c * R * s / m) = 2 * c ^ 2 * R / m := by
      field_simp
    rw [this, hc]
    field_simp
  rw [orbitRate, orbitMomentum, h2m]
  exact key _ _ _ hs hc2

/-- The derivative of the factorization of `E − U`. -/
theorem neg_deriv_eq (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (x : ℝ) :
    -deriv U x = (a + b - 2 * x) * wellFactor U a b x +
      (x - a) * (b - x) * deriv (wellFactor U a b) x := by
  have hW : DifferentiableAt ℝ (wellFactor U a b) x :=
    (contDiff_wellFactor_right hU a b).differentiable (by simp) x
  have h1 : HasDerivAt (fun y => (y - a) * (b - y) * wellFactor U a b y)
      ((1 * (b - x) + (x - a) * -1) * wellFactor U a b x +
        (x - a) * (b - x) * deriv (wellFactor U a b) x) x :=
    (((hasDerivAt_id x).sub_const a).mul ((hasDerivAt_id x).const_sub b)).mul hW.hasDerivAt
  have h2 : HasDerivAt (fun y => E - U y) (-deriv U x) x :=
    ((hU.differentiable (by simp) x).hasDerivAt).const_sub E
  have hfun : (fun y => E - U y) = fun y => (y - a) * (b - y) * wellFactor U a b y :=
    funext fun y => h.sub_eq hU y
  rw [hfun] at h2
  rw [h2.unique h1]
  ring

/-- The second component of the tangent of the curve: `dp/dθ = −λ U′(x)`. -/
theorem hasDerivAt_orbitMomentum (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (m θ : ℝ) :
    HasDerivAt (orbitMomentum m U a b)
      (-(orbitRate m U a b θ * deriv U (orbitPosition a b θ))) θ := by
  have hWpos := h.wellFactor_orbitPosition_pos hU θ
  have hWd : HasDerivAt (wellFactor U a b)
      (deriv (wellFactor U a b) (orbitPosition a b θ)) (orbitPosition a b θ) :=
    ((contDiff_wellFactor_right hU a b).differentiable (by simp) _).hasDerivAt
  have hcomp := hWd.comp θ (hasDerivAt_orbitPosition a b θ)
  have hsqrt := hcomp.sqrt hWpos.ne'
  have hsin : HasDerivAt (fun θ : ℝ => (b - a) / 2 * Real.sin θ) ((b - a) / 2 * Real.cos θ) θ :=
    (Real.hasDerivAt_sin θ).const_mul ((b - a) / 2)
  have hP := (hsin.const_mul (√(2 * m))).mul hsqrt
  refine hP.congr_deriv ?_
  -- the algebraic identity, with `s = √W` and `√(2m) = 2 √(m/2)`
  have hs : √(wellFactor U a b (orbitPosition a b θ)) ≠ 0 := (Real.sqrt_pos.mpr hWpos).ne'
  have hs2 : √(wellFactor U a b (orbitPosition a b θ)) ^ 2 =
      wellFactor U a b (orbitPosition a b θ) := Real.sq_sqrt hWpos.le
  have h2m : √(2 * m) = 2 * √(m / 2) := by
    have h4 : (2 * m) = 2 ^ 2 * (m / 2) := by ring
    rw [h4, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  have hid := h.neg_deriv_eq hU (orbitPosition a b θ)
  rw [orbitPosition_sub_mul_sub] at hid
  have hsum : a + b - 2 * orbitPosition a b θ = 2 * ((b - a) / 2 * Real.cos θ) := by
    simp only [orbitPosition]
    ring
  rw [hsum] at hid
  have key : ∀ c s rc rs W' Up Wv : ℝ, s ≠ 0 → s ^ 2 = Wv →
      -Up = 2 * rc * Wv + rs ^ 2 * W' →
      2 * c * rc * s + 2 * c * rs * (W' * rs / (2 * s)) = -(c / s * Up) := by
    intro c s rc rs W' Up Wv hs0 hsq hUp
    have hUp' : Up = -(2 * rc * Wv + rs ^ 2 * W') := by linarith
    rw [hUp', ← hsq]
    field_simp
  simp only [Function.comp_apply, orbitRate, h2m]
  exact key _ _ _ _ _ _ _ hs hs2 hid

/-- The period is the integral of Landau–Lifshitz (11.5):
`T = √(2m) ∫ₐᵇ dx / √(E − U(x))`. -/
theorem orbitPeriod_eq (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (m : ℝ) :
    orbitPeriod m U a b = √(2 * m) * ∫ x in a..b, 1 / √(E - U x) := by
  have hcont : Continuous (orbitRate m U a b) := by
    have hWc : Continuous fun θ => wellFactor U a b (orbitPosition a b θ) :=
      (contDiff_wellFactor_right hU a b).continuous.comp (contDiff_orbitPosition a b).continuous
    exact continuous_const.div (Real.continuous_sqrt.comp hWc) fun θ =>
      (Real.sqrt_pos.mpr (h.wellFactor_orbitPosition_pos hU θ)).ne'
  -- the two halves of the circle give the same integral
  have hsplit : ∫ θ in (0 : ℝ)..2 * π, orbitRate m U a b θ =
      (∫ θ in (0 : ℝ)..π, orbitRate m U a b θ) + ∫ θ in π..2 * π, orbitRate m U a b θ :=
    (intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)).symm
  have hsecond : ∫ θ in π..2 * π, orbitRate m U a b θ = ∫ θ in (0 : ℝ)..π, orbitRate m U a b θ := by
    have hsub := intervalIntegral.integral_comp_sub_left (a := 0) (b := π)
      (fun θ => orbitRate m U a b θ) (2 * π)
    have hfun : (fun θ => orbitRate m U a b (2 * π - θ)) = orbitRate m U a b := by
      funext θ
      have e : 2 * π - θ = -θ + 2 * π := by ring
      rw [e, orbitRate_add_two_pi, orbitRate_neg]
    rw [hfun] at hsub
    rw [hsub]
    congr 1 <;> ring
  -- the half circle in the variable of `turningParam`
  have hhalf : ∫ θ in (0 : ℝ)..π, orbitRate m U a b θ =
      √(m / 2) * ∫ x in a..b, 1 / √(E - U x) := by
    have hrefl := intervalIntegral.integral_comp_sub_left (a := 0) (b := π)
      (fun θ => orbitRate m U a b θ) π
    have hfun : (fun θ => orbitRate m U a b (π - θ)) =
        fun θ => √(m / 2) * ((fun _ : ℝ => (1 : ℝ)) (turningParam a b θ) /
          √(wellFactor U a b (turningParam a b θ))) := by
      funext θ
      have hpos : orbitPosition a b (π - θ) = turningParam a b θ := by
        simp only [orbitPosition, turningParam, Real.cos_pi_sub]
        ring
      rw [orbitRate, hpos]
      ring
    rw [hfun] at hrefl
    have hlim : ∫ θ in (0 : ℝ)..π, orbitRate m U a b θ =
        ∫ θ in (0 : ℝ)..π, √(m / 2) * ((fun _ : ℝ => (1 : ℝ)) (turningParam a b θ) /
          √(wellFactor U a b (turningParam a b θ))) := by
      rw [hrefl]
      congr 1 <;> ring
    rw [hlim, intervalIntegral.integral_const_mul,
      ← integral_div_sqrt_turning h.lt (fun _ => 1) (wellFactor U a b)]
    congr 1
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [h.sub_eq hU x]
  have h2m : √(2 * m) = 2 * √(m / 2) := by
    have h4 : (2 * m) = 2 ^ 2 * (m / 2) := by ring
    rw [h4, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  rw [orbitPeriod, hsplit, hsecond, hhalf, h2m]
  ring

/-- The period is positive. -/
theorem orbitPeriod_pos (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m) :
    0 < orbitPeriod m U a b := by
  have hcont : Continuous (orbitRate m U a b) := by
    have hWc : Continuous fun θ => wellFactor U a b (orbitPosition a b θ) :=
      (contDiff_wellFactor_right hU a b).continuous.comp (contDiff_orbitPosition a b).continuous
    exact continuous_const.div (Real.continuous_sqrt.comp hWc) fun θ =>
      (Real.sqrt_pos.mpr (h.wellFactor_orbitPosition_pos hU θ)).ne'
  exact intervalIntegral.intervalIntegral_pos_of_pos (hcont.intervalIntegrable _ _)
    (fun θ => h.orbitRate_pos hU hm θ) (by positivity)

end IsWell

end ProjectAinos.Mechanics.OneDim
