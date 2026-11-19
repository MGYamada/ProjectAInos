/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Mechanics.TurningPoint
public import ProjectAinos.SpecialRelativity.NewtonianExpansion
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The integral of the perihelion advance

Let `u₁ = 1/r_min ≥ u₂ = 1/r_max ≥ 0` be the inverse radii of the two apsides of an orbit. In
the Schwarzschild field the orbit equation reads
`(du/dφ)² = (u₁ − u)(u − u₂)(1 − 2M(u₁ + u₂ + u))`, and with the substitution
`u = (u₁ + u₂)/2 + (u₁ − u₂)/2 · cos θ` the angle between the apsides becomes the integral
`∫₀^π dθ / √(1 − 2M(u₁ + u₂ + u(θ)))` (Landau–Lifshitz, §101, (101.7)). This file studies the
integral as a function of the parameters; the connection with the geodesics is not made here.

* `apsidalAngle`: the integral.
* `integral_turningParam`: `∫₀^π u(θ) dθ = π(u₁ + u₂)/2`.
* `apsidalAngle_bounds`: for `2M(2u₁ + u₂) ≤ 1/4`, the advance per revolution
  `2 · apsidalAngle − 2π` equals `3πM(u₁ + u₂)` up to a remainder in `[0, 4πM²(2u₁ + u₂)²]`.
* `advance_eq_semiMajor`: for `u₁ = 1/(a(1 − e))` and `u₂ = 1/(a(1 + e))` the leading term is
  `6πM/(a(1 − e²))`, Landau–Lifshitz (101.7) in the units `k = c = 1`.
* `apsidalAngle_bounds_semiMajor`: the bounds in terms of the semi-major axis `a` and the
  eccentricity `e`.
* `apsidalAngle_zero_mass`: for `M = 0` the angle is `π`, and the Newtonian orbit closes.
-/

@[expose] public section

noncomputable section

namespace ProjectAinos.GeneralRelativity.Perihelion

open Set MeasureTheory
open scoped Real

/-- The angle `∫₀^π dθ / √(1 − 2M(u₁ + u₂ + u(θ)))` between the apsides of an orbit with inverse
apsidal radii `u₂ ≤ u₁` in the field of a mass `M`, where
`u(θ) = (u₁ + u₂)/2 + (u₁ − u₂)/2 · cos θ`. -/
def apsidalAngle (M u₂ u₁ : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..π,
    1 / Real.sqrt (1 - 2 * M * (u₁ + u₂ + Mechanics.turningParam u₂ u₁ θ))

/-- `∫₀^π u(θ) dθ = π(u₁ + u₂)/2`. -/
theorem integral_turningParam (u₂ u₁ : ℝ) :
    ∫ θ in (0 : ℝ)..π, Mechanics.turningParam u₂ u₁ θ = π * (u₁ + u₂) / 2 := by
  rw [Mechanics.integral_turningParam]
  ring

/-- The parametrization `u(θ)` stays in `[u₂, u₁]` for every real `θ`. -/
theorem turningParam_mem_Icc_of_le {u₂ u₁ : ℝ} (hu : u₂ ≤ u₁) (θ : ℝ) :
    Mechanics.turningParam u₂ u₁ θ ∈ Icc u₂ u₁ := by
  have h1 : 0 ≤ (u₁ - u₂) * (1 - Real.cos θ) :=
    mul_nonneg (by linarith) (by linarith [Real.cos_le_one θ])
  have h2 : 0 ≤ (u₁ - u₂) * (1 + Real.cos θ) :=
    mul_nonneg (by linarith) (by linarith [Real.neg_one_le_cos θ])
  simp only [Mechanics.turningParam, mem_Icc]
  constructor <;> nlinarith

/-- For `M ≥ 0` and `0 ≤ u₂ ≤ u₁`, the argument `x(θ) = 2M(u₁ + u₂ + u(θ))` satisfies
`0 ≤ x(θ) ≤ 2M(2u₁ + u₂)`. -/
theorem apsidalArgument_mem_Icc {M u₂ u₁ : ℝ} (hM : 0 ≤ M) (hu₂ : 0 ≤ u₂) (hu : u₂ ≤ u₁)
    (θ : ℝ) :
    2 * M * (u₁ + u₂ + Mechanics.turningParam u₂ u₁ θ) ∈ Icc 0 (2 * M * (2 * u₁ + u₂)) := by
  obtain ⟨h1, h2⟩ := turningParam_mem_Icc_of_le hu θ
  constructor
  · have : 0 ≤ u₁ + u₂ + Mechanics.turningParam u₂ u₁ θ := by linarith
    positivity
  · have : u₁ + u₂ + Mechanics.turningParam u₂ u₁ θ ≤ 2 * u₁ + u₂ := by linarith
    have h2M : 0 ≤ 2 * M := by linarith
    exact mul_le_mul_of_nonneg_left this h2M

/-- **The perihelion advance** (Landau–Lifshitz, §101). For `M ≥ 0`, `0 ≤ u₂ ≤ u₁` and
`2M(2u₁ + u₂) ≤ 1/4`,
`0 ≤ 2 · apsidalAngle M u₂ u₁ − 2π − 3πM(u₁ + u₂) ≤ 4πM²(2u₁ + u₂)²`. -/
theorem apsidalAngle_bounds {M u₂ u₁ : ℝ} (hM : 0 ≤ M) (hu₂ : 0 ≤ u₂) (hu : u₂ ≤ u₁)
    (hsmall : 2 * M * (2 * u₁ + u₂) ≤ 1 / 4) :
    0 ≤ 2 * apsidalAngle M u₂ u₁ - 2 * π - 3 * π * M * (u₁ + u₂) ∧
      2 * apsidalAngle M u₂ u₁ - 2 * π - 3 * π * M * (u₁ + u₂) ≤
        4 * π * M ^ 2 * (2 * u₁ + u₂) ^ 2 := by
  set K := 2 * M * (2 * u₁ + u₂) with hK
  set x : ℝ → ℝ := fun θ => 2 * M * (u₁ + u₂ + Mechanics.turningParam u₂ u₁ θ) with hx
  have hxmem : ∀ θ, 0 ≤ x θ ∧ x θ ≤ K := fun θ => apsidalArgument_mem_Icc hM hu₂ hu θ
  have hcx : Continuous x :=
    continuous_const.mul (continuous_const.add (Mechanics.continuous_turningParam u₂ u₁))
  have hcf : Continuous fun θ => 1 / Real.sqrt (1 - x θ) := by
    refine continuous_const.div (continuous_const.sub hcx).sqrt fun θ => ?_
    have := (hxmem θ).2
    exact (Real.sqrt_pos.mpr (by linarith)).ne'
  have hcl : Continuous fun θ => 1 + x θ / 2 := continuous_const.add (hcx.div_const 2)
  have hsub : ∫ θ in (0 : ℝ)..π, (1 / Real.sqrt (1 - x θ) - (1 + x θ / 2)) =
      apsidalAngle M u₂ u₁ - ∫ θ in (0 : ℝ)..π, (1 + x θ / 2) :=
    intervalIntegral.integral_sub (hcf.intervalIntegrable _ _) (hcl.intervalIntegrable _ _)
  have hlin : ∫ θ in (0 : ℝ)..π, (1 + x θ / 2) = π + 3 / 2 * π * M * (u₁ + u₂) := by
    have he : (fun θ => 1 + x θ / 2) =
        fun θ => (1 + M * (u₁ + u₂)) + M * Mechanics.turningParam u₂ u₁ θ := by
      funext θ
      simp only [hx]
      ring
    rw [he, intervalIntegral.integral_add intervalIntegrable_const
      (((Mechanics.continuous_turningParam u₂ u₁).const_mul M).intervalIntegrable _ _),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      integral_turningParam, smul_eq_mul]
    ring
  have hpt : ∀ θ, 0 ≤ 1 / Real.sqrt (1 - x θ) - (1 + x θ / 2) ∧
      1 / Real.sqrt (1 - x θ) - (1 + x θ / 2) ≤ K ^ 2 / 2 := fun θ => by
    obtain ⟨h0, h1⟩ := hxmem θ
    obtain ⟨b0, b1⟩ :=
      SpecialRelativity.Newtonian.inv_sqrt_one_sub_bounds h0 (h1.trans hsmall)
    have hsq : x θ ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ h0 h1 2
    rw [one_div]
    constructor <;> linarith
  have hlo : 0 ≤ ∫ θ in (0 : ℝ)..π, (1 / Real.sqrt (1 - x θ) - (1 + x θ / 2)) :=
    intervalIntegral.integral_nonneg Real.pi_pos.le fun θ _ => (hpt θ).1
  have hhi : ∫ θ in (0 : ℝ)..π, (1 / Real.sqrt (1 - x θ) - (1 + x θ / 2)) ≤ π * (K ^ 2 / 2) := by
    have h := intervalIntegral.integral_mono_on Real.pi_pos.le
      ((hcf.sub hcl).intervalIntegrable 0 π) (continuous_const.intervalIntegrable (μ := volume) 0 π)
      fun θ _ => (hpt θ).2
    rwa [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h
  rw [hsub, hlin] at hlo hhi
  have hK2 : 4 * π * M ^ 2 * (2 * u₁ + u₂) ^ 2 = π * K ^ 2 := by
    rw [hK]
    ring
  rw [hK2]
  constructor <;> linarith

/-- For the apsides `u₁ = 1/(a(1 − e))` and `u₂ = 1/(a(1 + e))` of an orbit with semi-major
axis `a > 0` and eccentricity `0 ≤ e < 1`, the leading term of the advance is
`3πM(u₁ + u₂) = 6πM/(a(1 − e²))`, Landau–Lifshitz (101.7) with `k = c = 1`. -/
theorem advance_eq_semiMajor (M a e : ℝ) (ha : 0 < a) (he : 0 ≤ e) (he1 : e < 1) :
    3 * π * M * (1 / (a * (1 - e)) + 1 / (a * (1 + e))) = 6 * π * M / (a * (1 - e ^ 2)) := by
  have h1 : 1 - e ≠ 0 := by linarith
  have h2 : 1 + e ≠ 0 := by linarith
  have h3 : 1 - e ^ 2 ≠ 0 := by nlinarith
  have ha' : a ≠ 0 := ha.ne'
  field_simp
  ring

/-- **The perihelion advance in terms of the orbital elements.** For a semi-major axis `a > 0`,
an eccentricity `0 ≤ e < 1`, `M ≥ 0` and `8M(3 + e) ≤ a(1 − e²)`, the advance per revolution
`2 · apsidalAngle − 2π` equals `6πM/(a(1 − e²))` up to a remainder in
`[0, 4πM²((3 + e)/(a(1 − e²)))²]`. -/
theorem apsidalAngle_bounds_semiMajor {M a e : ℝ} (hM : 0 ≤ M) (ha : 0 < a) (he : 0 ≤ e)
    (he1 : e < 1) (hsmall : 8 * M * (3 + e) ≤ a * (1 - e ^ 2)) :
    0 ≤ 2 * apsidalAngle M (1 / (a * (1 + e))) (1 / (a * (1 - e))) - 2 * π -
        6 * π * M / (a * (1 - e ^ 2)) ∧
      2 * apsidalAngle M (1 / (a * (1 + e))) (1 / (a * (1 - e))) - 2 * π -
          6 * π * M / (a * (1 - e ^ 2)) ≤
        4 * π * M ^ 2 * ((3 + e) / (a * (1 - e ^ 2))) ^ 2 := by
  have hp1 : 0 < a * (1 - e) := mul_pos ha (by linarith)
  have hp2 : 0 < a * (1 + e) := mul_pos ha (by linarith)
  have hp3 : 0 < a * (1 - e ^ 2) := mul_pos ha (by nlinarith)
  have hsum : 2 * (1 / (a * (1 - e))) + 1 / (a * (1 + e)) = (3 + e) / (a * (1 - e ^ 2)) := by
    have h1 : 1 - e ≠ 0 := by linarith
    have h2 : 1 + e ≠ 0 := by linarith
    have h3 : 1 - e ^ 2 ≠ 0 := by nlinarith
    have ha' : a ≠ 0 := ha.ne'
    field_simp
    ring
  have hu₂ : 0 ≤ 1 / (a * (1 + e)) := by positivity
  have hu : 1 / (a * (1 + e)) ≤ 1 / (a * (1 - e)) :=
    one_div_le_one_div_of_le hp1 (by nlinarith)
  have hs : 2 * M * (2 * (1 / (a * (1 - e))) + 1 / (a * (1 + e))) ≤ 1 / 4 := by
    rw [hsum, mul_div_assoc', div_le_div_iff₀ hp3 (by norm_num)]
    linarith
  have h := apsidalAngle_bounds hM hu₂ hu hs
  rw [advance_eq_semiMajor M a e ha he he1, hsum] at h
  exact h

/-- Without a mass the angle between the apsides is `π`: the Newtonian orbit closes. -/
theorem apsidalAngle_zero_mass (u₂ u₁ : ℝ) : apsidalAngle 0 u₂ u₁ = π := by
  simp [apsidalAngle]

/- The hypotheses of `apsidalAngle_bounds_semiMajor` hold for a nonzero mass: `M = 1/100`,
`a = 1` and `e = 1/2` give `8M(3 + e) = 7/25 ≤ 3/4 = a(1 − e²)`. -/
example :
    0 ≤ 2 * apsidalAngle (1 / 100) (1 / (1 * (1 + 1 / 2))) (1 / (1 * (1 - 1 / 2))) - 2 * π -
        6 * π * (1 / 100) / (1 * (1 - (1 / 2) ^ 2)) :=
  (apsidalAngle_bounds_semiMajor (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).1

end ProjectAinos.GeneralRelativity.Perihelion
