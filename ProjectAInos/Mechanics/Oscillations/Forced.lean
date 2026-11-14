/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Oscillations.Damped
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Forced oscillations under friction

The equation `ẍ + 2γ ẋ + ω₀² x = g` for a smooth function of time
(Landau–Lifshitz §26, where the damping coefficient `γ` is written `λ` and the
frequency `Ω` of the force is written `γ`).

The solutions for a given force differ by solutions of the damped equation, so
a solution is determined by its position and velocity at time zero. For
`γ > 0` and `ω₀ ≠ 0` every solution of the damped equation tends to zero, so
any two solutions for the same force approach each other: the motion forgets
its initial conditions.

For the force `F cos Ωt` the steady state is `b cos (Ωt + δ)` with
`b = |F| / √((ω₀² − Ω²)² + 4γ² Ω²)`. The amplitude is largest at
`Ω² = ω₀² − 2γ²`. The mean power absorbed over a period is `m γ b² Ω²`; it is
largest at `Ω = ω₀`, and it is half of its largest value exactly at
`Ω = √(ω₀² + γ²) ± γ`, two frequencies that differ by `2γ`.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics

open SmoothAlgebra SmoothRing Filter
open scoped Topology

@[simp] theorem TimeFunction.zero_apply (x : Fin 1 → ℝ) : (0 : TimeFunction) x = 0 := rfl

/-! ### The equation `ẍ + 2γ ẋ + ω₀² x = g` -/

/-- `x` is a forced oscillation under friction: `ẍ = g − 2γ ẋ − ω₀² x`, with
`g` the force divided by the mass (Landau–Lifshitz (26.1)). -/
def IsForced (γ ω₀ : ℝ) (g x : TimeFunction) : Prop :=
  timeDerivative (timeDerivative x) =
    g - algebraMap ℝ TimeFunction (2 * γ) * timeDerivative x -
      algebraMap ℝ TimeFunction (ω₀ ^ 2) * x

/-- Without a force the equation is the damped equation. -/
theorem isForced_zero_iff {γ ω₀ : ℝ} {x : TimeFunction} :
    IsForced γ ω₀ 0 x ↔ IsDamped γ ω₀ x := by
  unfold IsForced IsDamped
  rw [zero_sub]

namespace IsForced

variable {γ ω₀ : ℝ} {g g' x y : TimeFunction}

/-- Superposition: the sum of solutions for two forces is a solution for the
sum of the forces. -/
theorem add (hx : IsForced γ ω₀ g x) (hy : IsForced γ ω₀ g' y) :
    IsForced γ ω₀ (g + g') (x + y) := by
  unfold IsForced at hx hy ⊢
  rw [map_add, map_add, hx, hy]
  ring

/-- A constant multiple of a solution is a solution for the multiple of the
force. -/
theorem const_mul (c : ℝ) (hx : IsForced γ ω₀ g x) :
    IsForced γ ω₀ (algebraMap ℝ TimeFunction c * g) (algebraMap ℝ TimeFunction c * x) := by
  unfold IsForced at hx ⊢
  rw [SmoothDerivation.map_algebraMap_mul, smul_eq_mul, SmoothDerivation.map_algebraMap_mul,
    smul_eq_mul, hx]
  ring

/-- Adding a solution of the damped equation gives a solution for the same
force. -/
theorem add_isDamped (hx : IsForced γ ω₀ g x) (hy : IsDamped γ ω₀ y) :
    IsForced γ ω₀ g (x + y) := by
  have h := hx.add (isForced_zero_iff.mpr hy)
  rwa [add_zero] at h

/-- Two solutions for the same force differ by a solution of the damped
equation. -/
theorem sub (hx : IsForced γ ω₀ g x) (hy : IsForced γ ω₀ g y) : IsDamped γ ω₀ (x - y) := by
  unfold IsForced at hx hy
  unfold IsDamped
  rw [map_sub, map_sub, hx, hy]
  ring

/-- A solution is determined by its position and velocity at time zero. -/
theorem eq_of_initial (hx : IsForced γ ω₀ g x) (hy : IsForced γ ω₀ g y)
    (h0 : x (fun _ => 0) = y fun _ => 0)
    (h1 : timeDerivative x (fun _ => 0) = timeDerivative y fun _ => 0) : x = y := by
  have hz : IsDamped γ ω₀ (0 : TimeFunction) := by
    unfold IsDamped
    simp
  have h := (hx.sub hy).eq_of_initial hz
    (by rw [TimeFunction.sub_apply, TimeFunction.zero_apply, h0, sub_self])
    (by rw [map_sub, map_zero, TimeFunction.sub_apply, TimeFunction.zero_apply, h1, sub_self])
  exact sub_eq_zero.mp h

/-- The balance of energy: `d/dt (ẋ² + ω₀² x²) = 2 ẋ g − 4γ ẋ²`. -/
theorem timeDerivative_energy (h : IsForced γ ω₀ g x) :
    timeDerivative (timeDerivative x * timeDerivative x +
        algebraMap ℝ TimeFunction (ω₀ ^ 2) * (x * x)) =
      2 * (timeDerivative x * g) -
        algebraMap ℝ TimeFunction (4 * γ) * (timeDerivative x * timeDerivative x) := by
  have h4 : algebraMap ℝ TimeFunction (4 * γ) = 2 * algebraMap ℝ TimeFunction (2 * γ) := by
    rw [← map_ofNat (algebraMap ℝ TimeFunction) 2, ← map_mul]
    congr 1
    ring
  unfold IsForced at h
  rw [map_add, SmoothDerivation.map_mul, SmoothDerivation.map_algebraMap_mul,
    SmoothDerivation.map_mul, h, h4]
  simp only [smul_eq_mul]
  ring

end IsForced

/-- The velocity of a solution is a solution for the derivative of the force. -/
theorem IsForced.timeDerivative {γ ω₀ : ℝ} {g x : TimeFunction} (hx : IsForced γ ω₀ g x) :
    IsForced γ ω₀ (timeDerivative g) (timeDerivative x) := by
  unfold IsForced at hx ⊢
  rw [hx, map_sub, map_sub, SmoothDerivation.map_algebraMap_mul,
    SmoothDerivation.map_algebraMap_mul, smul_eq_mul, smul_eq_mul, hx]

/-! ### Decay of the damped motion -/

theorem tendsto_exp_neg_mul_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (fun t : ℝ => Real.exp (-a * t)) atTop (𝓝 0) := by
  have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop ha)
  refine h.congr fun t => ?_
  simp

theorem tendsto_mul_exp_neg_mul_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (fun t : ℝ => t * Real.exp (-a * t)) atTop (𝓝 0) := by
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
    (tendsto_id.const_mul_atTop ha)).const_mul a⁻¹
  rw [mul_zero] at h
  refine h.congr fun t => ?_
  simp only [Function.comp_apply, id, pow_one, neg_mul]
  field_simp

/-- With positive damping and `ω₀ ≠ 0`, every solution of the damped equation
tends to zero. -/
theorem IsDamped.tendsto_zero {γ ω₀ : ℝ} {x : TimeFunction} (h : IsDamped γ ω₀ x) (hγ : 0 < γ)
    (hω₀ : ω₀ ≠ 0) : Tendsto (fun t : ℝ => x fun _ => t) atTop (𝓝 0) := by
  have hE := tendsto_exp_neg_mul_atTop hγ
  rcases lt_trichotomy (ω₀ ^ 2) (γ ^ 2) with hlt | heq | hgt
  · have hβ : Real.sqrt (γ ^ 2 - ω₀ ^ 2) ^ 2 = γ ^ 2 - ω₀ ^ 2 :=
      Real.sq_sqrt (sub_pos.mpr hlt).le
    have hβ0 : 0 < Real.sqrt (γ ^ 2 - ω₀ ^ 2) := Real.sqrt_pos.mpr (sub_pos.mpr hlt)
    have hβγ : Real.sqrt (γ ^ 2 - ω₀ ^ 2) < γ :=
      (Real.sqrt_lt' hγ).mpr (by linarith [sq_pos_of_ne_zero hω₀])
    have h1 := tendsto_exp_neg_mul_atTop (sub_pos.mpr hβγ)
    have h2 := tendsto_exp_neg_mul_atTop (add_pos hγ hβ0)
    have hlim := (h1.const_mul (((γ + Real.sqrt (γ ^ 2 - ω₀ ^ 2)) * x (fun _ => 0) +
        timeDerivative x fun _ => 0) / (2 * Real.sqrt (γ ^ 2 - ω₀ ^ 2)))).sub
      (h2.const_mul (((γ - Real.sqrt (γ ^ 2 - ω₀ ^ 2)) * x (fun _ => 0) +
        timeDerivative x fun _ => 0) / (2 * Real.sqrt (γ ^ 2 - ω₀ ^ 2))))
    rw [mul_zero, mul_zero, sub_zero] at hlim
    exact hlim.congr fun t => (h.apply_eq_overdamped hβ hβ0.ne' t).symm
  · have h2 := tendsto_mul_exp_neg_mul_atTop hγ
    have hlim := (hE.const_mul (x fun _ => 0)).add
      (h2.const_mul (timeDerivative x (fun _ => 0) + γ * x fun _ => 0))
    rw [mul_zero, mul_zero, add_zero] at hlim
    refine hlim.congr fun t => ?_
    rw [h.apply_eq_critical heq t]
    ring
  · have hω : Real.sqrt (ω₀ ^ 2 - γ ^ 2) ^ 2 = ω₀ ^ 2 - γ ^ 2 :=
      Real.sq_sqrt (sub_pos.mpr hgt).le
    have hω0 : Real.sqrt (ω₀ ^ 2 - γ ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (sub_pos.mpr hgt)).ne'
    have hlim := hE.const_mul (amplitude (x fun _ => 0)
      ((timeDerivative x (fun _ => 0) + γ * x fun _ => 0) / Real.sqrt (ω₀ ^ 2 - γ ^ 2)))
    rw [mul_zero] at hlim
    exact squeeze_zero_norm (fun t => h.abs_apply_le hω hω0 t) hlim

/-- With positive damping and `ω₀ ≠ 0`, two solutions for the same force
approach each other: the motion forgets its initial conditions. -/
theorem IsForced.tendsto_sub {γ ω₀ : ℝ} {g x y : TimeFunction} (hx : IsForced γ ω₀ g x)
    (hy : IsForced γ ω₀ g y) (hγ : 0 < γ) (hω₀ : ω₀ ≠ 0) :
    Tendsto (fun t : ℝ => x (fun _ => t) - y fun _ => t) atTop (𝓝 0) :=
  (hx.sub hy).tendsto_zero hγ hω₀

/-! ### The periodic force -/

theorem amplitude_mul_cos_phase (c₁ c₂ : ℝ) :
    amplitude c₁ c₂ * Real.cos (phase c₁ c₂) = c₁ := by
  have h := amplitude_mul_cos_add c₁ c₂ 0
  simpa using h

theorem amplitude_mul_sin_phase (c₁ c₂ : ℝ) :
    amplitude c₁ c₂ * Real.sin (phase c₁ c₂) = -c₂ := by
  have h := amplitude_mul_cos_add c₁ c₂ (Real.pi / 2)
  rw [Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two] at h
  linarith

/-- The denominator `(ω₀² − Ω²)² + 4γ² Ω²` of the response to a force of
frequency `Ω`. -/
def responseDenominator (γ ω₀ Ω : ℝ) : ℝ := (ω₀ ^ 2 - Ω ^ 2) ^ 2 + 4 * γ ^ 2 * Ω ^ 2

theorem responseDenominator_nonneg (γ ω₀ Ω : ℝ) : 0 ≤ responseDenominator γ ω₀ Ω := by
  unfold responseDenominator
  positivity

theorem responseDenominator_pos {γ ω₀ : ℝ} (hγ : γ ≠ 0) (hω₀ : ω₀ ≠ 0) (Ω : ℝ) :
    0 < responseDenominator γ ω₀ Ω := by
  unfold responseDenominator
  rcases eq_or_ne Ω 0 with rfl | hΩ
  · have h : 0 < ω₀ ^ 2 := sq_pos_of_ne_zero hω₀
    nlinarith
  · have h : 0 < 4 * γ ^ 2 * Ω ^ 2 := by positivity
    nlinarith [sq_nonneg (ω₀ ^ 2 - Ω ^ 2)]

/-- The denominator as a function of `Ω²`: it is smallest at
`Ω² = ω₀² − 2γ²`. -/
theorem responseDenominator_eq (γ ω₀ Ω : ℝ) :
    responseDenominator γ ω₀ Ω =
      (Ω ^ 2 - (ω₀ ^ 2 - 2 * γ ^ 2)) ^ 2 + 4 * γ ^ 2 * (ω₀ ^ 2 - γ ^ 2) := by
  unfold responseDenominator
  ring

/-- The coefficient of `cos Ωt` in the steady state. -/
def steadyCos (γ ω₀ F Ω : ℝ) : ℝ := F * (ω₀ ^ 2 - Ω ^ 2) / responseDenominator γ ω₀ Ω

/-- The coefficient of `sin Ωt` in the steady state. -/
def steadySin (γ ω₀ F Ω : ℝ) : ℝ := F * (2 * γ * Ω) / responseDenominator γ ω₀ Ω

/-- The steady state for the force `F cos Ωt` per unit mass. -/
def steadyState (γ ω₀ F Ω : ℝ) : TimeFunction :=
  algebraMap ℝ TimeFunction (steadyCos γ ω₀ F Ω) * TimeFunction.cosMul Ω +
    algebraMap ℝ TimeFunction (steadySin γ ω₀ F Ω) * TimeFunction.sinMul Ω

/-- The first equation for the coefficients of the steady state. -/
theorem steadyCos_mul_add_steadySin_mul {γ ω₀ Ω : ℝ} (hD : responseDenominator γ ω₀ Ω ≠ 0)
    (F : ℝ) :
    steadyCos γ ω₀ F Ω * (ω₀ ^ 2 - Ω ^ 2) + steadySin γ ω₀ F Ω * (2 * γ * Ω) = F := by
  rw [steadyCos, steadySin, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hD]
  unfold responseDenominator
  ring

/-- The second equation for the coefficients of the steady state. -/
theorem steadySin_mul_eq_steadyCos_mul (γ ω₀ F Ω : ℝ) :
    steadySin γ ω₀ F Ω * (ω₀ ^ 2 - Ω ^ 2) = steadyCos γ ω₀ F Ω * (2 * γ * Ω) := by
  unfold steadyCos steadySin
  ring

/-- The steady state is a solution for the force `F cos Ωt`. -/
theorem isForced_steadyState {γ ω₀ Ω : ℝ} (hD : responseDenominator γ ω₀ Ω ≠ 0) (F : ℝ) :
    IsForced γ ω₀ (algebraMap ℝ TimeFunction F * TimeFunction.cosMul Ω)
      (steadyState γ ω₀ F Ω) := by
  have hA := steadyCos_mul_add_steadySin_mul hD F
  have hB := steadySin_mul_eq_steadyCos_mul γ ω₀ F Ω
  unfold IsForced steadyState
  simp only [map_add, SmoothDerivation.map_algebraMap_mul, TimeFunction.timeDerivative_cosMul,
    TimeFunction.timeDerivative_sinMul, smul_eq_mul, map_neg]
  refine TimeFunction.ext_apply_const fun t => ?_
  simp only [TimeFunction.add_apply, TimeFunction.sub_apply, TimeFunction.mul_apply,
    TimeFunction.neg_apply, TimeFunction.algebraMap_apply, TimeFunction.cosMul_apply,
    TimeFunction.sinMul_apply]
  linear_combination Real.cos (Ω * t) * hA + Real.sin (Ω * t) * hB

/-- The response is linear in the force. -/
theorem steadyState_const_mul (γ ω₀ c F Ω : ℝ) :
    steadyState γ ω₀ (c * F) Ω = algebraMap ℝ TimeFunction c * steadyState γ ω₀ F Ω := by
  have hc : steadyCos γ ω₀ (c * F) Ω = c * steadyCos γ ω₀ F Ω := by
    unfold steadyCos
    ring
  have hs : steadySin γ ω₀ (c * F) Ω = c * steadySin γ ω₀ F Ω := by
    unfold steadySin
    ring
  rw [steadyState, steadyState, hc, hs, map_mul, map_mul]
  ring

/-- The amplitude of the steady state (Landau–Lifshitz (26.3)):
`b = |F| / √((ω₀² − Ω²)² + 4γ² Ω²)`. -/
def steadyAmplitude (γ ω₀ F Ω : ℝ) : ℝ := |F| / Real.sqrt (responseDenominator γ ω₀ Ω)

/-- The phase of the steady state. -/
def steadyPhase (γ ω₀ F Ω : ℝ) : ℝ := phase (steadyCos γ ω₀ F Ω) (steadySin γ ω₀ F Ω)

theorem steadyAmplitude_sq (γ ω₀ F Ω : ℝ) :
    steadyAmplitude γ ω₀ F Ω ^ 2 = F ^ 2 / responseDenominator γ ω₀ Ω := by
  rw [steadyAmplitude, div_pow, sq_abs, Real.sq_sqrt (responseDenominator_nonneg _ _ _)]

theorem amplitude_steadyCos_steadySin {γ ω₀ Ω : ℝ} (hD : responseDenominator γ ω₀ Ω ≠ 0)
    (F : ℝ) :
    amplitude (steadyCos γ ω₀ F Ω) (steadySin γ ω₀ F Ω) = steadyAmplitude γ ω₀ F Ω := by
  have hnum : (F * (ω₀ ^ 2 - Ω ^ 2)) ^ 2 + (F * (2 * γ * Ω)) ^ 2 =
      F ^ 2 * responseDenominator γ ω₀ Ω := by
    unfold responseDenominator
    ring
  have hsq : steadyCos γ ω₀ F Ω ^ 2 + steadySin γ ω₀ F Ω ^ 2 =
      F ^ 2 / responseDenominator γ ω₀ Ω := by
    rw [steadyCos, steadySin, div_pow, div_pow, ← add_div, hnum, sq (responseDenominator γ ω₀ Ω),
      mul_div_mul_right _ _ hD]
  rw [amplitude, hsq, steadyAmplitude, Real.sqrt_div (sq_nonneg F), Real.sqrt_sq_eq_abs]

/-- The steady state is `b cos (Ωt + δ)` (Landau–Lifshitz (26.4)). -/
theorem steadyState_apply {γ ω₀ Ω : ℝ} (hD : responseDenominator γ ω₀ Ω ≠ 0) (F t : ℝ) :
    steadyState γ ω₀ F Ω (fun _ => t) =
      steadyAmplitude γ ω₀ F Ω * Real.cos (Ω * t + steadyPhase γ ω₀ F Ω) := by
  rw [← amplitude_steadyCos_steadySin hD, steadyPhase, amplitude_mul_cos_add]
  rfl

/-- `b cos δ = F (ω₀² − Ω²) / D`. -/
theorem steadyAmplitude_mul_cos_steadyPhase {γ ω₀ Ω : ℝ}
    (hD : responseDenominator γ ω₀ Ω ≠ 0) (F : ℝ) :
    steadyAmplitude γ ω₀ F Ω * Real.cos (steadyPhase γ ω₀ F Ω) = steadyCos γ ω₀ F Ω := by
  rw [← amplitude_steadyCos_steadySin hD, steadyPhase, amplitude_mul_cos_phase]

/-- `b sin δ = −2 F γ Ω / D`, so that `tan δ = 2γΩ / (Ω² − ω₀²)`
(Landau–Lifshitz (26.3)). -/
theorem steadyAmplitude_mul_sin_steadyPhase {γ ω₀ Ω : ℝ}
    (hD : responseDenominator γ ω₀ Ω ≠ 0) (F : ℝ) :
    steadyAmplitude γ ω₀ F Ω * Real.sin (steadyPhase γ ω₀ F Ω) = -steadySin γ ω₀ F Ω := by
  rw [← amplitude_steadyCos_steadySin hD, steadyPhase, amplitude_mul_sin_phase]

/-- The oscillation lags behind the force: `sin δ ≤ 0`. -/
theorem sin_steadyPhase_nonpos {γ ω₀ F Ω : ℝ} (hD : responseDenominator γ ω₀ Ω ≠ 0)
    (hF : 0 < F) (hγ : 0 ≤ γ) (hΩ : 0 ≤ Ω) : Real.sin (steadyPhase γ ω₀ F Ω) ≤ 0 := by
  have hDpos : 0 < responseDenominator γ ω₀ Ω :=
    lt_of_le_of_ne (responseDenominator_nonneg _ _ _) (Ne.symm hD)
  have hb : 0 < steadyAmplitude γ ω₀ F Ω :=
    div_pos (abs_pos.mpr hF.ne') (Real.sqrt_pos.mpr hDpos)
  have hs : 0 ≤ steadySin γ ω₀ F Ω :=
    div_nonneg (mul_nonneg hF.le (mul_nonneg (mul_nonneg (by norm_num) hγ) hΩ)) hDpos.le
  have h := steadyAmplitude_mul_sin_steadyPhase hD F
  by_contra hpos
  have hlt : 0 < steadyAmplitude γ ω₀ F Ω * Real.sin (steadyPhase γ ω₀ F Ω) :=
    mul_pos hb (not_le.mp hpos)
  linarith

/-- The velocity in the steady state: `−b Ω sin (Ωt + δ)`. -/
theorem timeDerivative_steadyState_apply {γ ω₀ Ω : ℝ} (hD : responseDenominator γ ω₀ Ω ≠ 0)
    (F t : ℝ) :
    timeDerivative (steadyState γ ω₀ F Ω) (fun _ => t) =
      -(steadyAmplitude γ ω₀ F Ω * Ω * Real.sin (Ω * t + steadyPhase γ ω₀ F Ω)) := by
  have hc := steadyAmplitude_mul_cos_steadyPhase hD F
  have hs := steadyAmplitude_mul_sin_steadyPhase hD F
  have hv : timeDerivative (steadyState γ ω₀ F Ω) (fun _ => t) =
      steadyCos γ ω₀ F Ω * -(Ω * Real.sin (Ω * t)) +
        steadySin γ ω₀ F Ω * (Ω * Real.cos (Ω * t)) := by
    unfold steadyState
    simp only [map_add, SmoothDerivation.map_algebraMap_mul, TimeFunction.timeDerivative_cosMul,
      TimeFunction.timeDerivative_sinMul, smul_eq_mul]
    rfl
  rw [hv, Real.sin_add]
  linear_combination (Ω * Real.sin (Ω * t)) * hc + (Ω * Real.cos (Ω * t)) * hs

namespace IsForced

variable {γ ω₀ F Ω : ℝ} {x : TimeFunction}

/-- The general solution for weak damping (Landau–Lifshitz (26.4)):
`x = a e^{−γt} cos (ωt + α) + b cos (Ωt + δ)`, where `a` and `α` are the
amplitude and phase of the transient `x − steadyState`. -/
theorem apply_eq_transient_add_steadyState {ω : ℝ}
    (hx : IsForced γ ω₀ (algebraMap ℝ TimeFunction F * TimeFunction.cosMul Ω) x)
    (hD : responseDenominator γ ω₀ Ω ≠ 0) (hω : ω ^ 2 = ω₀ ^ 2 - γ ^ 2) (hω0 : ω ≠ 0) (t : ℝ) :
    x (fun _ => t) =
      amplitude ((x - steadyState γ ω₀ F Ω) fun _ => 0)
            ((Mechanics.timeDerivative (x - steadyState γ ω₀ F Ω) (fun _ => 0) +
              γ * (x - steadyState γ ω₀ F Ω) fun _ => 0) / ω) *
          Real.exp (-γ * t) *
          Real.cos (ω * t + phase ((x - steadyState γ ω₀ F Ω) fun _ => 0)
            ((Mechanics.timeDerivative (x - steadyState γ ω₀ F Ω) (fun _ => 0) +
              γ * (x - steadyState γ ω₀ F Ω) fun _ => 0) / ω)) +
        steadyAmplitude γ ω₀ F Ω * Real.cos (Ω * t + steadyPhase γ ω₀ F Ω) := by
  have hz := (hx.sub (isForced_steadyState hD F)).apply_eq_amplitude_mul_exp_mul_cos hω hω0 t
  rw [← hz, ← steadyState_apply hD, TimeFunction.sub_apply, sub_add_cancel]

/-- With positive damping every solution approaches the steady state. -/
theorem tendsto_sub_steadyState
    (hx : IsForced γ ω₀ (algebraMap ℝ TimeFunction F * TimeFunction.cosMul Ω) x) (hγ : 0 < γ)
    (hω₀ : ω₀ ≠ 0) :
    Tendsto (fun t : ℝ => x (fun _ => t) -
      steadyAmplitude γ ω₀ F Ω * Real.cos (Ω * t + steadyPhase γ ω₀ F Ω)) atTop (𝓝 0) := by
  have hD := (responseDenominator_pos hγ.ne' hω₀ Ω).ne'
  refine (hx.tendsto_sub (isForced_steadyState hD F) hγ hω₀).congr fun t => ?_
  rw [steadyState_apply hD]

end IsForced

/-! ### The resonance curve -/

/-- The amplitude of the steady state is at most `|F| / (2γω)`, with
`ω² = ω₀² − γ²`. -/
theorem steadyAmplitude_le {γ ω₀ ω : ℝ} (hγ : 0 < γ) (hω : 0 < ω) (hω2 : ω ^ 2 = ω₀ ^ 2 - γ ^ 2)
    (F Ω : ℝ) : steadyAmplitude γ ω₀ F Ω ≤ |F| / (2 * γ * ω) := by
  have h1 : (2 * γ * ω) ^ 2 ≤ responseDenominator γ ω₀ Ω := by
    rw [responseDenominator_eq, ← hω2]
    nlinarith [sq_nonneg (Ω ^ 2 - (ω₀ ^ 2 - 2 * γ ^ 2))]
  have h2 : 2 * γ * ω ≤ Real.sqrt (responseDenominator γ ω₀ Ω) :=
    (Real.le_sqrt' (by positivity)).mpr h1
  exact div_le_div_of_nonneg_left (abs_nonneg F) (by positivity) h2

/-- The amplitude is largest at `Ω² = ω₀² − 2γ²`. -/
theorem steadyAmplitude_eq_max {γ ω₀ ω Ω : ℝ} (hγ : 0 < γ) (hω : 0 < ω)
    (hω2 : ω ^ 2 = ω₀ ^ 2 - γ ^ 2) (hΩ : Ω ^ 2 = ω₀ ^ 2 - 2 * γ ^ 2) (F : ℝ) :
    steadyAmplitude γ ω₀ F Ω = |F| / (2 * γ * ω) := by
  have h : responseDenominator γ ω₀ Ω = (2 * γ * ω) ^ 2 := by
    rw [responseDenominator_eq, hΩ, ← hω2]
    ring
  rw [steadyAmplitude, h, Real.sqrt_sq (by positivity)]

/-- The mean power absorbed in the steady state, for a particle of mass `m`
(Landau–Lifshitz (26.8)): `I = m γ b² Ω²`. -/
def absorption (m γ ω₀ F Ω : ℝ) : ℝ := m * γ * steadyAmplitude γ ω₀ F Ω ^ 2 * Ω ^ 2

theorem absorption_eq (m γ ω₀ F Ω : ℝ) :
    absorption m γ ω₀ F Ω = m * γ * F ^ 2 * Ω ^ 2 / responseDenominator γ ω₀ Ω := by
  rw [absorption, steadyAmplitude_sq]
  ring

/-- Twice the dissipative function `m γ ẋ²` in the steady state is the
absorption plus a term that oscillates with frequency `2Ω`. -/
theorem two_mul_dissipation_steadyState {γ ω₀ Ω : ℝ} (hD : responseDenominator γ ω₀ Ω ≠ 0)
    (m F t : ℝ) :
    2 * m * γ * timeDerivative (steadyState γ ω₀ F Ω) (fun _ => t) ^ 2 =
      absorption m γ ω₀ F Ω * (1 - Real.cos (2 * (Ω * t + steadyPhase γ ω₀ F Ω))) := by
  rw [timeDerivative_steadyState_apply hD, absorption, Real.cos_two_mul]
  linear_combination (2 * m * γ * steadyAmplitude γ ω₀ F Ω ^ 2 * Ω ^ 2) *
    Real.sin_sq_add_cos_sq (Ω * t + steadyPhase γ ω₀ F Ω)

/-- The absorption is the mean over a period of twice the dissipative
function. -/
theorem mean_dissipation_steadyState {γ ω₀ Ω : ℝ} (hD : responseDenominator γ ω₀ Ω ≠ 0)
    (hΩ : Ω ≠ 0) (m F : ℝ) :
    Ω / (2 * Real.pi) * ∫ t in (0 : ℝ)..(2 * Real.pi / Ω),
        2 * m * γ * timeDerivative (steadyState γ ω₀ F Ω) (fun _ => t) ^ 2 =
      absorption m γ ω₀ F Ω := by
  have hint (t : ℝ) : 2 * m * γ * timeDerivative (steadyState γ ω₀ F Ω) (fun _ => t) ^ 2 =
      2 * m * γ * (steadyAmplitude γ ω₀ F Ω * Ω) ^ 2 *
        Real.sin (Ω * t + steadyPhase γ ω₀ F Ω) ^ 2 := by
    rw [timeDerivative_steadyState_apply hD]
    ring
  have hb : Ω * (2 * Real.pi / Ω) + steadyPhase γ ω₀ F Ω =
      steadyPhase γ ω₀ F Ω + 2 * Real.pi := by
    field_simp
    ring
  have hcomp := intervalIntegral.integral_comp_mul_add (a := 0) (b := 2 * Real.pi / Ω)
    (fun x : ℝ => Real.sin x ^ 2) hΩ (steadyPhase γ ω₀ F Ω)
  simp only [hint]
  rw [intervalIntegral.integral_const_mul, hcomp, integral_sin_sq, mul_zero, zero_add, hb,
    Real.sin_add_two_pi, Real.cos_add_two_pi, absorption, smul_eq_mul]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- The absorption is at most `m F² / 4γ`. -/
theorem absorption_le {m γ ω₀ : ℝ} (hm : 0 ≤ m) (hγ : 0 < γ) (hω₀ : ω₀ ≠ 0) (F Ω : ℝ) :
    absorption m γ ω₀ F Ω ≤ m * F ^ 2 / (4 * γ) := by
  have hD := responseDenominator_pos hγ.ne' hω₀ Ω
  have h1 : 4 * γ ^ 2 * Ω ^ 2 ≤ responseDenominator γ ω₀ Ω := by
    unfold responseDenominator
    nlinarith [sq_nonneg (ω₀ ^ 2 - Ω ^ 2)]
  have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hm (sq_nonneg F))
  rw [absorption_eq, div_le_div_iff₀ hD (by positivity)]
  linarith

/-- The absorption is largest at resonance, `Ω = ω₀`. -/
theorem absorption_resonance {γ ω₀ : ℝ} (hγ : γ ≠ 0) (hω₀ : ω₀ ≠ 0) (m F : ℝ) :
    absorption m γ ω₀ F ω₀ = m * F ^ 2 / (4 * γ) := by
  have hD : responseDenominator γ ω₀ ω₀ = 4 * γ ^ 2 * ω₀ ^ 2 := by
    unfold responseDenominator
    ring
  rw [absorption_eq, hD]
  field_simp

/-- The absorption is half of its largest value exactly when
`(ω₀² − Ω²)² = 4γ² Ω²`. -/
theorem absorption_eq_half_max_iff_sq {m γ ω₀ F Ω : ℝ} (hm : m ≠ 0) (hF : F ≠ 0) (hγ : γ ≠ 0)
    (hΩ : Ω ≠ 0) :
    absorption m γ ω₀ F Ω = m * F ^ 2 / (8 * γ) ↔
      (ω₀ ^ 2 - Ω ^ 2) ^ 2 = 4 * γ ^ 2 * Ω ^ 2 := by
  have hD : responseDenominator γ ω₀ Ω ≠ 0 := by
    have h : 0 < 4 * γ ^ 2 * Ω ^ 2 := by positivity
    unfold responseDenominator
    nlinarith [sq_nonneg (ω₀ ^ 2 - Ω ^ 2)]
  have hmF : m * F ^ 2 ≠ 0 := mul_ne_zero hm (pow_ne_zero 2 hF)
  rw [absorption_eq, div_eq_div_iff hD (mul_ne_zero (by norm_num) hγ)]
  unfold responseDenominator
  constructor
  · intro h
    have h0 : m * F ^ 2 * ((ω₀ ^ 2 - Ω ^ 2) ^ 2 - 4 * γ ^ 2 * Ω ^ 2) = 0 := by
      linear_combination (-1 : ℝ) * h
    have h1 := (mul_eq_zero.mp h0).resolve_left hmF
    linarith
  · intro h
    linear_combination (-(m * F ^ 2)) * h

/-- For positive `γ` and `Ω`, `(ω₀² − Ω²)² = 4γ² Ω²` exactly when
`Ω = s ± γ`, where `s² = ω₀² + γ²` and `s ≥ γ`. -/
theorem sq_sub_sq_eq_iff {γ ω₀ Ω s : ℝ} (hγ : 0 < γ) (hΩ : 0 < Ω)
    (hs : s ^ 2 = ω₀ ^ 2 + γ ^ 2) (hsγ : γ ≤ s) :
    (ω₀ ^ 2 - Ω ^ 2) ^ 2 = 4 * γ ^ 2 * Ω ^ 2 ↔ Ω = s + γ ∨ Ω = s - γ := by
  constructor
  · intro h
    have hfac : (s - Ω - γ) * (s - Ω + γ) * ((s + Ω + γ) * (s + Ω - γ)) = 0 := by
      linear_combination h +
        (s ^ 2 + ω₀ ^ 2 + γ ^ 2 - (Ω + γ) ^ 2 - (Ω - γ) ^ 2) * hs
    have hpos : 0 < (s + Ω + γ) * (s + Ω - γ) := mul_pos (by linarith) (by linarith)
    rcases mul_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_right hpos.ne') with h1 | h2
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
  · rintro (rfl | rfl)
    · linear_combination (s ^ 2 - ω₀ ^ 2 - γ ^ 2 + 4 * γ * (s + γ)) * hs
    · linear_combination (s ^ 2 - ω₀ ^ 2 - γ ^ 2 - 4 * γ * (s - γ)) * hs

/-- The width of the resonance curve: the absorption is half of its largest
value exactly at the two frequencies `√(ω₀² + γ²) ± γ`, which differ by `2γ`. -/
theorem absorption_eq_half_max_iff {m γ ω₀ F Ω : ℝ} (hm : m ≠ 0) (hF : F ≠ 0) (hγ : 0 < γ)
    (hΩ : 0 < Ω) :
    absorption m γ ω₀ F Ω = m * F ^ 2 / (8 * γ) ↔
      Ω = Real.sqrt (ω₀ ^ 2 + γ ^ 2) + γ ∨ Ω = Real.sqrt (ω₀ ^ 2 + γ ^ 2) - γ := by
  have hs : Real.sqrt (ω₀ ^ 2 + γ ^ 2) ^ 2 = ω₀ ^ 2 + γ ^ 2 := Real.sq_sqrt (by positivity)
  have hsγ : γ ≤ Real.sqrt (ω₀ ^ 2 + γ ^ 2) :=
    (Real.le_sqrt' hγ).mpr (by nlinarith [sq_nonneg ω₀])
  rw [absorption_eq_half_max_iff_sq hm hF hγ.ne' hΩ.ne', sq_sub_sq_eq_iff hγ hΩ hs hsγ]

end ProjectAInos.Mechanics
