/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Oscillations.Forced
public import ProjectAInos.Mechanics.TimePrimitive
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Forced oscillations without friction

The equation `ẍ + ω² x = g` for a smooth force `g` per unit mass
(Landau–Lifshitz §22). It is `IsForced 0 ω g x`.

The two functions `ẋ cos ωt + ω x sin ωt` and `ω x cos ωt − ẋ sin ωt` are the
real and the imaginary part of `(ẋ + iωx) e^{−iωt}`. Without a force they are
constant; with a force their derivatives are `g cos ωt` and `−g sin ωt`. The
fundamental theorem of calculus gives their values as integrals of the force,
and from them the velocity, the position (Duhamel's formula) and the energy.
The formula for the position also defines a solution, so a solution exists for
every smooth force and all initial data.

For the periodic force `F cos Ωt` with `Ω² ≠ ω²` the forced oscillation is
`F/(ω² − Ω²) cos Ωt`. At resonance, `Ω = ω`, it is `(F/2ω) t sin ωt`, and no
solution is bounded.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics

open SmoothAlgebra SmoothRing

/-- Without friction the equation is `ẍ = g − ω² x` (Landau–Lifshitz (22.2)). -/
theorem isForced_zero_damping_iff {ω : ℝ} {g x : TimeFunction} :
    IsForced 0 ω g x ↔
      timeDerivative (timeDerivative x) = g - algebraMap ℝ TimeFunction (ω ^ 2) * x := by
  unfold IsForced
  rw [mul_zero, map_zero, zero_mul, sub_zero]

/-- `ẋ cos ωt + ω x sin ωt`, the real part of `(ẋ + iωx) e^{−iωt}`. -/
def complexAmplitudeRe (ω : ℝ) (x : TimeFunction) : TimeFunction :=
  timeDerivative x * TimeFunction.cosMul ω +
    algebraMap ℝ TimeFunction ω * (x * TimeFunction.sinMul ω)

/-- `ω x cos ωt − ẋ sin ωt`, the imaginary part of `(ẋ + iωx) e^{−iωt}`. -/
def complexAmplitudeIm (ω : ℝ) (x : TimeFunction) : TimeFunction :=
  algebraMap ℝ TimeFunction ω * (x * TimeFunction.cosMul ω) -
    timeDerivative x * TimeFunction.sinMul ω

theorem complexAmplitudeRe_apply (ω : ℝ) (x : TimeFunction) (t : ℝ) :
    complexAmplitudeRe ω x (fun _ => t) =
      timeDerivative x (fun _ => t) * Real.cos (ω * t) +
        ω * (x (fun _ => t) * Real.sin (ω * t)) := rfl

theorem complexAmplitudeIm_apply (ω : ℝ) (x : TimeFunction) (t : ℝ) :
    complexAmplitudeIm ω x (fun _ => t) =
      ω * (x (fun _ => t) * Real.cos (ω * t)) -
        timeDerivative x (fun _ => t) * Real.sin (ω * t) := rfl

theorem complexAmplitudeRe_apply_zero (ω : ℝ) (x : TimeFunction) :
    complexAmplitudeRe ω x (fun _ => 0) = timeDerivative x fun _ => 0 := by
  rw [complexAmplitudeRe_apply]
  simp

theorem complexAmplitudeIm_apply_zero (ω : ℝ) (x : TimeFunction) :
    complexAmplitudeIm ω x (fun _ => 0) = ω * x fun _ => 0 := by
  rw [complexAmplitudeIm_apply]
  simp

/-- The integral of the force against `sin ω(t − s)`, in terms of the
integrals against `cos ωs` and `sin ωs`. -/
theorem integral_mul_sin_sub (ω : ℝ) (g : TimeFunction) (t : ℝ) :
    ∫ s in (0 : ℝ)..t, g (fun _ => s) * Real.sin (ω * (t - s)) =
      Real.sin (ω * t) * (∫ s in (0 : ℝ)..t, g (fun _ => s) * Real.cos (ω * s)) -
        Real.cos (ω * t) * (∫ s in (0 : ℝ)..t, g (fun _ => s) * Real.sin (ω * s)) := by
  have hc : Continuous fun s : ℝ => g (fun _ => s) * Real.cos (ω * s) :=
    (g * TimeFunction.cosMul ω).continuous_apply_const
  have hs : Continuous fun s : ℝ => g (fun _ => s) * Real.sin (ω * s) :=
    (g * TimeFunction.sinMul ω).continuous_apply_const
  have h : (fun s : ℝ => g (fun _ => s) * Real.sin (ω * (t - s))) = fun s =>
      Real.sin (ω * t) * (g (fun _ => s) * Real.cos (ω * s)) -
        Real.cos (ω * t) * (g (fun _ => s) * Real.sin (ω * s)) := by
    funext s
    rw [mul_sub, Real.sin_sub]
    ring
  have i1 : IntervalIntegrable
      (fun s : ℝ => Real.sin (ω * t) * (g (fun _ => s) * Real.cos (ω * s)))
      MeasureTheory.volume 0 t :=
    (continuous_const.mul hc).intervalIntegrable 0 t
  have i2 : IntervalIntegrable
      (fun s : ℝ => Real.cos (ω * t) * (g (fun _ => s) * Real.sin (ω * s)))
      MeasureTheory.volume 0 t :=
    (continuous_const.mul hs).intervalIntegrable 0 t
  rw [h, intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]

namespace IsForced

variable {ω : ℝ} {g x : TimeFunction}

theorem timeDerivative_complexAmplitudeRe (h : IsForced 0 ω g x) :
    Mechanics.timeDerivative (complexAmplitudeRe ω x) = g * TimeFunction.cosMul ω := by
  have hsq : algebraMap ℝ TimeFunction (ω ^ 2) =
      algebraMap ℝ TimeFunction ω * algebraMap ℝ TimeFunction ω := by
    rw [sq, map_mul]
  rw [isForced_zero_damping_iff, hsq] at h
  rw [complexAmplitudeRe, map_add, SmoothDerivation.map_mul, SmoothDerivation.map_algebraMap_mul,
    SmoothDerivation.map_mul, h, TimeFunction.timeDerivative_cosMul,
    TimeFunction.timeDerivative_sinMul]
  simp only [smul_eq_mul]
  ring

theorem timeDerivative_complexAmplitudeIm (h : IsForced 0 ω g x) :
    Mechanics.timeDerivative (complexAmplitudeIm ω x) = -(g * TimeFunction.sinMul ω) := by
  have hsq : algebraMap ℝ TimeFunction (ω ^ 2) =
      algebraMap ℝ TimeFunction ω * algebraMap ℝ TimeFunction ω := by
    rw [sq, map_mul]
  rw [isForced_zero_damping_iff, hsq] at h
  rw [complexAmplitudeIm, map_sub, SmoothDerivation.map_algebraMap_mul, SmoothDerivation.map_mul,
    SmoothDerivation.map_mul, h, TimeFunction.timeDerivative_cosMul,
    TimeFunction.timeDerivative_sinMul]
  simp only [smul_eq_mul]
  ring

/-- The real part of `(ẋ + iωx) e^{−iωt}` at time `t`
(Landau–Lifshitz (22.10)). -/
theorem complexAmplitudeRe_eq (h : IsForced 0 ω g x) (t : ℝ) :
    complexAmplitudeRe ω x (fun _ => t) =
      Mechanics.timeDerivative x (fun _ => 0) +
        ∫ s in (0 : ℝ)..t, g (fun _ => s) * Real.cos (ω * s) := by
  have hI : complexAmplitudeRe ω x (fun _ => t) - complexAmplitudeRe ω x (fun _ => 0) =
      ∫ s in (0 : ℝ)..t, g (fun _ => s) * Real.cos (ω * s) := by
    have h0 := TimeFunction.apply_sub_apply_eq_integral (complexAmplitudeRe ω x) 0 t
    rw [h.timeDerivative_complexAmplitudeRe] at h0
    exact h0
  rw [complexAmplitudeRe_apply_zero] at hI
  linarith

/-- The imaginary part of `(ẋ + iωx) e^{−iωt}` at time `t`
(Landau–Lifshitz (22.10)). -/
theorem complexAmplitudeIm_eq (h : IsForced 0 ω g x) (t : ℝ) :
    complexAmplitudeIm ω x (fun _ => t) =
      ω * x (fun _ => 0) - ∫ s in (0 : ℝ)..t, g (fun _ => s) * Real.sin (ω * s) := by
  have hI : complexAmplitudeIm ω x (fun _ => t) - complexAmplitudeIm ω x (fun _ => 0) =
      ∫ s in (0 : ℝ)..t, -(g (fun _ => s) * Real.sin (ω * s)) := by
    have h0 := TimeFunction.apply_sub_apply_eq_integral (complexAmplitudeIm ω x) 0 t
    rw [h.timeDerivative_complexAmplitudeIm] at h0
    exact h0
  rw [complexAmplitudeIm_apply_zero, intervalIntegral.integral_neg] at hI
  linarith

/-- The velocity at time `t`. -/
theorem timeDerivative_apply_eq_integral (h : IsForced 0 ω g x) (t : ℝ) :
    Mechanics.timeDerivative x (fun _ => t) =
      (Mechanics.timeDerivative x (fun _ => 0) +
          ∫ s in (0 : ℝ)..t, g (fun _ => s) * Real.cos (ω * s)) * Real.cos (ω * t) -
        (ω * x (fun _ => 0) - ∫ s in (0 : ℝ)..t, g (fun _ => s) * Real.sin (ω * s)) *
          Real.sin (ω * t) := by
  rw [← h.complexAmplitudeRe_eq t, ← h.complexAmplitudeIm_eq t, complexAmplitudeRe_apply,
    complexAmplitudeIm_apply]
  linear_combination (-(Mechanics.timeDerivative x fun _ => t)) *
    Real.sin_sq_add_cos_sq (ω * t)

/-- Duhamel's formula: the position at time `t` in terms of the initial data
and the integrals of the force. -/
theorem apply_eq_integral (h : IsForced 0 ω g x) (hω : ω ≠ 0) (t : ℝ) :
    x (fun _ => t) =
      x (fun _ => 0) * Real.cos (ω * t) +
        Mechanics.timeDerivative x (fun _ => 0) / ω * Real.sin (ω * t) +
        (∫ s in (0 : ℝ)..t, g (fun _ => s) * Real.sin (ω * (t - s))) / ω := by
  have hre := h.complexAmplitudeRe_eq t
  have him := h.complexAmplitudeIm_eq t
  rw [complexAmplitudeRe_apply] at hre
  rw [complexAmplitudeIm_apply] at him
  have key : ω * x (fun _ => t) =
      ω * x (fun _ => 0) * Real.cos (ω * t) +
        Mechanics.timeDerivative x (fun _ => 0) * Real.sin (ω * t) +
        (Real.sin (ω * t) * (∫ s in (0 : ℝ)..t, g (fun _ => s) * Real.cos (ω * s)) -
          Real.cos (ω * t) * (∫ s in (0 : ℝ)..t, g (fun _ => s) * Real.sin (ω * s))) := by
    linear_combination Real.sin (ω * t) * hre + Real.cos (ω * t) * him -
      (ω * x fun _ => t) * Real.sin_sq_add_cos_sq (ω * t)
  rw [integral_mul_sin_sub]
  refine mul_left_cancel₀ hω ?_
  rw [key]
  field_simp

/-- The energy at time `t` (Landau–Lifshitz (22.11)): `ẋ² + ω² x²` is the
squared modulus of `(ẋ + iωx) e^{−iωt}`. -/
theorem energy_apply (h : IsForced 0 ω g x) (t : ℝ) :
    Mechanics.timeDerivative x (fun _ => t) ^ 2 + ω ^ 2 * x (fun _ => t) ^ 2 =
      (Mechanics.timeDerivative x (fun _ => 0) +
          ∫ s in (0 : ℝ)..t, g (fun _ => s) * Real.cos (ω * s)) ^ 2 +
        (ω * x (fun _ => 0) - ∫ s in (0 : ℝ)..t, g (fun _ => s) * Real.sin (ω * s)) ^ 2 := by
  rw [← h.complexAmplitudeRe_eq t, ← h.complexAmplitudeIm_eq t, complexAmplitudeRe_apply,
    complexAmplitudeIm_apply]
  linear_combination (-(Mechanics.timeDerivative x (fun _ => t) ^ 2 +
    ω ^ 2 * x (fun _ => t) ^ 2)) * Real.sin_sq_add_cos_sq (ω * t)

end IsForced

/-- The energy transferred to an oscillator at rest by a force `F` in the time
`T` (Landau–Lifshitz (22.12), for a finite time):
`E = ((∫ F cos ωt)² + (∫ F sin ωt)²) / 2m`. -/
theorem IsForced.energy_transfer {ω m : ℝ} {F x : TimeFunction} (hm : m ≠ 0)
    (h : IsForced 0 ω (algebraMap ℝ TimeFunction m⁻¹ * F) x) (h0 : x (fun _ => 0) = 0)
    (h1 : Mechanics.timeDerivative x (fun _ => 0) = 0) (T : ℝ) :
    m / 2 * (Mechanics.timeDerivative x (fun _ => T) ^ 2 + ω ^ 2 * x (fun _ => T) ^ 2) =
      ((∫ s in (0 : ℝ)..T, F (fun _ => s) * Real.cos (ω * s)) ^ 2 +
        (∫ s in (0 : ℝ)..T, F (fun _ => s) * Real.sin (ω * s)) ^ 2) / (2 * m) := by
  have hc : (∫ s in (0 : ℝ)..T, (algebraMap ℝ TimeFunction m⁻¹ * F) (fun _ => s) *
      Real.cos (ω * s)) = m⁻¹ * ∫ s in (0 : ℝ)..T, F (fun _ => s) * Real.cos (ω * s) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    change m⁻¹ * F (fun _ => s) * Real.cos (ω * s) = _
    ring
  have hs : (∫ s in (0 : ℝ)..T, (algebraMap ℝ TimeFunction m⁻¹ * F) (fun _ => s) *
      Real.sin (ω * s)) = m⁻¹ * ∫ s in (0 : ℝ)..T, F (fun _ => s) * Real.sin (ω * s) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    change m⁻¹ * F (fun _ => s) * Real.sin (ω * s) = _
    ring
  rw [h.energy_apply T, hc, hs, h0, h1]
  field_simp
  ring

/-! ### Existence -/

/-- The solution at rest at time zero, given by Duhamel's formula. -/
def duhamel (ω : ℝ) (g : TimeFunction) : TimeFunction :=
  algebraMap ℝ TimeFunction ω⁻¹ *
    (TimeFunction.sinMul ω * TimeFunction.primitive (g * TimeFunction.cosMul ω) -
      TimeFunction.cosMul ω * TimeFunction.primitive (g * TimeFunction.sinMul ω))

theorem timeDerivative_duhamel {ω : ℝ} (hω : ω ≠ 0) (g : TimeFunction) :
    timeDerivative (duhamel ω g) =
      TimeFunction.cosMul ω * TimeFunction.primitive (g * TimeFunction.cosMul ω) +
        TimeFunction.sinMul ω * TimeFunction.primitive (g * TimeFunction.sinMul ω) := by
  have hinv : algebraMap ℝ TimeFunction ω⁻¹ * algebraMap ℝ TimeFunction ω = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hω, map_one]
  rw [duhamel, SmoothDerivation.map_algebraMap_mul, map_sub, SmoothDerivation.map_mul,
    SmoothDerivation.map_mul, TimeFunction.timeDerivative_primitive,
    TimeFunction.timeDerivative_primitive, TimeFunction.timeDerivative_sinMul,
    TimeFunction.timeDerivative_cosMul]
  simp only [smul_eq_mul]
  linear_combination (TimeFunction.cosMul ω * TimeFunction.primitive (g * TimeFunction.cosMul ω) +
    TimeFunction.sinMul ω * TimeFunction.primitive (g * TimeFunction.sinMul ω)) * hinv

/-- Duhamel's formula defines a solution. -/
theorem isForced_duhamel {ω : ℝ} (hω : ω ≠ 0) (g : TimeFunction) :
    IsForced 0 ω g (duhamel ω g) := by
  have hinv : algebraMap ℝ TimeFunction ω⁻¹ * algebraMap ℝ TimeFunction ω = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hω, map_one]
  have hsq : algebraMap ℝ TimeFunction (ω ^ 2) =
      algebraMap ℝ TimeFunction ω * algebraMap ℝ TimeFunction ω := by
    rw [sq, map_mul]
  have hCS := TimeFunction.cosMul_mul_cosMul_add_sinMul_mul_sinMul ω
  rw [isForced_zero_damping_iff, timeDerivative_duhamel hω, map_add, SmoothDerivation.map_mul,
    SmoothDerivation.map_mul, TimeFunction.timeDerivative_primitive,
    TimeFunction.timeDerivative_primitive, TimeFunction.timeDerivative_cosMul,
    TimeFunction.timeDerivative_sinMul, hsq, duhamel]
  simp only [smul_eq_mul]
  linear_combination g * hCS + (algebraMap ℝ TimeFunction ω *
    (TimeFunction.sinMul ω * TimeFunction.primitive (g * TimeFunction.cosMul ω) -
      TimeFunction.cosMul ω * TimeFunction.primitive (g * TimeFunction.sinMul ω))) * hinv

theorem duhamel_apply_zero (ω : ℝ) (g : TimeFunction) : duhamel ω g (fun _ => 0) = 0 := by
  simp [duhamel]

theorem timeDerivative_duhamel_apply_zero {ω : ℝ} (hω : ω ≠ 0) (g : TimeFunction) :
    timeDerivative (duhamel ω g) (fun _ => 0) = 0 := by
  rw [timeDerivative_duhamel hω]
  simp

/-- The solution at rest at time zero is `(1/ω) ∫₀ᵗ g(s) sin ω(t − s) ds`. -/
theorem duhamel_apply (ω : ℝ) (g : TimeFunction) (t : ℝ) :
    duhamel ω g (fun _ => t) =
      (∫ s in (0 : ℝ)..t, g (fun _ => s) * Real.sin (ω * (t - s))) / ω := by
  rw [integral_mul_sin_sub, div_eq_inv_mul]
  simp only [duhamel, TimeFunction.mul_apply, TimeFunction.sub_apply,
    TimeFunction.algebraMap_apply, TimeFunction.sinMul_apply, TimeFunction.cosMul_apply,
    TimeFunction.primitive_apply]

/-- For every smooth force and all initial data there is a solution. By
`IsForced.eq_of_initial` it is unique. -/
theorem exists_isForced {ω : ℝ} (hω : ω ≠ 0) (g : TimeFunction) (x₀ v₀ : ℝ) :
    ∃ x : TimeFunction, IsForced 0 ω g x ∧ x (fun _ => 0) = x₀ ∧
      timeDerivative x (fun _ => 0) = v₀ := by
  refine ⟨duhamel ω g + (algebraMap ℝ TimeFunction x₀ * TimeFunction.cosMul ω +
    algebraMap ℝ TimeFunction (v₀ / ω) * TimeFunction.sinMul ω),
    (isForced_duhamel hω g).add_isDamped (isDamped_zero_iff.mpr (IsHarmonic.combination ω x₀ _)),
    ?_, ?_⟩
  · simp [duhamel_apply_zero]
  · rw [map_add, map_add, SmoothDerivation.map_algebraMap_mul, SmoothDerivation.map_algebraMap_mul,
      TimeFunction.timeDerivative_cosMul, TimeFunction.timeDerivative_sinMul]
    simp only [smul_eq_mul, TimeFunction.add_apply, TimeFunction.mul_apply,
      TimeFunction.neg_apply, TimeFunction.algebraMap_apply, TimeFunction.cosMul_apply,
      TimeFunction.sinMul_apply, timeDerivative_duhamel_apply_zero hω, mul_zero, Real.sin_zero,
      Real.cos_zero, neg_zero, mul_one, zero_add]
    field_simp

/-! ### The periodic force -/

/-- Away from resonance the forced oscillation is `F/(ω² − Ω²) cos Ωt`
(Landau–Lifshitz (22.3)). -/
theorem isForced_cos_of_sq_ne {ω Ω : ℝ} (hne : ω ^ 2 ≠ Ω ^ 2) (F : ℝ) :
    IsForced 0 ω (algebraMap ℝ TimeFunction F * TimeFunction.cosMul Ω)
      (algebraMap ℝ TimeFunction (F / (ω ^ 2 - Ω ^ 2)) * TimeFunction.cosMul Ω) := by
  have hc : F / (ω ^ 2 - Ω ^ 2) * (ω ^ 2 - Ω ^ 2) = F :=
    div_mul_cancel₀ F (sub_ne_zero.mpr hne)
  rw [isForced_zero_damping_iff, SmoothDerivation.map_algebraMap_mul,
    TimeFunction.timeDerivative_cosMul, smul_eq_mul, SmoothDerivation.map_algebraMap_mul, map_neg,
    SmoothDerivation.map_algebraMap_mul, TimeFunction.timeDerivative_sinMul, smul_eq_mul,
    smul_eq_mul]
  refine TimeFunction.ext_apply_const fun t => ?_
  simp only [TimeFunction.sub_apply, TimeFunction.mul_apply, TimeFunction.neg_apply,
    TimeFunction.algebraMap_apply, TimeFunction.cosMul_apply]
  linear_combination Real.cos (Ω * t) * hc

/-- Without friction and away from resonance, the steady state of
`Oscillations/Forced` is this forced oscillation. -/
theorem steadyState_zero_damping {ω Ω : ℝ} (hne : ω ^ 2 ≠ Ω ^ 2) (F : ℝ) :
    steadyState 0 ω F Ω =
      algebraMap ℝ TimeFunction (F / (ω ^ 2 - Ω ^ 2)) * TimeFunction.cosMul Ω := by
  have hd : ω ^ 2 - Ω ^ 2 ≠ 0 := sub_ne_zero.mpr hne
  have hD : responseDenominator 0 ω Ω = (ω ^ 2 - Ω ^ 2) * (ω ^ 2 - Ω ^ 2) := by
    unfold responseDenominator
    ring
  have h1 : steadyCos 0 ω F Ω = F / (ω ^ 2 - Ω ^ 2) := by
    rw [steadyCos, hD, mul_div_mul_right _ _ hd]
  have h2 : steadySin 0 ω F Ω = 0 := by
    unfold steadySin
    simp
  rw [steadyState, h1, h2, map_zero, zero_mul, add_zero]

/-- The general solution away from resonance (Landau–Lifshitz (22.4)):
`x = a cos (ωt + α) + F/(ω² − Ω²) cos Ωt`. -/
theorem IsForced.apply_eq_of_sq_ne {ω Ω F : ℝ} {x : TimeFunction}
    (hx : IsForced 0 ω (algebraMap ℝ TimeFunction F * TimeFunction.cosMul Ω) x)
    (hne : ω ^ 2 ≠ Ω ^ 2) (hω : ω ≠ 0) (t : ℝ) :
    x (fun _ => t) =
      amplitude
          ((x - algebraMap ℝ TimeFunction (F / (ω ^ 2 - Ω ^ 2)) * TimeFunction.cosMul Ω)
            fun _ => 0)
          (Mechanics.timeDerivative
            (x - algebraMap ℝ TimeFunction (F / (ω ^ 2 - Ω ^ 2)) * TimeFunction.cosMul Ω)
            (fun _ => 0) / ω) *
        Real.cos (ω * t + phase
          ((x - algebraMap ℝ TimeFunction (F / (ω ^ 2 - Ω ^ 2)) * TimeFunction.cosMul Ω)
            fun _ => 0)
          (Mechanics.timeDerivative
            (x - algebraMap ℝ TimeFunction (F / (ω ^ 2 - Ω ^ 2)) * TimeFunction.cosMul Ω)
            (fun _ => 0) / ω)) +
        F / (ω ^ 2 - Ω ^ 2) * Real.cos (Ω * t) := by
  have hz : IsHarmonic ω
      (x - algebraMap ℝ TimeFunction (F / (ω ^ 2 - Ω ^ 2)) * TimeFunction.cosMul Ω) :=
    isDamped_zero_iff.mp (hx.sub (isForced_cos_of_sq_ne hne F))
  rw [← hz.apply_eq_amplitude_mul_cos hω t]
  simp only [TimeFunction.sub_apply, TimeFunction.mul_apply, TimeFunction.algebraMap_apply,
    TimeFunction.cosMul_apply, sub_add_cancel]

theorem timeDerivative_time_mul_sinMul (ω : ℝ) :
    timeDerivative (TimeFunction.time * TimeFunction.sinMul ω) =
      TimeFunction.time * (algebraMap ℝ TimeFunction ω * TimeFunction.cosMul ω) +
        TimeFunction.sinMul ω := by
  rw [SmoothDerivation.map_mul, TimeFunction.timeDerivative_sinMul,
    TimeFunction.timeDerivative_time, smul_eq_mul, smul_eq_mul, mul_one]

/-- At resonance the forced oscillation is `(F/2ω) t sin ωt`
(Landau–Lifshitz (22.5)). -/
theorem isForced_resonance {ω : ℝ} (hω : ω ≠ 0) (F : ℝ) :
    IsForced 0 ω (algebraMap ℝ TimeFunction F * TimeFunction.cosMul ω)
      (algebraMap ℝ TimeFunction (F / (2 * ω)) *
        (TimeFunction.time * TimeFunction.sinMul ω)) := by
  have hsq : algebraMap ℝ TimeFunction (ω ^ 2) =
      algebraMap ℝ TimeFunction ω * algebraMap ℝ TimeFunction ω := by
    rw [sq, map_mul]
  have hcF : algebraMap ℝ TimeFunction (F / (2 * ω)) * algebraMap ℝ TimeFunction ω +
      algebraMap ℝ TimeFunction (F / (2 * ω)) * algebraMap ℝ TimeFunction ω =
      algebraMap ℝ TimeFunction F := by
    rw [← map_mul, ← map_add]
    congr 1
    field_simp
    ring
  have h2 : timeDerivative (TimeFunction.time *
      (algebraMap ℝ TimeFunction ω * TimeFunction.cosMul ω) + TimeFunction.sinMul ω) =
      TimeFunction.time * (algebraMap ℝ TimeFunction ω *
        -(algebraMap ℝ TimeFunction ω * TimeFunction.sinMul ω)) +
        algebraMap ℝ TimeFunction ω * TimeFunction.cosMul ω +
        algebraMap ℝ TimeFunction ω * TimeFunction.cosMul ω := by
    rw [map_add, SmoothDerivation.map_mul, SmoothDerivation.map_algebraMap_mul,
      TimeFunction.timeDerivative_cosMul, TimeFunction.timeDerivative_sinMul,
      TimeFunction.timeDerivative_time, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_one]
  rw [isForced_zero_damping_iff, SmoothDerivation.map_algebraMap_mul,
    timeDerivative_time_mul_sinMul, smul_eq_mul, SmoothDerivation.map_algebraMap_mul, h2,
    smul_eq_mul, hsq]
  linear_combination TimeFunction.cosMul ω * hcF

/-- At resonance, the motion from rest is `(F/2ω) t sin ωt`: its amplitude
increases linearly with the time. -/
theorem IsForced.eq_resonance_of_rest {ω F : ℝ} {x : TimeFunction}
    (hx : IsForced 0 ω (algebraMap ℝ TimeFunction F * TimeFunction.cosMul ω) x) (hω : ω ≠ 0)
    (h0 : x (fun _ => 0) = 0) (h1 : Mechanics.timeDerivative x (fun _ => 0) = 0) :
    x = algebraMap ℝ TimeFunction (F / (2 * ω)) *
      (TimeFunction.time * TimeFunction.sinMul ω) := by
  refine hx.eq_of_initial (isForced_resonance hω F) ?_ ?_
  · rw [h0]
    simp
  · rw [h1, SmoothDerivation.map_algebraMap_mul, timeDerivative_time_mul_sinMul]
    simp

/-- At resonance no solution is bounded. -/
theorem IsForced.exists_abs_gt_of_resonance {ω F : ℝ} {x : TimeFunction}
    (hx : IsForced 0 ω (algebraMap ℝ TimeFunction F * TimeFunction.cosMul ω) x) (hω : 0 < ω)
    (hF : F ≠ 0) (B : ℝ) : ∃ t : ℝ, B < |x fun _ => t| := by
  have hz : IsHarmonic ω (x - algebraMap ℝ TimeFunction (F / (2 * ω)) *
      (TimeFunction.time * TimeFunction.sinMul ω)) :=
    isDamped_zero_iff.mp (hx.sub (isForced_resonance hω.ne' F))
  obtain ⟨a, ha⟩ : ∃ a : ℝ, ∀ t : ℝ, |(x - algebraMap ℝ TimeFunction (F / (2 * ω)) *
      (TimeFunction.time * TimeFunction.sinMul ω)) fun _ => t| ≤ a := by
    refine ⟨amplitude
      ((x - algebraMap ℝ TimeFunction (F / (2 * ω)) *
        (TimeFunction.time * TimeFunction.sinMul ω)) fun _ => 0)
      (Mechanics.timeDerivative (x - algebraMap ℝ TimeFunction (F / (2 * ω)) *
        (TimeFunction.time * TimeFunction.sinMul ω)) (fun _ => 0) / ω), fun t => ?_⟩
    rw [hz.apply_eq_amplitude_mul_cos hω.ne' t, abs_mul, abs_of_nonneg (amplitude_nonneg _ _)]
    exact mul_le_of_le_one_right (amplitude_nonneg _ _) (Real.abs_cos_le_one _)
  have hc : 0 < |F / (2 * ω)| := abs_pos.mpr (div_ne_zero hF (by positivity))
  obtain ⟨n, hn⟩ := exists_nat_gt ((B + a) / |F / (2 * ω)| * ω / (2 * Real.pi))
  have hπ := Real.pi_pos
  have hn' : (B + a) / |F / (2 * ω)| * ω < n * (2 * Real.pi) :=
    (div_lt_iff₀ (by positivity)).mp hn
  have ht : (B + a) / |F / (2 * ω)| < (Real.pi / 2 + n * (2 * Real.pi)) / ω :=
    (lt_div_iff₀ hω).mpr (by linarith)
  have htpos : 0 < (Real.pi / 2 + n * (2 * Real.pi)) / ω := by positivity
  have harg : ω * ((Real.pi / 2 + n * (2 * Real.pi)) / ω) = Real.pi / 2 + n * (2 * Real.pi) := by
    field_simp
  have hp : (algebraMap ℝ TimeFunction (F / (2 * ω)) *
      (TimeFunction.time * TimeFunction.sinMul ω))
      (fun _ => (Real.pi / 2 + n * (2 * Real.pi)) / ω) =
      F / (2 * ω) * ((Real.pi / 2 + n * (2 * Real.pi)) / ω) := by
    simp only [TimeFunction.mul_apply, TimeFunction.algebraMap_apply, TimeFunction.time_apply,
      TimeFunction.sinMul_apply, harg, Real.sin_add_nat_mul_two_pi, Real.sin_pi_div_two, mul_one]
  have hlarge : B + a < |F / (2 * ω)| * ((Real.pi / 2 + n * (2 * Real.pi)) / ω) :=
    (div_lt_iff₀' hc).mp ht
  have hsub := abs_sub (x fun _ => (Real.pi / 2 + n * (2 * Real.pi)) / ω)
    ((x - algebraMap ℝ TimeFunction (F / (2 * ω)) *
      (TimeFunction.time * TimeFunction.sinMul ω))
      fun _ => (Real.pi / 2 + n * (2 * Real.pi)) / ω)
  rw [TimeFunction.sub_apply, sub_sub_cancel, hp, abs_mul, abs_of_pos htpos] at hsub
  have hzn := ha ((Real.pi / 2 + n * (2 * Real.pi)) / ω)
  rw [TimeFunction.sub_apply, hp] at hzn
  refine ⟨(Real.pi / 2 + n * (2 * Real.pi)) / ω, ?_⟩
  linarith

end ProjectAInos.Mechanics
