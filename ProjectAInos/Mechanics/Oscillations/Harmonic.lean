/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.TimeFunction
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Free oscillations in one dimension

The equation `ẍ + ω² x = 0` for a smooth function of time (Landau–Lifshitz §21).
For `ω ≠ 0` every solution is `x(0) cos ωt + (ẋ(0)/ω) sin ωt`: the two
combinations `x cos ωt − (ẋ/ω) sin ωt` and `x sin ωt + (ẋ/ω) cos ωt` have zero
derivative. The solution is `a cos (ωt + α)` with the amplitude
`a = √(x(0)² + (ẋ(0)/ω)²)`, its energy is `½ m ω² a²`, and its period `2π/ω`
does not depend on the amplitude.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics

open SmoothAlgebra SmoothRing

namespace TimeFunction

/-- The function `cos ωt` of time. -/
def cosMul (ω : ℝ) : TimeFunction :=
  SmoothOperation.ofContDiff (fun x => Real.cos (ω * x 0))
    (Real.contDiff_cos.comp (contDiff_const.mul (contDiff_apply ℝ (fun _ => ℝ) 0)))

/-- The function `sin ωt` of time. -/
def sinMul (ω : ℝ) : TimeFunction :=
  SmoothOperation.ofContDiff (fun x => Real.sin (ω * x 0))
    (Real.contDiff_sin.comp (contDiff_const.mul (contDiff_apply ℝ (fun _ => ℝ) 0)))

@[simp] theorem cosMul_apply (ω : ℝ) (x : Fin 1 → ℝ) : cosMul ω x = Real.cos (ω * x 0) := rfl

@[simp] theorem sinMul_apply (ω : ℝ) (x : Fin 1 → ℝ) : sinMul ω x = Real.sin (ω * x 0) := rfl

@[simp] theorem algebraMap_apply (r : ℝ) (x : Fin 1 → ℝ) :
    algebraMap ℝ TimeFunction r x = r := rfl

@[simp] theorem mul_apply (f g : TimeFunction) (x : Fin 1 → ℝ) : (f * g) x = f x * g x := rfl

@[simp] theorem add_apply (f g : TimeFunction) (x : Fin 1 → ℝ) : (f + g) x = f x + g x := rfl

@[simp] theorem sub_apply (f g : TimeFunction) (x : Fin 1 → ℝ) : (f - g) x = f x - g x := rfl

@[simp] theorem neg_apply (f : TimeFunction) (x : Fin 1 → ℝ) : (-f) x = -f x := rfl

theorem timeDerivative_cosMul (ω : ℝ) :
    timeDerivative (cosMul ω) = -(algebraMap ℝ TimeFunction ω * sinMul ω) := by
  refine ext_apply_const fun t => ?_
  rw [timeDerivative_apply]
  have h : (fun s : ℝ => cosMul ω (fun _ => s)) = fun s => Real.cos (ω * s) := rfl
  have hd : HasDerivAt (fun s : ℝ => Real.cos (ω * s)) (-Real.sin (ω * t) * (ω * 1)) t :=
    (Real.hasDerivAt_cos (ω * t)).comp t ((hasDerivAt_id t).const_mul ω)
  rw [h, hd.deriv]
  change _ = -(ω * Real.sin (ω * t))
  ring

theorem timeDerivative_sinMul (ω : ℝ) :
    timeDerivative (sinMul ω) = algebraMap ℝ TimeFunction ω * cosMul ω := by
  refine ext_apply_const fun t => ?_
  rw [timeDerivative_apply]
  have h : (fun s : ℝ => sinMul ω (fun _ => s)) = fun s => Real.sin (ω * s) := rfl
  have hd : HasDerivAt (fun s : ℝ => Real.sin (ω * s)) (Real.cos (ω * t) * (ω * 1)) t :=
    (Real.hasDerivAt_sin (ω * t)).comp t ((hasDerivAt_id t).const_mul ω)
  rw [h, hd.deriv]
  change _ = ω * Real.cos (ω * t)
  ring

theorem cosMul_mul_cosMul_add_sinMul_mul_sinMul (ω : ℝ) :
    cosMul ω * cosMul ω + sinMul ω * sinMul ω = 1 := by
  refine ext_apply_const fun t => ?_
  change Real.cos (ω * t) * Real.cos (ω * t) + Real.sin (ω * t) * Real.sin (ω * t) = 1
  rw [← sq, ← sq]
  exact Real.cos_sq_add_sin_sq (ω * t)

/-- A smooth function of time with zero derivative is the constant function
with its value at time zero. -/
theorem eq_algebraMap_of_timeDerivative_eq_zero {f : TimeFunction}
    (h : timeDerivative f = 0) : f = algebraMap ℝ TimeFunction (f fun _ => 0) :=
  ext_apply_const fun t => eq_of_timeDerivative_eq_zero h (fun _ => t) fun _ => 0

end TimeFunction

/-! ### Amplitude and phase -/

/-- The amplitude `√(c₁² + c₂²)` of `c₁ cos θ + c₂ sin θ`. -/
def amplitude (c₁ c₂ : ℝ) : ℝ := Real.sqrt (c₁ ^ 2 + c₂ ^ 2)

/-- The phase `α` of `c₁ cos θ + c₂ sin θ = a cos (θ + α)`: the argument of
`c₁ − i c₂`. -/
def phase (c₁ c₂ : ℝ) : ℝ := Complex.arg ⟨c₁, -c₂⟩

theorem amplitude_nonneg (c₁ c₂ : ℝ) : 0 ≤ amplitude c₁ c₂ := Real.sqrt_nonneg _

theorem amplitude_sq (c₁ c₂ : ℝ) : amplitude c₁ c₂ ^ 2 = c₁ ^ 2 + c₂ ^ 2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg c₁) (sq_nonneg c₂))

/-- `c₁ cos θ + c₂ sin θ = a cos (θ + α)` (Landau–Lifshitz (21.8), (21.10)). -/
theorem amplitude_mul_cos_add (c₁ c₂ θ : ℝ) :
    amplitude c₁ c₂ * Real.cos (θ + phase c₁ c₂) = c₁ * Real.cos θ + c₂ * Real.sin θ := by
  have hn : ‖(⟨c₁, -c₂⟩ : ℂ)‖ = amplitude c₁ c₂ := by
    rw [Complex.norm_def, Complex.normSq_apply, amplitude]
    congr 1
    ring
  have hc : amplitude c₁ c₂ * Real.cos (phase c₁ c₂) = c₁ := by
    rw [← hn]
    exact Complex.norm_mul_cos_arg _
  have hs : amplitude c₁ c₂ * Real.sin (phase c₁ c₂) = -c₂ := by
    rw [← hn]
    exact Complex.norm_mul_sin_arg _
  rw [Real.cos_add]
  linear_combination Real.cos θ * hc - Real.sin θ * hs

/-! ### The equation `ẍ + ω² x = 0` -/

/-- `x` is a free oscillation of angular frequency `ω`: `ẍ = −ω² x`
(Landau–Lifshitz (21.5)). -/
def IsHarmonic (ω : ℝ) (x : TimeFunction) : Prop :=
  timeDerivative (timeDerivative x) = -(algebraMap ℝ TimeFunction (ω ^ 2) * x)

theorem isHarmonic_cosMul (ω : ℝ) : IsHarmonic ω (TimeFunction.cosMul ω) := by
  unfold IsHarmonic
  rw [TimeFunction.timeDerivative_cosMul, map_neg, SmoothDerivation.map_algebraMap_mul,
    TimeFunction.timeDerivative_sinMul, smul_eq_mul, ← mul_assoc, ← map_mul, ← sq]

theorem isHarmonic_sinMul (ω : ℝ) : IsHarmonic ω (TimeFunction.sinMul ω) := by
  unfold IsHarmonic
  rw [TimeFunction.timeDerivative_sinMul, SmoothDerivation.map_algebraMap_mul,
    TimeFunction.timeDerivative_cosMul, smul_eq_mul, mul_neg, ← mul_assoc, ← map_mul, ← sq]

namespace IsHarmonic

variable {ω : ℝ} {x y : TimeFunction}

/-- The sum of two free oscillations of the same frequency is one. -/
theorem add (hx : IsHarmonic ω x) (hy : IsHarmonic ω y) : IsHarmonic ω (x + y) := by
  unfold IsHarmonic at hx hy ⊢
  rw [map_add, map_add, hx, hy]
  ring

/-- A constant multiple of a free oscillation is one. -/
theorem const_mul (c : ℝ) (hx : IsHarmonic ω x) :
    IsHarmonic ω (algebraMap ℝ TimeFunction c * x) := by
  unfold IsHarmonic at hx ⊢
  rw [SmoothDerivation.map_algebraMap_mul, smul_eq_mul, SmoothDerivation.map_algebraMap_mul,
    smul_eq_mul, hx]
  ring

/-- The velocity of a free oscillation is a free oscillation. -/
theorem timeDerivative (hx : IsHarmonic ω x) : IsHarmonic ω (timeDerivative x) := by
  unfold IsHarmonic at hx ⊢
  rw [hx, map_neg, SmoothDerivation.map_algebraMap_mul, smul_eq_mul]

/-- `c₁ cos ωt + c₂ sin ωt` is a free oscillation (Landau–Lifshitz (21.7)). -/
theorem combination (ω c₁ c₂ : ℝ) :
    IsHarmonic ω (algebraMap ℝ TimeFunction c₁ * TimeFunction.cosMul ω +
      algebraMap ℝ TimeFunction c₂ * TimeFunction.sinMul ω) :=
  ((isHarmonic_cosMul ω).const_mul c₁).add ((isHarmonic_sinMul ω).const_mul c₂)

/-- The general solution (Landau–Lifshitz (21.7)): for `ω ≠ 0` a free
oscillation is `x(0) cos ωt + (ẋ(0)/ω) sin ωt`. -/
theorem eq_cos_add_sin (h : IsHarmonic ω x) (hω : ω ≠ 0) :
    x = algebraMap ℝ TimeFunction (x fun _ => 0) * TimeFunction.cosMul ω +
      algebraMap ℝ TimeFunction (Mechanics.timeDerivative x (fun _ => 0) / ω) *
        TimeFunction.sinMul ω := by
  have hba : algebraMap ℝ TimeFunction ω⁻¹ * algebraMap ℝ TimeFunction ω = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hω, map_one]
  have hv : Mechanics.timeDerivative (Mechanics.timeDerivative x) =
      -(algebraMap ℝ TimeFunction ω * algebraMap ℝ TimeFunction ω * x) := by
    rw [← map_mul, ← sq]
    exact h
  have hCS := TimeFunction.cosMul_mul_cosMul_add_sinMul_mul_sinMul ω
  have h1 : Mechanics.timeDerivative (x * TimeFunction.cosMul ω -
      algebraMap ℝ TimeFunction ω⁻¹ * (Mechanics.timeDerivative x * TimeFunction.sinMul ω)) =
      0 := by
    rw [map_sub, SmoothDerivation.map_mul, SmoothDerivation.map_algebraMap_mul,
      SmoothDerivation.map_mul, hv, TimeFunction.timeDerivative_cosMul,
      TimeFunction.timeDerivative_sinMul]
    simp only [smul_eq_mul]
    linear_combination (algebraMap ℝ TimeFunction ω * TimeFunction.sinMul ω * x -
      Mechanics.timeDerivative x * TimeFunction.cosMul ω) * hba
  have h2 : Mechanics.timeDerivative (x * TimeFunction.sinMul ω +
      algebraMap ℝ TimeFunction ω⁻¹ * (Mechanics.timeDerivative x * TimeFunction.cosMul ω)) =
      0 := by
    rw [map_add, SmoothDerivation.map_mul, SmoothDerivation.map_algebraMap_mul,
      SmoothDerivation.map_mul, hv, TimeFunction.timeDerivative_cosMul,
      TimeFunction.timeDerivative_sinMul]
    simp only [smul_eq_mul]
    linear_combination (-(algebraMap ℝ TimeFunction ω * TimeFunction.cosMul ω * x) -
      Mechanics.timeDerivative x * TimeFunction.sinMul ω) * hba
  have e1 := TimeFunction.eq_algebraMap_of_timeDerivative_eq_zero h1
  have e2 := TimeFunction.eq_algebraMap_of_timeDerivative_eq_zero h2
  have v1 : (x * TimeFunction.cosMul ω - algebraMap ℝ TimeFunction ω⁻¹ *
      (Mechanics.timeDerivative x * TimeFunction.sinMul ω)) (fun _ => 0) = x fun _ => 0 := by
    change x (fun _ => 0) * Real.cos (ω * 0) -
      ω⁻¹ * (Mechanics.timeDerivative x (fun _ => 0) * Real.sin (ω * 0)) = _
    simp
  have v2 : (x * TimeFunction.sinMul ω + algebraMap ℝ TimeFunction ω⁻¹ *
      (Mechanics.timeDerivative x * TimeFunction.cosMul ω)) (fun _ => 0) =
      Mechanics.timeDerivative x (fun _ => 0) / ω := by
    change x (fun _ => 0) * Real.sin (ω * 0) +
      ω⁻¹ * (Mechanics.timeDerivative x (fun _ => 0) * Real.cos (ω * 0)) = _
    simp [div_eq_inv_mul]
  rw [v1] at e1
  rw [v2] at e2
  rw [← e1, ← e2]
  linear_combination (-x) * hCS

/-- A function is a free oscillation of frequency `ω ≠ 0` exactly when it is a
combination of `cos ωt` and `sin ωt`. -/
theorem _root_.ProjectAInos.Mechanics.isHarmonic_iff (hω : ω ≠ 0) :
    IsHarmonic ω x ↔ ∃ c₁ c₂ : ℝ, x = algebraMap ℝ TimeFunction c₁ * TimeFunction.cosMul ω +
      algebraMap ℝ TimeFunction c₂ * TimeFunction.sinMul ω :=
  ⟨fun h => ⟨_, _, h.eq_cos_add_sin hω⟩, fun ⟨c₁, c₂, h⟩ => h ▸ combination ω c₁ c₂⟩

/-- The position at time `t`. -/
theorem apply_eq (h : IsHarmonic ω x) (hω : ω ≠ 0) (t : ℝ) :
    x (fun _ => t) = x (fun _ => 0) * Real.cos (ω * t) +
      Mechanics.timeDerivative x (fun _ => 0) / ω * Real.sin (ω * t) :=
  congrArg (fun f : TimeFunction => f fun _ => t) (h.eq_cos_add_sin hω)

/-- The velocity at time `t`. -/
theorem timeDerivative_apply_eq (h : IsHarmonic ω x) (hω : ω ≠ 0) (t : ℝ) :
    Mechanics.timeDerivative x (fun _ => t) =
      Mechanics.timeDerivative x (fun _ => 0) * Real.cos (ω * t) -
        ω * x (fun _ => 0) * Real.sin (ω * t) := by
  have h0 : Mechanics.timeDerivative (Mechanics.timeDerivative x) (fun _ => 0) =
      -(ω ^ 2 * x fun _ => 0) :=
    congrArg (fun f : TimeFunction => f fun _ => 0) h
  rw [h.timeDerivative.apply_eq hω t, h0]
  field_simp
  ring

/-- A free oscillation is determined by its position and velocity at time zero. -/
theorem eq_of_initial (hx : IsHarmonic ω x) (hy : IsHarmonic ω y) (hω : ω ≠ 0)
    (h0 : x (fun _ => 0) = y fun _ => 0)
    (h1 : Mechanics.timeDerivative x (fun _ => 0) = Mechanics.timeDerivative y fun _ => 0) :
    x = y := by
  rw [hx.eq_cos_add_sin hω, hy.eq_cos_add_sin hω, h0, h1]

/-- Amplitude and phase (Landau–Lifshitz (21.8)): a free oscillation is
`a cos (ωt + α)`. -/
theorem apply_eq_amplitude_mul_cos (h : IsHarmonic ω x) (hω : ω ≠ 0) (t : ℝ) :
    x (fun _ => t) =
      amplitude (x fun _ => 0) (Mechanics.timeDerivative x (fun _ => 0) / ω) *
        Real.cos (ω * t +
          phase (x fun _ => 0) (Mechanics.timeDerivative x (fun _ => 0) / ω)) := by
  rw [amplitude_mul_cos_add, h.apply_eq hω]

/-- The period `2π/ω` does not depend on the amplitude. -/
theorem apply_add_period (h : IsHarmonic ω x) (hω : ω ≠ 0) (t : ℝ) :
    x (fun _ => t + 2 * Real.pi / ω) = x fun _ => t := by
  have hp : ω * (t + 2 * Real.pi / ω) = ω * t + 2 * Real.pi := by
    field_simp
  rw [h.apply_eq hω, h.apply_eq hω t, hp, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- `ẋ² + ω² x²` takes the same value at all times. -/
theorem energy_eq (h : IsHarmonic ω x) (s t : Fin 1 → ℝ) :
    (Mechanics.timeDerivative x * Mechanics.timeDerivative x +
        algebraMap ℝ TimeFunction (ω ^ 2) * (x * x)) s =
      (Mechanics.timeDerivative x * Mechanics.timeDerivative x +
        algebraMap ℝ TimeFunction (ω ^ 2) * (x * x)) t := by
  refine TimeFunction.eq_of_timeDerivative_eq_zero ?_ s t
  unfold IsHarmonic at h
  rw [map_add, SmoothDerivation.map_mul, SmoothDerivation.map_algebraMap_mul,
    SmoothDerivation.map_mul, h]
  simp only [smul_eq_mul]
  ring

/-- The energy of a free oscillation (Landau–Lifshitz (21.11)):
`½ m (ẋ² + ω² x²) = ½ m ω² a²`. -/
theorem energy_eq_amplitude (h : IsHarmonic ω x) (hω : ω ≠ 0) (m t : ℝ) :
    m / 2 * (Mechanics.timeDerivative x (fun _ => t) ^ 2 + ω ^ 2 * x (fun _ => t) ^ 2) =
      m / 2 * ω ^ 2 *
        amplitude (x fun _ => 0) (Mechanics.timeDerivative x (fun _ => 0) / ω) ^ 2 := by
  have he : Mechanics.timeDerivative x (fun _ => t) * Mechanics.timeDerivative x (fun _ => t) +
      ω ^ 2 * (x (fun _ => t) * x fun _ => t) =
      Mechanics.timeDerivative x (fun _ => 0) * Mechanics.timeDerivative x (fun _ => 0) +
        ω ^ 2 * (x (fun _ => 0) * x fun _ => 0) :=
    h.energy_eq (fun _ => t) fun _ => 0
  rw [amplitude_sq, div_pow]
  field_simp
  linear_combination m * he

end IsHarmonic

end ProjectAInos.Mechanics
