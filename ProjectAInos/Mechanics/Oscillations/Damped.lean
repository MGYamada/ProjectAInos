/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Oscillations.Harmonic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Damped oscillations

The equation `ẍ + 2γ ẋ + ω₀² x = 0` for a smooth function of time
(Landau–Lifshitz §25, where the damping coefficient `γ` is written `λ`).

The substitution `y = e^{γt} x` removes the first-order term:
`ÿ = −(ω₀² − γ²) y`. The three cases of the book follow.

* `ω₀² − γ² = ω²` with `ω ≠ 0`: `y` is a free oscillation, and
  `x = a e^{−γt} cos (ωt + α)`.
* `ω₀² = γ²`: `ÿ = 0`, and `x = (c₁ + c₂ t) e^{−γt}`.
* `γ² − ω₀² = β²` with `β ≠ 0`: `x = c₁ e^{−(γ−β)t} + c₂ e^{−(γ+β)t}`.

In every case the solution is determined by its position and velocity at time
zero, for all real `γ` and `ω₀`. For `γ ≥ 0` the energy `ẋ² + ω₀² x²` does not
increase.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics

open SmoothAlgebra SmoothRing

namespace TimeFunction

/-- The function `e^{at}` of time. -/
def expMul (a : ℝ) : TimeFunction :=
  SmoothOperation.ofContDiff (fun x => Real.exp (a * x 0))
    (Real.contDiff_exp.comp (contDiff_const.mul (contDiff_apply ℝ (fun _ => ℝ) 0)))

@[simp] theorem expMul_apply (a : ℝ) (x : Fin 1 → ℝ) : expMul a x = Real.exp (a * x 0) := rfl

theorem timeDerivative_expMul (a : ℝ) :
    timeDerivative (expMul a) = algebraMap ℝ TimeFunction a * expMul a := by
  refine ext_apply_const fun t => ?_
  rw [timeDerivative_apply]
  have h : (fun s : ℝ => expMul a (fun _ => s)) = fun s => Real.exp (a * s) := rfl
  have hd : HasDerivAt (fun s : ℝ => Real.exp (a * s)) (Real.exp (a * t) * (a * 1)) t :=
    (Real.hasDerivAt_exp (a * t)).comp t ((hasDerivAt_id t).const_mul a)
  rw [h, hd.deriv]
  change _ = a * Real.exp (a * t)
  ring

theorem expMul_mul_expMul_neg (a : ℝ) : expMul a * expMul (-a) = 1 := by
  refine ext_apply_const fun t => ?_
  change Real.exp (a * t) * Real.exp (-a * t) = 1
  rw [← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero]

/-- The time, as a function of time. -/
def time : TimeFunction := SmoothOperation.proj 0

@[simp] theorem time_apply (x : Fin 1 → ℝ) : time x = x 0 := rfl

theorem timeDerivative_time : timeDerivative time = 1 := by
  rw [timeDerivative, time, SmoothDerivation.partialDerivation_proj]
  simp

/-- A smooth function of time with zero second derivative is
`y(0) + ẏ(0) t`. -/
theorem eq_add_mul_time {y : TimeFunction} (h : timeDerivative (timeDerivative y) = 0) :
    y = algebraMap ℝ TimeFunction (y fun _ => 0) +
      algebraMap ℝ TimeFunction (timeDerivative y fun _ => 0) * time := by
  have h1 := eq_algebraMap_of_timeDerivative_eq_zero h
  have h2 : timeDerivative
      (y - algebraMap ℝ TimeFunction (timeDerivative y fun _ => 0) * time) = 0 := by
    rw [map_sub, SmoothDerivation.map_algebraMap_mul, timeDerivative_time, smul_eq_mul, mul_one,
      ← h1, sub_self]
  have h3 := eq_algebraMap_of_timeDerivative_eq_zero h2
  have h4 : (y - algebraMap ℝ TimeFunction (timeDerivative y fun _ => 0) * time) (fun _ => 0) =
      y fun _ => 0 := by
    simp
  rw [h4] at h3
  linear_combination h3

/-- A smooth function of time whose derivative is nowhere positive does not
increase. -/
theorem antitone_of_timeDerivative_nonpos {f : TimeFunction}
    (h : ∀ t : ℝ, timeDerivative f (fun _ => t) ≤ 0) : Antitone fun t : ℝ => f fun _ => t := by
  refine antitone_of_deriv_nonpos (f.contDiff_apply_const.differentiable (by simp)) fun t => ?_
  rw [← timeDerivative_apply]
  exact h t

end TimeFunction

/-! ### The equation `ẍ + 2γ ẋ + ω₀² x = 0` -/

/-- `x` is a damped oscillation: `ẍ = −2γ ẋ − ω₀² x` (Landau–Lifshitz (25.1)). -/
def IsDamped (γ ω₀ : ℝ) (x : TimeFunction) : Prop :=
  timeDerivative (timeDerivative x) =
    -(algebraMap ℝ TimeFunction (2 * γ) * timeDerivative x) -
      algebraMap ℝ TimeFunction (ω₀ ^ 2) * x

/-- Without damping the equation is that of a free oscillation. -/
theorem isDamped_zero_iff {ω₀ : ℝ} {x : TimeFunction} : IsDamped 0 ω₀ x ↔ IsHarmonic ω₀ x := by
  unfold IsDamped IsHarmonic
  rw [mul_zero, map_zero, zero_mul, neg_zero, zero_sub]

theorem timeDerivative_expMul_mul (γ : ℝ) (x : TimeFunction) :
    timeDerivative (TimeFunction.expMul γ * x) =
      TimeFunction.expMul γ * (timeDerivative x + algebraMap ℝ TimeFunction γ * x) := by
  rw [SmoothDerivation.map_mul, TimeFunction.timeDerivative_expMul]
  simp only [smul_eq_mul]
  ring

theorem timeDerivative_timeDerivative_expMul_mul (γ : ℝ) (x : TimeFunction) :
    timeDerivative (timeDerivative (TimeFunction.expMul γ * x)) =
      TimeFunction.expMul γ * (timeDerivative (timeDerivative x) +
        algebraMap ℝ TimeFunction (2 * γ) * timeDerivative x +
        algebraMap ℝ TimeFunction (γ ^ 2) * x) := by
  have h2 : algebraMap ℝ TimeFunction (2 * γ) = 2 * algebraMap ℝ TimeFunction γ := by
    rw [map_mul, map_ofNat]
  rw [timeDerivative_expMul_mul, timeDerivative_expMul_mul, map_add,
    SmoothDerivation.map_algebraMap_mul, smul_eq_mul, h2, map_pow]
  ring

/-- The substitution `y = e^{γt} x` removes the first-order term:
`ÿ = −(ω₀² − γ²) y`. -/
theorem isDamped_iff_expMul_mul (γ ω₀ : ℝ) (x : TimeFunction) :
    IsDamped γ ω₀ x ↔
      timeDerivative (timeDerivative (TimeFunction.expMul γ * x)) =
        -(algebraMap ℝ TimeFunction (ω₀ ^ 2 - γ ^ 2) * (TimeFunction.expMul γ * x)) := by
  have hE := TimeFunction.expMul_mul_expMul_neg γ
  rw [timeDerivative_timeDerivative_expMul_mul, map_sub]
  unfold IsDamped
  constructor
  · intro h
    linear_combination TimeFunction.expMul γ * h
  · intro h
    linear_combination TimeFunction.expMul (-γ) * h -
      (timeDerivative (timeDerivative x) +
        algebraMap ℝ TimeFunction (2 * γ) * timeDerivative x +
        algebraMap ℝ TimeFunction (ω₀ ^ 2) * x) * hE

/-- For `ω₀² − γ² = ω²` the function `e^{γt} x` is a free oscillation of
frequency `ω`. -/
theorem isDamped_iff_isHarmonic {γ ω₀ ω : ℝ} (hω : ω ^ 2 = ω₀ ^ 2 - γ ^ 2) (x : TimeFunction) :
    IsDamped γ ω₀ x ↔ IsHarmonic ω (TimeFunction.expMul γ * x) := by
  rw [isDamped_iff_expMul_mul, ← hω]
  rfl

namespace IsDamped

variable {γ ω₀ : ℝ} {x y : TimeFunction}

/-- The sum of two solutions is a solution. -/
theorem add (hx : IsDamped γ ω₀ x) (hy : IsDamped γ ω₀ y) : IsDamped γ ω₀ (x + y) := by
  unfold IsDamped at hx hy ⊢
  rw [map_add, map_add, hx, hy]
  ring

/-- A constant multiple of a solution is a solution. -/
theorem const_mul (c : ℝ) (hx : IsDamped γ ω₀ x) :
    IsDamped γ ω₀ (algebraMap ℝ TimeFunction c * x) := by
  unfold IsDamped at hx ⊢
  rw [SmoothDerivation.map_algebraMap_mul, smul_eq_mul, SmoothDerivation.map_algebraMap_mul,
    smul_eq_mul, hx]
  ring

/-- The value of `e^{γt} x` at time `t`. -/
theorem expMul_mul_apply (γ : ℝ) (x : TimeFunction) (t : ℝ) :
    (TimeFunction.expMul γ * x) (fun _ => t) = Real.exp (γ * t) * x fun _ => t := rfl

/-- The velocity of `e^{γt} x` at time zero is `ẋ(0) + γ x(0)`. -/
theorem timeDerivative_expMul_mul_apply_zero (γ : ℝ) (x : TimeFunction) :
    timeDerivative (TimeFunction.expMul γ * x) (fun _ => 0) =
      timeDerivative x (fun _ => 0) + γ * x fun _ => 0 := by
  rw [timeDerivative_expMul_mul]
  simp

/-- Recover `x(t)` from `e^{γt} x(t)`. -/
theorem apply_eq_exp_neg_mul (γ : ℝ) (x : TimeFunction) (t : ℝ) :
    x (fun _ => t) = Real.exp (-γ * t) * (TimeFunction.expMul γ * x) fun _ => t := by
  rw [expMul_mul_apply, ← mul_assoc, ← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero,
    one_mul]

/-- Weak damping (Landau–Lifshitz (25.4)): for `ω₀² − γ² = ω²` with `ω ≠ 0`,
`x = e^{−γt} (x(0) cos ωt + ((ẋ(0) + γ x(0))/ω) sin ωt)`. -/
theorem apply_eq_underdamped {ω : ℝ} (h : IsDamped γ ω₀ x) (hω : ω ^ 2 = ω₀ ^ 2 - γ ^ 2)
    (hω0 : ω ≠ 0) (t : ℝ) :
    x (fun _ => t) = Real.exp (-γ * t) *
      (x (fun _ => 0) * Real.cos (ω * t) +
        (timeDerivative x (fun _ => 0) + γ * x fun _ => 0) / ω * Real.sin (ω * t)) := by
  have hy := (isDamped_iff_isHarmonic hω x).mp h
  rw [apply_eq_exp_neg_mul γ x t, hy.apply_eq hω0 t, timeDerivative_expMul_mul_apply_zero,
    expMul_mul_apply]
  simp

/-- Weak damping in amplitude and phase: `x = a e^{−γt} cos (ωt + α)`. -/
theorem apply_eq_amplitude_mul_exp_mul_cos {ω : ℝ} (h : IsDamped γ ω₀ x)
    (hω : ω ^ 2 = ω₀ ^ 2 - γ ^ 2) (hω0 : ω ≠ 0) (t : ℝ) :
    x (fun _ => t) =
      amplitude (x fun _ => 0) ((timeDerivative x (fun _ => 0) + γ * x fun _ => 0) / ω) *
        Real.exp (-γ * t) *
        Real.cos (ω * t +
          phase (x fun _ => 0) ((timeDerivative x (fun _ => 0) + γ * x fun _ => 0) / ω)) := by
  rw [mul_right_comm, amplitude_mul_cos_add, h.apply_eq_underdamped hω hω0 t]
  ring

/-- The envelope of a weakly damped oscillation: `|x(t)| ≤ a e^{−γt}`. -/
theorem abs_apply_le {ω : ℝ} (h : IsDamped γ ω₀ x) (hω : ω ^ 2 = ω₀ ^ 2 - γ ^ 2)
    (hω0 : ω ≠ 0) (t : ℝ) :
    |x fun _ => t| ≤
      amplitude (x fun _ => 0) ((timeDerivative x (fun _ => 0) + γ * x fun _ => 0) / ω) *
        Real.exp (-γ * t) := by
  rw [h.apply_eq_amplitude_mul_exp_mul_cos hω hω0 t, abs_mul,
    abs_of_nonneg (mul_nonneg (amplitude_nonneg _ _) (Real.exp_pos _).le)]
  exact mul_le_of_le_one_right (mul_nonneg (amplitude_nonneg _ _) (Real.exp_pos _).le)
    (Real.abs_cos_le_one _)

/-- Critical damping (Landau–Lifshitz (25.7)): for `ω₀² = γ²`,
`x = (x(0) + (ẋ(0) + γ x(0)) t) e^{−γt}`. -/
theorem apply_eq_critical (h : IsDamped γ ω₀ x) (hc : ω₀ ^ 2 = γ ^ 2) (t : ℝ) :
    x (fun _ => t) = Real.exp (-γ * t) *
      (x (fun _ => 0) + (timeDerivative x (fun _ => 0) + γ * x fun _ => 0) * t) := by
  have hy := (isDamped_iff_expMul_mul γ ω₀ x).mp h
  rw [hc, sub_self, map_zero, zero_mul, neg_zero] at hy
  have ht : (TimeFunction.expMul γ * x) (fun _ => t) =
      (TimeFunction.expMul γ * x) (fun _ => 0) +
        timeDerivative (TimeFunction.expMul γ * x) (fun _ => 0) * t :=
    congrArg (fun f : TimeFunction => f fun _ => t) (TimeFunction.eq_add_mul_time hy)
  rw [apply_eq_exp_neg_mul γ x t, ht, timeDerivative_expMul_mul_apply_zero, expMul_mul_apply]
  simp

/-- A smooth function with `ÿ = β² y` and `β ≠ 0` is a combination of
`e^{βt}` and `e^{−βt}`. -/
theorem _root_.ProjectAInos.Mechanics.TimeFunction.apply_eq_of_timeDerivative_eq_sq_mul
    {β : ℝ} {y : TimeFunction}
    (h : timeDerivative (timeDerivative y) = algebraMap ℝ TimeFunction (β ^ 2) * y)
    (hβ : β ≠ 0) (t : ℝ) :
    y (fun _ => t) =
      ((timeDerivative y (fun _ => 0) + β * y fun _ => 0) * Real.exp (β * t) -
        (timeDerivative y (fun _ => 0) - β * y fun _ => 0) * Real.exp (-β * t)) / (2 * β) := by
  have hsq : algebraMap ℝ TimeFunction (β ^ 2) =
      algebraMap ℝ TimeFunction β * algebraMap ℝ TimeFunction β := by
    rw [sq, map_mul]
  rw [hsq] at h
  have h1 : timeDerivative ((timeDerivative y - algebraMap ℝ TimeFunction β * y) *
      TimeFunction.expMul β) = 0 := by
    rw [SmoothDerivation.map_mul, map_sub, SmoothDerivation.map_algebraMap_mul, h,
      TimeFunction.timeDerivative_expMul]
    simp only [smul_eq_mul]
    ring
  have h2 : timeDerivative ((timeDerivative y + algebraMap ℝ TimeFunction β * y) *
      TimeFunction.expMul (-β)) = 0 := by
    rw [SmoothDerivation.map_mul, map_add, SmoothDerivation.map_algebraMap_mul, h,
      TimeFunction.timeDerivative_expMul, map_neg]
    simp only [smul_eq_mul]
    ring
  have e1 := TimeFunction.eq_of_timeDerivative_eq_zero h1 (fun _ => t) fun _ => 0
  have e2 := TimeFunction.eq_of_timeDerivative_eq_zero h2 (fun _ => t) fun _ => 0
  simp only [TimeFunction.mul_apply, TimeFunction.sub_apply, TimeFunction.add_apply,
    TimeFunction.algebraMap_apply, TimeFunction.expMul_apply, mul_zero, Real.exp_zero, mul_one]
    at e1 e2
  have hPN : Real.exp (β * t) * Real.exp (-β * t) = 1 := by
    rw [← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero]
  rw [eq_div_iff (mul_ne_zero two_ne_zero hβ), ← e1, ← e2]
  linear_combination (-(2 * β * y fun _ => t)) * hPN

/-- Strong damping (Landau–Lifshitz (25.6)): for `γ² − ω₀² = β²` with `β ≠ 0`,
`x = c₁ e^{−(γ−β)t} + c₂ e^{−(γ+β)t}`. -/
theorem apply_eq_overdamped {β : ℝ} (h : IsDamped γ ω₀ x) (hβ : β ^ 2 = γ ^ 2 - ω₀ ^ 2)
    (hβ0 : β ≠ 0) (t : ℝ) :
    x (fun _ => t) =
      ((γ + β) * x (fun _ => 0) + timeDerivative x fun _ => 0) / (2 * β) *
          Real.exp (-(γ - β) * t) -
        ((γ - β) * x (fun _ => 0) + timeDerivative x fun _ => 0) / (2 * β) *
          Real.exp (-(γ + β) * t) := by
  have hy := (isDamped_iff_expMul_mul γ ω₀ x).mp h
  have hneg : ω₀ ^ 2 - γ ^ 2 = -β ^ 2 := by rw [hβ]; ring
  rw [hneg, map_neg, neg_mul, neg_neg] at hy
  have e1 : Real.exp (-(γ - β) * t) = Real.exp (-γ * t) * Real.exp (β * t) := by
    rw [← Real.exp_add]
    ring_nf
  have e2 : Real.exp (-(γ + β) * t) = Real.exp (-γ * t) * Real.exp (-β * t) := by
    rw [← Real.exp_add]
    ring_nf
  rw [apply_eq_exp_neg_mul γ x t, TimeFunction.apply_eq_of_timeDerivative_eq_sq_mul hy hβ0 t,
    timeDerivative_expMul_mul_apply_zero, expMul_mul_apply, e1, e2]
  simp only [mul_zero, Real.exp_zero, one_mul]
  field_simp
  ring

/-- A solution is determined by its position and velocity at time zero, for
all real `γ` and `ω₀`. -/
theorem eq_of_initial (hx : IsDamped γ ω₀ x) (hy : IsDamped γ ω₀ y)
    (h0 : x (fun _ => 0) = y fun _ => 0)
    (h1 : timeDerivative x (fun _ => 0) = timeDerivative y fun _ => 0) : x = y := by
  refine TimeFunction.ext_apply_const fun t => ?_
  rcases lt_trichotomy (ω₀ ^ 2) (γ ^ 2) with hlt | heq | hgt
  · have hβ : Real.sqrt (γ ^ 2 - ω₀ ^ 2) ^ 2 = γ ^ 2 - ω₀ ^ 2 :=
      Real.sq_sqrt (sub_pos.mpr hlt).le
    have hβ0 : Real.sqrt (γ ^ 2 - ω₀ ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (sub_pos.mpr hlt)).ne'
    rw [hx.apply_eq_overdamped hβ hβ0, hy.apply_eq_overdamped hβ hβ0, h0, h1]
  · rw [hx.apply_eq_critical heq, hy.apply_eq_critical heq, h0, h1]
  · have hω : Real.sqrt (ω₀ ^ 2 - γ ^ 2) ^ 2 = ω₀ ^ 2 - γ ^ 2 :=
      Real.sq_sqrt (sub_pos.mpr hgt).le
    have hω0 : Real.sqrt (ω₀ ^ 2 - γ ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (sub_pos.mpr hgt)).ne'
    rw [hx.apply_eq_underdamped hω hω0, hy.apply_eq_underdamped hω hω0, h0, h1]

/-- The rate of loss of energy (Landau–Lifshitz (25.13) for one co-ordinate):
`d/dt (ẋ² + ω₀² x²) = −4γ ẋ²`. -/
theorem timeDerivative_energy (h : IsDamped γ ω₀ x) :
    timeDerivative (timeDerivative x * timeDerivative x +
        algebraMap ℝ TimeFunction (ω₀ ^ 2) * (x * x)) =
      -(algebraMap ℝ TimeFunction (4 * γ) * (timeDerivative x * timeDerivative x)) := by
  have h4 : algebraMap ℝ TimeFunction (4 * γ) = 2 * algebraMap ℝ TimeFunction (2 * γ) := by
    rw [← map_ofNat (algebraMap ℝ TimeFunction) 2, ← map_mul]
    congr 1
    ring
  unfold IsDamped at h
  rw [map_add, SmoothDerivation.map_mul, SmoothDerivation.map_algebraMap_mul,
    SmoothDerivation.map_mul, h, h4]
  simp only [smul_eq_mul]
  ring

/-- With non-negative damping the energy `ẋ² + ω₀² x²` does not increase. -/
theorem energy_antitone (h : IsDamped γ ω₀ x) (hγ : 0 ≤ γ) :
    Antitone fun t : ℝ =>
      timeDerivative x (fun _ => t) ^ 2 + ω₀ ^ 2 * x (fun _ => t) ^ 2 := by
  have ha := TimeFunction.antitone_of_timeDerivative_nonpos
    (f := timeDerivative x * timeDerivative x + algebraMap ℝ TimeFunction (ω₀ ^ 2) * (x * x))
    fun t => by
      rw [h.timeDerivative_energy]
      change -(4 * γ * (timeDerivative x (fun _ => t) * timeDerivative x fun _ => t)) ≤ 0
      exact neg_nonpos.mpr (mul_nonneg (mul_nonneg (by norm_num) hγ) (mul_self_nonneg _))
  intro s t hst
  have hst' := ha hst
  simp only [TimeFunction.add_apply, TimeFunction.mul_apply, TimeFunction.algebraMap_apply]
    at hst'
  have e (a b : ℝ) : a ^ 2 + ω₀ ^ 2 * b ^ 2 = a * a + ω₀ ^ 2 * (b * b) := by ring
  beta_reduce
  rw [e, e]
  exact hst'

end IsDamped

/-! ### Existence -/

/-- `e^{rt}` is a solution for a root `r` of `r² + 2γ r + ω₀² = 0`. -/
theorem isDamped_expMul {γ ω₀ r : ℝ} (hr : r ^ 2 + 2 * γ * r + ω₀ ^ 2 = 0) :
    IsDamped γ ω₀ (TimeFunction.expMul r) := by
  have hr' : algebraMap ℝ TimeFunction r * algebraMap ℝ TimeFunction r +
      algebraMap ℝ TimeFunction (2 * γ) * algebraMap ℝ TimeFunction r +
      algebraMap ℝ TimeFunction (ω₀ ^ 2) = 0 := by
    rw [← map_mul, ← map_mul, ← map_add, ← map_add, ← sq, hr, map_zero]
  unfold IsDamped
  rw [TimeFunction.timeDerivative_expMul, SmoothDerivation.map_algebraMap_mul,
    TimeFunction.timeDerivative_expMul, smul_eq_mul]
  linear_combination TimeFunction.expMul r * hr'

/-- For critical damping `t e^{−γt}` is a solution. -/
theorem isDamped_time_mul_expMul {γ ω₀ : ℝ} (hc : ω₀ ^ 2 = γ ^ 2) :
    IsDamped γ ω₀ (TimeFunction.time * TimeFunction.expMul (-γ)) := by
  rw [isDamped_iff_expMul_mul, hc, sub_self, map_zero, zero_mul, neg_zero]
  have h : TimeFunction.expMul γ * (TimeFunction.time * TimeFunction.expMul (-γ)) =
      TimeFunction.time := by
    linear_combination TimeFunction.time * TimeFunction.expMul_mul_expMul_neg γ
  rw [h, TimeFunction.timeDerivative_time, SmoothDerivation.map_one]

/-- For weak damping, `e^{−γt} y` is a solution for every free oscillation `y`
of frequency `ω`, `ω² = ω₀² − γ²`. -/
theorem IsHarmonic.isDamped_expMul_neg_mul {γ ω₀ ω : ℝ} {y : TimeFunction}
    (hy : IsHarmonic ω y) (hω : ω ^ 2 = ω₀ ^ 2 - γ ^ 2) :
    IsDamped γ ω₀ (TimeFunction.expMul (-γ) * y) := by
  rw [isDamped_iff_isHarmonic hω]
  have h : TimeFunction.expMul γ * (TimeFunction.expMul (-γ) * y) = y := by
    linear_combination y * TimeFunction.expMul_mul_expMul_neg γ
  rw [h]
  exact hy

end ProjectAInos.Mechanics
