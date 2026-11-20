/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.ThreePlusOne
public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

/-!
# The retarded time of a point charge

A point charge moves on a smooth world line `t ↦ r(t)` in space with a speed bounded by a
constant `v₀ < 1` (`SubluminalWorldline`; units with `c = 1`). The **retarded time** `τ` of an
event `(t, x)` is the time at which the light that reaches `x` at the time `t` left the charge,
`t − τ = ‖x − r(τ)‖` (Landau–Lifshitz, *The Classical Theory of Fields*, §63, (63.1)).

* `SubluminalWorldline`: a smooth path `r : ℝ → Space 3` with `‖ṙ(t)‖ ≤ v₀ < 1`. Instances:
  the uniform motion `r₀ + t v` with `‖v‖ < 1` (`SubluminalWorldline.uniform`, at rest:
  `SubluminalWorldline.rest`) and the uniform
  circular motion of the radius `ρ` and the angular frequency `Ω` with `|ρΩ| < 1`
  (`SubluminalWorldline.circular`, of the speed `|ρΩ|`).
* `SubluminalWorldline.existsUnique_retardedTime`: for every event `(t, x)` there is exactly one
  `τ` with `t − τ = ‖x − r(τ)‖`, since `s ↦ t − s − ‖x − r(s)‖` is continuous and strictly
  decreasing with the slope at most `−(1 − v₀)`. `SubluminalWorldline.retardedTime` is this
  time, characterized by `retardedTime_eq_iff`; `retardedTime_le`: `τ ≤ t`, and
  `retardedTime_lt_iff`: `τ < t` exactly off the world line `x ≠ r(t)`.
  `retardedTime_add_norm`: the retarded time of `(τ + ‖y‖, r(τ) + y)` is `τ`, so that
  `(τ, y) ↦ (τ + ‖y‖, r(τ) + y)` parametrizes space-time by the retarded time and the
  separation (`lightConeEquiv`, `retardedSeparation_add_norm`, `retardedDenominator_add_norm`).
* The retarded quantities: the separation `R = x − r(τ)` (`retardedSeparation`, of the norm
  `t − τ`), the direction `n = R/‖R‖`, the velocity `v = ṙ(τ)`, the acceleration `v̇ = r̈(τ)`, and
  `R − R·v` (`retardedDenominator`), which lies between `(1 − v₀) R` and `(1 + v₀) R`, so that
  it is positive off the world line.
* `contDiffAt_retardedTime`: off the world line the retarded time is a smooth function of
  `(t, x)`, by the implicit function theorem; `hasFDerivAt_retardedTime`: its derivative is
  `dτ = (R dt − R · dx)/(R − R·v)`, that is `∂τ/∂t = R/(R − R·v)` (`fderiv_retardedTime_time`)
  and `∇τ = −n/(1 − n·v)` (`fderiv_retardedTime_space`, `fderiv_retardedTime_space_direction`).
* On space-time: `offWorldline` is the open set of the events off the world line;
  `contDiffOn_retardedTime_spacetime`, `hasFDerivAt_retardedTime_spacetime`, and
  `partialAt_retardedTime_zero`, `partialAt_retardedTime_succ` give `∂₀τ = R/(R − R·v)` and
  `∂ᵢτ = −Rᵢ/(R − R·v)`.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.Minkowski SpecialRelativity

/-- A **subluminal world line**: the smooth path `t ↦ r(t)` of a point charge in space whose
speed is bounded by a constant `v₀ < 1`, `‖ṙ(t)‖ ≤ v₀` for all `t`. -/
structure SubluminalWorldline where
  /-- The position `r(t)` of the charge at the time `t`. -/
  r : ℝ → Space 3
  /-- The path is smooth. -/
  contDiff_r : ContDiff ℝ ∞ r
  /-- The bound `v₀` of the speed. -/
  v₀ : ℝ
  /-- The bound of the speed is not negative. -/
  v₀_nonneg : 0 ≤ v₀
  /-- The bound of the speed is below the speed of light. -/
  v₀_lt_one : v₀ < 1
  /-- The speed is at most `v₀` at all times. -/
  norm_deriv_le : ∀ t, ‖deriv r t‖ ≤ v₀

namespace SubluminalWorldline

variable (w : SubluminalWorldline)

/-! ### The world line -/

/-- The path is differentiable. -/
theorem differentiable_r : Differentiable ℝ w.r := w.contDiff_r.differentiable (by simp)

/-- The velocity `ṙ` is smooth. -/
theorem contDiff_deriv : ContDiff ℝ ∞ (deriv w.r) := (contDiff_infty_iff_deriv.mp w.contDiff_r).2

/-- The acceleration `r̈` is smooth. -/
theorem contDiff_deriv_deriv : ContDiff ℝ ∞ (deriv (deriv w.r)) :=
  (contDiff_infty_iff_deriv.mp w.contDiff_deriv).2

/-- The distance travelled between two times is at most `v₀` times the elapsed time. -/
theorem norm_sub_le (s₁ s₂ : ℝ) : ‖w.r s₂ - w.r s₁‖ ≤ w.v₀ * |s₂ - s₁| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (s := univ)
    (fun s _ => w.differentiable_r s) (fun s _ => w.norm_deriv_le s) convex_univ (mem_univ s₁)
    (mem_univ s₂)
  rwa [Real.norm_eq_abs] at h

/-- The **uniform motion** `r(t) = r₀ + t v` with a speed `‖v‖ < 1`. -/
def uniform (r₀ v : Space 3) (hv : ‖v‖ < 1) : SubluminalWorldline where
  r t := r₀ + t • v
  contDiff_r := contDiff_const.add (contDiff_id.smul contDiff_const)
  v₀ := ‖v‖
  v₀_nonneg := norm_nonneg v
  v₀_lt_one := hv
  norm_deriv_le t := by
    rw [(by simpa using ((hasDerivAt_id t).smul_const v).const_add r₀ :
      HasDerivAt (fun t : ℝ => r₀ + t • v) v t).deriv]

/-- The velocity of the uniform motion is `v`. -/
theorem deriv_uniform (r₀ v : Space 3) (hv : ‖v‖ < 1) (t : ℝ) :
    deriv (uniform r₀ v hv).r t = v :=
  (by simpa using ((hasDerivAt_id t).smul_const v).const_add r₀ :
    HasDerivAt (fun t : ℝ => r₀ + t • v) v t).deriv

/-- The charge at rest at the point `r₀`, the uniform motion with no velocity. -/
def rest (r₀ : Space 3) : SubluminalWorldline := uniform r₀ 0 (by simp)

/-- The position of the uniform circular motion of the radius `ρ` and the angular frequency
`Ω` in the plane of the first two axes. -/
def circularPath (ρ Ω : ℝ) (t : ℝ) : Space 3 :=
  (ρ * Real.cos (Ω * t)) • EuclideanSpace.single 0 1 +
    (ρ * Real.sin (Ω * t)) • EuclideanSpace.single 1 1

/-- The velocity of the uniform circular motion. -/
theorem hasDerivAt_circularPath (ρ Ω t : ℝ) :
    HasDerivAt (circularPath ρ Ω)
      ((-(ρ * Ω) * Real.sin (Ω * t)) • EuclideanSpace.single 0 1 +
        (ρ * Ω * Real.cos (Ω * t)) • EuclideanSpace.single 1 1) t := by
  have hc : HasDerivAt (fun s => ρ * Real.cos (Ω * s)) (-(ρ * Ω) * Real.sin (Ω * t)) t := by
    convert ((hasDerivAt_id' t).const_mul Ω).cos.const_mul ρ using 1
    ring
  have hs : HasDerivAt (fun s => ρ * Real.sin (Ω * s)) (ρ * Ω * Real.cos (Ω * t)) t := by
    convert ((hasDerivAt_id' t).const_mul Ω).sin.const_mul ρ using 1
    ring
  exact (hc.smul_const _).add (hs.smul_const _)

/-- The speed of the uniform circular motion is `|ρΩ|`. -/
theorem norm_deriv_circularPath (ρ Ω t : ℝ) : ‖deriv (circularPath ρ Ω) t‖ = |ρ * Ω| := by
  rw [(hasDerivAt_circularPath ρ Ω t).deriv]
  have h : ‖(-(ρ * Ω) * Real.sin (Ω * t)) • (EuclideanSpace.single 0 1 : Space 3) +
      (ρ * Ω * Real.cos (Ω * t)) • EuclideanSpace.single 1 1‖ ^ 2 = |ρ * Ω| ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, sq_abs]
    simp
    linear_combination (ρ * Ω) ^ 2 * Real.sin_sq_add_cos_sq (Ω * t)
  exact (pow_left_inj₀ (norm_nonneg _) (abs_nonneg _) two_ne_zero).mp h

/-- The **uniform circular motion** `r(t) = ρ (cos Ωt, sin Ωt, 0)` with the speed `|ρΩ| < 1`. -/
def circular (ρ Ω : ℝ) (h : |ρ * Ω| < 1) : SubluminalWorldline where
  r := circularPath ρ Ω
  contDiff_r := by
    unfold circularPath
    fun_prop
  v₀ := |ρ * Ω|
  v₀_nonneg := abs_nonneg _
  v₀_lt_one := h
  norm_deriv_le t := (norm_deriv_circularPath ρ Ω t).le

/-! ### The retarded time -/

/-- **The retarded time exists and is unique**: for every event `(t, x)` there is exactly one
time `τ` with `t − τ = ‖x − r(τ)‖` (Landau–Lifshitz (63.1)). -/
theorem existsUnique_retardedTime (t : ℝ) (x : Space 3) : ∃! τ : ℝ, t - τ = ‖x - w.r τ‖ := by
  set g : ℝ → ℝ := fun s => t - s - ‖x - w.r s‖ with hg
  have hcont : Continuous g :=
    (continuous_const.sub continuous_id).sub (continuous_const.sub w.contDiff_r.continuous).norm
  have htri (s₁ s₂ : ℝ) : ‖x - w.r s₁‖ ≤ ‖x - w.r s₂‖ + ‖w.r s₂ - w.r s₁‖ := by
    calc ‖x - w.r s₁‖ = ‖(x - w.r s₂) + (w.r s₂ - w.r s₁)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  have hanti : StrictAnti g := by
    intro s₁ s₂ h12
    have h := w.norm_sub_le s₁ s₂
    rw [abs_of_pos (sub_pos.mpr h12)] at h
    have hv := mul_lt_mul_of_pos_right w.v₀_lt_one (sub_pos.mpr h12)
    simp only [g]
    linarith [htri s₁ s₂]
  have hv₀ : 0 < 1 - w.v₀ := by linarith [w.v₀_lt_one]
  set a := t - ‖x - w.r t‖ / (1 - w.v₀) with ha_def
  have ha : a ≤ t := by
    have : 0 ≤ ‖x - w.r t‖ / (1 - w.v₀) := div_nonneg (norm_nonneg _) hv₀.le
    linarith
  have h1 : (1 - w.v₀) * (t - a) = ‖x - w.r t‖ := by
    rw [ha_def]
    field_simp
    ring
  have hga : 0 ≤ g a := by
    have h := w.norm_sub_le a t
    rw [abs_of_nonneg (sub_nonneg.mpr ha)] at h
    simp only [g]
    nlinarith [htri a t]
  have hgt : g t ≤ 0 := by simp [g]
  obtain ⟨τ, -, hτ⟩ := intermediate_value_Icc' ha hcont.continuousOn ⟨hgt, hga⟩
  refine ⟨τ, by simp only [g] at hτ; linarith, fun s hs => hanti.injective ?_⟩
  simp only [g] at hτ ⊢
  linarith

/-- The **retarded time** `τ` of the event `(t, x)`: the unique time with
`t − τ = ‖x − r(τ)‖`. -/
def retardedTime (t : ℝ) (x : Space 3) : ℝ := (w.existsUnique_retardedTime t x).exists.choose

/-- The retarded time solves `t − τ = ‖x − r(τ)‖`. -/
theorem sub_retardedTime (t : ℝ) (x : Space 3) :
    t - w.retardedTime t x = ‖x - w.r (w.retardedTime t x)‖ :=
  (w.existsUnique_retardedTime t x).exists.choose_spec

/-- The retarded time is the only solution of `t − τ = ‖x − r(τ)‖`. -/
theorem retardedTime_eq_iff {t s : ℝ} {x : Space 3} :
    w.retardedTime t x = s ↔ t - s = ‖x - w.r s‖ :=
  ⟨fun h => h ▸ w.sub_retardedTime t x,
    fun h => (w.existsUnique_retardedTime t x).unique (w.sub_retardedTime t x) h⟩

/-- The retarded time is not later than the time of the event. -/
theorem retardedTime_le (t : ℝ) (x : Space 3) : w.retardedTime t x ≤ t := by
  have h := w.sub_retardedTime t x
  linarith [norm_nonneg (x - w.r (w.retardedTime t x))]

/-- The retarded time is earlier than the time of the event exactly off the world line. -/
theorem retardedTime_lt_iff {t : ℝ} {x : Space 3} : w.retardedTime t x < t ↔ x ≠ w.r t := by
  constructor
  · rintro hlt rfl
    have h := w.sub_retardedTime t (w.r t)
    have hn := w.norm_sub_le (w.retardedTime t (w.r t)) t
    rw [abs_of_pos (sub_pos.mpr hlt), ← h] at hn
    have := mul_lt_mul_of_pos_right w.v₀_lt_one (sub_pos.mpr hlt)
    linarith
  · intro hx
    refine lt_of_le_of_ne (w.retardedTime_le t x) fun heq => hx ?_
    have h := w.sub_retardedTime t x
    rw [heq, sub_self] at h
    exact (sub_eq_zero.mp (norm_eq_zero.mp h.symm))

/-- On the world line the retarded time is the time of the event. -/
theorem retardedTime_self (t : ℝ) : w.retardedTime t (w.r t) = t :=
  w.retardedTime_eq_iff.mpr (by simp)

/-- The retarded time of the event `(τ + ‖y‖, r(τ) + y)` on the future light cone of the point
`r(τ)` of the world line is `τ`. -/
theorem retardedTime_add_norm (τ : ℝ) (y : Space 3) :
    w.retardedTime (τ + ‖y‖) (w.r τ + y) = τ :=
  w.retardedTime_eq_iff.mpr (by simp)

/-! ### The retarded quantities -/

/-- The separation `R = x − r(τ)` of the event from the position of the charge at the retarded
time. -/
def retardedSeparation (t : ℝ) (x : Space 3) : Space 3 := x - w.r (w.retardedTime t x)

/-- The velocity `v = ṙ(τ)` of the charge at the retarded time. -/
def retardedVelocity (t : ℝ) (x : Space 3) : Space 3 := deriv w.r (w.retardedTime t x)

/-- The acceleration `v̇ = r̈(τ)` of the charge at the retarded time. -/
def retardedAcceleration (t : ℝ) (x : Space 3) : Space 3 := deriv (deriv w.r) (w.retardedTime t x)

/-- The unit vector `n = R/R` from the retarded position of the charge to the event. -/
def retardedDirection (t : ℝ) (x : Space 3) : Space 3 :=
  ‖w.retardedSeparation t x‖⁻¹ • w.retardedSeparation t x

/-- The denominator `R − R·v` of the potentials of Liénard and Wiechert, with `R = ‖R‖`. -/
def retardedDenominator (t : ℝ) (x : Space 3) : ℝ :=
  ‖w.retardedSeparation t x‖ - inner ℝ (w.retardedSeparation t x) (w.retardedVelocity t x)

/-- The distance from the retarded position is the time of flight of the light, `R = t − τ`. -/
theorem norm_retardedSeparation (t : ℝ) (x : Space 3) :
    ‖w.retardedSeparation t x‖ = t - w.retardedTime t x :=
  (w.sub_retardedTime t x).symm

/-- Off the world line the separation from the retarded position does not vanish. -/
theorem retardedSeparation_ne_zero {t : ℝ} {x : Space 3} (h : x ≠ w.r t) :
    w.retardedSeparation t x ≠ 0 := by
  rw [← norm_pos_iff, norm_retardedSeparation, sub_pos]
  exact w.retardedTime_lt_iff.mpr h

/-- The retarded velocity is bounded by `v₀`. -/
theorem norm_retardedVelocity_le (t : ℝ) (x : Space 3) : ‖w.retardedVelocity t x‖ ≤ w.v₀ :=
  w.norm_deriv_le _

/-- The direction `n` is a unit vector off the world line. -/
theorem norm_retardedDirection {t : ℝ} {x : Space 3} (h : x ≠ w.r t) :
    ‖w.retardedDirection t x‖ = 1 := by
  have hR := norm_ne_zero_iff.mpr (w.retardedSeparation_ne_zero h)
  rw [retardedDirection, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hR]

/-- The lower bound `(1 − v₀) R ≤ R − R·v`. -/
theorem mul_norm_le_retardedDenominator (t : ℝ) (x : Space 3) :
    (1 - w.v₀) * ‖w.retardedSeparation t x‖ ≤ w.retardedDenominator t x := by
  have h1 := real_inner_le_norm (w.retardedSeparation t x) (w.retardedVelocity t x)
  have h2 := mul_le_mul_of_nonneg_left (w.norm_retardedVelocity_le t x)
    (norm_nonneg (w.retardedSeparation t x))
  rw [retardedDenominator]
  nlinarith

/-- The upper bound `R − R·v ≤ (1 + v₀) R`. -/
theorem retardedDenominator_le_mul_norm (t : ℝ) (x : Space 3) :
    w.retardedDenominator t x ≤ (1 + w.v₀) * ‖w.retardedSeparation t x‖ := by
  have h1 := neg_abs_le (inner ℝ (w.retardedSeparation t x) (w.retardedVelocity t x))
  have h1' := abs_real_inner_le_norm (w.retardedSeparation t x) (w.retardedVelocity t x)
  have h2 := mul_le_mul_of_nonneg_left (w.norm_retardedVelocity_le t x)
    (norm_nonneg (w.retardedSeparation t x))
  rw [retardedDenominator]
  nlinarith

/-- Off the world line `R − R·v > 0`. -/
theorem retardedDenominator_pos {t : ℝ} {x : Space 3} (h : x ≠ w.r t) :
    0 < w.retardedDenominator t x := by
  have hR := norm_pos_iff.mpr (w.retardedSeparation_ne_zero h)
  have hv : 0 < 1 - w.v₀ := by linarith [w.v₀_lt_one]
  exact lt_of_lt_of_le (mul_pos hv hR) (w.mul_norm_le_retardedDenominator t x)

/-- `R − R·v = R (1 − n·v)`. -/
theorem retardedDenominator_eq_mul (t : ℝ) (x : Space 3) :
    w.retardedDenominator t x = ‖w.retardedSeparation t x‖ *
      (1 - inner ℝ (w.retardedDirection t x) (w.retardedVelocity t x)) := by
  rcases eq_or_ne (w.retardedSeparation t x) 0 with h | h
  · simp [retardedDenominator, retardedDirection, h]
  · have hR := norm_ne_zero_iff.mpr h
    rw [retardedDenominator, retardedDirection, real_inner_smul_left]
    field_simp

/-- The separation at the event `(τ + ‖y‖, r(τ) + y)` is `y`. -/
theorem retardedSeparation_add_norm (τ : ℝ) (y : Space 3) :
    w.retardedSeparation (τ + ‖y‖) (w.r τ + y) = y := by
  rw [retardedSeparation, w.retardedTime_add_norm, add_sub_cancel_left]

/-- The retarded velocity at the event `(τ + ‖y‖, r(τ) + y)` is `ṙ(τ)`. -/
theorem retardedVelocity_add_norm (τ : ℝ) (y : Space 3) :
    w.retardedVelocity (τ + ‖y‖) (w.r τ + y) = deriv w.r τ := by
  rw [retardedVelocity, w.retardedTime_add_norm]

/-- The retarded acceleration at the event `(τ + ‖y‖, r(τ) + y)` is `r̈(τ)`. -/
theorem retardedAcceleration_add_norm (τ : ℝ) (y : Space 3) :
    w.retardedAcceleration (τ + ‖y‖) (w.r τ + y) = deriv (deriv w.r) τ := by
  rw [retardedAcceleration, w.retardedTime_add_norm]

/-- At the event `(τ + ‖y‖, r(τ) + y)` the denominator is `‖y‖ − y·ṙ(τ)`. -/
theorem retardedDenominator_add_norm (τ : ℝ) (y : Space 3) :
    w.retardedDenominator (τ + ‖y‖) (w.r τ + y) = ‖y‖ - inner ℝ y (deriv w.r τ) := by
  rw [retardedDenominator, retardedSeparation_add_norm, retardedVelocity_add_norm]

/-- The retarded time and the separation recover the event: `τ + ‖R‖ = t`. -/
theorem retardedTime_add_norm_retardedSeparation (t : ℝ) (x : Space 3) :
    w.retardedTime t x + ‖w.retardedSeparation t x‖ = t := by
  rw [norm_retardedSeparation]
  ring

/-- The retarded time and the separation recover the event: `r(τ) + R = x`. -/
theorem r_add_retardedSeparation (t : ℝ) (x : Space 3) :
    w.r (w.retardedTime t x) + w.retardedSeparation t x = x := by
  rw [retardedSeparation, add_sub_cancel]

/-- The co-ordinates of the light cones of the world line: `(τ, y) ↦ (τ + ‖y‖, r(τ) + y)` is a
bijection of `ℝ × Space 3`, with the inverse `(t, x) ↦ (τ, R)` given by the retarded time and
the separation from the retarded position. -/
def lightConeEquiv : ℝ × Space 3 ≃ ℝ × Space 3 where
  toFun q := (q.1 + ‖q.2‖, w.r q.1 + q.2)
  invFun p := (w.retardedTime p.1 p.2, w.retardedSeparation p.1 p.2)
  left_inv q := by
    simp only [w.retardedTime_add_norm, w.retardedSeparation_add_norm]
  right_inv p := by
    simp only [w.retardedTime_add_norm_retardedSeparation, w.r_add_retardedSeparation]

/-! ### The smoothness of the retarded time -/

/-- The derivative of the Euclidean norm away from the origin. -/
private theorem hasFDerivAt_norm {p : Space 3} (hp : p ≠ 0) :
    HasFDerivAt (fun z : Space 3 => ‖z‖) (‖p‖⁻¹ • innerSL ℝ p) p := by
  have hn : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hp
  have h := (hasStrictFDerivAt_norm_sq p).hasFDerivAt.sqrt (pow_ne_zero 2 hn)
  simp only [Real.sqrt_sq (norm_nonneg _)] at h
  refine h.congr_fderiv ?_
  ext v
  simp
  field_simp

/-- A continuous linear map of `ℝ` that does not vanish at `1` is invertible. -/
private theorem isInvertible_of_apply_one_ne_zero {L : ℝ →L[ℝ] ℝ} (h : L 1 ≠ 0) :
    L.IsInvertible := by
  refine ContinuousLinearMap.IsInvertible.of_inverse
    (g := (L 1)⁻¹ • ContinuousLinearMap.id ℝ ℝ) ?_ ?_
  · ext
    change L ((L 1)⁻¹ • (1 : ℝ)) = 1
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ h]
  · ext
    change (L 1)⁻¹ • L 1 = (1 : ℝ)
    rw [smul_eq_mul, inv_mul_cancel₀ h]

/-- The equation `t − s − ‖x − r(s)‖ = 0` of the retarded time `s` of `(t, x)`. -/
def lagEquation (q : (ℝ × Space 3) × ℝ) : ℝ := q.1.1 - q.2 - ‖q.1.2 - w.r q.2‖

/-- The equation of the retarded time is smooth where the separation does not vanish. -/
theorem contDiffAt_lagEquation {q : (ℝ × Space 3) × ℝ} (hq : q.1.2 - w.r q.2 ≠ 0) :
    ContDiffAt ℝ ∞ w.lagEquation q := by
  have hS : ContDiffAt ℝ ∞ (fun q : (ℝ × Space 3) × ℝ => q.1.2 - w.r q.2) q :=
    contDiffAt_fst.snd.sub (w.contDiff_r.contDiffAt.comp q contDiffAt_snd)
  exact (contDiffAt_fst.fst.sub contDiffAt_snd).sub ((contDiffAt_norm ℝ hq).comp q hS)

/-- The derivative `−1 + n·v` of the equation of the retarded time in the retarded time. -/
theorem hasDerivAt_lagEquation (p : ℝ × Space 3) {s : ℝ} (hs : p.2 - w.r s ≠ 0) :
    HasDerivAt (fun s => w.lagEquation (p, s))
      (-1 + ‖p.2 - w.r s‖⁻¹ * inner ℝ (p.2 - w.r s) (deriv w.r s)) s := by
  have hS : HasDerivAt (fun s => p.2 - w.r s) (-deriv w.r s) s := by
    simpa using ((w.differentiable_r s).hasDerivAt).const_sub p.2
  have hN : HasDerivAt (fun s => ‖p.2 - w.r s‖)
      ((‖p.2 - w.r s‖⁻¹ • innerSL ℝ (p.2 - w.r s)) (-deriv w.r s)) s :=
    (hasFDerivAt_norm hs).comp_hasDerivAt s hS
  have h : HasDerivAt (fun s => p.1 - s - ‖p.2 - w.r s‖)
      (0 - 1 - (‖p.2 - w.r s‖⁻¹ • innerSL ℝ (p.2 - w.r s)) (-deriv w.r s)) s :=
    ((hasDerivAt_const s p.1).sub (hasDerivAt_id' s)).sub hN
  show HasDerivAt (fun s => p.1 - s - ‖p.2 - w.r s‖) _ s
  convert h using 1
  simp [inner_neg_right, inner_sub_left]
  ring

/-- **The retarded time is smooth off the world line** as a function of `(t, x)`, by the
implicit function theorem. -/
theorem contDiffAt_retardedTime {t : ℝ} {x : Space 3} (h : x ≠ w.r t) :
    ContDiffAt ℝ ∞ (fun p : ℝ × Space 3 => w.retardedTime p.1 p.2) (t, x) := by
  set τ := w.retardedTime t x with hτ
  have hR : x - w.r τ ≠ 0 := w.retardedSeparation_ne_zero h
  set u : (ℝ × Space 3) × ℝ := ((t, x), τ) with hu
  have hF : ContDiffAt ℝ ∞ w.lagEquation u := w.contDiffAt_lagEquation hR
  have hd : (fderiv ℝ w.lagEquation u ∘L ContinuousLinearMap.inr ℝ (ℝ × Space 3) ℝ) 1 =
      -(w.retardedDenominator t x / ‖x - w.r τ‖) := by
    have hγ : HasDerivAt (fun s : ℝ => ((t, x), s)) ((0 : ℝ × Space 3), (1 : ℝ)) τ :=
      (hasDerivAt_const τ (t, x)).prodMk (hasDerivAt_id' τ)
    have h1 := ((hF.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt τ hγ)
    have h2 := w.hasDerivAt_lagEquation (t, x) hR
    have hn : ‖x - w.r τ‖ ≠ 0 := norm_ne_zero_iff.mpr hR
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, h1.unique h2,
      retardedDenominator, retardedSeparation, retardedVelocity]
    field_simp
    ring
  have hinv : (fderiv ℝ w.lagEquation u ∘L ContinuousLinearMap.inr ℝ (ℝ × Space 3) ℝ).IsInvertible
      := by
    refine isInvertible_of_apply_one_ne_zero ?_
    rw [hd, neg_ne_zero]
    exact div_ne_zero (w.retardedDenominator_pos h).ne' (norm_ne_zero_iff.mpr hR)
  have hψ := hF.contDiffAt_implicitFunction (by simp) hinv
  have heq := hF.eventually_apply_implicitFunction (by simp) hinv
  have hu0 : w.lagEquation u = 0 := by
    simp only [lagEquation, hu, hτ, w.sub_retardedTime, sub_self]
  refine hψ.congr_of_eventuallyEq ?_
  filter_upwards [heq] with p hp
  rw [hu0, lagEquation, sub_sub, sub_eq_zero] at hp
  exact w.retardedTime_eq_iff.mpr (by linarith)

/-- The set `x ≠ r(t)` of the events off the world line, in `ℝ × Space 3`. -/
theorem isOpen_offWorldline_prod : IsOpen {p : ℝ × Space 3 | p.2 ≠ w.r p.1} :=
  isOpen_ne_fun continuous_snd (w.contDiff_r.continuous.comp continuous_fst)

/-- The retarded time is smooth on the set of the events off the world line. -/
theorem contDiffOn_retardedTime :
    ContDiffOn ℝ ∞ (fun p : ℝ × Space 3 => w.retardedTime p.1 p.2)
      {p : ℝ × Space 3 | p.2 ≠ w.r p.1} := fun p hp =>
  (w.contDiffAt_retardedTime (t := p.1) (x := p.2) hp).contDiffWithinAt

/-- **The derivative of the retarded time** off the world line:
`dτ = (R dt − R · dx)/(R − R·v)`. -/
theorem hasFDerivAt_retardedTime {t : ℝ} {x : Space 3} (h : x ≠ w.r t) :
    HasFDerivAt (fun p : ℝ × Space 3 => w.retardedTime p.1 p.2)
      ((w.retardedDenominator t x)⁻¹ •
        (‖w.retardedSeparation t x‖ • ContinuousLinearMap.fst ℝ ℝ (Space 3) -
          (innerSL ℝ (w.retardedSeparation t x)).comp (ContinuousLinearMap.snd ℝ ℝ (Space 3))))
      (t, x) := by
  set T := fun p : ℝ × Space 3 => w.retardedTime p.1 p.2 with hT_def
  have hT : HasFDerivAt T (fderiv ℝ T (t, x)) (t, x) :=
    ((w.contDiffAt_retardedTime h).differentiableAt (by simp)).hasFDerivAt
  set T' := fderiv ℝ T (t, x) with hT'
  set R := w.retardedSeparation t x with hR_def
  set v := w.retardedVelocity t x with hv_def
  have hR : R ≠ 0 := w.retardedSeparation_ne_zero h
  have hn : ‖R‖ ≠ 0 := norm_ne_zero_iff.mpr hR
  have hD : w.retardedDenominator t x ≠ 0 := (w.retardedDenominator_pos h).ne'
  have hr : HasFDerivAt w.r ((1 : ℝ →L[ℝ] ℝ).smulRight v) (T (t, x)) :=
    (w.differentiable_r _).hasDerivAt.hasFDerivAt
  have hS : HasFDerivAt (fun p : ℝ × Space 3 => p.2 - w.r (T p))
      (ContinuousLinearMap.snd ℝ ℝ (Space 3) - ((1 : ℝ →L[ℝ] ℝ).smulRight v).comp T') (t, x) :=
    hasFDerivAt_snd.sub (hr.comp (t, x) hT)
  have hN := (hasFDerivAt_norm hR).comp (t, x) hS
  have hL : HasFDerivAt (fun p : ℝ × Space 3 => p.1 - T p)
      (ContinuousLinearMap.fst ℝ ℝ (Space 3) - T') (t, x) := hasFDerivAt_fst.sub hT
  have heq : (fun p : ℝ × Space 3 => p.1 - T p) = fun p => ‖p.2 - w.r (T p)‖ :=
    funext fun p => w.sub_retardedTime p.1 p.2
  rw [heq] at hL
  have hu := hL.unique hN
  convert hT using 1
  refine ContinuousLinearMap.ext fun δ => ?_
  have hδ := congrArg (fun L : ℝ × Space 3 →L[ℝ] ℝ => L δ) hu
  simp only [_root_.sub_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.comp_apply, _root_.smul_apply, innerSL_apply_apply,
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.smulRight_apply,
    one_apply_eq_self, smul_eq_mul, inner_sub_right, real_inner_smul_right] at hδ
  simp only [_root_.smul_apply, _root_.sub_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    ContinuousLinearMap.coe_snd', smul_eq_mul]
  rw [retardedDenominator, ← hR_def, ← hv_def] at hD ⊢
  field_simp at hδ ⊢
  linear_combination hδ

/-- **The time derivative of the retarded time**, `∂τ/∂t = R/(R − R·v)`. -/
theorem fderiv_retardedTime_time {t : ℝ} {x : Space 3} (h : x ≠ w.r t) :
    fderiv ℝ (fun p : ℝ × Space 3 => w.retardedTime p.1 p.2) (t, x) (1, 0) =
      ‖w.retardedSeparation t x‖ / w.retardedDenominator t x := by
  rw [(w.hasFDerivAt_retardedTime h).fderiv]
  simp [div_eq_inv_mul]

/-- **The gradient of the retarded time**, `∇τ · h = −R · h/(R − R·v)`. -/
theorem fderiv_retardedTime_space {t : ℝ} {x : Space 3} (h : x ≠ w.r t) (k : Space 3) :
    fderiv ℝ (fun p : ℝ × Space 3 => w.retardedTime p.1 p.2) (t, x) (0, k) =
      -inner ℝ (w.retardedSeparation t x) k / w.retardedDenominator t x := by
  rw [(w.hasFDerivAt_retardedTime h).fderiv]
  simp [div_eq_inv_mul]

/-- The gradient of the retarded time in the direction `n`, `∇τ = −n/(1 − n·v)`. -/
theorem fderiv_retardedTime_space_direction {t : ℝ} {x : Space 3} (h : x ≠ w.r t)
    (k : Space 3) :
    fderiv ℝ (fun p : ℝ × Space 3 => w.retardedTime p.1 p.2) (t, x) (0, k) =
      -inner ℝ (w.retardedDirection t x) k /
        (1 - inner ℝ (w.retardedDirection t x) (w.retardedVelocity t x)) := by
  have hn : ‖w.retardedSeparation t x‖ ≠ 0 := norm_ne_zero_iff.mpr (w.retardedSeparation_ne_zero h)
  rw [w.fderiv_retardedTime_space h, w.retardedDenominator_eq_mul, retardedDirection,
    real_inner_smul_left, real_inner_smul_left]
  have hD := w.retardedDenominator_pos h
  rw [w.retardedDenominator_eq_mul, retardedDirection, real_inner_smul_left] at hD
  have h1 : 1 - ‖w.retardedSeparation t x‖⁻¹ *
      inner ℝ (w.retardedSeparation t x) (w.retardedVelocity t x) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hD
    exact lt_irrefl 0 hD
  field_simp

/-! ### The retarded time on space-time -/

/-- The set of the events `x ≠ r(t)` of space-time off the world line. -/
def offWorldline : Set Spacetime := {y | space y ≠ w.r (y 0)}

/-- The set of the events off the world line is open. -/
theorem isOpen_offWorldline : IsOpen w.offWorldline :=
  isOpen_ne_fun (space : Spacetime →L[ℝ] Space 3).continuous
    (w.contDiff_r.continuous.comp (continuous_apply 0))

/-- The splitting `y ↦ (y⁰, 𝐲)` of space-time into time and space. -/
private def split : Spacetime →L[ℝ] ℝ × Space 3 :=
  (time : Spacetime →L[ℝ] ℝ).prod (space : Spacetime →L[ℝ] Space 3)

/-- The retarded time is smooth off the world line, as a function on space-time. -/
theorem contDiffAt_retardedTime_spacetime {y : Spacetime} (hy : y ∈ w.offWorldline) :
    ContDiffAt ℝ ∞ (fun z : Spacetime => w.retardedTime (z 0) (space z)) y :=
  (w.contDiffAt_retardedTime (t := y 0) (x := space y) hy).comp y split.contDiff.contDiffAt

/-- The retarded time is smooth on the set of the events off the world line. -/
theorem contDiffOn_retardedTime_spacetime :
    ContDiffOn ℝ ∞ (fun z : Spacetime => w.retardedTime (z 0) (space z)) w.offWorldline :=
  fun _ hy => (w.contDiffAt_retardedTime_spacetime hy).contDiffWithinAt

/-- **The derivative of the retarded time on space-time**:
`dτ = (R dt − R · d𝐱)/(R − R·v)` off the world line. -/
theorem hasFDerivAt_retardedTime_spacetime {y : Spacetime} (hy : y ∈ w.offWorldline) :
    HasFDerivAt (fun z : Spacetime => w.retardedTime (z 0) (space z))
      ((w.retardedDenominator (y 0) (space y))⁻¹ •
        (‖w.retardedSeparation (y 0) (space y)‖ • (time : Spacetime →L[ℝ] ℝ) -
          (innerSL ℝ (w.retardedSeparation (y 0) (space y))).comp
            (space : Spacetime →L[ℝ] Space 3))) y := by
  have h := (w.hasFDerivAt_retardedTime (t := y 0) (x := space y) hy).comp y split.hasFDerivAt
  have hfun : (fun z : Spacetime => w.retardedTime (z 0) (space z)) =
      (fun p : ℝ × Space 3 => w.retardedTime p.1 p.2) ∘ split := rfl
  rw [hfun]
  refine h.congr_fderiv ?_
  ext δ
  simp [split]

/-- The derivative `∂₀τ = R/(R − R·v)` of the retarded time on space-time. -/
theorem partialAt_retardedTime_zero {y : Spacetime} (hy : y ∈ w.offWorldline) :
    partialAt (fun z : Spacetime => w.retardedTime (z 0) (space z)) 0 y =
      ‖w.retardedSeparation (y 0) (space y)‖ / w.retardedDenominator (y 0) (space y) := by
  rw [partialAt, (w.hasFDerivAt_retardedTime_spacetime hy).fderiv]
  have h0 : space (Pi.single 0 1 : Spacetime) = 0 := by
    ext j
    simp [Fin.succ_ne_zero]
  simp [h0, div_eq_inv_mul]

/-- The derivatives `∂ᵢτ = −Rᵢ/(R − R·v)` of the retarded time on space-time. -/
theorem partialAt_retardedTime_succ {y : Spacetime} (hy : y ∈ w.offWorldline) (i : Fin 3) :
    partialAt (fun z : Spacetime => w.retardedTime (z 0) (space z)) i.succ y =
      -w.retardedSeparation (y 0) (space y) i / w.retardedDenominator (y 0) (space y) := by
  rw [partialAt, (w.hasFDerivAt_retardedTime_spacetime hy).fderiv]
  have hs : space (Pi.single i.succ 1 : Spacetime) = EuclideanSpace.single i 1 := by
    ext j
    simp [Pi.single_apply, Fin.succ_inj]
  simp [hs, div_eq_inv_mul, Fin.succ_ne_zero, EuclideanSpace.inner_single_right]

end SubluminalWorldline

end ProjectAinos.Electrodynamics
