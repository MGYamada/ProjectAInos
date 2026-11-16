/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.OneDimension.ActionAngle
public import ProjectAInos.Mechanics.OneDimension.Abel
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The oscillator as a well

For `U = k x²/2` with `k > 0` and an energy `E > 0` the turning points are
`∓√(2E/k)`. The factor of the well is the constant `k/2`, so

* the period is `2π √(m/k)`, the same at every energy (`orbitPeriod_oscillator`);
* the action variable is `E √(m/k) = E/ω` (`orbitAction_oscillator`);
* the wells are nested as the energy increases from zero, and Abel's inversion
  formula holds for them (`abel_inversion_oscillator`).

These are instances in which the hypotheses of the theorems on wells are
verified.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped Real ContDiff

namespace ProjectAInos.Mechanics.OneDim

variable {k m E : ℝ}

theorem contDiff_oscillator (k : ℝ) : ContDiff ℝ ∞ fun x : ℝ => k / 2 * x ^ 2 := by
  fun_prop

theorem deriv_oscillator (k x : ℝ) : deriv (fun x : ℝ => k / 2 * x ^ 2) x = k * x := by
  have h : HasDerivAt (fun x : ℝ => k / 2 * x ^ 2) (k * x) x := by
    refine (((hasDerivAt_id x).pow 2).const_mul (k / 2)).congr_deriv ?_
    simp
    ring
  exact h.deriv

/-- The factor of the well of the oscillator is the constant `k/2`. -/
theorem wellFactor_oscillator (hk : 0 < k) (hE : 0 < E) {x : ℝ}
    (hx : x ∈ Icc (-√(2 * E / k)) √(2 * E / k)) :
    wellFactor (fun x : ℝ => k / 2 * x ^ 2) (-√(2 * E / k)) √(2 * E / k) x = k / 2 := by
  have h := isWell_oscillator hk hE
  have hU := contDiff_oscillator k
  have hpos : 0 < 2 * E / k := by positivity
  have hs : 0 < √(2 * E / k) := Real.sqrt_pos.mpr hpos
  have hsq : √(2 * E / k) ^ 2 = 2 * E / k := Real.sq_sqrt hpos.le
  rcases eq_or_lt_of_le hx.1 with rfl | hax
  · rw [h.wellFactor_left hU, deriv_oscillator]
    field_simp
    ring
  rcases eq_or_lt_of_le hx.2 with rfl | hxb
  · rw [h.wellFactor_right hU, deriv_oscillator]
    field_simp
    ring
  have hfac := h.sub_eq hU x
  have hprod : (x - -√(2 * E / k)) * (√(2 * E / k) - x) ≠ 0 :=
    (mul_pos (by linarith) (by linarith)).ne'
  have hE' : E = k / 2 * √(2 * E / k) ^ 2 := by
    rw [hsq]
    field_simp
  have hleft : E - k / 2 * x ^ 2 =
      (x - -√(2 * E / k)) * (√(2 * E / k) - x) * (k / 2) := by
    nlinarith [hE']
  exact mul_left_cancel₀ hprod (hfac.symm.trans hleft)

theorem orbitRate_oscillator (hk : 0 < k) (hE : 0 < E) (m θ : ℝ) :
    orbitRate m (fun x : ℝ => k / 2 * x ^ 2) (-√(2 * E / k)) √(2 * E / k) θ = √(m / k) := by
  have hs : 0 < √(2 * E / k) := Real.sqrt_pos.mpr (by positivity)
  rw [orbitRate, wellFactor_oscillator hk hE (orbitPosition_mem_Icc (by linarith) θ),
    ← Real.sqrt_div' _ (by positivity)]
  congr 1
  field_simp

/-- The period of the oscillator is `2π √(m/k)` at every energy. -/
theorem orbitPeriod_oscillator (hk : 0 < k) (hE : 0 < E) (m : ℝ) :
    orbitPeriod m (fun x : ℝ => k / 2 * x ^ 2) (-√(2 * E / k)) √(2 * E / k) =
      2 * π * √(m / k) := by
  rw [orbitPeriod]
  simp_rw [orbitRate_oscillator hk hE m]
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]

/-- The action variable of the oscillator is `E √(m/k)`, the energy divided by
the frequency. -/
theorem orbitAction_oscillator (hk : 0 < k) (hm : 0 < m) (hE : 0 < E) :
    orbitAction m (fun x : ℝ => k / 2 * x ^ 2) (-√(2 * E / k)) √(2 * E / k) =
      E * √(m / k) := by
  have hpos : 0 < 2 * E / k := by positivity
  have hs : 0 < √(2 * E / k) := Real.sqrt_pos.mpr hpos
  have hsq : √(2 * E / k) ^ 2 = 2 * E / k := Real.sq_sqrt hpos.le
  have hint : ∀ θ : ℝ, orbitMomentum m (fun x : ℝ => k / 2 * x ^ 2) (-√(2 * E / k))
      √(2 * E / k) θ * ((√(2 * E / k) - -√(2 * E / k)) / 2 * Real.sin θ) =
      √(2 * m) * √(k / 2) * (2 * E / k) * Real.sin θ ^ 2 := by
    intro θ
    rw [orbitMomentum, wellFactor_oscillator hk hE (orbitPosition_mem_Icc (by linarith) θ)]
    have hr : (√(2 * E / k) - -√(2 * E / k)) / 2 = √(2 * E / k) := by ring
    rw [hr]
    linear_combination (√(2 * m) * √(k / 2) * Real.sin θ ^ 2) * hsq
  have hsin : ∫ θ in (0 : ℝ)..2 * π, Real.sin θ ^ 2 = π := by
    rw [integral_sin_sq]
    simp
  have hroot : √(2 * m) * √(k / 2) = k * √(m / k) := by
    rw [← Real.sqrt_mul (by positivity)]
    have h1 : 2 * m * (k / 2) = k ^ 2 * (m / k) := by
      field_simp
    rw [h1, Real.sqrt_mul (by positivity), Real.sqrt_sq hk.le]
  rw [orbitAction, orbitArea]
  simp_rw [hint]
  rw [intervalIntegral.integral_const_mul, hsin, hroot]
  field_simp

/-- Abel's inversion formula for the oscillator: the hypotheses of
`abel_inversion` hold for the wells between `∓√(2E/k)`, with the bottom of the
well at the energy zero. -/
theorem abel_inversion_oscillator (hk : 0 < k) (hm : 0 < m) {V : ℝ} (hV : 0 < V) :
    √(2 * V / k) - -√(2 * V / k) = 1 / (π * √(2 * m)) *
      ∫ E in Ioo 0 V, orbitPeriod m (fun x : ℝ => k / 2 * x ^ 2) (-√(2 * E / k))
        √(2 * E / k) / √(V - E) := by
  refine abel_inversion (U := fun x : ℝ => k / 2 * x ^ 2) (contDiff_oscillator k) hm
    (x₁ := fun E => -√(2 * E / k)) (x₂ := fun E => √(2 * E / k)) (isWell_oscillator hk hV)
    (fun E hE => isWell_oscillator hk hE.1) (fun E hE x => ?_) fun x _ => by positivity
  have hposE : 0 < 2 * E / k := by have := hE.1; positivity
  have hsqE : √(2 * E / k) ^ 2 = 2 * E / k := Real.sq_sqrt hposE.le
  have hsE : 0 < √(2 * E / k) := Real.sqrt_pos.mpr hposE
  have hle : √(2 * E / k) < √(2 * V / k) := by
    apply Real.sqrt_lt_sqrt hposE.le
    have := hE.2
    gcongr
  have hiff : x ∈ Ioo (-√(2 * E / k)) √(2 * E / k) ↔ k / 2 * x ^ 2 < E := by
    rw [mem_Ioo, ← abs_lt, ← abs_of_pos hsE, ← sq_lt_sq, hsqE]
    constructor
    · intro hlt
      have h1 : k / 2 * x ^ 2 < k / 2 * (2 * E / k) := by gcongr
      have h2 : k / 2 * (2 * E / k) = E := by field_simp
      linarith
    · intro hlt
      rw [lt_div_iff₀ hk]
      linarith
  constructor
  · intro hx
    exact ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, hiff.mp hx⟩
  · intro hx
    exact hiff.mpr hx.2

end ProjectAInos.Mechanics.OneDim
