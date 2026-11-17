/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.ODE.Averaging
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# Resonance in non-linear oscillations

Landau–Lifshitz §29, for a cubic anharmonic term. The forced and damped
oscillator

`ẍ + 2λ ẋ + ω₀² x = F cos γt − β x³`

is written in the amplitudes `a`, `b` of `x = a cos γt + b sin γt`,
`ẋ = γ (−a sin γt + b cos γt)` (`amplitude`). With the slow parameters

`ε = (γ² − ω₀²)/2γ`, `κ = 3β/8γ`, `f = F/2γ`

(`detuning`, `nonlinearity`, `forcing`) the amplitudes follow the field

`ȧ = −λ a − (ε − κ r²) b`, `ḃ = −λ b + (ε − κ r²) a + f`, `r² = a² + b²`,

(`averagedField`) up to terms that oscillate with the frequencies `2γ` and
`4γ` (`IsMotionOn.hasDerivAt_amplitude`).

* `amplitude_equation`: at an equilibrium of the averaged field the amplitude
  satisfies `r² ((ε − κ r²)² + λ²) = f²`, the equation (29.4);
  `exists_averagedField_eq_zero`: every solution of this equation is the
  amplitude of an equilibrium.
* `exists_forall_norm_amplitude_sub_le`: for fixed `λ`, `ε`, `κ`, `f`, a radius
  `ρ` and a length `L` there is a constant `C` such that for every `γ` the
  amplitudes of a motion and the solution of the averaged equations with the
  same initial value differ by at most `C/γ` on `[0, L]`, as long as both stay
  in the disc of the radius `ρ`.
* `exists_forall_abs_sub_steady_le`: in particular a motion that starts with
  the amplitudes of an equilibrium stays within `2C/γ` of the oscillation
  `a₀ cos γt + b₀ sin γt`.
-/

@[expose] public section
noncomputable section

open Set

namespace ProjectAinos.Mechanics.NonlinearResonance

open SmoothGeometry.Averaging

/-- A motion of the forced, damped oscillator with a cubic term on a set of
times: `ẋ = v` and `v̇ = −2λ v − ω₀² x + F cos γt − β x³`. -/
def IsMotionOn (lam ω₀ β F γ : ℝ) (x v : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∀ t ∈ I, HasDerivAt x (v t) t ∧
    HasDerivAt v (-(2 * lam * v t) - ω₀ ^ 2 * x t + F * Real.cos (γ * t) - β * x t ^ 3) t

/-- The amplitudes `a`, `b` with `x = a cos γt + b sin γt` and
`v = γ (−a sin γt + b cos γt)`. -/
def amplitude (γ : ℝ) (x v : ℝ → ℝ) (t : ℝ) : ℝ × ℝ :=
  (x t * Real.cos (γ * t) - v t / γ * Real.sin (γ * t),
    x t * Real.sin (γ * t) + v t / γ * Real.cos (γ * t))

/-- The detuning `ε = (γ² − ω₀²)/2γ`. -/
def detuning (ω₀ γ : ℝ) : ℝ := (γ ^ 2 - ω₀ ^ 2) / (2 * γ)

/-- The coefficient `κ = 3β/8γ` of the shift of the frequency. -/
def nonlinearity (β γ : ℝ) : ℝ := 3 * β / (8 * γ)

/-- The amplitude `f = F/2γ` of the force in the slow equations. -/
def forcing (F γ : ℝ) : ℝ := F / (2 * γ)

/-- The field of the averaged equations of the amplitudes. -/
def averagedField (lam e k f : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (-(lam * z.1) - (e - k * (z.1 ^ 2 + z.2 ^ 2)) * z.2,
    -(lam * z.2) + (e - k * (z.1 ^ 2 + z.2 ^ 2)) * z.1 + f)

/-- The frequencies of the oscillating terms, in units of `γ`. -/
def multiple : Fin 2 → ℝ := ![2, 4]

/-- The amplitudes of the terms in `cos 2γt` and `cos 4γt`. -/
def cosAmplitude (lam e k f : ℝ) : Fin 2 → ℝ × ℝ → ℝ × ℝ :=
  ![fun z => (lam * z.1 + e * z.2 - 4 / 3 * k * z.2 ^ 3,
      -(lam * z.2) + e * z.1 + f - 4 / 3 * k * z.1 ^ 3),
    fun z => (1 / 3 * k * (z.2 ^ 3 - 3 * z.1 ^ 2 * z.2),
      -(1 / 3 * k * (z.1 ^ 3 - 3 * z.1 * z.2 ^ 2)))]

/-- The amplitudes of the terms in `sin 2γt` and `sin 4γt`. -/
def sinAmplitude (lam e k f : ℝ) : Fin 2 → ℝ × ℝ → ℝ × ℝ :=
  ![fun z => (lam * z.2 - e * z.1 - f + 2 / 3 * k * (z.1 ^ 3 + 3 * z.1 * z.2 ^ 2),
      lam * z.1 + e * z.2 - 2 / 3 * k * (3 * z.1 ^ 2 * z.2 + z.2 ^ 3)),
    fun z => (1 / 3 * k * (z.1 ^ 3 - 3 * z.1 * z.2 ^ 2),
      -(1 / 3 * k * (3 * z.1 ^ 2 * z.2 - z.2 ^ 3)))]

variable {lam ω₀ β F γ e k f : ℝ} {x v : ℝ → ℝ} {I : Set ℝ}

/-! ### The amplitudes -/

/-- `x = a cos γt + b sin γt`. -/
theorem amplitude_fst_mul_cos_add (γ : ℝ) (x v : ℝ → ℝ) (t : ℝ) :
    (amplitude γ x v t).1 * Real.cos (γ * t) + (amplitude γ x v t).2 * Real.sin (γ * t) =
      x t := by
  simp only [amplitude]
  linear_combination x t * Real.sin_sq_add_cos_sq (γ * t)

/-- `v = γ (−a sin γt + b cos γt)`. -/
theorem amplitude_velocity (hγ : γ ≠ 0) (x v : ℝ → ℝ) (t : ℝ) :
    γ * (-((amplitude γ x v t).1 * Real.sin (γ * t)) +
      (amplitude γ x v t).2 * Real.cos (γ * t)) = v t := by
  simp only [amplitude]
  field_simp
  linear_combination v t * Real.sin_sq_add_cos_sq (γ * t)

/-! ### The slow equations -/

theorem slow_identity₁ (X U c s lam e k f : ℝ) (h : s ^ 2 + c ^ 2 = 1) :
    -(-(2 * lam * U) + 2 * e * X + 2 * f * c - 8 / 3 * k * X ^ 3) * s =
      -(lam * (X * c - U * s)) -
          (e - k * ((X * c - U * s) ^ 2 + (X * s + U * c) ^ 2)) * (X * s + U * c) +
        ((2 * c ^ 2 - 1) *
            (lam * (X * c - U * s) + e * (X * s + U * c) - 4 / 3 * k * (X * s + U * c) ^ 3) +
          2 * s * c * (lam * (X * s + U * c) - e * (X * c - U * s) - f +
            2 / 3 * k * ((X * c - U * s) ^ 3 + 3 * (X * c - U * s) * (X * s + U * c) ^ 2)) +
          ((2 * (2 * c ^ 2 - 1) ^ 2 - 1) *
              (1 / 3 * k * ((X * s + U * c) ^ 3 - 3 * (X * c - U * s) ^ 2 * (X * s + U * c))) +
            2 * (2 * s * c) * (2 * c ^ 2 - 1) *
              (1 / 3 * k *
                ((X * c - U * s) ^ 3 - 3 * (X * c - U * s) * (X * s + U * c) ^ 2)))) := by
  linear_combination ((-2 : ℝ) * c * e * U + (-2 : ℝ) * c * lam * X +
    ((-8 : ℝ) / 3) * k * s * X ^ 3 + ((-8 : ℝ) / 3) * k * c ^ 5 * U ^ 3 +
    ((8 : ℝ) / 3) * k * c ^ 3 * U ^ 3 + 8 * k * U * c ^ 5 * X ^ 2 +
    ((-8 : ℝ) / 3) * k * s * c ^ 2 * X ^ 3 + ((8 : ℝ) / 3) * k * c ^ 3 * s ^ 2 * U ^ 3 +
    ((16 : ℝ) / 3) * k * s * c ^ 4 * X ^ 3 + (-16 : ℝ) * k * s * X * c ^ 4 * U ^ 2 +
    (-8 : ℝ) * k * U * c ^ 3 * s ^ 2 * X ^ 2 + 8 * c * k * U * s ^ 2 * X ^ 2 +
    8 * k * s * X * c ^ 2 * U ^ 2) * h

theorem slow_identity₂ (X U c s lam e k f : ℝ) (h : s ^ 2 + c ^ 2 = 1) :
    (-(2 * lam * U) + 2 * e * X + 2 * f * c - 8 / 3 * k * X ^ 3) * c =
      -(lam * (X * s + U * c)) +
          (e - k * ((X * c - U * s) ^ 2 + (X * s + U * c) ^ 2)) * (X * c - U * s) + f +
        ((2 * c ^ 2 - 1) *
            (-(lam * (X * s + U * c)) + e * (X * c - U * s) + f -
              4 / 3 * k * (X * c - U * s) ^ 3) +
          2 * s * c * (lam * (X * c - U * s) + e * (X * s + U * c) -
            2 / 3 * k * (3 * (X * c - U * s) ^ 2 * (X * s + U * c) + (X * s + U * c) ^ 3)) +
          ((2 * (2 * c ^ 2 - 1) ^ 2 - 1) *
              -(1 / 3 * k * ((X * c - U * s) ^ 3 - 3 * (X * c - U * s) * (X * s + U * c) ^ 2)) +
            2 * (2 * s * c) * (2 * c ^ 2 - 1) *
              -(1 / 3 * k *
                (3 * (X * c - U * s) ^ 2 * (X * s + U * c) - (X * s + U * c) ^ 3)))) := by
  linear_combination ((-2 : ℝ) * c * e * X + 2 * c * lam * U + ((8 : ℝ) / 3) * c * k * X ^ 3 +
    ((8 : ℝ) / 3) * k * c ^ 3 * X ^ 3 + ((8 : ℝ) / 3) * k * c ^ 5 * X ^ 3 +
    (-8 : ℝ) * k * X * c ^ 5 * U ^ 2 + ((-8 : ℝ) / 3) * k * c ^ 3 * s ^ 2 * X ^ 3 +
    ((8 : ℝ) / 3) * c * k * s ^ 2 * X ^ 3 + ((16 : ℝ) / 3) * k * s * c ^ 4 * U ^ 3 +
    (-16 : ℝ) * k * s * U * c ^ 4 * X ^ 2 + 8 * k * X * c ^ 3 * s ^ 2 * U ^ 2) * h

/-- The amplitudes of a motion follow the averaged field up to terms that
oscillate with the frequencies `2γ` and `4γ`. -/
theorem IsMotionOn.hasDerivAt_amplitude (h : IsMotionOn lam ω₀ β F γ x v I) (hγ : γ ≠ 0)
    {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (amplitude γ x v)
      (averagedField lam (detuning ω₀ γ) (nonlinearity β γ) (forcing F γ) (amplitude γ x v t) +
        harmonics multiple
          (cosAmplitude lam (detuning ω₀ γ) (nonlinearity β γ) (forcing F γ))
          (sinAmplitude lam (detuning ω₀ γ) (nonlinearity β γ) (forcing F γ)) γ t
          (amplitude γ x v t)) t := by
  obtain ⟨hx, hv⟩ := h t ht
  have hc : HasDerivAt (fun s => Real.cos (γ * s)) (-(Real.sin (γ * t) * γ)) t := by
    have h1 := ((hasDerivAt_id t).const_mul γ).cos
    simpa using h1
  have hs : HasDerivAt (fun s => Real.sin (γ * s)) (Real.cos (γ * t) * γ) t := by
    have h1 := ((hasDerivAt_id t).const_mul γ).sin
    simpa using h1
  have ha : HasDerivAt (fun s => x s * Real.cos (γ * s) - v s / γ * Real.sin (γ * s))
      (v t * Real.cos (γ * t) + x t * -(Real.sin (γ * t) * γ) -
        ((-(2 * lam * v t) - ω₀ ^ 2 * x t + F * Real.cos (γ * t) - β * x t ^ 3) / γ *
            Real.sin (γ * t) + v t / γ * (Real.cos (γ * t) * γ))) t :=
    (hx.mul hc).sub ((hv.div_const γ).mul hs)
  have hb : HasDerivAt (fun s => x s * Real.sin (γ * s) + v s / γ * Real.cos (γ * s))
      (v t * Real.sin (γ * t) + x t * (Real.cos (γ * t) * γ) +
        ((-(2 * lam * v t) - ω₀ ^ 2 * x t + F * Real.cos (γ * t) - β * x t ^ 3) / γ *
            Real.cos (γ * t) + v t / γ * -(Real.sin (γ * t) * γ))) t :=
    (hx.mul hs).add ((hv.div_const γ).mul hc)
  have hpair : HasDerivAt (amplitude γ x v)
      (v t * Real.cos (γ * t) + x t * -(Real.sin (γ * t) * γ) -
        ((-(2 * lam * v t) - ω₀ ^ 2 * x t + F * Real.cos (γ * t) - β * x t ^ 3) / γ *
            Real.sin (γ * t) + v t / γ * (Real.cos (γ * t) * γ)),
        v t * Real.sin (γ * t) + x t * (Real.cos (γ * t) * γ) +
          ((-(2 * lam * v t) - ω₀ ^ 2 * x t + F * Real.cos (γ * t) - β * x t ^ 3) / γ *
              Real.cos (γ * t) + v t / γ * -(Real.sin (γ * t) * γ))) t :=
    ha.prodMk hb
  refine hpair.congr_deriv ?_
  have hcs : Real.sin (γ * t) ^ 2 + Real.cos (γ * t) ^ 2 = 1 := Real.sin_sq_add_cos_sq (γ * t)
  have h2c : Real.cos (multiple 0 * γ * t) = 2 * Real.cos (γ * t) ^ 2 - 1 := by
    have e : multiple 0 * γ * t = 2 * (γ * t) := by
      simp only [multiple, Matrix.cons_val_zero]
      ring
    rw [e, Real.cos_two_mul]
  have h2s : Real.sin (multiple 0 * γ * t) = 2 * Real.sin (γ * t) * Real.cos (γ * t) := by
    have e : multiple 0 * γ * t = 2 * (γ * t) := by
      simp only [multiple, Matrix.cons_val_zero]
      ring
    rw [e, Real.sin_two_mul]
  have h4c : Real.cos (multiple 1 * γ * t) = 2 * (2 * Real.cos (γ * t) ^ 2 - 1) ^ 2 - 1 := by
    have e : multiple 1 * γ * t = 2 * (2 * (γ * t)) := by
      simp only [multiple, Matrix.cons_val_one, Matrix.cons_val_zero]
      ring
    rw [e, Real.cos_two_mul, Real.cos_two_mul]
  have h4s : Real.sin (multiple 1 * γ * t) =
      2 * (2 * Real.sin (γ * t) * Real.cos (γ * t)) * (2 * Real.cos (γ * t) ^ 2 - 1) := by
    have e : multiple 1 * γ * t = 2 * (2 * (γ * t)) := by
      simp only [multiple, Matrix.cons_val_one, Matrix.cons_val_zero]
      ring
    rw [e, Real.sin_two_mul, Real.sin_two_mul, Real.cos_two_mul]
  obtain ⟨U, hU⟩ : ∃ U, v t = γ * U := ⟨v t / γ, by field_simp⟩
  have hUd : v t / γ = U := by
    rw [hU]
    field_simp
  have he : ω₀ ^ 2 = γ ^ 2 - 2 * γ * detuning ω₀ γ := by
    simp only [detuning]
    field_simp
    ring
  have hk : β = 8 / 3 * γ * nonlinearity β γ := by
    simp only [nonlinearity]
    field_simp
  have hf : F = 2 * γ * forcing F γ := by
    simp only [forcing]
    field_simp
  generalize detuning ω₀ γ = e at he ⊢
  generalize nonlinearity β γ = k at hk ⊢
  generalize forcing F γ = f at hf ⊢
  have hdiv : (-(2 * lam * (γ * U)) - (γ ^ 2 - 2 * γ * e) * x t +
      2 * γ * f * Real.cos (γ * t) - 8 / 3 * γ * k * x t ^ 3) / γ =
      -(2 * lam * U) - γ * x t + 2 * e * x t + 2 * f * Real.cos (γ * t) -
        8 / 3 * k * x t ^ 3 := by
    field_simp
    ring
  refine Prod.ext ?_ ?_
  · simp only [harmonics, Fin.sum_univ_two, Prod.fst_add, Prod.smul_fst, smul_eq_mul,
      averagedField, amplitude, cosAmplitude, sinAmplitude, Matrix.cons_val_zero,
      Matrix.cons_val_one, h2c, h2s, h4c, h4s]
    rw [hUd, hU, he, hk, hf, hdiv]
    linear_combination slow_identity₁ (x t) U (Real.cos (γ * t)) (Real.sin (γ * t)) lam e k f hcs
  · simp only [harmonics, Fin.sum_univ_two, Prod.snd_add, Prod.smul_snd, smul_eq_mul,
      averagedField, amplitude, cosAmplitude, sinAmplitude, Matrix.cons_val_zero,
      Matrix.cons_val_one, h2c, h2s, h4c, h4s]
    rw [hUd, hU, he, hk, hf, hdiv]
    linear_combination slow_identity₂ (x t) U (Real.cos (γ * t)) (Real.sin (γ * t)) lam e k f hcs

/-! ### Equilibria and the equation of the amplitude -/

/-- The equation (29.4) of the amplitude: at an equilibrium of the averaged
field, `r² ((ε − κ r²)² + λ²) = f²`. -/
theorem amplitude_equation {z : ℝ × ℝ} (hz : averagedField lam e k f z = 0) :
    (z.1 ^ 2 + z.2 ^ 2) * ((e - k * (z.1 ^ 2 + z.2 ^ 2)) ^ 2 + lam ^ 2) = f ^ 2 := by
  have h1 : -(lam * z.1) - (e - k * (z.1 ^ 2 + z.2 ^ 2)) * z.2 = 0 := congrArg Prod.fst hz
  have h2 : -(lam * z.2) + (e - k * (z.1 ^ 2 + z.2 ^ 2)) * z.1 + f = 0 := congrArg Prod.snd hz
  have hf : f = lam * z.2 - (e - k * (z.1 ^ 2 + z.2 ^ 2)) * z.1 := by linarith
  rw [hf]
  linear_combination (-(lam * z.1) - (e - k * (z.1 ^ 2 + z.2 ^ 2)) * z.2) * h1

/-- Every non-negative solution `s` of the equation of the amplitude, with
`(ε − κ s)² + λ² ≠ 0`, is the squared amplitude of an equilibrium of the
averaged field. -/
theorem exists_averagedField_eq_zero {s : ℝ}
    (hs : s * ((e - k * s) ^ 2 + lam ^ 2) = f ^ 2) (hD : (e - k * s) ^ 2 + lam ^ 2 ≠ 0) :
    ∃ z : ℝ × ℝ, z.1 ^ 2 + z.2 ^ 2 = s ∧ averagedField lam e k f z = 0 := by
  have hsq : (-(f * (e - k * s)) / ((e - k * s) ^ 2 + lam ^ 2)) ^ 2 +
      (f * lam / ((e - k * s) ^ 2 + lam ^ 2)) ^ 2 = s := by
    rw [div_pow, div_pow, ← add_div, div_eq_iff (pow_ne_zero 2 hD)]
    linear_combination (-((e - k * s) ^ 2 + lam ^ 2)) * hs
  refine ⟨(-(f * (e - k * s)) / ((e - k * s) ^ 2 + lam ^ 2),
    f * lam / ((e - k * s) ^ 2 + lam ^ 2)), hsq, ?_⟩
  refine Prod.ext ?_ ?_
  · simp only [averagedField, Prod.fst_zero]
    rw [hsq]
    field_simp
    ring
  · simp only [averagedField, Prod.snd_zero]
    rw [hsq]
    field_simp
    ring

/-! ### Averaging -/

theorem contDiff_averagedField (lam e k f : ℝ) : ContDiff ℝ 1 (averagedField lam e k f) := by
  unfold averagedField
  fun_prop

theorem contDiff_cosAmplitude (lam e k f : ℝ) (j : Fin 2) :
    ContDiff ℝ 1 (cosAmplitude lam e k f j) := by
  fin_cases j
  · change ContDiff ℝ 1 fun z : ℝ × ℝ => (lam * z.1 + e * z.2 - 4 / 3 * k * z.2 ^ 3,
      -(lam * z.2) + e * z.1 + f - 4 / 3 * k * z.1 ^ 3)
    fun_prop
  · change ContDiff ℝ 1 fun z : ℝ × ℝ => (1 / 3 * k * (z.2 ^ 3 - 3 * z.1 ^ 2 * z.2),
      -(1 / 3 * k * (z.1 ^ 3 - 3 * z.1 * z.2 ^ 2)))
    fun_prop

theorem contDiff_sinAmplitude (lam e k f : ℝ) (j : Fin 2) :
    ContDiff ℝ 1 (sinAmplitude lam e k f j) := by
  fin_cases j
  · change ContDiff ℝ 1 fun z : ℝ × ℝ =>
      (lam * z.2 - e * z.1 - f + 2 / 3 * k * (z.1 ^ 3 + 3 * z.1 * z.2 ^ 2),
        lam * z.1 + e * z.2 - 2 / 3 * k * (3 * z.1 ^ 2 * z.2 + z.2 ^ 3))
    fun_prop
  · change ContDiff ℝ 1 fun z : ℝ × ℝ => (1 / 3 * k * (z.1 ^ 3 - 3 * z.1 * z.2 ^ 2),
      -(1 / 3 * k * (3 * z.1 ^ 2 * z.2 - z.2 ^ 3)))
    fun_prop

theorem multiple_pos (j : Fin 2) : 0 < multiple j := by
  fin_cases j <;> simp [multiple]

/-- Averaging for the resonance. For fixed slow parameters `λ`, `ε`, `κ`, `f`,
a radius `ρ` and a length `L` of the interval of time there is a constant `C`
such that, for every frequency `γ` of the force, the amplitudes of a motion
and the solution of the averaged equations with the same initial value differ
by at most `C/γ` on `[0, L]`, as long as both stay in the disc of the radius
`ρ`. -/
theorem exists_forall_norm_amplitude_sub_le (lam e k f ρ L : ℝ) :
    ∃ C : ℝ, ∀ γ : ℝ, 0 < γ → ∀ (ω₀ β F : ℝ) (x v : ℝ → ℝ) (Z : ℝ → ℝ × ℝ),
      detuning ω₀ γ = e → nonlinearity β γ = k → forcing F γ = f →
      IsMotionOn lam ω₀ β F γ x v (Icc 0 L) →
      (∀ t ∈ Icc 0 L, HasDerivAt Z (averagedField lam e k f (Z t)) t) →
      (∀ t ∈ Icc 0 L, amplitude γ x v t ∈ Metric.closedBall (0 : ℝ × ℝ) ρ) →
      (∀ t ∈ Icc 0 L, Z t ∈ Metric.closedBall (0 : ℝ × ℝ) ρ) → amplitude γ x v 0 = Z 0 →
      ∀ t ∈ Icc 0 L, ‖amplitude γ x v t - Z t‖ ≤ C / γ := by
  obtain ⟨C, hC⟩ := exists_forall_norm_sub_le (contDiff_averagedField lam e k f)
    (contDiff_cosAmplitude lam e k f) (contDiff_sinAmplitude lam e k f) multiple_pos
    (isCompact_closedBall (0 : ℝ × ℝ) ρ) (convex_closedBall (0 : ℝ × ℝ) ρ) L
  refine ⟨C, fun γ hγ ω₀ β F x v Z he hk hf hm hZ hzK hZK h0 => ?_⟩
  refine hC γ hγ (amplitude γ x v) Z (fun t ht => ?_) hZ hzK hZK h0
  have h := hm.hasDerivAt_amplitude hγ.ne' ht
  rwa [he, hk, hf] at h

/-- The response at resonance. A motion that starts with the amplitudes of an
equilibrium `(a₀, b₀)` of the averaged field stays within `2C/γ` of the
oscillation `a₀ cos γt + b₀ sin γt` on `[0, L]`, as long as its amplitudes stay
in the disc of the radius `ρ`. -/
theorem exists_forall_abs_sub_steady_le (lam e k f ρ L : ℝ) :
    ∃ C : ℝ, ∀ γ : ℝ, 0 < γ → ∀ (ω₀ β F : ℝ) (x v : ℝ → ℝ) (z₀ : ℝ × ℝ),
      detuning ω₀ γ = e → nonlinearity β γ = k → forcing F γ = f →
      IsMotionOn lam ω₀ β F γ x v (Icc 0 L) → averagedField lam e k f z₀ = 0 →
      z₀ ∈ Metric.closedBall (0 : ℝ × ℝ) ρ →
      (∀ t ∈ Icc 0 L, amplitude γ x v t ∈ Metric.closedBall (0 : ℝ × ℝ) ρ) →
      amplitude γ x v 0 = z₀ →
      ∀ t ∈ Icc 0 L,
        |x t - (z₀.1 * Real.cos (γ * t) + z₀.2 * Real.sin (γ * t))| ≤ 2 * C / γ := by
  obtain ⟨C, hC⟩ := exists_forall_norm_amplitude_sub_le lam e k f ρ L
  refine ⟨C, fun γ hγ ω₀ β F x v z₀ he hk hf hm hz₀ hz₀K hzK h0 t ht => ?_⟩
  have hbound := hC γ hγ ω₀ β F x v (fun _ => z₀) he hk hf hm
    (fun s _ => by rw [hz₀]; exact hasDerivAt_const s z₀) hzK (fun _ _ => hz₀K) h0 t ht
  have h1 : |(amplitude γ x v t).1 - z₀.1| ≤ C / γ := by
    rw [← Real.norm_eq_abs]
    exact (norm_fst_le (amplitude γ x v t - z₀)).trans hbound
  have h2 : |(amplitude γ x v t).2 - z₀.2| ≤ C / γ := by
    rw [← Real.norm_eq_abs]
    exact (norm_snd_le (amplitude γ x v t - z₀)).trans hbound
  have hx : x t - (z₀.1 * Real.cos (γ * t) + z₀.2 * Real.sin (γ * t)) =
      ((amplitude γ x v t).1 - z₀.1) * Real.cos (γ * t) +
        ((amplitude γ x v t).2 - z₀.2) * Real.sin (γ * t) := by
    rw [← amplitude_fst_mul_cos_add γ x v t]
    ring
  rw [hx]
  have h3 : |((amplitude γ x v t).1 - z₀.1) * Real.cos (γ * t)| ≤ C / γ := by
    rw [abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)).trans h1
  have h4 : |((amplitude γ x v t).2 - z₀.2) * Real.sin (γ * t)| ≤ C / γ := by
    rw [abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)).trans h2
  calc |((amplitude γ x v t).1 - z₀.1) * Real.cos (γ * t) +
        ((amplitude γ x v t).2 - z₀.2) * Real.sin (γ * t)|
      ≤ C / γ + C / γ := (abs_add_le _ _).trans (add_le_add h3 h4)
    _ = 2 * C / γ := by ring

end ProjectAinos.Mechanics.NonlinearResonance
