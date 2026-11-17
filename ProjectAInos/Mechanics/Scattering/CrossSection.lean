/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Scattering.Coulomb
public import ProjectAInos.Mechanics.Rutherford
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# The cross-section as a measure

Landau–Lifshitz §18. The particles of a uniform beam are labelled by the
impact parameter `ρ`, and the area of the beam with impact parameters in a set
is the integral of `2πρ dρ` (`impactMeasure`). The effective cross-section is
the push-forward of this measure by the deflection function `χ(ρ)`
(`crossSection`).

* `crossSection_apply`: on a set `A` of angles on which the deflection function
  has an injective differentiable inverse `b`, the cross-section has the density
  `b |b′| / sin χ` with respect to the solid angle `2π sin χ dχ`
  (Landau–Lifshitz (18.8)).
* `crossSection_coulomb`: Rutherford's formula (19.3): in a repulsive Coulomb
  field the density is `(a/2)² / sin⁴ (χ/2)`, with `a = α/m v∞²`.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped Real ENNReal

namespace ProjectAInos.Mechanics.Scattering

/-- The area of the beam as a measure on the impact parameter: `2πρ dρ` on
`ρ > 0`. -/
def impactMeasure : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity fun ρ => ENNReal.ofReal (2 * π * ρ)

/-- The solid angle as a measure on the angle of deflection: `2π sin χ dχ` on
`0 < χ < π`. -/
def solidAngle : Measure ℝ :=
  (volume.restrict (Ioo 0 π)).withDensity fun χ => ENNReal.ofReal (2 * π * Real.sin χ)

/-- The effective cross-section: the push-forward of the area of the beam by
the deflection function. -/
def crossSection (χ : ℝ → ℝ) : Measure ℝ := Measure.map χ impactMeasure

theorem impactMeasure_apply {S : Set ℝ} (hS : MeasurableSet S) :
    impactMeasure S = ∫⁻ ρ in S ∩ Ioi 0, ENNReal.ofReal (2 * π * ρ) := by
  rw [impactMeasure, withDensity_apply _ hS, Measure.restrict_restrict hS]

theorem setLIntegral_solidAngle {A : Set ℝ} (hA : MeasurableSet A) (hAπ : A ⊆ Ioo 0 π)
    (g : ℝ → ℝ≥0∞) :
    ∫⁻ x in A, g x ∂solidAngle = ∫⁻ x in A, ENNReal.ofReal (2 * π * Real.sin x) * g x := by
  have hmeas : Measurable fun χ : ℝ => ENNReal.ofReal (2 * π * Real.sin χ) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul Real.measurable_sin)
  rw [solidAngle, setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable _ hmeas g hA
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    Measure.restrict_restrict_of_subset hAπ]
  rfl

/-- Landau–Lifshitz (18.8): on a branch of the deflection function with the
inverse `b`, `dσ = (ρ/sin χ) |dρ/dχ| do`. -/
theorem crossSection_apply {χ b b' : ℝ → ℝ} (hχ : Measurable χ) {A : Set ℝ}
    (hA : MeasurableSet A) (hAπ : A ⊆ Ioo 0 π)
    (hb : ∀ x ∈ A, HasDerivWithinAt b (b' x) A x) (hinj : InjOn b A)
    (hpre : χ ⁻¹' A ∩ Ioi 0 = b '' A) :
    crossSection χ A = ∫⁻ x in A, ENNReal.ofReal (b x * |b' x| / Real.sin x) ∂solidAngle := by
  rw [crossSection, Measure.map_apply hχ hA, impactMeasure_apply (hχ hA), hpre,
    lintegral_image_eq_lintegral_abs_deriv_mul hA hb hinj, setLIntegral_solidAngle hA hAπ]
  refine setLIntegral_congr_fun hA fun x hx => ?_
  have hsin : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi (hAπ hx).1 (hAπ hx).2
  have hbpos : 0 < b x := by
    have : b x ∈ χ ⁻¹' A ∩ Ioi 0 := hpre ▸ mem_image_of_mem b hx
    exact this.2
  rw [← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

/-! ### Rutherford's formula -/

namespace Coulomb

theorem continuous_deflection {a : ℝ} (ha : 0 < a) : Continuous (deflection a) := by
  have hpos : ∀ ρ : ℝ, 0 < a ^ 2 + ρ ^ 2 := fun ρ => by positivity
  unfold deflection hyp
  exact continuous_const.sub (continuous_const.mul (Real.continuous_arccos.comp
    (continuous_const.div ((continuous_const.add (continuous_id.pow 2)).sqrt)
      fun ρ => (Real.sqrt_pos.mpr (hpos ρ)).ne')))

/-- The impact parameter of the angle of deflection `χ`: `ρ = a cot (χ/2)`. -/
def impact (a χ : ℝ) : ℝ := a * (Real.cos (χ / 2) / Real.sin (χ / 2))

theorem impact_pos {a χ : ℝ} (ha : 0 < a) (hχ : χ ∈ Ioo 0 π) : 0 < impact a χ := by
  have hs : 0 < Real.sin (χ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hχ.1]) (by linarith [hχ.2, Real.pi_pos])
  have hc : 0 < Real.cos (χ / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hχ.1, Real.pi_pos], by linarith [hχ.2]⟩
  exact mul_pos ha (div_pos hc hs)

/-- The impact parameter `a cot (χ/2)` is deflected by the angle `χ`. -/
theorem deflection_impact {a χ : ℝ} (ha : 0 < a) (hχ : χ ∈ Ioo 0 π) :
    deflection a (impact a χ) = χ := by
  have hs : 0 < Real.sin (χ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hχ.1]) (by linarith [hχ.2, Real.pi_pos])
  have hhyp : hyp a (impact a χ) = a / Real.sin (χ / 2) := by
    have e : a ^ 2 + impact a χ ^ 2 = (a / Real.sin (χ / 2)) ^ 2 := by
      have hsq := Real.sin_sq_add_cos_sq (χ / 2)
      rw [impact]
      field_simp
      linear_combination hsq
    rw [hyp, e, Real.sqrt_sq (by positivity)]
  have hratio : a / hyp a (impact a χ) = Real.cos (π / 2 - χ / 2) := by
    rw [hhyp, Real.cos_pi_div_two_sub]
    field_simp
  rw [deflection, hratio, Real.arccos_cos (by linarith [hχ.2]) (by linarith [hχ.1, Real.pi_pos])]
  ring

/-- The angle of deflection of the impact parameter `ρ` gives `ρ` back. -/
theorem impact_deflection {a ρ : ℝ} (ha : 0 < a) (hρ : 0 < ρ) :
    impact a (deflection a ρ) = ρ := by
  rw [impact, cot_half_deflection hρ ha.ne']
  field_simp

/-- **Rutherford's formula** (Landau–Lifshitz (19.3)) as a statement about the
cross-section: in the repulsive Coulomb field `α/r`, with `a = α/m v∞²`,
`dσ = (a/2)² do / sin⁴ (χ/2)`. -/
theorem crossSection_coulomb {a : ℝ} (ha : 0 < a) {A : Set ℝ} (hA : MeasurableSet A)
    (hAπ : A ⊆ Ioo 0 π) :
    crossSection (deflection a) A =
      ∫⁻ x in A, ENNReal.ofReal ((a / 2) ^ 2 / Real.sin (x / 2) ^ 4) ∂solidAngle := by
  have hsin : ∀ x ∈ A, 0 < Real.sin (x / 2) := fun x hx =>
    Real.sin_pos_of_pos_of_lt_pi (by linarith [(hAπ hx).1])
      (by linarith [(hAπ hx).2, Real.pi_pos])
  have hcos : ∀ x ∈ A, 0 < Real.cos (x / 2) := fun x hx =>
    Real.cos_pos_of_mem_Ioo ⟨by linarith [(hAπ hx).1, Real.pi_pos], by linarith [(hAπ hx).2]⟩
  have hb : ∀ x ∈ A, HasDerivWithinAt (impact a) (-(a / (2 * Real.sin (x / 2) ^ 2))) A x :=
    fun x hx => (Rutherford.hasDerivAt_impactParameter a (hsin x hx).ne').hasDerivWithinAt
  have hinj : InjOn (impact a) A := fun x hx y hy hxy => by
    rw [← deflection_impact ha (hAπ hx), hxy, deflection_impact ha (hAπ hy)]
  have hpre : deflection a ⁻¹' A ∩ Ioi 0 = impact a '' A := by
    ext ρ
    constructor
    · rintro ⟨hρA, hρ⟩
      exact ⟨deflection a ρ, hρA, impact_deflection ha hρ⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨?_, impact_pos ha (hAπ hx)⟩
      rw [mem_preimage, deflection_impact ha (hAπ hx)]
      exact hx
  rw [crossSection_apply (continuous_deflection ha).measurable hA hAπ hb hinj hpre]
  refine setLIntegral_congr_fun hA fun x hx => ?_
  have hs := hsin x hx
  have hc := hcos x hx
  rw [abs_neg, abs_of_pos (by positivity), impact,
    Rutherford.rutherford a hs.ne' hc.ne']

theorem deflection_nonneg {a : ℝ} (ha : 0 < a) (ρ : ℝ) : 0 ≤ deflection a ρ := by
  have hhyp : 0 < hyp a ρ := by
    rw [hyp]
    positivity
  have h1 : 0 ≤ a / hyp a ρ := (div_pos ha hhyp).le
  have h2 := Real.arccos_le_pi_div_two.mpr h1
  rw [deflection]
  linarith

/-- The magnitude of the deflection depends on the magnitude of `a` only. -/
theorem abs_deflection {a : ℝ} (ha : a ≠ 0) (ρ : ℝ) : |deflection a ρ| = deflection |a| ρ := by
  rcases lt_or_gt_of_ne ha with h | h
  · have e : deflection a ρ = -deflection (-a) ρ := by rw [deflection_neg, neg_neg]
    rw [abs_of_neg h, e, abs_neg, abs_of_nonneg (deflection_nonneg (neg_pos.mpr h) ρ)]
  · rw [abs_of_pos h, abs_of_nonneg (deflection_nonneg h ρ)]

/-- Rutherford's formula for either sign of the field: the cross-section in
the magnitude of the angle of deflection is `(a/2)² do / sin⁴ (χ/2)`. -/
theorem crossSection_coulomb_abs {a : ℝ} (ha : a ≠ 0) {A : Set ℝ} (hA : MeasurableSet A)
    (hAπ : A ⊆ Ioo 0 π) :
    crossSection (fun ρ => |deflection a ρ|) A =
      ∫⁻ x in A, ENNReal.ofReal ((a / 2) ^ 2 / Real.sin (x / 2) ^ 4) ∂solidAngle := by
  have hfun : (fun ρ => |deflection a ρ|) = deflection |a| := funext (abs_deflection ha)
  rw [hfun, crossSection_coulomb (abs_pos.mpr ha) hA hAπ]
  refine setLIntegral_congr_fun hA fun x _ => ?_
  simp only [div_pow, sq_abs]

end Coulomb

end ProjectAInos.Mechanics.Scattering
