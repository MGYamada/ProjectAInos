/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.OneDimension.Orbit
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Abel's inversion formula

Landau–Lifshitz §12: the width of a well at the energy `V` is determined by the
period as a function of the energy,

`x₂(V) − x₁(V) = (1 / π√(2m)) ∫ T(E) dE / √(V − E)`.

The proof is an exchange of two integrals with integrable singularities.

* `lintegral_inv_sqrt_mul_inv_sqrt`: `∫ dE / √((E − u)(V − E)) = π` for `u < V`,
  as an integral of a non-negative function over the whole line; the integrand
  vanishes outside `(u, V)` because the square root of a negative number is
  zero.
* `lintegral_levelTime_mul`: for any measurable `U` and any set `Ω`,
  `∫ (∫_Ω dx / √(E − U(x))) dE / √(V − E) = π · |{x ∈ Ω : U(x) < V}|`,
  by Tonelli's theorem. No property of a well is used.
* `abel_inversion`: for wells that are nested as the energy increases from the
  bottom `E₀` to `V`, the inner integral is `T(E) / √(2m)`, which gives the
  formula. The oscillator is an instance (`abel_inversion_oscillator`).
-/

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped Real ContDiff ENNReal

namespace ProjectAInos.Mechanics.OneDim

variable {U : ℝ → ℝ}

/-- The integral `∫ dE / √((E − u)(V − E))` over the whole line is `π` when
`u < V`, and zero otherwise. -/
theorem lintegral_inv_sqrt_mul_inv_sqrt (u V : ℝ) :
    ∫⁻ E, ENNReal.ofReal (1 / √(E - u)) * ENNReal.ofReal (1 / √(V - E)) =
      if u < V then ENNReal.ofReal π else 0 := by
  split_ifs with huV
  · have hint : IntegrableOn (fun E => (fun _ : ℝ => (1 : ℝ)) E /
        √((E - u) * (V - E) * (fun _ : ℝ => (1 : ℝ)) E)) (Ioo u V) :=
      (integrableOn_div_sqrt_turning huV continuousOn_const continuousOn_const
        fun _ _ => one_pos).mono_set Ioo_subset_Icc_self
    have hval : ∫ E in Ioo u V, (fun _ : ℝ => (1 : ℝ)) E /
        √((E - u) * (V - E) * (fun _ : ℝ => (1 : ℝ)) E) = π := by
      have h := integral_div_sqrt_turning huV (fun _ => 1) fun _ => 1
      rw [intervalIntegral.integral_of_le huV.le, integral_Ioc_eq_integral_Ioo] at h
      rw [h]
      simp
    have hfun : (fun E => ENNReal.ofReal (1 / √(E - u)) * ENNReal.ofReal (1 / √(V - E))) =
        (Ioo u V).indicator fun E => ENNReal.ofReal ((fun _ : ℝ => (1 : ℝ)) E /
          √((E - u) * (V - E) * (fun _ : ℝ => (1 : ℝ)) E)) := by
      funext E
      by_cases hE : E ∈ Ioo u V
      · rw [indicator_of_mem hE, ← ENNReal.ofReal_mul (by positivity), mul_one,
          Real.sqrt_mul (sub_pos.mpr hE.1).le]
        congr 1
        field_simp
      · rw [indicator_of_notMem hE]
        rw [mem_Ioo, not_and_or, not_lt, not_lt] at hE
        rcases hE with hE | hE
        · rw [Real.sqrt_eq_zero_of_nonpos (by linarith)]
          simp
        · rw [Real.sqrt_eq_zero_of_nonpos (by linarith : V - E ≤ 0)]
          simp
    rw [hfun, lintegral_indicator measurableSet_Ioo,
      ← ofReal_integral_eq_lintegral_ofReal hint, hval]
    exact (ae_restrict_iff' measurableSet_Ioo).mpr (Filter.Eventually.of_forall fun E hE => by
      change (0 : ℝ) ≤ 1 / √((E - u) * (V - E) * 1)
      positivity)
  · have hzero : (fun E => ENNReal.ofReal (1 / √(E - u)) * ENNReal.ofReal (1 / √(V - E))) =
        fun _ => 0 := by
      funext E
      rcases le_or_gt E u with hE | hE
      · rw [Real.sqrt_eq_zero_of_nonpos (by linarith)]
        simp
      · rw [Real.sqrt_eq_zero_of_nonpos (by linarith : V - E ≤ 0)]
        simp
    rw [hzero]
    simp

/-- Abel's exchange of integrals: for any measurable potential and any set,
`∫ (∫_Ω dx / √(E − U(x))) dE / √(V − E) = π · |{x ∈ Ω : U(x) < V}|`. -/
theorem lintegral_levelTime_mul (hU : Measurable U) (Ω : Set ℝ) (V : ℝ) :
    ∫⁻ E, (∫⁻ x in Ω, ENNReal.ofReal (1 / √(E - U x))) * ENNReal.ofReal (1 / √(V - E)) =
      ENNReal.ofReal π * volume (Ω ∩ {x | U x < V}) := by
  have hmeas : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal (1 / √(p.1 - U p.2)) * ENNReal.ofReal (1 / √(V - p.1)) := by
    have h1 : Measurable fun p : ℝ × ℝ => 1 / √(p.1 - U p.2) :=
      measurable_const.div
        (Real.continuous_sqrt.measurable.comp (measurable_fst.sub (hU.comp measurable_snd)))
    have h2 : Measurable fun p : ℝ × ℝ => 1 / √(V - p.1) :=
      measurable_const.div
        (Real.continuous_sqrt.measurable.comp (measurable_const.sub measurable_fst))
    exact (ENNReal.measurable_ofReal.comp h1).mul (ENNReal.measurable_ofReal.comp h2)
  have hstep : ∀ E : ℝ, (∫⁻ x in Ω, ENNReal.ofReal (1 / √(E - U x))) *
      ENNReal.ofReal (1 / √(V - E)) =
      ∫⁻ x in Ω, ENNReal.ofReal (1 / √(E - U x)) * ENNReal.ofReal (1 / √(V - E)) := by
    intro E
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  simp_rw [hstep]
  rw [lintegral_lintegral_swap (μ := volume) (ν := volume.restrict Ω)
    (f := fun E x => ENNReal.ofReal (1 / √(E - U x)) * ENNReal.ofReal (1 / √(V - E)))
    hmeas.aemeasurable]
  simp_rw [lintegral_inv_sqrt_mul_inv_sqrt]
  have hind : (fun x => if U x < V then ENNReal.ofReal π else 0) =
      {x | U x < V}.indicator fun _ => ENNReal.ofReal π := by
    funext x
    by_cases hx : U x < V
    · simp [Set.indicator, hx]
    · simp [Set.indicator, hx]
  have hset : MeasurableSet {x | U x < V} := measurableSet_lt hU measurable_const
  rw [hind, lintegral_indicator hset, setLIntegral_const, Measure.restrict_apply hset,
    inter_comm]

namespace IsWell

/-- The inner integral of Abel's formula over a well is the period divided by
`√(2m)`. -/
theorem lintegral_inv_sqrt_eq {E a b m : ℝ} (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U)
    (hm : 0 < m) :
    ∫⁻ x in Ioo a b, ENNReal.ofReal (1 / √(E - U x)) =
      ENNReal.ofReal (orbitPeriod m U a b / √(2 * m)) := by
  have hfun : ∀ x : ℝ, 1 / √(E - U x) = (fun _ : ℝ => (1 : ℝ)) x /
      √((x - a) * (b - x) * wellFactor U a b x) := fun x => by rw [h.sub_eq hU x]
  have hint : IntegrableOn (fun x => 1 / √(E - U x)) (Ioo a b) := by
    simp_rw [hfun]
    exact (integrableOn_div_sqrt_turning h.lt continuousOn_const
      (contDiff_wellFactor_right hU a b).continuous.continuousOn
      fun x hx => h.wellFactor_pos hU hx).mono_set Ioo_subset_Icc_self
  have hs : √(2 * m) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun x => by positivity), h.orbitPeriod_eq hU m,
    intervalIntegral.integral_of_le h.lt.le, integral_Ioc_eq_integral_Ioo]
  congr 1
  field_simp

end IsWell

/-- Abel's inversion formula (Landau–Lifshitz (12.1)): for wells that are nested
as the energy increases from the bottom `E₀` to `V`, the width at the energy `V`
is `(1 / π√(2m)) ∫ T(E) dE / √(V − E)`. -/
theorem abel_inversion (hU : ContDiff ℝ ∞ U) {m : ℝ} (hm : 0 < m) {E₀ V : ℝ} {x₁ x₂ : ℝ → ℝ}
    (hV : IsWell U V (x₁ V) (x₂ V)) (hw : ∀ E ∈ Ioo E₀ V, IsWell U E (x₁ E) (x₂ E))
    (hnest : ∀ E ∈ Ioo E₀ V, ∀ x, x ∈ Ioo (x₁ E) (x₂ E) ↔ x ∈ Ioo (x₁ V) (x₂ V) ∧ U x < E)
    (hbot : ∀ x ∈ Ioo (x₁ V) (x₂ V), E₀ ≤ U x) :
    x₂ V - x₁ V = 1 / (π * √(2 * m)) *
      ∫ E in Ioo E₀ V, orbitPeriod m U (x₁ E) (x₂ E) / √(V - E) := by
  have hs : 0 < √(2 * m) := Real.sqrt_pos.mpr (by positivity)
  -- the measure of the well at the energy `V`
  have hvol : volume (Ioo (x₁ V) (x₂ V) ∩ {x | U x < V}) = ENNReal.ofReal (x₂ V - x₁ V) := by
    have hsub : Ioo (x₁ V) (x₂ V) ∩ {x | U x < V} = Ioo (x₁ V) (x₂ V) :=
      inter_eq_left.mpr fun x hx => hV.lt_energy x hx
    rw [hsub, Real.volume_Ioo]
  have hmain := lintegral_levelTime_mul hU.continuous.measurable (Ioo (x₁ V) (x₂ V)) V
  rw [hvol] at hmain
  -- the inner integral at each energy
  have hinner : ∀ E : ℝ, (∫⁻ x in Ioo (x₁ V) (x₂ V), ENNReal.ofReal (1 / √(E - U x))) *
      ENNReal.ofReal (1 / √(V - E)) =
      (Ioo E₀ V).indicator (fun E => ENNReal.ofReal
        (orbitPeriod m U (x₁ E) (x₂ E) / √(2 * m) / √(V - E))) E := by
    intro E
    by_cases hE : E ∈ Ioo E₀ V
    · rw [indicator_of_mem hE]
      have hrestr : ∫⁻ x in Ioo (x₁ V) (x₂ V), ENNReal.ofReal (1 / √(E - U x)) =
          ∫⁻ x in Ioo (x₁ E) (x₂ E), ENNReal.ofReal (1 / √(E - U x)) := by
        have hind : ∀ x ∈ Ioo (x₁ V) (x₂ V), ENNReal.ofReal (1 / √(E - U x)) =
            (Ioo (x₁ E) (x₂ E)).indicator (fun x => ENNReal.ofReal (1 / √(E - U x))) x := by
          intro x hx
          by_cases hxE : x ∈ Ioo (x₁ E) (x₂ E)
          · rw [indicator_of_mem hxE]
          · rw [indicator_of_notMem hxE]
            have hge : E ≤ U x := by
              by_contra hlt
              exact hxE ((hnest E hE x).mpr ⟨hx, not_le.mp hlt⟩)
            rw [Real.sqrt_eq_zero_of_nonpos (by linarith)]
            simp
        rw [setLIntegral_congr_fun measurableSet_Ioo hind, lintegral_indicator measurableSet_Ioo,
          Measure.restrict_restrict measurableSet_Ioo]
        congr 2
        exact inter_eq_left.mpr fun x hx => ((hnest E hE x).mp hx).1
      rw [hrestr, (hw E hE).lintegral_inv_sqrt_eq hU hm,
        ← ENNReal.ofReal_mul (div_nonneg ((hw E hE).orbitPeriod_pos hU hm).le hs.le)]
      congr 1
      ring
    · rw [indicator_of_notMem hE]
      rw [mem_Ioo, not_and_or, not_lt, not_lt] at hE
      rcases hE with hE | hE
      · have hzero : ∀ x ∈ Ioo (x₁ V) (x₂ V), ENNReal.ofReal (1 / √(E - U x)) = 0 := by
          intro x hx
          rw [Real.sqrt_eq_zero_of_nonpos (by linarith [hbot x hx])]
          simp
        rw [setLIntegral_congr_fun measurableSet_Ioo hzero]
        simp
      · rw [Real.sqrt_eq_zero_of_nonpos (by linarith : V - E ≤ 0)]
        simp
  simp_rw [hinner] at hmain
  rw [lintegral_indicator measurableSet_Ioo] at hmain
  -- from the integral of a non-negative function to the real integral
  have hnonneg : ∀ E ∈ Ioo E₀ V, 0 ≤ orbitPeriod m U (x₁ E) (x₂ E) / √(2 * m) / √(V - E) :=
    fun E hE => div_nonneg (div_nonneg ((hw E hE).orbitPeriod_pos hU hm).le hs.le)
      (Real.sqrt_nonneg _)
  have hreal : ∫ E in Ioo E₀ V, orbitPeriod m U (x₁ E) (x₂ E) / √(2 * m) / √(V - E) =
      π * (x₂ V - x₁ V) := by
    by_cases hint : IntegrableOn
        (fun E => orbitPeriod m U (x₁ E) (x₂ E) / √(2 * m) / √(V - E)) (Ioo E₀ V)
    · have h1 := ofReal_integral_eq_lintegral_ofReal hint
        ((ae_restrict_iff' measurableSet_Ioo).mpr (Filter.Eventually.of_forall hnonneg))
      rw [hmain, ← ENNReal.ofReal_mul Real.pi_pos.le] at h1
      have hpos : 0 ≤ π * (x₂ V - x₁ V) :=
        mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hV.lt.le)
      have hint_nonneg : 0 ≤ ∫ E in Ioo E₀ V,
          orbitPeriod m U (x₁ E) (x₂ E) / √(2 * m) / √(V - E) :=
        setIntegral_nonneg measurableSet_Ioo hnonneg
      exact (ENNReal.ofReal_eq_ofReal_iff hint_nonneg hpos).mp h1
    · -- a non-negative function with a finite integral that agrees with a measurable one
      exfalso
      apply hint
      have hmeasG : Measurable fun E : ℝ =>
          ∫⁻ x in Ioo (x₁ V) (x₂ V), ENNReal.ofReal (1 / √(E - U x)) := by
        have h1 : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (1 / √(p.1 - U p.2)) :=
          ENNReal.measurable_ofReal.comp (measurable_const.div
            (Real.continuous_sqrt.measurable.comp
              (measurable_fst.sub (hU.continuous.measurable.comp measurable_snd))))
        exact h1.lintegral_prod_right'
      have hae : (fun E => orbitPeriod m U (x₁ E) (x₂ E) / √(2 * m) / √(V - E))
          =ᵐ[volume.restrict (Ioo E₀ V)] fun E =>
            ((∫⁻ x in Ioo (x₁ V) (x₂ V), ENNReal.ofReal (1 / √(E - U x))) *
              ENNReal.ofReal (1 / √(V - E))).toReal :=
        (ae_restrict_iff' measurableSet_Ioo).mpr (Filter.Eventually.of_forall fun E hE => by
          change _ = (_ : ℝ≥0∞).toReal
          rw [hinner E, indicator_of_mem hE, ENNReal.toReal_ofReal (hnonneg E hE)])
      have hmeasF : AEStronglyMeasurable
          (fun E => orbitPeriod m U (x₁ E) (x₂ E) / √(2 * m) / √(V - E))
          (volume.restrict (Ioo E₀ V)) := by
        refine AEStronglyMeasurable.congr ?_ hae.symm
        exact ((hmeasG.mul (ENNReal.measurable_ofReal.comp (measurable_const.div
          (Real.continuous_sqrt.measurable.comp
            (measurable_const.sub measurable_id))))).ennreal_toReal).aestronglyMeasurable
      refine ⟨hmeasF, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal ((ae_restrict_iff' measurableSet_Ioo).mpr
        (Filter.Eventually.of_forall hnonneg)), hmain]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hfun : (fun E => orbitPeriod m U (x₁ E) (x₂ E) / √(V - E)) =
      fun E => √(2 * m) * (orbitPeriod m U (x₁ E) (x₂ E) / √(2 * m) / √(V - E)) := by
    funext E
    field_simp
  rw [hfun, integral_const_mul, hreal]
  field_simp

end ProjectAInos.Mechanics.OneDim
