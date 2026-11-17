/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The angle described from the closest approach to infinity

Landau–Lifshitz (18.4). Along a motion in a central field the radius and the
polar angle satisfy `ṙ² = F(r)` and `φ̇ = ℓ/r²`, with `ℓ = M/m` and
`F(r) = (2/m)(E − U(r)) − ℓ²/r²`. After the closest approach `ṙ > 0`.

* `angleDensity ℓ F ρ = (ℓ/ρ²)/√F(ρ)` is the integrand of (18.4).
* `integral_angleDensity_eq`: up to a finite time the angle described is the
  integral of the density from the closest approach to the radius reached. The
  integrand has an integrable singularity at the closest approach, and the
  integral is a Lebesgue integral.
* `tendsto_angle_atTop`: if the radius tends to infinity and the density is
  integrable at infinity, the angle tends to
  `φ(0) + ∫_{r₀}^∞ (ℓ/ρ²) dρ/√F(ρ)`.
* `integrableOn_angleDensity_Ioi`: the density is integrable at infinity when
  `F` is bounded below by a positive constant there.
-/

@[expose] public section
noncomputable section

open Set Filter MeasureTheory
open scoped Real Topology

namespace ProjectAinos.Mechanics.Scattering

/-- The integrand `(ℓ/ρ²)/√F(ρ)` of the angle as an integral over the radius. -/
def angleDensity (ℓ : ℝ) (F : ℝ → ℝ) (ρ : ℝ) : ℝ := ℓ / ρ ^ 2 / √(F ρ)

/-- The angle of deflection `χ = π − 2φ₀` of Landau–Lifshitz (18.1), (18.4),
with `φ₀` the integral of the density from the closest approach `r₀` to
infinity. This is the unwrapped angle: the angle between the asymptotes is
`arccos (cos χ)`, which is `|χ|` when `|χ| ≤ π`. -/
def deflectionAngle (ℓ : ℝ) (F : ℝ → ℝ) (r₀ : ℝ) : ℝ :=
  π - 2 * ∫ ρ in Ioi r₀, angleDensity ℓ F ρ

variable {ℓ : ℝ} {F r v φ : ℝ → ℝ}

/-- The radius increases after the closest approach. -/
theorem strictMonoOn_radius_of_pos (hrc : ContinuousOn r (Ici 0))
    (hr : ∀ t, 0 < t → HasDerivAt r (v t) t) (hv : ∀ t, 0 < t → 0 < v t) :
    StrictMonoOn r (Ici 0) :=
  strictMonoOn_of_deriv_pos (convex_Ici 0) hrc fun t ht => by
    rw [interior_Ici] at ht
    rw [(hr t ht).deriv]
    exact hv t ht

theorem image_Ioc_radius (hrc : ContinuousOn r (Ici 0))
    (hr : ∀ t, 0 < t → HasDerivAt r (v t) t) (hv : ∀ t, 0 < t → 0 < v t) {T : ℝ}
    (hT : 0 ≤ T) : r '' Ioc 0 T = Ioc (r 0) (r T) := by
  have hmono := strictMonoOn_radius_of_pos hrc hr hv
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨hmono self_mem_Ici ht.1.le ht.1,
      hmono.monotoneOn (mem_Ici.mpr ht.1.le) (mem_Ici.mpr hT) ht.2⟩
  · intro hy
    obtain ⟨t, ht, rfl⟩ := intermediate_value_Icc hT (hrc.mono Icc_subset_Ici_self)
      ⟨hy.1.le, hy.2⟩
    refine ⟨t, ⟨lt_of_le_of_ne ht.1 fun h0 => ?_, ht.2⟩, rfl⟩
    rw [← h0] at hy
    exact lt_irrefl _ hy.1

/-- Landau–Lifshitz (18.4) up to a finite time: the angle described after the
closest approach is the integral of the density over the radius. -/
theorem integral_angleDensity_eq (hrc : ContinuousOn r (Ici 0))
    (hr : ∀ t, 0 < t → HasDerivAt r (v t) t) (hv : ∀ t, 0 < t → 0 < v t)
    (hF : ∀ t, 0 < t → v t ^ 2 = F (r t)) (hr0 : 0 < r 0)
    (hφc : ContinuousOn φ (Ici 0)) (hφ : ∀ t, 0 < t → HasDerivAt φ (ℓ / r t ^ 2) t) {T : ℝ}
    (hT : 0 ≤ T) :
    IntegrableOn (angleDensity ℓ F) (Ioc (r 0) (r T)) ∧
      ∫ ρ in Ioc (r 0) (r T), angleDensity ℓ F ρ = φ T - φ 0 := by
  have hmono := strictMonoOn_radius_of_pos hrc hr hv
  have hinj : InjOn r (Ioc 0 T) := (hmono.mono fun t ht => mem_Ici.mpr ht.1.le).injOn
  have hd : ∀ t ∈ Ioc 0 T, HasDerivWithinAt r (v t) (Ioc 0 T) t := fun t ht =>
    (hr t ht.1).hasDerivWithinAt
  have hpt : ∀ t ∈ Ioc 0 T, |v t| • angleDensity ℓ F (r t) = ℓ / r t ^ 2 := by
    intro t ht
    have hvt := hv t ht.1
    have hsq : √(F (r t)) = v t := by
      rw [← hF t ht.1, Real.sqrt_sq hvt.le]
    rw [abs_of_pos hvt, smul_eq_mul, angleDensity, hsq]
    field_simp
  have hrpos : ∀ t ∈ Icc 0 T, 0 < r t := fun t ht =>
    hr0.trans_le (hmono.monotoneOn self_mem_Ici (mem_Ici.mpr ht.1) ht.1)
  have hcont : ContinuousOn (fun t => ℓ / r t ^ 2) (Icc 0 T) :=
    continuousOn_const.div ((hrc.mono Icc_subset_Ici_self).pow 2) fun t ht =>
      pow_ne_zero 2 (hrpos t ht).ne'
  have hint : IntervalIntegrable (fun t => ℓ / r t ^ 2) volume 0 T :=
    (hcont.mono (by rw [uIcc_of_le hT])).intervalIntegrable
  have hint' : IntegrableOn (fun t => ℓ / r t ^ 2) (Ioc 0 T) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp hint
  have himage := image_Ioc_radius hrc hr hv hT
  constructor
  · rw [← himage, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioc hd hinj]
    exact hint'.congr_fun (fun t ht => (hpt t ht).symm) measurableSet_Ioc
  · rw [← himage, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc hd hinj,
      setIntegral_congr_fun measurableSet_Ioc hpt, ← intervalIntegral.integral_of_le hT]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT
      (hφc.mono Icc_subset_Ici_self) (fun t ht => hφ t ht.1) hint

/-- Landau–Lifshitz (18.4): the angle described from the closest approach to
infinity is the integral of the density from the closest approach to
infinity. -/
theorem tendsto_angle_atTop (hrc : ContinuousOn r (Ici 0))
    (hr : ∀ t, 0 < t → HasDerivAt r (v t) t) (hv : ∀ t, 0 < t → 0 < v t)
    (hF : ∀ t, 0 < t → v t ^ 2 = F (r t)) (hr0 : 0 < r 0)
    (hφc : ContinuousOn φ (Ici 0)) (hφ : ∀ t, 0 < t → HasDerivAt φ (ℓ / r t ^ 2) t)
    (hinf : Tendsto r atTop atTop) {R : ℝ} (htail : IntegrableOn (angleDensity ℓ F) (Ioi R)) :
    IntegrableOn (angleDensity ℓ F) (Ioi (r 0)) ∧
      Tendsto φ atTop (𝓝 (φ 0 + ∫ ρ in Ioi (r 0), angleDensity ℓ F ρ)) := by
  have hfin := fun (T : ℝ) (hT : 0 ≤ T) => integral_angleDensity_eq hrc hr hv hF hr0 hφc hφ hT
  obtain ⟨T₁, hT₁⟩ := (hinf.eventually_ge_atTop R).and (eventually_ge_atTop 0) |>.exists
  have hI : IntegrableOn (angleDensity ℓ F) (Ioi (r 0)) := by
    refine ((hfin T₁ hT₁.2).1.union (htail.mono_set (Ioi_subset_Ioi hT₁.1))).mono_set ?_
    intro ρ hρ
    rcases le_or_gt ρ (r T₁) with h | h
    · exact Or.inl ⟨hρ, h⟩
    · exact Or.inr h
  refine ⟨hI, ?_⟩
  have hlim := intervalIntegral_tendsto_integral_Ioi (r 0) hI hinf
  have hmono := strictMonoOn_radius_of_pos hrc hr hv
  have hev : (fun T => ∫ ρ in r 0..r T, angleDensity ℓ F ρ) =ᶠ[atTop] fun T => φ T - φ 0 := by
    filter_upwards [eventually_ge_atTop 0] with T hT
    rw [intervalIntegral.integral_of_le
      (hmono.monotoneOn self_mem_Ici (mem_Ici.mpr hT) hT), (hfin T hT).2]
  have h2 := (hlim.congr' hev).const_add (φ 0)
  simpa using h2

/-- The density is integrable at infinity when `F` is bounded below there by
a positive constant. -/
theorem integrableOn_angleDensity_Ioi {R c : ℝ} (hR : 0 < R) (hc : 0 < c)
    (hFc : ContinuousOn F (Ici R)) (hF : ∀ ρ, R ≤ ρ → c ^ 2 ≤ F ρ) (ℓ : ℝ) :
    IntegrableOn (angleDensity ℓ F) (Ioi R) := by
  have hbound : IntegrableOn (fun ρ : ℝ => |ℓ| / c * ρ ^ (-2 : ℝ)) (Ioi R) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hR).const_mul _
  have hpos : ∀ ρ ∈ Ioi R, 0 < F ρ := fun ρ hρ =>
    (pow_pos hc 2).trans_le (hF ρ (mem_Ioi.mp hρ).le)
  have hmeas : AEStronglyMeasurable (angleDensity ℓ F) (volume.restrict (Ioi R)) := by
    have hcont : ContinuousOn (angleDensity ℓ F) (Ioi R) :=
      (continuousOn_const.div (continuousOn_id.pow 2) fun ρ hρ =>
        pow_ne_zero 2 (hR.trans hρ).ne').div
        ((hFc.mono Ioi_subset_Ici_self).sqrt) fun ρ hρ => (Real.sqrt_pos.mpr (hpos ρ hρ)).ne'
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  refine Integrable.mono' hbound hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ
  have hρpos : 0 < ρ := hR.trans hρ
  have hsqrt : c ≤ √(F ρ) := by
    rw [← Real.sqrt_sq hc.le]
    exact Real.sqrt_le_sqrt (hF ρ (mem_Ioi.mp hρ).le)
  have hrpow : ρ ^ (-2 : ℝ) = (ρ ^ 2)⁻¹ := by
    rw [Real.rpow_neg hρpos.le]
    norm_num
  rw [Real.norm_eq_abs, angleDensity, abs_div, abs_div, abs_of_pos (pow_pos hρpos 2),
    abs_of_pos (Real.sqrt_pos.mpr (hpos ρ hρ)), hrpow, div_div, div_mul_eq_mul_div,
    ← div_eq_mul_inv, div_div]
  exact div_le_div_of_nonneg_left (abs_nonneg ℓ) (by positivity)
    (by nlinarith [mul_le_mul_of_nonneg_left hsqrt (sq_nonneg ρ)])

end ProjectAinos.Mechanics.Scattering
