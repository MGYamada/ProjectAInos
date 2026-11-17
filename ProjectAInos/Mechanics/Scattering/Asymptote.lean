/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Scattering.RadialMotion
public import ProjectAInos.Mechanics.Scattering.Deflection
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The asymptotes of a scattering motion

For the radial motion `radius W r₀` with the angle `angle W r₀ ℓ`:

* `IsFactor.tendsto_angle_atTop`, `IsFactor.tendsto_angle_atBot`: the angle
  tends to `± φ₀` at `t → ± ∞`, with `φ₀ = ∫_{r₀}^∞ (ℓ/ρ²) dρ/√F(ρ)`
  (Landau–Lifshitz (18.4)).
* `position`, `velocity`: the motion in the plane; `hasDerivAt_velocity`: the
  acceleration is along the radius, with the coefficient `F′(r)/2 − ℓ²/r³`,
  which is `−U′(r)/m` for `F = (2/m)(E − U) − ℓ²/r²`.
* `position_cross_velocity`: the moment of the velocity is `ℓ`.
* `tendsto_velocity_atTop`, `tendsto_velocity_atBot`: the velocity tends to
  `v∞ (cos φ₀, sin φ₀)` and to `v∞ (−cos φ₀, sin φ₀)`.
* `asymptote_inner`: the scalar product of the two limits is
  `v∞² cos (π − 2φ₀)`, so the angle of deflection is `|π − 2φ₀|` (18.1).
-/

@[expose] public section
noncomputable section

open Set Filter MeasureTheory
open scoped Real Topology

namespace ProjectAInos.Mechanics.Scattering

variable {W : ℝ → ℝ} {r₀ C : ℝ}

namespace IsFactor

/-- Landau–Lifshitz (18.4) for the motion `radius W r₀`. -/
theorem tendsto_angle_atTop (h : IsFactor W r₀ C) (hr₀ : 0 < r₀) {F : ℝ → ℝ}
    (hF : ∀ r, r₀ ≤ r → F r = (r - r₀) * W r) (ℓ : ℝ) {R : ℝ}
    (htail : IntegrableOn (angleDensity ℓ F) (Ioi R)) :
    IntegrableOn (angleDensity ℓ F) (Ioi r₀) ∧
      Tendsto (angle W r₀ ℓ) atTop (𝓝 (∫ ρ in Ioi r₀, angleDensity ℓ F ρ)) := by
  have hmain := Scattering.tendsto_angle_atTop (r := radius W r₀) (v := radialVelocity W r₀)
    (φ := angle W r₀ ℓ) (ℓ := ℓ) (F := F) h.contDiff_radius.continuous.continuousOn
    (fun t _ => h.hasDerivAt_radius t) (fun t ht => h.radialVelocity_pos ht)
    (fun t _ => by rw [h.radialVelocity_sq, hF _ (le_radius W r₀ t)])
    (by rw [radius_zero]; exact hr₀)
    (continuous_iff_continuousAt.mpr fun t =>
      (h.hasDerivAt_angle hr₀ ℓ t).continuousAt).continuousOn
    (fun t _ => h.hasDerivAt_angle hr₀ ℓ t) h.tendsto_radius_atTop htail
  rw [radius_zero, angle_zero, zero_add] at hmain
  exact hmain

theorem tendsto_angle_atBot (h : IsFactor W r₀ C) (hr₀ : 0 < r₀) {F : ℝ → ℝ}
    (hF : ∀ r, r₀ ≤ r → F r = (r - r₀) * W r) (ℓ : ℝ) {R : ℝ}
    (htail : IntegrableOn (angleDensity ℓ F) (Ioi R)) :
    Tendsto (angle W r₀ ℓ) atBot (𝓝 (-∫ ρ in Ioi r₀, angleDensity ℓ F ρ)) := by
  have h1 := ((h.tendsto_angle_atTop hr₀ hF ℓ htail).2.comp tendsto_neg_atBot_atTop).neg
  refine h1.congr fun t => ?_
  rw [Function.comp_apply, h.angle_neg, neg_neg]

/-- The radial velocity tends to the speed at infinity. -/
theorem tendsto_radialVelocity_atTop (h : IsFactor W r₀ C) {F : ℝ → ℝ}
    (hF : ∀ r, r₀ ≤ r → F r = (r - r₀) * W r) {vinf : ℝ} (hv : 0 ≤ vinf)
    (hlim : Tendsto F atTop (𝓝 (vinf ^ 2))) :
    Tendsto (radialVelocity W r₀) atTop (𝓝 vinf) := by
  have h1 : Tendsto (fun t => √(F (radius W r₀ t))) atTop (𝓝 √(vinf ^ 2)) :=
    (Real.continuous_sqrt.tendsto _).comp (hlim.comp h.tendsto_radius_atTop)
  rw [Real.sqrt_sq hv] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [hF _ (le_radius W r₀ t), ← h.radialVelocity_sq, Real.sqrt_sq (h.radialVelocity_pos ht).le]

end IsFactor

/-! ### The motion in the plane -/

/-- The position in the plane. -/
def position (W : ℝ → ℝ) (r₀ ℓ t : ℝ) : ℝ × ℝ :=
  (radius W r₀ t * Real.cos (angle W r₀ ℓ t), radius W r₀ t * Real.sin (angle W r₀ ℓ t))

/-- The velocity in the plane. -/
def velocity (W : ℝ → ℝ) (r₀ ℓ t : ℝ) : ℝ × ℝ :=
  (radialVelocity W r₀ t * Real.cos (angle W r₀ ℓ t) -
      ℓ / radius W r₀ t * Real.sin (angle W r₀ ℓ t),
    radialVelocity W r₀ t * Real.sin (angle W r₀ ℓ t) +
      ℓ / radius W r₀ t * Real.cos (angle W r₀ ℓ t))

/-- The moment of the velocity about the centre is `ℓ`: for the speed `v∞` at
infinity the impact parameter is `ℓ/v∞`. -/
theorem position_cross_velocity (W : ℝ → ℝ) {r₀ : ℝ} (hr₀ : 0 < r₀) (ℓ t : ℝ) :
    (position W r₀ ℓ t).1 * (velocity W r₀ ℓ t).2 -
      (position W r₀ ℓ t).2 * (velocity W r₀ ℓ t).1 = ℓ := by
  have hpos : radius W r₀ t ≠ 0 := (hr₀.trans_le (le_radius W r₀ t)).ne'
  have hsq := Real.sin_sq_add_cos_sq (angle W r₀ ℓ t)
  simp only [position, velocity]
  field_simp
  linear_combination ℓ * hsq

namespace IsFactor

theorem hasDerivAt_position (h : IsFactor W r₀ C) (hr₀ : 0 < r₀) (ℓ t : ℝ) :
    HasDerivAt (position W r₀ ℓ) (velocity W r₀ ℓ t) t := by
  have hr := h.hasDerivAt_radius t
  have hφ := h.hasDerivAt_angle hr₀ ℓ t
  have hpos : radius W r₀ t ≠ 0 := (hr₀.trans_le (le_radius W r₀ t)).ne'
  have hc : HasDerivAt (fun s => Real.cos (angle W r₀ ℓ s))
      (-Real.sin (angle W r₀ ℓ t) * (ℓ / radius W r₀ t ^ 2)) t :=
    HasDerivAt.comp t (Real.hasDerivAt_cos _) hφ
  have hs : HasDerivAt (fun s => Real.sin (angle W r₀ ℓ s))
      (Real.cos (angle W r₀ ℓ t) * (ℓ / radius W r₀ t ^ 2)) t :=
    HasDerivAt.comp t (Real.hasDerivAt_sin _) hφ
  have h1 := hr.mul hc
  have h2 := hr.mul hs
  have h3 : HasDerivAt (position W r₀ ℓ)
      (radialVelocity W r₀ t * Real.cos (angle W r₀ ℓ t) +
          radius W r₀ t * (-Real.sin (angle W r₀ ℓ t) * (ℓ / radius W r₀ t ^ 2)),
        radialVelocity W r₀ t * Real.sin (angle W r₀ ℓ t) +
          radius W r₀ t * (Real.cos (angle W r₀ ℓ t) * (ℓ / radius W r₀ t ^ 2))) t :=
    h1.prodMk h2
  refine h3.congr_deriv (Prod.ext ?_ ?_)
  · simp only [velocity]
    field_simp
    ring
  · simp only [velocity]
    field_simp

/-- The acceleration is along the radius: Newton's equation in a central
field. -/
theorem hasDerivAt_velocity (h : IsFactor W r₀ C) (hr₀ : 0 < r₀) {F F' : ℝ → ℝ}
    (hF : ∀ r, r₀ ≤ r → F r = (r - r₀) * W r) (hF' : ∀ r, r₀ ≤ r → HasDerivAt F (F' r) r)
    (ℓ t : ℝ) :
    HasDerivAt (velocity W r₀ ℓ)
      ((F' (radius W r₀ t) / 2 - ℓ ^ 2 / radius W r₀ t ^ 3) •
        (Real.cos (angle W r₀ ℓ t), Real.sin (angle W r₀ ℓ t))) t := by
  have hr := h.hasDerivAt_radius t
  have hv := h.hasDerivAt_radialVelocity hF hF' t
  have hφ := h.hasDerivAt_angle hr₀ ℓ t
  have hpos : radius W r₀ t ≠ 0 := (hr₀.trans_le (le_radius W r₀ t)).ne'
  have hc : HasDerivAt (fun s => Real.cos (angle W r₀ ℓ s))
      (-Real.sin (angle W r₀ ℓ t) * (ℓ / radius W r₀ t ^ 2)) t :=
    HasDerivAt.comp t (Real.hasDerivAt_cos _) hφ
  have hs : HasDerivAt (fun s => Real.sin (angle W r₀ ℓ s))
      (Real.cos (angle W r₀ ℓ t) * (ℓ / radius W r₀ t ^ 2)) t :=
    HasDerivAt.comp t (Real.hasDerivAt_sin _) hφ
  have hinv : HasDerivAt (fun s => ℓ / radius W r₀ s)
      (-(ℓ * radialVelocity W r₀ t) / radius W r₀ t ^ 2) t := by
    have := (hasDerivAt_const t ℓ).div hr hpos
    refine this.congr_deriv ?_
    ring
  have h1 := (hv.mul hc).sub (hinv.mul hs)
  have h2 := (hv.mul hs).add (hinv.mul hc)
  have h3 : HasDerivAt (velocity W r₀ ℓ)
      (F' (radius W r₀ t) / 2 * Real.cos (angle W r₀ ℓ t) +
          radialVelocity W r₀ t * (-Real.sin (angle W r₀ ℓ t) * (ℓ / radius W r₀ t ^ 2)) -
        (-(ℓ * radialVelocity W r₀ t) / radius W r₀ t ^ 2 * Real.sin (angle W r₀ ℓ t) +
          ℓ / radius W r₀ t * (Real.cos (angle W r₀ ℓ t) * (ℓ / radius W r₀ t ^ 2))),
        F' (radius W r₀ t) / 2 * Real.sin (angle W r₀ ℓ t) +
          radialVelocity W r₀ t * (Real.cos (angle W r₀ ℓ t) * (ℓ / radius W r₀ t ^ 2)) +
        (-(ℓ * radialVelocity W r₀ t) / radius W r₀ t ^ 2 * Real.cos (angle W r₀ ℓ t) +
          ℓ / radius W r₀ t * (-Real.sin (angle W r₀ ℓ t) * (ℓ / radius W r₀ t ^ 2)))) t :=
    h1.prodMk h2
  refine h3.congr_deriv (Prod.ext ?_ ?_)
  · simp only [Prod.smul_mk, smul_eq_mul]
    field_simp
    ring
  · simp only [Prod.smul_mk, smul_eq_mul]
    field_simp
    ring

/-- The velocity after the scattering. -/
theorem tendsto_velocity_atTop (h : IsFactor W r₀ C) (ℓ : ℝ) {vinf φinf : ℝ}
    (hv : Tendsto (radialVelocity W r₀) atTop (𝓝 vinf))
    (hφ : Tendsto (angle W r₀ ℓ) atTop (𝓝 φinf)) :
    Tendsto (velocity W r₀ ℓ) atTop (𝓝 (vinf * Real.cos φinf, vinf * Real.sin φinf)) := by
  have hrot : Tendsto (fun t => ℓ / radius W r₀ t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop h.tendsto_radius_atTop
  have hc := (Real.continuous_cos.tendsto φinf).comp hφ
  have hs := (Real.continuous_sin.tendsto φinf).comp hφ
  have h1 := (hv.mul hc).sub (hrot.mul hs)
  have h2 := (hv.mul hs).add (hrot.mul hc)
  simp only [zero_mul, sub_zero, add_zero] at h1 h2
  exact h1.prodMk_nhds h2

/-- The velocity before the scattering. -/
theorem tendsto_velocity_atBot (h : IsFactor W r₀ C) (ℓ : ℝ) {vinf φinf : ℝ}
    (hv : Tendsto (radialVelocity W r₀) atTop (𝓝 vinf))
    (hφ : Tendsto (angle W r₀ ℓ) atTop (𝓝 φinf)) :
    Tendsto (velocity W r₀ ℓ) atBot (𝓝 (-(vinf * Real.cos φinf), vinf * Real.sin φinf)) := by
  have hrot : Tendsto (fun t => ℓ / radius W r₀ t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop h.tendsto_radius_atTop
  have hc := (Real.continuous_cos.tendsto φinf).comp hφ
  have hs := (Real.continuous_sin.tendsto φinf).comp hφ
  have h1 := ((hv.mul hc).neg).add (hrot.mul hs)
  have h2 := (hv.mul hs).add (hrot.mul hc)
  simp only [zero_mul, add_zero] at h1 h2
  have h3 := (h1.prodMk_nhds h2).comp tendsto_neg_atBot_atTop
  refine h3.congr fun t => ?_
  simp only [Function.comp_apply, velocity, h.radialVelocity_neg, h.angle_neg, h.radius_neg,
    Real.cos_neg, Real.sin_neg]
  refine Prod.ext ?_ ?_ <;> simp only <;> ring

end IsFactor

/-- The scalar product of the velocities before and after the scattering is
`v∞² cos (π − 2φ₀)`: the angle of deflection is `|π − 2φ₀|`
(Landau–Lifshitz (18.1)). -/
theorem asymptote_inner (vinf φinf : ℝ) :
    -(vinf * Real.cos φinf) * (vinf * Real.cos φinf) +
        vinf * Real.sin φinf * (vinf * Real.sin φinf) =
      vinf ^ 2 * Real.cos (π - 2 * φinf) := by
  rw [Real.cos_pi_sub, Real.cos_two_mul]
  have h := Real.sin_sq_add_cos_sq φinf
  linear_combination (vinf ^ 2) * h

end ProjectAInos.Mechanics.Scattering
