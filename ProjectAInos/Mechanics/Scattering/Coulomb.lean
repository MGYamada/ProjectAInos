/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Scattering.Asymptote
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# Scattering in a Coulomb field

Landau–Lifshitz §19. For `U = α/r`, the speed `v∞` at infinity and the impact
parameter `ρ`, let `a = α/m v∞²`. The square of the radial velocity is
`F(r) = v∞² (1 − 2a/r − ρ²/r²) = v∞² (r − r₀)(r + r₁)/r²`, with the closest
approach `r₀ = a + √(a² + ρ²)` and `r₁ = √(a² + ρ²) − a`. Both signs of `a`
are allowed: the field is repulsive for `a > 0`.

* `isFactor`: the motion `radius (factor a ρ v∞) (closest a ρ)` exists for all
  times; `hasDerivAt_velocity`: its acceleration is `(v∞² a/r²)` along the
  radius, which is `α/m r²`.
* `integral_angleDensity`: the integral (18.4) is `arccos (a/√(a² + ρ²))`.
* `tendsto_angle_atTop`, `tendsto_velocity_atTop`, `tendsto_velocity_atBot`:
  the asymptotes of the motion.
* `deflection a ρ = π − 2 arccos (a/√(a² + ρ²))`, with
  `sin (χ/2) = a/√(a² + ρ²)` and `cot (χ/2) = ρ/a` (19.1).
-/

@[expose] public section
noncomputable section

open Set Filter MeasureTheory
open scoped Real Topology

namespace ProjectAInos.Mechanics.Scattering.Coulomb

variable {a ρ vinf : ℝ}

/-- `√(a² + ρ²)`. -/
def hyp (a ρ : ℝ) : ℝ := √(a ^ 2 + ρ ^ 2)

/-- The distance of closest approach `a + √(a² + ρ²)`. -/
def closest (a ρ : ℝ) : ℝ := a + hyp a ρ

/-- The other root `√(a² + ρ²) − a` of the square of the radial velocity, with
the opposite sign. -/
def conjugate (a ρ : ℝ) : ℝ := hyp a ρ - a

/-- The square of the radial velocity, `v∞² (1 − 2a/r − ρ²/r²)`. -/
def speedSq (a ρ vinf r : ℝ) : ℝ := vinf ^ 2 * (1 - 2 * a / r - ρ ^ 2 / r ^ 2)

/-- The factor `v∞² (r + r₁)/r²` of the square of the radial velocity. -/
def factor (a ρ vinf r : ℝ) : ℝ := vinf ^ 2 * (r + conjugate a ρ) / r ^ 2

theorem hyp_sq (a ρ : ℝ) : hyp a ρ ^ 2 = a ^ 2 + ρ ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem abs_lt_hyp (a : ℝ) (hρ : 0 < ρ) : |a| < hyp a ρ := by
  rw [← Real.sqrt_sq_eq_abs, hyp]
  exact Real.sqrt_lt_sqrt (sq_nonneg a) (by nlinarith)

theorem hyp_pos (a : ℝ) (hρ : 0 < ρ) : 0 < hyp a ρ :=
  (abs_nonneg a).trans_lt (abs_lt_hyp a hρ)

theorem closest_pos (a : ℝ) (hρ : 0 < ρ) : 0 < closest a ρ := by
  have h := abs_lt_hyp a hρ
  have h2 := neg_abs_le a
  rw [closest]
  linarith

theorem conjugate_pos (a : ℝ) (hρ : 0 < ρ) : 0 < conjugate a ρ := by
  have h := abs_lt_hyp a hρ
  have h2 := le_abs_self a
  rw [conjugate]
  linarith

theorem closest_mul_conjugate (a ρ : ℝ) : closest a ρ * conjugate a ρ = ρ ^ 2 := by
  rw [closest, conjugate]
  linear_combination hyp_sq a ρ

theorem closest_sub_conjugate (a ρ : ℝ) : closest a ρ - conjugate a ρ = 2 * a := by
  rw [closest, conjugate]
  ring

theorem sub_mul_add (a ρ r : ℝ) :
    (r - closest a ρ) * (r + conjugate a ρ) = r ^ 2 - 2 * a * r - ρ ^ 2 := by
  linear_combination (-r) * closest_sub_conjugate a ρ - closest_mul_conjugate a ρ

theorem speedSq_eq_div (a ρ vinf : ℝ) {r : ℝ} (hr : r ≠ 0) :
    speedSq a ρ vinf r = vinf ^ 2 * (r ^ 2 - 2 * a * r - ρ ^ 2) / r ^ 2 := by
  rw [speedSq]
  field_simp

theorem speedSq_eq (hρ : 0 < ρ) (vinf : ℝ) {r : ℝ} (hr : closest a ρ ≤ r) :
    speedSq a ρ vinf r = (r - closest a ρ) * factor a ρ vinf r := by
  have hr0 : r ≠ 0 := ((closest_pos a hρ).trans_le hr).ne'
  rw [speedSq_eq_div a ρ vinf hr0, ← sub_mul_add, factor]
  ring

/-- The radial motion exists for all times. -/
theorem isFactor (a : ℝ) (hρ : 0 < ρ) (hv : 0 < vinf) :
    IsFactor (factor a ρ vinf) (closest a ρ)
      (vinf ^ 2 * (1 / closest a ρ + conjugate a ρ / closest a ρ ^ 2)) where
  contDiff := by
    have hpos : ∀ s : ℝ, 0 < closest a ρ + s ^ 2 := fun s =>
      add_pos_of_pos_of_nonneg (closest_pos a hρ) (sq_nonneg s)
    unfold factor
    exact (contDiff_const.mul ((contDiff_const.add (contDiff_id.pow 2)).add contDiff_const)).div
      ((contDiff_const.add (contDiff_id.pow 2)).pow 2) fun s => pow_ne_zero 2 (hpos s).ne'
  pos s := by
    have hpos : 0 < closest a ρ + s ^ 2 :=
      add_pos_of_pos_of_nonneg (closest_pos a hρ) (sq_nonneg s)
    have hc := conjugate_pos a hρ
    unfold factor
    positivity
  le s := by
    have h0 := closest_pos a hρ
    have hc := conjugate_pos a hρ
    have hle : closest a ρ ≤ closest a ρ + s ^ 2 := le_add_of_nonneg_right (sq_nonneg s)
    have hpos : 0 < closest a ρ + s ^ 2 := h0.trans_le hle
    have h1 : 1 / (closest a ρ + s ^ 2) ≤ 1 / closest a ρ := one_div_le_one_div_of_le h0 hle
    have h2 : conjugate a ρ / (closest a ρ + s ^ 2) ^ 2 ≤ conjugate a ρ / closest a ρ ^ 2 :=
      div_le_div_of_nonneg_left hc.le (pow_pos h0 2) (pow_le_pow_left₀ h0.le hle 2)
    have e : factor a ρ vinf (closest a ρ + s ^ 2) =
        vinf ^ 2 * (1 / (closest a ρ + s ^ 2) +
          conjugate a ρ / (closest a ρ + s ^ 2) ^ 2) := by
      rw [factor]
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left (add_le_add h1 h2) (sq_nonneg vinf)

theorem hasDerivAt_speedSq (a ρ vinf : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (speedSq a ρ vinf) (vinf ^ 2 * (2 * a / r ^ 2 + 2 * ρ ^ 2 / r ^ 3)) r := by
  have h1 : HasDerivAt (fun r : ℝ => 2 * a / r) (-(2 * a) / r ^ 2) r := by
    have := (hasDerivAt_const r (2 * a)).div (hasDerivAt_id r) hr
    refine this.congr_deriv ?_
    simp
  have h2 : HasDerivAt (fun r : ℝ => ρ ^ 2 / r ^ 2) (-(2 * ρ ^ 2) / r ^ 3) r := by
    have hpow : HasDerivAt (fun r : ℝ => r ^ 2) (2 * r) r := by
      simpa using hasDerivAt_pow 2 r
    have h : HasDerivAt (fun r : ℝ => ρ ^ 2 / r ^ 2)
        ((0 * r ^ 2 - ρ ^ 2 * (2 * r)) / (r ^ 2) ^ 2) r :=
      (hasDerivAt_const r (ρ ^ 2)).div hpow (pow_ne_zero 2 hr)
    refine h.congr_deriv ?_
    field_simp
    ring
  have h3 := (((hasDerivAt_const r (1 : ℝ)).sub h1).sub h2).const_mul (vinf ^ 2)
  refine h3.congr_deriv ?_
  ring

theorem tendsto_speedSq_atTop (a ρ vinf : ℝ) :
    Tendsto (speedSq a ρ vinf) atTop (𝓝 (vinf ^ 2)) := by
  have h1 : Tendsto (fun r : ℝ => 2 * a / r) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have h2 : Tendsto (fun r : ℝ => ρ ^ 2 / r ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)
  have h3 := ((tendsto_const_nhds (x := (1 : ℝ))).sub h1).sub h2
  have h4 : Tendsto (fun r : ℝ => vinf ^ 2 * (1 - 2 * a / r - ρ ^ 2 / r ^ 2)) atTop
      (𝓝 (vinf ^ 2 * (1 - 0 - 0))) := h3.const_mul (vinf ^ 2)
  rw [sub_zero, sub_zero, mul_one] at h4
  exact h4

/-! ### The integral of the angle -/

/-- A primitive of the density of the angle. -/
def primitive (a ρ r : ℝ) : ℝ := Real.arccos ((ρ ^ 2 / r + a) / hyp a ρ)

theorem primitive_closest (a : ℝ) (hρ : 0 < ρ) : primitive a ρ (closest a ρ) = 0 := by
  have h0 := closest_pos a hρ
  have hc := hyp_pos a hρ
  have h1 : ρ ^ 2 / closest a ρ = conjugate a ρ := by
    rw [← closest_mul_conjugate a ρ]
    field_simp
  rw [primitive, h1, conjugate, sub_add_cancel, div_self hc.ne', Real.arccos_one]

theorem tendsto_primitive_atTop (a ρ : ℝ) :
    Tendsto (primitive a ρ) atTop (𝓝 (Real.arccos (a / hyp a ρ))) := by
  have h1 : Tendsto (fun r : ℝ => ρ ^ 2 / r) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have h2 : Tendsto (fun r : ℝ => (ρ ^ 2 / r + a) / hyp a ρ) atTop (𝓝 ((0 + a) / hyp a ρ)) :=
    (h1.add_const a).div_const _
  rw [zero_add] at h2
  exact (Real.continuous_arccos.tendsto _).comp h2

theorem hasDerivAt_primitive (hρ : 0 < ρ) (hv : 0 < vinf) {r : ℝ} (hr : closest a ρ < r) :
    HasDerivAt (primitive a ρ) (angleDensity (ρ * vinf) (speedSq a ρ vinf) r) r := by
  have hr0 : 0 < r := (closest_pos a hρ).trans hr
  have hc := hyp_pos a hρ
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = r ^ 2 - 2 * a * r - ρ ^ 2 := ⟨_, rfl⟩
  have hQpos : 0 < Q := by
    rw [hQ, ← sub_mul_add]
    exact mul_pos (sub_pos.mpr hr) (add_pos hr0 (conjugate_pos a hρ))
  have hsQ : √Q ^ 2 = Q := Real.sq_sqrt hQpos.le
  have hsQpos : 0 < √Q := Real.sqrt_pos.mpr hQpos
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (ρ ^ 2 / r + a) / hyp a ρ := ⟨_, rfl⟩
  have hkey : hyp a ρ ^ 2 * r ^ 2 - (ρ ^ 2 + a * r) ^ 2 = ρ ^ 2 * Q := by
    rw [hQ]
    linear_combination (r ^ 2) * hyp_sq a ρ
  have h1u : 1 - u ^ 2 = (ρ * √Q / (hyp a ρ * r)) ^ 2 := by
    have e : (ρ * √Q / (hyp a ρ * r)) ^ 2 = ρ ^ 2 * Q / (hyp a ρ ^ 2 * r ^ 2) := by
      rw [div_pow, mul_pow, mul_pow, hsQ]
    rw [e, ← hkey, hu]
    field_simp
  have hroot : √(1 - u ^ 2) = ρ * √Q / (hyp a ρ * r) := by
    rw [h1u, Real.sqrt_sq (by positivity)]
  have hpos1 : 0 < 1 - u ^ 2 := by
    rw [h1u]
    positivity
  have hne1 : u ≠ 1 := fun h => by
    rw [h] at hpos1
    norm_num at hpos1
  have hne2 : u ≠ -1 := fun h => by
    rw [h] at hpos1
    norm_num at hpos1
  have hud : HasDerivAt (fun r : ℝ => (ρ ^ 2 / r + a) / hyp a ρ)
      (-(ρ ^ 2) / r ^ 2 / hyp a ρ) r := by
    have h1 := (hasDerivAt_const r (ρ ^ 2)).div (hasDerivAt_id r) hr0.ne'
    refine ((h1.add_const a).div_const (hyp a ρ)).congr_deriv ?_
    simp
  have harccos := Real.hasDerivAt_arccos hne2 hne1
  rw [hu] at harccos
  have hcomp := HasDerivAt.comp r harccos hud
  refine hcomp.congr_deriv ?_
  rw [← hu, hroot]
  have hF : √(speedSq a ρ vinf r) = vinf * √Q / r := by
    have e : speedSq a ρ vinf r = (vinf * √Q / r) ^ 2 := by
      rw [speedSq_eq_div a ρ vinf hr0.ne', ← hQ, div_pow, mul_pow, hsQ]
    rw [e, Real.sqrt_sq (by positivity)]
  rw [angleDensity, hF]
  field_simp

/-- Landau–Lifshitz (18.4) for the Coulomb field: the angle between the
direction of the closest approach and an asymptote is
`arccos (a/√(a² + ρ²))`. -/
theorem integral_angleDensity (a : ℝ) (hρ : 0 < ρ) (hv : 0 < vinf) :
    IntegrableOn (angleDensity (ρ * vinf) (speedSq a ρ vinf)) (Ioi (closest a ρ)) ∧
      ∫ r in Ioi (closest a ρ), angleDensity (ρ * vinf) (speedSq a ρ vinf) r =
        Real.arccos (a / hyp a ρ) := by
  have h0 := closest_pos a hρ
  have hcont : ContinuousWithinAt (primitive a ρ) (Ici (closest a ρ)) (closest a ρ) := by
    have h1 : ContinuousAt (fun r : ℝ => (ρ ^ 2 / r + a) / hyp a ρ) (closest a ρ) :=
      ((continuousAt_const.div continuousAt_id h0.ne').add continuousAt_const).div_const _
    exact (Real.continuous_arccos.continuousAt.comp h1).continuousWithinAt
  have hderiv : ∀ r ∈ Ioi (closest a ρ),
      HasDerivAt (primitive a ρ) (angleDensity (ρ * vinf) (speedSq a ρ vinf) r) r :=
    fun r hr => hasDerivAt_primitive hρ hv hr
  have hnonneg : ∀ r ∈ Ioi (closest a ρ), 0 ≤ angleDensity (ρ * vinf) (speedSq a ρ vinf) r := by
    intro _ _
    rw [angleDensity]
    positivity
  have hint := integrableOn_Ioi_deriv_of_nonneg hcont hderiv hnonneg
    (tendsto_primitive_atTop a ρ)
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint (tendsto_primitive_atTop a ρ),
    primitive_closest a hρ, sub_zero]

/-! ### The motion and its asymptotes -/

theorem tendsto_angle_atTop (a : ℝ) (hρ : 0 < ρ) (hv : 0 < vinf) :
    Tendsto (angle (factor a ρ vinf) (closest a ρ) (ρ * vinf)) atTop
      (𝓝 (Real.arccos (a / hyp a ρ))) := by
  have h := ((isFactor a hρ hv).tendsto_angle_atTop (closest_pos a hρ)
    (F := speedSq a ρ vinf) (fun _ hr => speedSq_eq hρ vinf hr) (ρ * vinf)
    (integral_angleDensity a hρ hv).1).2
  rwa [(integral_angleDensity a hρ hv).2] at h

theorem tendsto_radialVelocity_atTop (a : ℝ) (hρ : 0 < ρ) (hv : 0 < vinf) :
    Tendsto (radialVelocity (factor a ρ vinf) (closest a ρ)) atTop (𝓝 vinf) :=
  (isFactor a hρ hv).tendsto_radialVelocity_atTop (F := speedSq a ρ vinf)
    (fun _ hr => speedSq_eq hρ vinf hr) hv.le (tendsto_speedSq_atTop a ρ vinf)

/-- The velocity after the scattering. -/
theorem tendsto_velocity_atTop (a : ℝ) (hρ : 0 < ρ) (hv : 0 < vinf) :
    Tendsto (velocity (factor a ρ vinf) (closest a ρ) (ρ * vinf)) atTop
      (𝓝 (vinf * Real.cos (Real.arccos (a / hyp a ρ)),
        vinf * Real.sin (Real.arccos (a / hyp a ρ)))) :=
  (isFactor a hρ hv).tendsto_velocity_atTop (ρ * vinf) (tendsto_radialVelocity_atTop a hρ hv)
    (tendsto_angle_atTop a hρ hv)

/-- The velocity before the scattering. -/
theorem tendsto_velocity_atBot (a : ℝ) (hρ : 0 < ρ) (hv : 0 < vinf) :
    Tendsto (velocity (factor a ρ vinf) (closest a ρ) (ρ * vinf)) atBot
      (𝓝 (-(vinf * Real.cos (Real.arccos (a / hyp a ρ))),
        vinf * Real.sin (Real.arccos (a / hyp a ρ)))) :=
  (isFactor a hρ hv).tendsto_velocity_atBot (ρ * vinf) (tendsto_radialVelocity_atTop a hρ hv)
    (tendsto_angle_atTop a hρ hv)

/-- Newton's equation in the Coulomb field: the acceleration is `v∞² a/r²`
along the radius, which is `α/m r²` for `a = α/m v∞²`. -/
theorem hasDerivAt_velocity (a : ℝ) (hρ : 0 < ρ) (hv : 0 < vinf) (t : ℝ) :
    HasDerivAt (velocity (factor a ρ vinf) (closest a ρ) (ρ * vinf))
      ((vinf ^ 2 * a / radius (factor a ρ vinf) (closest a ρ) t ^ 2) •
        (Real.cos (angle (factor a ρ vinf) (closest a ρ) (ρ * vinf) t),
          Real.sin (angle (factor a ρ vinf) (closest a ρ) (ρ * vinf) t))) t := by
  have h0 := closest_pos a hρ
  have hr : 0 < radius (factor a ρ vinf) (closest a ρ) t :=
    h0.trans_le (le_radius _ _ t)
  have h := (isFactor a hρ hv).hasDerivAt_velocity h0 (F := speedSq a ρ vinf)
    (F' := fun r => vinf ^ 2 * (2 * a / r ^ 2 + 2 * ρ ^ 2 / r ^ 3))
    (fun _ hr => speedSq_eq hρ vinf hr)
    (fun r hr => hasDerivAt_speedSq a ρ vinf (h0.trans_le hr).ne') (ρ * vinf) t
  refine h.congr_deriv ?_
  congr 1
  field_simp
  ring

/-! ### The angle of deflection -/

/-- The angle of deflection `χ = π − 2φ₀` in the Coulomb field. It is positive
for a repulsive field. -/
def deflection (a ρ : ℝ) : ℝ := π - 2 * Real.arccos (a / hyp a ρ)

/-- The angle of deflection is that of the integral (18.4). -/
theorem deflection_eq_deflectionAngle (a : ℝ) (hρ : 0 < ρ) (hv : 0 < vinf) :
    deflection a ρ = deflectionAngle (ρ * vinf) (speedSq a ρ vinf) (closest a ρ) := by
  rw [deflection, deflectionAngle, (integral_angleDensity a hρ hv).2]

theorem hyp_neg (a ρ : ℝ) : hyp (-a) ρ = hyp a ρ := by
  rw [hyp, hyp, neg_sq]

/-- The attractive field deflects by the opposite angle. -/
theorem deflection_neg (a ρ : ℝ) : deflection (-a) ρ = -deflection a ρ := by
  rw [deflection, deflection, hyp_neg, neg_div, Real.arccos_neg]
  ring

theorem abs_div_hyp_lt_one (a : ℝ) (hρ : 0 < ρ) : |a / hyp a ρ| < 1 := by
  rw [abs_div, abs_of_pos (hyp_pos a hρ), div_lt_one (hyp_pos a hρ)]
  exact abs_lt_hyp a hρ

theorem sin_half_deflection (a : ℝ) (hρ : 0 < ρ) :
    Real.sin (deflection a ρ / 2) = a / hyp a ρ := by
  have h := abs_lt.mp (abs_div_hyp_lt_one a hρ)
  rw [deflection, show (π - 2 * Real.arccos (a / hyp a ρ)) / 2 =
    π / 2 - Real.arccos (a / hyp a ρ) by ring, Real.sin_pi_div_two_sub,
    Real.cos_arccos h.1.le h.2.le]

theorem cos_half_deflection (a : ℝ) (hρ : 0 < ρ) :
    Real.cos (deflection a ρ / 2) = ρ / hyp a ρ := by
  have hc := hyp_pos a hρ
  rw [deflection, show (π - 2 * Real.arccos (a / hyp a ρ)) / 2 =
    π / 2 - Real.arccos (a / hyp a ρ) by ring, Real.cos_pi_div_two_sub, Real.sin_arccos]
  have e : 1 - (a / hyp a ρ) ^ 2 = (ρ / hyp a ρ) ^ 2 := by
    rw [div_pow, div_pow, hyp_sq]
    field_simp
    ring
  rw [e, Real.sqrt_sq (by positivity)]

/-- Landau–Lifshitz (19.1): `cot (χ/2) = ρ/a = m v∞² ρ/α`. -/
theorem cot_half_deflection (hρ : 0 < ρ) (ha : a ≠ 0) :
    Real.cos (deflection a ρ / 2) / Real.sin (deflection a ρ / 2) = ρ / a := by
  have hc := hyp_pos a hρ
  rw [cos_half_deflection a hρ, sin_half_deflection a hρ]
  field_simp

theorem deflection_mem_Ioo (hρ : 0 < ρ) (ha : 0 < a) : deflection a ρ ∈ Ioo 0 π := by
  have hc := hyp_pos a hρ
  have h1 : 0 < a / hyp a ρ := div_pos ha hc
  have h2 : a / hyp a ρ < 1 := (abs_lt.mp (abs_div_hyp_lt_one a hρ)).2
  have h3 : Real.arccos (a / hyp a ρ) < π / 2 := Real.arccos_lt_pi_div_two.mpr h1
  have h4 : 0 < Real.arccos (a / hyp a ρ) := Real.arccos_pos.mpr h2
  rw [deflection]
  constructor <;> linarith

end ProjectAInos.Mechanics.Scattering.Coulomb
