/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAInos.Mechanics.Scattering.CrossSection

/-! Typed contracts for scattering: the radial motion from a simple turning
point, the angle described from the closest approach to infinity, the
asymptotes of the motion in the plane, the Coulomb field with the angle of
deflection, and the cross-section as a measure with Rutherford's formula.
These examples use default elaborator options. -/

open ProjectAInos ProjectAInos.Mechanics ProjectAInos.Mechanics.Scattering
open ProjectAInos.SmoothGeometry.NonlinearODE
open Set Filter MeasureTheory
open scoped Real Topology ENNReal

noncomputable section

section RadialMotion

open scoped ContDiff

variable {W : ℝ → ℝ} {r₀ C : ℝ}

example (W : ℝ → ℝ) (r₀ s : ℝ) :
    parameterField W r₀ s =
      √(W (r₀ + s ^ 2)) / 2 := rfl

example (W : ℝ → ℝ) (r₀ t : ℝ) :
    parameter W r₀ t =
      flow (parameterField W r₀) (t, 0) := rfl

example (W : ℝ → ℝ) (r₀ t : ℝ) :
    radius W r₀ t =
      r₀ + parameter W r₀ t ^ 2 := rfl

example (W : ℝ → ℝ) (r₀ t : ℝ) :
    radialVelocity W r₀ t =
      2 * parameter W r₀ t * parameterField W r₀ (parameter W r₀ t) := rfl

example (h : IsFactor W r₀ C) : ContDiff ℝ ∞ fun s : ℝ => W (r₀ + s ^ 2) := h.contDiff

example (h : IsFactor W r₀ C) (s : ℝ) : 0 < W (r₀ + s ^ 2) := h.pos s

example (h : IsFactor W r₀ C) (s : ℝ) : W (r₀ + s ^ 2) ≤ C := h.le s

example (h : IsFactor W r₀ C) :
    ContDiff ℝ ∞ (parameterField W r₀) :=
  IsFactor.contDiff_parameterField h

example (h : IsFactor W r₀ C) (s : ℝ) :
    0 < parameterField W r₀ s :=
  IsFactor.parameterField_pos h s

example (h : IsFactor W r₀ C) (s : ℝ) :
    |parameterField W r₀ s| ≤ √C / 2 :=
  IsFactor.abs_parameterField_le h s

example (W : ℝ → ℝ) (r₀ s : ℝ) :
    parameterField W r₀ (-s) = parameterField W r₀ s :=
  IsFactor.parameterField_neg W r₀ s

example (h : IsFactor W r₀ C) (t : ℝ) :
    HasDerivAt (parameter W r₀) (parameterField W r₀ (parameter W r₀ t)) t :=
  IsFactor.hasDerivAt_parameter h t

example (h : IsFactor W r₀ C) :
    StrictMono (parameter W r₀) :=
  IsFactor.strictMono_parameter h

example (W : ℝ → ℝ) (r₀ : ℝ) :
    parameter W r₀ 0 = 0 :=
  parameter_zero W r₀

example (W : ℝ → ℝ) (r₀ : ℝ) :
    radius W r₀ 0 = r₀ :=
  radius_zero W r₀

example (W : ℝ → ℝ) (r₀ t : ℝ) :
    r₀ ≤ radius W r₀ t :=
  le_radius W r₀ t

example (h : IsFactor W r₀ C) {t : ℝ} (ht : 0 < t) :
    0 < parameter W r₀ t :=
  IsFactor.parameter_pos h ht

example (h : IsFactor W r₀ C) (t : ℝ) :
    parameter W r₀ (-t) = -parameter W r₀ t :=
  IsFactor.parameter_neg h t

example (h : IsFactor W r₀ C) (t : ℝ) :
    radius W r₀ (-t) = radius W r₀ t :=
  IsFactor.radius_neg h t

example (h : IsFactor W r₀ C) (t : ℝ) :
    HasDerivAt (radius W r₀) (radialVelocity W r₀ t) t :=
  IsFactor.hasDerivAt_radius h t

example (h : IsFactor W r₀ C) (t : ℝ) :
    radialVelocity W r₀ t ^ 2 = (radius W r₀ t - r₀) * W (radius W r₀ t) :=
  IsFactor.radialVelocity_sq h t

example (h : IsFactor W r₀ C) {t : ℝ} (ht : 0 < t) :
    0 < radialVelocity W r₀ t :=
  IsFactor.radialVelocity_pos h ht

example (h : IsFactor W r₀ C) :
    Tendsto (parameter W r₀) atTop atTop :=
  IsFactor.tendsto_parameter_atTop h

example (h : IsFactor W r₀ C) :
    Tendsto (radius W r₀) atTop atTop :=
  IsFactor.tendsto_radius_atTop h

example (h : IsFactor W r₀ C) :
    StrictMonoOn (radius W r₀) (Ici 0) :=
  IsFactor.strictMonoOn_radius h

example (h : IsFactor W r₀ C) :
    ContDiff ℝ ∞ (parameter W r₀) :=
  IsFactor.contDiff_parameter h

example (h : IsFactor W r₀ C) :
    ContDiff ℝ ∞ (radius W r₀) :=
  IsFactor.contDiff_radius h

example (h : IsFactor W r₀ C) :
    ContDiff ℝ ∞ (radialVelocity W r₀) :=
  IsFactor.contDiff_radialVelocity h

example (h : IsFactor W r₀ C) (t : ℝ) :
    radialVelocity W r₀ (-t) = -radialVelocity W r₀ t :=
  IsFactor.radialVelocity_neg h t

example (h : IsFactor W r₀ C) {F F' : ℝ → ℝ}
    (hF : ∀ r, r₀ ≤ r → F r = (r - r₀) * W r) (hF' : ∀ r, r₀ ≤ r → HasDerivAt F (F' r) r)
    (t : ℝ) :
    HasDerivAt (radialVelocity W r₀) (F' (radius W r₀ t) / 2) t :=
  IsFactor.hasDerivAt_radialVelocity h hF hF' t

example {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) {r₀ B : ℝ}
    (h0 : G r₀ = 0) (hd : 0 < deriv G r₀) (hpos : ∀ r, r₀ < r → 0 < G r)
    (hB : ∀ r, r₀ ≤ r → G r ≤ B) :
    (∀ r, G r = (r - r₀) * SmoothAlgebra.dividedDifference G (r, r₀)) ∧
      ∃ C : ℝ, IsFactor (fun r => SmoothAlgebra.dividedDifference G (r, r₀)) r₀ C :=
  exists_isFactor_dividedDifference hG h0 hd hpos hB

example (W : ℝ → ℝ) (r₀ ℓ t : ℝ) :
    angle W r₀ ℓ t =
      ∫ τ in (0 : ℝ)..t, ℓ / radius W r₀ τ ^ 2 := rfl

example (W : ℝ → ℝ) (r₀ ℓ : ℝ) :
    angle W r₀ ℓ 0 = 0 :=
  angle_zero W r₀ ℓ

example (h : IsFactor W r₀ C) (hr₀ : 0 < r₀) (ℓ : ℝ) :
    Continuous fun τ => ℓ / radius W r₀ τ ^ 2 :=
  IsFactor.continuous_angleRate h hr₀ ℓ

example (h : IsFactor W r₀ C) (hr₀ : 0 < r₀) (ℓ t : ℝ) :
    HasDerivAt (angle W r₀ ℓ) (ℓ / radius W r₀ t ^ 2) t :=
  IsFactor.hasDerivAt_angle h hr₀ ℓ t

example (h : IsFactor W r₀ C) (ℓ t : ℝ) :
    angle W r₀ ℓ (-t) = -angle W r₀ ℓ t :=
  IsFactor.angle_neg h ℓ t

end RadialMotion

section Deflection

variable {ℓ : ℝ} {F r v φ : ℝ → ℝ}

example (ℓ : ℝ) (F : ℝ → ℝ) (ρ : ℝ) :
    angleDensity ℓ F ρ =
      ℓ / ρ ^ 2 / √(F ρ) := rfl

example (ℓ : ℝ) (F : ℝ → ℝ) (r₀ : ℝ) :
    deflectionAngle ℓ F r₀ =
      π - 2 * ∫ ρ in Ioi r₀, angleDensity ℓ F ρ := rfl

example (hrc : ContinuousOn r (Ici 0))
    (hr : ∀ t, 0 < t → HasDerivAt r (v t) t) (hv : ∀ t, 0 < t → 0 < v t) :
    StrictMonoOn r (Ici 0) :=
  strictMonoOn_radius_of_pos hrc hr hv

example (hrc : ContinuousOn r (Ici 0))
    (hr : ∀ t, 0 < t → HasDerivAt r (v t) t) (hv : ∀ t, 0 < t → 0 < v t) {T : ℝ}
    (hT : 0 ≤ T) :
    r '' Ioc 0 T = Ioc (r 0) (r T) :=
  image_Ioc_radius hrc hr hv hT

example (hrc : ContinuousOn r (Ici 0))
    (hr : ∀ t, 0 < t → HasDerivAt r (v t) t) (hv : ∀ t, 0 < t → 0 < v t)
    (hF : ∀ t, 0 < t → v t ^ 2 = F (r t)) (hr0 : 0 < r 0)
    (hφc : ContinuousOn φ (Ici 0)) (hφ : ∀ t, 0 < t → HasDerivAt φ (ℓ / r t ^ 2) t) {T : ℝ}
    (hT : 0 ≤ T) :
    IntegrableOn (angleDensity ℓ F) (Ioc (r 0) (r T)) ∧
      ∫ ρ in Ioc (r 0) (r T), angleDensity ℓ F ρ = φ T - φ 0 :=
  integral_angleDensity_eq hrc hr hv hF hr0 hφc hφ hT

example (hrc : ContinuousOn r (Ici 0))
    (hr : ∀ t, 0 < t → HasDerivAt r (v t) t) (hv : ∀ t, 0 < t → 0 < v t)
    (hF : ∀ t, 0 < t → v t ^ 2 = F (r t)) (hr0 : 0 < r 0)
    (hφc : ContinuousOn φ (Ici 0)) (hφ : ∀ t, 0 < t → HasDerivAt φ (ℓ / r t ^ 2) t)
    (hinf : Tendsto r atTop atTop) {R : ℝ} (htail : IntegrableOn (angleDensity ℓ F) (Ioi R)) :
    IntegrableOn (angleDensity ℓ F) (Ioi (r 0)) ∧
      Tendsto φ atTop (𝓝 (φ 0 + ∫ ρ in Ioi (r 0), angleDensity ℓ F ρ)) :=
  tendsto_angle_atTop hrc hr hv hF hr0 hφc hφ hinf htail

example {R c : ℝ} (hR : 0 < R) (hc : 0 < c)
    (hFc : ContinuousOn F (Ici R)) (hF : ∀ ρ, R ≤ ρ → c ^ 2 ≤ F ρ) (ℓ : ℝ) :
    IntegrableOn (angleDensity ℓ F) (Ioi R) :=
  integrableOn_angleDensity_Ioi hR hc hFc hF ℓ

end Deflection

section Asymptote

variable {W : ℝ → ℝ} {r₀ C : ℝ}

example (h : IsFactor W r₀ C) (hr₀ : 0 < r₀) {F : ℝ → ℝ}
    (hF : ∀ r, r₀ ≤ r → F r = (r - r₀) * W r) (ℓ : ℝ) {R : ℝ}
    (htail : IntegrableOn (angleDensity ℓ F) (Ioi R)) :
    IntegrableOn (angleDensity ℓ F) (Ioi r₀) ∧
      Tendsto (angle W r₀ ℓ) atTop (𝓝 (∫ ρ in Ioi r₀, angleDensity ℓ F ρ)) :=
  IsFactor.tendsto_angle_atTop h hr₀ hF ℓ htail

example (h : IsFactor W r₀ C) (hr₀ : 0 < r₀) {F : ℝ → ℝ}
    (hF : ∀ r, r₀ ≤ r → F r = (r - r₀) * W r) (ℓ : ℝ) {R : ℝ}
    (htail : IntegrableOn (angleDensity ℓ F) (Ioi R)) :
    Tendsto (angle W r₀ ℓ) atBot (𝓝 (-∫ ρ in Ioi r₀, angleDensity ℓ F ρ)) :=
  IsFactor.tendsto_angle_atBot h hr₀ hF ℓ htail

example (h : IsFactor W r₀ C) {F : ℝ → ℝ}
    (hF : ∀ r, r₀ ≤ r → F r = (r - r₀) * W r) {vinf : ℝ} (hv : 0 ≤ vinf)
    (hlim : Tendsto F atTop (𝓝 (vinf ^ 2))) :
    Tendsto (radialVelocity W r₀) atTop (𝓝 vinf) :=
  IsFactor.tendsto_radialVelocity_atTop h hF hv hlim

example (W : ℝ → ℝ) (r₀ ℓ t : ℝ) :
    position W r₀ ℓ t =
      (radius W r₀ t * Real.cos (angle W r₀ ℓ t), radius W r₀ t * Real.sin (angle W r₀ ℓ t)) := rfl

example (W : ℝ → ℝ) (r₀ ℓ t : ℝ) :
    velocity W r₀ ℓ t =
      (radialVelocity W r₀ t * Real.cos (angle W r₀ ℓ t) -
      ℓ / radius W r₀ t * Real.sin (angle W r₀ ℓ t),
      radialVelocity W r₀ t * Real.sin (angle W r₀ ℓ t) +
      ℓ / radius W r₀ t * Real.cos (angle W r₀ ℓ t)) := rfl

example (W : ℝ → ℝ) {r₀ : ℝ} (hr₀ : 0 < r₀) (ℓ t : ℝ) :
    (position W r₀ ℓ t).1 * (velocity W r₀ ℓ t).2 -
      (position W r₀ ℓ t).2 * (velocity W r₀ ℓ t).1 = ℓ :=
  position_cross_velocity W hr₀ ℓ t

example (h : IsFactor W r₀ C) (hr₀ : 0 < r₀) (ℓ t : ℝ) :
    HasDerivAt (position W r₀ ℓ) (velocity W r₀ ℓ t) t :=
  IsFactor.hasDerivAt_position h hr₀ ℓ t

example (h : IsFactor W r₀ C) (hr₀ : 0 < r₀) {F F' : ℝ → ℝ}
    (hF : ∀ r, r₀ ≤ r → F r = (r - r₀) * W r) (hF' : ∀ r, r₀ ≤ r → HasDerivAt F (F' r) r)
    (ℓ t : ℝ) :
    HasDerivAt (velocity W r₀ ℓ)
      ((F' (radius W r₀ t) / 2 - ℓ ^ 2 / radius W r₀ t ^ 3) •
        (Real.cos (angle W r₀ ℓ t), Real.sin (angle W r₀ ℓ t))) t :=
  IsFactor.hasDerivAt_velocity h hr₀ hF hF' ℓ t

example (h : IsFactor W r₀ C) (ℓ : ℝ) {vinf φinf : ℝ}
    (hv : Tendsto (radialVelocity W r₀) atTop (𝓝 vinf))
    (hφ : Tendsto (angle W r₀ ℓ) atTop (𝓝 φinf)) :
    Tendsto (velocity W r₀ ℓ) atTop (𝓝 (vinf * Real.cos φinf, vinf * Real.sin φinf)) :=
  IsFactor.tendsto_velocity_atTop h ℓ hv hφ

example (h : IsFactor W r₀ C) (ℓ : ℝ) {vinf φinf : ℝ}
    (hv : Tendsto (radialVelocity W r₀) atTop (𝓝 vinf))
    (hφ : Tendsto (angle W r₀ ℓ) atTop (𝓝 φinf)) :
    Tendsto (velocity W r₀ ℓ) atBot (𝓝 (-(vinf * Real.cos φinf), vinf * Real.sin φinf)) :=
  IsFactor.tendsto_velocity_atBot h ℓ hv hφ

example (vinf φinf : ℝ) :
    -(vinf * Real.cos φinf) * (vinf * Real.cos φinf) +
        vinf * Real.sin φinf * (vinf * Real.sin φinf) =
      vinf ^ 2 * Real.cos (π - 2 * φinf) :=
  asymptote_inner vinf φinf

end Asymptote

section Coulomb

open Coulomb

variable {a ρ vinf : ℝ}

example (a ρ : ℝ) :
    hyp a ρ =
      √(a ^ 2 + ρ ^ 2) := rfl

example (a ρ : ℝ) :
    closest a ρ =
      a + hyp a ρ := rfl

example (a ρ : ℝ) :
    conjugate a ρ =
      hyp a ρ - a := rfl

example (a ρ vinf r : ℝ) :
    speedSq a ρ vinf r =
      vinf ^ 2 * (1 - 2 * a / r - ρ ^ 2 / r ^ 2) := rfl

example (a ρ vinf r : ℝ) :
    factor a ρ vinf r =
      vinf ^ 2 * (r + conjugate a ρ) / r ^ 2 := rfl

example (a ρ : ℝ) :
    hyp a ρ ^ 2 = a ^ 2 + ρ ^ 2 :=
  hyp_sq a ρ

example (a : ℝ) (hρ : 0 < ρ) :
    |a| < hyp a ρ :=
  abs_lt_hyp a hρ

example (a : ℝ) (hρ : 0 < ρ) :
    0 < hyp a ρ :=
  hyp_pos a hρ

example (a : ℝ) (hρ : 0 < ρ) :
    0 < closest a ρ :=
  closest_pos a hρ

example (a : ℝ) (hρ : 0 < ρ) :
    0 < conjugate a ρ :=
  conjugate_pos a hρ

example (a ρ : ℝ) :
    closest a ρ * conjugate a ρ = ρ ^ 2 :=
  closest_mul_conjugate a ρ

example (a ρ : ℝ) :
    closest a ρ - conjugate a ρ = 2 * a :=
  closest_sub_conjugate a ρ

example (a ρ r : ℝ) :
    (r - closest a ρ) * (r + conjugate a ρ) = r ^ 2 - 2 * a * r - ρ ^ 2 :=
  sub_mul_add a ρ r

example (a ρ vinf : ℝ) {r : ℝ} (hr : r ≠ 0) :
    speedSq a ρ vinf r = vinf ^ 2 * (r ^ 2 - 2 * a * r - ρ ^ 2) / r ^ 2 :=
  speedSq_eq_div a ρ vinf hr

example (hρ : 0 < ρ) (vinf : ℝ) {r : ℝ} (hr : closest a ρ ≤ r) :
    speedSq a ρ vinf r = (r - closest a ρ) * factor a ρ vinf r :=
  speedSq_eq hρ vinf hr

example (a : ℝ) (hρ : 0 < ρ) (hv : 0 < vinf) :
    IsFactor (factor a ρ vinf) (closest a ρ)
      (vinf ^ 2 * (1 / closest a ρ + conjugate a ρ / closest a ρ ^ 2)) :=
  isFactor a hρ hv

example (a ρ vinf : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (speedSq a ρ vinf) (vinf ^ 2 * (2 * a / r ^ 2 + 2 * ρ ^ 2 / r ^ 3)) r :=
  hasDerivAt_speedSq a ρ vinf hr

example (a ρ vinf : ℝ) :
    Tendsto (speedSq a ρ vinf) atTop (𝓝 (vinf ^ 2)) :=
  tendsto_speedSq_atTop a ρ vinf

example (a ρ r : ℝ) :
    primitive a ρ r =
      Real.arccos ((ρ ^ 2 / r + a) / hyp a ρ) := rfl

example (a : ℝ) (hρ : 0 < ρ) :
    primitive a ρ (closest a ρ) = 0 :=
  primitive_closest a hρ

example (a ρ : ℝ) :
    Tendsto (primitive a ρ) atTop (𝓝 (Real.arccos (a / hyp a ρ))) :=
  tendsto_primitive_atTop a ρ

example (hρ : 0 < ρ) (hv : 0 < vinf) {r : ℝ} (hr : closest a ρ < r) :
    HasDerivAt (primitive a ρ) (angleDensity (ρ * vinf) (speedSq a ρ vinf) r) r :=
  hasDerivAt_primitive hρ hv hr

example (a : ℝ) (hρ : 0 < ρ) (hv : 0 < vinf) :
    IntegrableOn (angleDensity (ρ * vinf) (speedSq a ρ vinf)) (Ioi (closest a ρ)) ∧
      ∫ r in Ioi (closest a ρ), angleDensity (ρ * vinf) (speedSq a ρ vinf) r =
        Real.arccos (a / hyp a ρ) :=
  integral_angleDensity a hρ hv

example (a : ℝ) (hρ : 0 < ρ) (hv : 0 < vinf) :
    Tendsto (angle (factor a ρ vinf) (closest a ρ) (ρ * vinf)) atTop
      (𝓝 (Real.arccos (a / hyp a ρ))) :=
  tendsto_angle_atTop a hρ hv

example (a : ℝ) (hρ : 0 < ρ) (hv : 0 < vinf) :
    Tendsto (radialVelocity (factor a ρ vinf) (closest a ρ)) atTop (𝓝 vinf) :=
  tendsto_radialVelocity_atTop a hρ hv

example (a : ℝ) (hρ : 0 < ρ) (hv : 0 < vinf) :
    Tendsto (velocity (factor a ρ vinf) (closest a ρ) (ρ * vinf)) atTop
      (𝓝 (vinf * Real.cos (Real.arccos (a / hyp a ρ)),
        vinf * Real.sin (Real.arccos (a / hyp a ρ)))) :=
  tendsto_velocity_atTop a hρ hv

example (a : ℝ) (hρ : 0 < ρ) (hv : 0 < vinf) :
    Tendsto (velocity (factor a ρ vinf) (closest a ρ) (ρ * vinf)) atBot
      (𝓝 (-(vinf * Real.cos (Real.arccos (a / hyp a ρ))),
        vinf * Real.sin (Real.arccos (a / hyp a ρ)))) :=
  tendsto_velocity_atBot a hρ hv

example (a : ℝ) (hρ : 0 < ρ) (hv : 0 < vinf) (t : ℝ) :
    HasDerivAt (velocity (factor a ρ vinf) (closest a ρ) (ρ * vinf))
      ((vinf ^ 2 * a / radius (factor a ρ vinf) (closest a ρ) t ^ 2) •
        (Real.cos (angle (factor a ρ vinf) (closest a ρ) (ρ * vinf) t),
          Real.sin (angle (factor a ρ vinf) (closest a ρ) (ρ * vinf) t))) t :=
  hasDerivAt_velocity a hρ hv t

example (a ρ : ℝ) :
    deflection a ρ =
      π - 2 * Real.arccos (a / hyp a ρ) := rfl

example (a : ℝ) (hρ : 0 < ρ) (hv : 0 < vinf) :
    deflection a ρ = deflectionAngle (ρ * vinf) (speedSq a ρ vinf) (closest a ρ) :=
  deflection_eq_deflectionAngle a hρ hv

example (a ρ : ℝ) :
    hyp (-a) ρ = hyp a ρ :=
  hyp_neg a ρ

example (a ρ : ℝ) :
    deflection (-a) ρ = -deflection a ρ :=
  deflection_neg a ρ

example (a : ℝ) (hρ : 0 < ρ) :
    |a / hyp a ρ| < 1 :=
  abs_div_hyp_lt_one a hρ

example (a : ℝ) (hρ : 0 < ρ) :
    Real.sin (deflection a ρ / 2) = a / hyp a ρ :=
  sin_half_deflection a hρ

example (a : ℝ) (hρ : 0 < ρ) :
    Real.cos (deflection a ρ / 2) = ρ / hyp a ρ :=
  cos_half_deflection a hρ

example (hρ : 0 < ρ) (ha : a ≠ 0) :
    Real.cos (deflection a ρ / 2) / Real.sin (deflection a ρ / 2) = ρ / a :=
  cot_half_deflection hρ ha

example (hρ : 0 < ρ) (ha : 0 < a) :
    deflection a ρ ∈ Ioo 0 π :=
  deflection_mem_Ioo hρ ha

end Coulomb

section CrossSection

open Coulomb

example :
    impactMeasure =
      (volume.restrict (Ioi 0)).withDensity fun ρ => ENNReal.ofReal (2 * π * ρ) := rfl

example :
    solidAngle =
      (volume.restrict (Ioo 0 π)).withDensity fun χ => ENNReal.ofReal (2 * π * Real.sin χ) := rfl

example (χ : ℝ → ℝ) :
    crossSection χ =
      Measure.map χ impactMeasure := rfl

example {S : Set ℝ} (hS : MeasurableSet S) :
    impactMeasure S = ∫⁻ ρ in S ∩ Ioi 0, ENNReal.ofReal (2 * π * ρ) :=
  impactMeasure_apply hS

example {A : Set ℝ} (hA : MeasurableSet A) (hAπ : A ⊆ Ioo 0 π)
    (g : ℝ → ℝ≥0∞) :
    ∫⁻ x in A, g x ∂solidAngle = ∫⁻ x in A, ENNReal.ofReal (2 * π * Real.sin x) * g x :=
  setLIntegral_solidAngle hA hAπ g

example {χ b b' : ℝ → ℝ} (hχ : Measurable χ) {A : Set ℝ}
    (hA : MeasurableSet A) (hAπ : A ⊆ Ioo 0 π)
    (hb : ∀ x ∈ A, HasDerivWithinAt b (b' x) A x) (hinj : InjOn b A)
    (hpre : χ ⁻¹' A ∩ Ioi 0 = b '' A) :
    crossSection χ A = ∫⁻ x in A, ENNReal.ofReal (b x * |b' x| / Real.sin x) ∂solidAngle :=
  crossSection_apply hχ hA hAπ hb hinj hpre

example {a : ℝ} (ha : 0 < a) :
    Continuous (deflection a) :=
  Coulomb.continuous_deflection ha

example (a χ : ℝ) :
    Coulomb.impact a χ =
      a * (Real.cos (χ / 2) / Real.sin (χ / 2)) := rfl

example {a χ : ℝ} (ha : 0 < a) (hχ : χ ∈ Ioo 0 π) :
    0 < impact a χ :=
  Coulomb.impact_pos ha hχ

example {a χ : ℝ} (ha : 0 < a) (hχ : χ ∈ Ioo 0 π) :
    deflection a (impact a χ) = χ :=
  Coulomb.deflection_impact ha hχ

example {a ρ : ℝ} (ha : 0 < a) (hρ : 0 < ρ) :
    impact a (deflection a ρ) = ρ :=
  Coulomb.impact_deflection ha hρ

example {a : ℝ} (ha : 0 < a) {A : Set ℝ} (hA : MeasurableSet A)
    (hAπ : A ⊆ Ioo 0 π) :
    crossSection (deflection a) A =
      ∫⁻ x in A, ENNReal.ofReal ((a / 2) ^ 2 / Real.sin (x / 2) ^ 4) ∂solidAngle :=
  Coulomb.crossSection_coulomb ha hA hAπ

example {a : ℝ} (ha : 0 < a) (ρ : ℝ) :
    0 ≤ deflection a ρ :=
  Coulomb.deflection_nonneg ha ρ

example {a : ℝ} (ha : a ≠ 0) (ρ : ℝ) :
    |deflection a ρ| = deflection |a| ρ :=
  Coulomb.abs_deflection ha ρ

example {a : ℝ} (ha : a ≠ 0) {A : Set ℝ} (hA : MeasurableSet A)
    (hAπ : A ⊆ Ioo 0 π) :
    crossSection (fun ρ => |deflection a ρ|) A =
      ∫⁻ x in A, ENNReal.ofReal ((a / 2) ^ 2 / Real.sin (x / 2) ^ 4) ∂solidAngle :=
  Coulomb.crossSection_coulomb_abs ha hA hAπ

end CrossSection
