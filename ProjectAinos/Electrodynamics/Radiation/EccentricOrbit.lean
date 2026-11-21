/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.Radiation.CoulombRadiation
public import ProjectAinos.SpecialFunctions.Kapteyn
import Mathlib.Tactic

/-! # Eccentric anomaly of the Coulomb radiation orbit

The polar angle in the existing orbit advances by a globally defined ODE. Integrating the
angular Jacobian lifts the eccentric anomaly through every perihelion. Kepler's mean anomaly
then grows linearly in physical time.
-/

@[expose] public section
noncomputable section

open Real Set
open ProjectAinos.SpecialFunctions.Kapteyn

namespace ProjectAinos.Electrodynamics.Radiation.CoulombRadiation

/-- Semi-major axis of the ellipse. -/
def semiMajor (k ℓ e : ℝ) : ℝ := semiLatus k ℓ / (1 - e ^ 2)

/-- Mean angular frequency, expressed in terms of the Coulomb and angular-momentum parameters. -/
def meanMotion (k ℓ e : ℝ) : ℝ := k ^ 2 / ℓ ^ 3 * ((1 - e ^ 2) * √(1 - e ^ 2))

private def jac (e φ : ℝ) := √(1 - e ^ 2) / (1 + e * cos φ)
private def angle (e φ : ℝ) := ∫ u in 0..φ, jac e u
private def ec (e φ : ℝ) := (e + cos φ) / (1 + e * cos φ)
private def es (e φ : ℝ) := √(1 - e ^ 2) * sin φ / (1 + e * cos φ)

private theorem da {e : ℝ} (h₀ : 0 ≤ e) (h₁ : e < 1) (φ : ℝ) :
    HasDerivAt (angle e) (jac e φ) φ := by
  have hc : Continuous (jac e) := continuous_const.div (continuous_const.add
    (continuous_const.mul Real.continuous_cos)) fun t => (one_add_mul_cos_pos h₀ h₁ t).ne'
  exact (hc.integral_hasStrictDerivAt 0 φ).hasDerivAt

private theorem trig {e : ℝ} (h₀ : 0 ≤ e) (h₁ : e < 1) (φ : ℝ) :
    cos (angle e φ) = ec e φ ∧ sin (angle e φ) = es e φ := by
  have hq := Real.sq_sqrt (by nlinarith : 0 ≤ 1 - e ^ 2)
  have he (u : ℝ) : HasDerivAt (ec e) (-(jac e u * es e u)) u := by
    have hd := ((Real.hasDerivAt_cos u).const_add e).div
      (((Real.hasDerivAt_cos u).const_mul e).const_add 1) (one_add_mul_cos_pos h₀ h₁ u).ne'
    convert hd using 1
    · rfl
    unfold es jac
    field_simp [(one_add_mul_cos_pos h₀ h₁ u).ne']
    linear_combination -(sin u) * hq
  have hs (u : ℝ) : HasDerivAt (es e) (jac e u * ec e u) u := by
    have hd := ((Real.hasDerivAt_sin u).const_mul (√(1 - e ^ 2))).div
      (((Real.hasDerivAt_cos u).const_mul e).const_add 1) (one_add_mul_cos_pos h₀ h₁ u).ne'
    convert hd using 1
    · rfl
    unfold ec jac
    field_simp [(one_add_mul_cos_pos h₀ h₁ u).ne']
    linear_combination -√(1-e^2) * e * Real.sin_sq_add_cos_sq u
  let err (u : ℝ) := (cos (angle e u) - ec e u) ^ 2 + (sin (angle e u) - es e u) ^ 2
  have hd (u : ℝ) : HasDerivAt err 0 u := by
    convert ((((da h₀ h₁ u).cos.sub (he u)).pow 2).add
      (((da h₀ h₁ u).sin.sub (hs u)).pow 2)) using 1
    simp only [Pi.sub_apply]
    ring
  have h := is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt) (fun u => (hd u).deriv) φ 0
  have hzero : err 0 = 0 := by
    simp [err, angle, ec, es, add_comm e 1, (by linarith : 1 + e ≠ 0)]
  rw [hzero] at h
  dsimp only [err] at h
  exact ⟨by nlinarith [sq_nonneg (sin (angle e φ) - es e φ)],
    by nlinarith [sq_nonneg (cos (angle e φ) - ec e φ)]⟩

private theorem mean_time {k ℓ e : ℝ} (hk : 0 < k) (hℓ : 0 < ℓ) (h₀ : 0 ≤ e) (h₁ : e < 1)
    (t : ℝ) : meanAnomaly e (angle e (keplerAngle k ℓ e t)) = meanMotion k ℓ e * t := by
  let F (s : ℝ) := meanAnomaly e (angle e (keplerAngle k ℓ e s)) - meanMotion k ℓ e * s
  have hd (s : ℝ) : HasDerivAt F 0 s := by
    let φ := keplerAngle k ℓ e s
    have hg := (da h₀ h₁ φ).comp s (hasDerivAt_keplerAngle hk hℓ h₀ h₁ s)
    have hm := (hasDerivAt_id (angle e φ)).sub ((Real.hasDerivAt_sin (angle e φ)).const_mul e)
    convert (hm.comp s hg).sub ((hasDerivAt_id s).const_mul (meanMotion k ℓ e)) using 1
    · rfl
    rw [(trig h₀ h₁ φ).1]
    change 0 = (1 - e * ec e φ) * (jac e φ * angleField k ℓ e φ) - meanMotion k ℓ e * 1
    unfold ec jac angleField meanMotion
    field_simp [(one_add_mul_cos_pos h₀ h₁ φ).ne']
    ring
  have h := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  have hzero : F 0 = 0 := by simp [F, keplerAngle_zero, angle, meanAnomaly]
  exact sub_eq_zero.mp (h.trans hzero)

/-- The Cartesian position of the previously constructed orbit in the eccentric-anomaly chart. -/
theorem keplerPosition_eccentric {k ℓ e : ℝ} (hk : 0 < k) (hℓ : 0 < ℓ) (h₀ : 0 ≤ e)
    (h₁ : e < 1) (t : ℝ) :
    keplerPosition k ℓ e t =
      (semiMajor k ℓ e * (cos (eccentricAnomaly e (meanMotion k ℓ e * t)) - e),
       semiMajor k ℓ e * √(1-e^2) * sin (eccentricAnomaly e (meanMotion k ℓ e * t))) := by
  let φ := keplerAngle k ℓ e t
  have he : |e| < 1 := (abs_of_nonneg h₀).symm ▸ h₁
  rw [← mean_time hk hℓ h₀ h₁ t, eccentric_mean he]
  change (_, _) =
    (semiMajor k ℓ e * (cos (angle e φ) - e), semiMajor k ℓ e * _ * sin (angle e φ))
  rw [(trig h₀ h₁ φ).1, (trig h₀ h₁ φ).2]
  have hq : 0 < 1 - e ^ 2 := by nlinarith
  have hd := (one_add_mul_cos_pos h₀ h₁ φ).ne'
  change (semiLatus k ℓ / (1+e*cos φ) * cos φ, semiLatus k ℓ / (1+e*cos φ) * sin φ) = _
  ext
  · unfold semiMajor ec
    field_simp [hq.ne', hd]
    ring
  · unfold semiMajor es
    field_simp [hq.ne', hd]
    linear_combination -(semiLatus k ℓ * sin φ) * Real.sq_sqrt hq.le

/-- The phase normalization agrees with the period of the original orbit. -/
theorem meanMotion_mul_period {k ℓ e : ℝ} (hk : 0 < k) (hℓ : 0 < ℓ)
    (h₀ : 0 ≤ e) (h₁ : e < 1) : meanMotion k ℓ e * keplerPeriod k ℓ e = 2 * π := by
  have hq : 0 < 1 - e ^ 2 := by nlinarith
  rw [meanMotion, keplerPeriod_eq hk hℓ h₀ h₁]
  field_simp [hk.ne', hℓ.ne', hq.ne', (Real.sqrt_pos.mpr hq).ne']

end ProjectAinos.Electrodynamics.Radiation.CoulombRadiation
