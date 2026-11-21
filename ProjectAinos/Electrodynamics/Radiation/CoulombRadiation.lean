/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.Radiation.Collision
public import ProjectAinos.SmoothGeometry.ODE.ScalarFlow
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic

/-!
# Radiation in the case of Coulomb interaction

Landau–Lifshitz, *The Classical Theory of Fields*, §70, in the dipole approximation of §68
(`Collision.dipolePower`): the dipole is `e 𝐫` for the relative coordinate `𝐫`, with
`e = Collision.reducedCharge m₁ m₂ e₁ e₂` for two charges.

The hyperbolic orbit of `Scattering.Coulomb` (speed `v∞` at infinity, impact parameter `ρ`,
`a = α/m v∞²`, both signs of `a`):

* `cos_orbitAngle`: the orbit is the conic `√(a² + ρ²) cos φ − a = ρ²/r`.
* `integral_inv_pow_four_div_sqrt`: the turning-point quadrature
  `∫_{r₀}^∞ dr/(r⁴ ṙ) = ((3a² + ρ²) φ₀ − 3aρ)/(2ρ⁵ v∞)`, `φ₀ = arccos (a/√(a² + ρ²))`.
* `totalEnergy_hyperbolic`: the energy radiated in the collision is
  `ΔE = (2/3)(1/4π) e² v∞³ a² ((3a² + ρ²) φ₀ − 3aρ)/ρ⁵`.
* `effectiveRadiation_repulsive`: for a repulsive field the effective radiation converges,
  `κ = (2/9) e² v∞³ a = (2/9) e² v∞ α/m`, which is `(8π/9)(e²/4π)(α/m) v∞`;
  `not_isEffectiveFinite_attractive`: for an attractive field it diverges at small `ρ`.
* `fourier_orbit`, `fourier_acceleration_fst`, `fourier_acceleration_snd`,
  `spectrum_hyperbolic`: the Fourier transform of `𝐝̈` is an integral over the angle,
  `(e v∞ a/ρ) ∫_{−φ₀}^{φ₀} e^{−2πiν t(φ)} (cos φ, sin φ) dφ`, with the time
  `t(φ) = ∫₀^φ ρ⁴ dψ/(ρ v∞ (√(a² + ρ²) cos ψ − a)²)` on the orbit (`timeOfAngle_orbitAngle`);
  the spectral density is `(2/3)(1/4π)` times its squared modulus.

The elliptic orbit of an attractive field `𝐫̈ = −k 𝐫/r³` (`k = α/m`), with the areal constant
`ℓ = r²φ̇` and the eccentricity `0 ≤ ε < 1`, is constructed from the flow of
`φ̇ = (k²/ℓ³)(1 + ε cos φ)²` (`keplerAngle`): `r = p/(1 + ε cos φ)` with `p = ℓ²/k`
(`hasDerivAt_keplerPosition`, `hasDerivAt_keplerVelocity`, `keplerPosition_cross_velocity`).

* `keplerPeriod_eq`: the period is `T = 2πℓ³/(k²(1 − ε²)^{3/2})`, from
  `∫₀^{2π} dφ/(1 + ε cos φ)² = 2π/(1 − ε²)^{3/2}` (`integral_inv_one_add_mul_cos_sq`);
  `keplerPeriod_eq_semiMajor`: `T = 2π √(A³/k)` with `A = p/(1 − ε²)` (*Mechanics* (15.8)).
* `average_dipolePower_kepler` (a problem of Landau–Lifshitz §70): the mean power is
  `(2/3)(1/4π) e² k⁶ (2 + ε²)(1 − ε²)^{3/2}/(2ℓ⁸)`.
* `harmonic_decomposition`: `𝐝̈` has the period `T` (`keplerAcceleration_add_period`); with its
  Fourier coefficients `c_n = (1/T) ∫₀ᵀ e^{−2πint/T} 𝐝̈ dt` (`harmonicCoeff`) the mean power is
  `Σ_n (2/3)(1/4π)|c_n|²` (Parseval), and `tsum_harmonic` evaluates the sum.

The companion module `KeplerHarmonics` evaluates the elliptic acceleration coefficients in terms
of Jₙ(nε) and J′ₙ(nε) through the eccentric anomaly. The hyperbolic spectrum below is given by
its orbit integral.
-/

@[expose] public section
noncomputable section

open Set Filter MeasureTheory
open scoped Real Topology FourierTransform ContDiff

namespace ProjectAinos.Electrodynamics.Radiation.CoulombRadiation

open Mechanics.Scattering Mechanics.Scattering.Coulomb Collision

variable {a ρ vinf : ℝ}

/-! ### The orbit equation -/

theorem sq_le_hyp_sq (hρ : 0 < ρ) {r : ℝ} (hr : closest a ρ ≤ r) :
    (ρ ^ 2 / r + a) ^ 2 ≤ hyp a ρ ^ 2 := by
  have hr0 : 0 < r := (closest_pos a hρ).trans_le hr
  have hQ : 0 ≤ r ^ 2 - 2 * a * r - ρ ^ 2 := by
    rw [← sub_mul_add]
    exact mul_nonneg (sub_nonneg.mpr hr) (add_pos hr0 (conjugate_pos a hρ)).le
  have e : hyp a ρ ^ 2 - (ρ ^ 2 / r + a) ^ 2 = ρ ^ 2 * (r ^ 2 - 2 * a * r - ρ ^ 2) / r ^ 2 := by
    rw [hyp_sq]
    field_simp
    ring
  have : 0 ≤ hyp a ρ ^ 2 - (ρ ^ 2 / r + a) ^ 2 := by
    rw [e]
    positivity
  linarith

/-- On the orbit, `cos (primitive r) = (ρ²/r + a)/√(a² + ρ²)`. -/
theorem cos_primitive (hρ : 0 < ρ) {r : ℝ} (hr : closest a ρ ≤ r) :
    Real.cos (primitive a ρ r) = (ρ ^ 2 / r + a) / hyp a ρ := by
  have hc := hyp_pos a hρ
  have h := sq_le_hyp_sq hρ hr
  have h1 : |ρ ^ 2 / r + a| ≤ hyp a ρ := by
    have := Real.abs_le_sqrt h
    rwa [Real.sqrt_sq hc.le] at this
  have h2 : |(ρ ^ 2 / r + a) / hyp a ρ| ≤ 1 := by
    rw [abs_div, abs_of_pos hc, div_le_one hc]
    exact h1
  rw [primitive, Real.cos_arccos (abs_le.mp h2).1 (abs_le.mp h2).2]

/-- After the closest approach the angle is the primitive of the density (18.4) at `r(t)`. -/
theorem orbitAngle_eq_primitive (hρ : 0 < ρ) (hv : 0 < vinf) {t : ℝ} (ht : 0 ≤ t) :
    orbitAngle a ρ vinf t = primitive a ρ (orbitRadius a ρ vinf t) := by
  have h0 := closest_pos a hρ
  have hF := isFactor a hρ hv
  have hcont : ContinuousOn (fun s => primitive a ρ (orbitRadius a ρ vinf s)) (Icc 0 t) := by
    have h1 : Continuous fun s => (ρ ^ 2 / orbitRadius a ρ vinf s + a) / hyp a ρ :=
      ((continuous_const.div (continuous_orbitRadius hρ hv) fun s =>
        (orbitRadius_pos hρ vinf s).ne').add continuous_const).div_const _
    exact (Real.continuous_arccos.comp h1).continuousOn
  have hderiv : ∀ s ∈ Ioo 0 t, HasDerivAt (fun s => primitive a ρ (orbitRadius a ρ vinf s))
      (ρ * vinf / orbitRadius a ρ vinf s ^ 2) s := by
    intro s hs
    have hrs : closest a ρ < orbitRadius a ρ vinf s := by
      have h := hF.strictMonoOn_radius (mem_Ici.mpr (le_refl (0 : ℝ))) (mem_Ici.mpr hs.1.le) hs.1
      rw [radius_zero] at h
      exact h
    have h1 := (hasDerivAt_primitive hρ hv hrs).comp s (hasDerivAt_orbitRadius hρ hv s)
    refine h1.congr_deriv ?_
    have hsq := (radialVelocity_eq_sqrt (a := a) hρ hv hs.1)
    have hpos := hF.radialVelocity_pos hs.1
    rw [angleDensity, ← hsq]
    field_simp
  have hint : IntervalIntegrable (fun s => ρ * vinf / orbitRadius a ρ vinf s ^ 2) volume 0 t :=
    ((isFactor a hρ hv).continuous_angleRate h0 _).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht hcont hderiv hint
  have hr0 : orbitRadius a ρ vinf 0 = closest a ρ := radius_zero _ _
  rw [hr0, primitive_closest a hρ, sub_zero] at h
  exact h

/-- The orbit is the conic `√(a² + ρ²) cos φ − a = ρ²/r` of the Coulomb field. -/
theorem cos_orbitAngle (hρ : 0 < ρ) (hv : 0 < vinf) (t : ℝ) :
    hyp a ρ * Real.cos (orbitAngle a ρ vinf t) - a = ρ ^ 2 / orbitRadius a ρ vinf t := by
  have hc := hyp_pos a hρ
  have key : ∀ s, 0 ≤ s →
      hyp a ρ * Real.cos (orbitAngle a ρ vinf s) - a = ρ ^ 2 / orbitRadius a ρ vinf s := by
    intro s hs
    rw [orbitAngle_eq_primitive hρ hv hs, cos_primitive hρ (closest_le_orbitRadius a ρ vinf s)]
    field_simp
    ring
  rcases le_total 0 t with ht | ht
  · exact key t ht
  · have h := key (-t) (neg_nonneg.mpr ht)
    rwa [orbitAngle_neg hρ hv, Real.cos_neg, orbitRadius_neg hρ hv] at h

/-! ### The energy radiated in a hyperbolic collision -/

/-- `∫₀^φ u(ψ)² dψ` for the inverse radius `u(ψ) = (√(a² + ρ²) cos ψ − a)/ρ²` of the orbit. -/
def angleIntegral (a ρ φ : ℝ) : ℝ :=
  (hyp a ρ ^ 2 * (φ + Real.sin φ * Real.cos φ) / 2 - 2 * a * hyp a ρ * Real.sin φ + a ^ 2 * φ) /
    ρ ^ 4

theorem hasDerivAt_angleIntegral (a ρ φ : ℝ) :
    HasDerivAt (angleIntegral a ρ) (((hyp a ρ * Real.cos φ - a) / ρ ^ 2) ^ 2) φ := by
  have hs := Real.hasDerivAt_sin φ
  have hc := Real.hasDerivAt_cos φ
  have h1 : HasDerivAt (fun φ => hyp a ρ ^ 2 * (φ + Real.sin φ * Real.cos φ) / 2 -
      2 * a * hyp a ρ * Real.sin φ + a ^ 2 * φ)
      (hyp a ρ ^ 2 * (1 + (Real.cos φ * Real.cos φ + Real.sin φ * -Real.sin φ)) / 2 -
        2 * a * hyp a ρ * Real.cos φ + a ^ 2 * 1) φ :=
    ((((hasDerivAt_id φ).add (hs.mul hc)).const_mul (hyp a ρ ^ 2)).div_const 2 |>.sub
      (hs.const_mul (2 * a * hyp a ρ))).add ((hasDerivAt_id φ).const_mul (a ^ 2))
  refine (h1.div_const (ρ ^ 4)).congr_deriv ?_
  have h := Real.sin_sq_add_cos_sq φ
  rw [div_pow, ← pow_mul]
  congr 1
  linear_combination (-(hyp a ρ ^ 2) / 2) * h

theorem angleIntegral_zero (a ρ : ℝ) : angleIntegral a ρ 0 = 0 := by
  simp [angleIntegral]

theorem continuous_angleIntegral (a ρ : ℝ) : Continuous (angleIntegral a ρ) :=
  continuous_iff_continuousAt.mpr fun φ => (hasDerivAt_angleIntegral a ρ φ).continuousAt

/-- The value at the asymptote: `((3a² + ρ²) φ₀ − 3aρ)/(2ρ⁴)`. -/
theorem angleIntegral_asymptoteAngle (a : ℝ) (hρ : 0 < ρ) :
    angleIntegral a ρ (asymptoteAngle a ρ) =
      ((3 * a ^ 2 + ρ ^ 2) * asymptoteAngle a ρ - 3 * a * ρ) / (2 * ρ ^ 4) := by
  have hc := hyp_pos a hρ
  have h := abs_lt.mp (abs_div_hyp_lt_one a hρ)
  have hcos : Real.cos (asymptoteAngle a ρ) = a / hyp a ρ :=
    Real.cos_arccos h.1.le h.2.le
  have hsin : Real.sin (asymptoteAngle a ρ) = ρ / hyp a ρ := by
    rw [asymptoteAngle, Real.sin_arccos]
    have e : 1 - (a / hyp a ρ) ^ 2 = (ρ / hyp a ρ) ^ 2 := by
      rw [div_pow, div_pow, hyp_sq]
      field_simp
      ring
    rw [e, Real.sqrt_sq (by positivity)]
  rw [angleIntegral, hcos, hsin]
  have hh := hyp_sq a ρ
  field_simp
  linear_combination asymptoteAngle a ρ * hh

/-- The primitive `(∫₀^{φ(r)} u²)/ℓ` of `1/(r⁴ ṙ)` along the outgoing branch. -/
def radialPrimitive (a ρ vinf r : ℝ) : ℝ := angleIntegral a ρ (primitive a ρ r) / (ρ * vinf)

theorem hasDerivAt_radialPrimitive (hρ : 0 < ρ) (hv : 0 < vinf) {r : ℝ} (hr : closest a ρ < r) :
    HasDerivAt (radialPrimitive a ρ vinf) ((r ^ 4)⁻¹ / √(speedSq a ρ vinf r)) r := by
  have hr0 : 0 < r := (closest_pos a hρ).trans hr
  have h1 := ((hasDerivAt_angleIntegral a ρ (primitive a ρ r)).comp r
    (hasDerivAt_primitive hρ hv hr)).div_const (ρ * vinf)
  refine h1.congr_deriv ?_
  rw [cos_primitive hρ hr.le, angleDensity]
  have hc := hyp_pos a hρ
  have hρ0 := hρ.ne'
  have hv0 := hv.ne'
  field_simp
  ring

theorem continuousWithinAt_radialPrimitive (hρ : 0 < ρ) :
    ContinuousWithinAt (radialPrimitive a ρ vinf) (Ici (closest a ρ)) (closest a ρ) := by
  have h0 := closest_pos a hρ
  have h1 : ContinuousAt (fun r : ℝ => (ρ ^ 2 / r + a) / hyp a ρ) (closest a ρ) :=
    ((continuousAt_const.div continuousAt_id h0.ne').add continuousAt_const).div_const _
  have h2 : ContinuousAt (primitive a ρ) (closest a ρ) :=
    Real.continuous_arccos.continuousAt.comp h1
  exact (((continuous_angleIntegral a ρ).continuousAt.comp h2).div_const _).continuousWithinAt

theorem tendsto_radialPrimitive_atTop (a ρ vinf : ℝ) :
    Tendsto (radialPrimitive a ρ vinf) atTop
      (𝓝 (angleIntegral a ρ (asymptoteAngle a ρ) / (ρ * vinf))) :=
  (((continuous_angleIntegral a ρ).tendsto _).comp (tendsto_primitive_atTop a ρ)).div_const _

/-- The turning-point quadrature `∫_{r₀}^∞ dr/(r⁴ ṙ) = ((3a² + ρ²) φ₀ − 3aρ)/(2ρ⁵ v∞)`, with
`ṙ = √(v∞²(1 − 2a/r − ρ²/r²))`. -/
theorem integral_inv_pow_four_div_sqrt (a : ℝ) (hρ : 0 < ρ) (hv : 0 < vinf) :
    IntegrableOn (fun r => (r ^ 4)⁻¹ / √(speedSq a ρ vinf r)) (Ioi (closest a ρ)) ∧
      ∫ r in Ioi (closest a ρ), (r ^ 4)⁻¹ / √(speedSq a ρ vinf r) =
        ((3 * a ^ 2 + ρ ^ 2) * asymptoteAngle a ρ - 3 * a * ρ) / (2 * ρ ^ 5 * vinf) := by
  have hcont := continuousWithinAt_radialPrimitive (a := a) (vinf := vinf) hρ
  have hderiv : ∀ r ∈ Ioi (closest a ρ), HasDerivAt (radialPrimitive a ρ vinf)
      ((r ^ 4)⁻¹ / √(speedSq a ρ vinf r)) r := fun r hr => hasDerivAt_radialPrimitive hρ hv hr
  have hnn : ∀ r ∈ Ioi (closest a ρ), 0 ≤ (r ^ 4)⁻¹ / √(speedSq a ρ vinf r) := fun r hr => by
    have : 0 < r := (closest_pos a hρ).trans hr
    positivity
  have hlim := tendsto_radialPrimitive_atTop a ρ vinf
  have hint := integrableOn_Ioi_deriv_of_nonneg hcont hderiv hnn hlim
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim, radialPrimitive,
    primitive_closest a hρ, angleIntegral_zero, zero_div, sub_zero,
    angleIntegral_asymptoteAngle a hρ]
  field_simp

/-- Landau–Lifshitz §70: the energy radiated in a collision on the hyperbolic Coulomb orbit,
`ΔE = (2/3)(1/4π) e² v∞³ a² ((3a² + ρ²) φ₀ − 3aρ)/ρ⁵` with `φ₀ = arccos (a/√(a² + ρ²))`,
`a = α/m v∞²`; for the repulsive (`a > 0`) and the attractive (`a < 0`) field. -/
theorem totalEnergy_hyperbolic (e a : ℝ) (hρ : 0 < ρ) (hv : 0 < vinf) :
    totalEnergy e a ρ vinf = 2 / 3 * (4 * π)⁻¹ * e ^ 2 * vinf ^ 3 * a ^ 2 *
      ((3 * a ^ 2 + ρ ^ 2) * asymptoteAngle a ρ - 3 * a * ρ) / ρ ^ 5 := by
  rw [integral_dipolePower_eq e a hρ hv]
  have e1 : (fun r => 2 / 3 * (4 * π)⁻¹ * (e * (vinf ^ 2 * a / r ^ 2)) ^ 2 /
      √(speedSq a ρ vinf r)) = fun r => 2 / 3 * (4 * π)⁻¹ * (e * (vinf ^ 2 * a)) ^ 2 *
        ((r ^ 4)⁻¹ / √(speedSq a ρ vinf r)) := by
    funext r
    ring
  rw [e1, integral_const_mul, (integral_inv_pow_four_div_sqrt a hρ hv).2]
  have hρ0 := hρ.ne'
  have hv0 := hv.ne'
  field_simp

/-- The bracket `(3a² + ρ²) φ₀ − 3aρ` of the radiated energy is nonnegative. -/
theorem radiationBracket_nonneg (a : ℝ) (hρ : 0 < ρ) :
    0 ≤ (3 * a ^ 2 + ρ ^ 2) * asymptoteAngle a ρ - 3 * a * ρ := by
  have h := (integral_inv_pow_four_div_sqrt a hρ one_pos).2
  have hnn : 0 ≤ ∫ r in Ioi (closest a ρ), (r ^ 4)⁻¹ / √(speedSq a ρ 1 r) :=
    setIntegral_nonneg measurableSet_Ioi fun r hr => by
      have : 0 < r := (closest_pos a hρ).trans hr
      positivity
  rw [h] at hnn
  have hd : 0 < 2 * ρ ^ 5 * 1 := by positivity
  exact (div_nonneg_iff.mp hnn).elim (fun h => h.1) fun h => absurd h.2 (not_le.mpr hd)

/-! ### The effective radiation of a repulsive field -/

/-- For a repulsive field `φ₀ = arctan (ρ/a)`. -/
theorem asymptoteAngle_eq_arctan (ha : 0 < a) (hρ : 0 < ρ) :
    asymptoteAngle a ρ = Real.arctan (ρ / a) := by
  have hc := hyp_pos a hρ
  rw [asymptoteAngle, Real.arccos_eq_arctan (div_pos ha hc)]
  congr 1
  have e : 1 - (a / hyp a ρ) ^ 2 = (ρ / hyp a ρ) ^ 2 := by
    rw [div_pow, div_pow, hyp_sq]
    field_simp
    ring
  rw [e, Real.sqrt_sq (by positivity)]
  field_simp

theorem arctan_lower (x : ℝ) (hx : 0 ≤ x) : x - x ^ 3 / 3 ≤ Real.arctan x := by
  let h : ℝ → ℝ := fun x => Real.arctan x - (x - x ^ 3 / 3)
  have hd : ∀ y, HasDerivAt h (1 / (1 + y ^ 2) - (1 - y ^ 2)) y := fun y => by
    have := (Real.hasDerivAt_arctan y).sub ((hasDerivAt_id y).sub
      ((hasDerivAt_pow 3 y).div_const 3))
    refine this.congr_deriv ?_
    push_cast
    ring
  have hmono : MonotoneOn h (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun y _ => (hd y).continuousAt.continuousWithinAt)
      (fun y _ => (hd y).differentiableAt.differentiableWithinAt) fun y _ => ?_
    rw [(hd y).deriv]
    have h1 : 0 < 1 + y ^ 2 := by positivity
    rw [show 1 / (1 + y ^ 2) - (1 - y ^ 2) = y ^ 4 / (1 + y ^ 2) by field_simp; ring]
    positivity
  have := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx) hx
  simp only [h, Real.arctan_zero] at this
  linarith

theorem arctan_upper (x : ℝ) (hx : 0 ≤ x) : Real.arctan x ≤ x - x ^ 3 / 3 + x ^ 5 / 5 := by
  let h : ℝ → ℝ := fun x => x - x ^ 3 / 3 + x ^ 5 / 5 - Real.arctan x
  have hd : ∀ y, HasDerivAt h (1 - y ^ 2 + y ^ 4 - 1 / (1 + y ^ 2)) y := fun y => by
    have := (((hasDerivAt_id y).sub ((hasDerivAt_pow 3 y).div_const 3)).add
      ((hasDerivAt_pow 5 y).div_const 5)).sub (Real.hasDerivAt_arctan y)
    refine this.congr_deriv ?_
    push_cast
    ring
  have hmono : MonotoneOn h (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun y _ => (hd y).continuousAt.continuousWithinAt)
      (fun y _ => (hd y).differentiableAt.differentiableWithinAt) fun y _ => ?_
    rw [(hd y).deriv]
    have h1 : 0 < 1 + y ^ 2 := by positivity
    rw [show 1 - y ^ 2 + y ^ 4 - 1 / (1 + y ^ 2) = y ^ 6 / (1 + y ^ 2) by field_simp; ring]
    positivity
  have := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx) hx
  simp only [h, Real.arctan_zero] at this
  linarith

/-- The primitive `a/ρ² − (a² + ρ²) arctan (ρ/a)/ρ³` of `((3a² + ρ²) arctan (ρ/a) − 3aρ)/ρ⁴`,
extended by its limit `−2/(3a)` at `ρ = 0`. -/
def impactPrimitive (a ρ : ℝ) : ℝ :=
  if ρ = 0 then -(2 / (3 * a)) else a / ρ ^ 2 - (a ^ 2 + ρ ^ 2) * Real.arctan (ρ / a) / ρ ^ 3

theorem hasDerivAt_impactPrimitive (ha : 0 < a) {ρ : ℝ} (hρ : 0 < ρ) :
    HasDerivAt (impactPrimitive a)
      (((3 * a ^ 2 + ρ ^ 2) * Real.arctan (ρ / a) - 3 * a * ρ) / ρ ^ 4) ρ := by
  have hρ0 := hρ.ne'
  have ha0 := ha.ne'
  have heq : impactPrimitive a =ᶠ[𝓝 ρ]
      fun ρ => a / ρ ^ 2 - (a ^ 2 + ρ ^ 2) * Real.arctan (ρ / a) / ρ ^ 3 := by
    filter_upwards [eventually_ne_nhds hρ0] with x hx
    simp [impactPrimitive, hx]
  have hd : HasDerivAt (fun x : ℝ => x / a) (1 / a) ρ := (hasDerivAt_id ρ).div_const a
  have hat : HasDerivAt (fun ρ => Real.arctan (ρ / a)) (1 / (1 + (ρ / a) ^ 2) * (1 / a)) ρ :=
    HasDerivAt.comp (h₂ := Real.arctan) ρ (Real.hasDerivAt_arctan (ρ / a)) hd
  have h2 : HasDerivAt (fun ρ : ℝ => ρ ^ 2) (2 * ρ) ρ := by simpa using hasDerivAt_pow 2 ρ
  have h3 : HasDerivAt (fun ρ : ℝ => ρ ^ 3) (3 * ρ ^ 2) ρ := by simpa using hasDerivAt_pow 3 ρ
  have hA : HasDerivAt (fun ρ : ℝ => a ^ 2 + ρ ^ 2) (0 + 2 * ρ) ρ :=
    (hasDerivAt_const ρ (a ^ 2)).fun_add h2
  have hB : HasDerivAt (fun ρ : ℝ => (a ^ 2 + ρ ^ 2) * Real.arctan (ρ / a))
      ((0 + 2 * ρ) * Real.arctan (ρ / a) + (a ^ 2 + ρ ^ 2) * (1 / (1 + (ρ / a) ^ 2) * (1 / a)))
      ρ := hA.fun_mul hat
  have h1 := ((hasDerivAt_const ρ a).div h2 (pow_ne_zero 2 hρ0)).fun_sub
    (hB.div h3 (pow_ne_zero 3 hρ0))
  refine (h1.congr_of_eventuallyEq heq).congr_deriv ?_
  have h4 : 1 + (ρ / a) ^ 2 ≠ 0 := by positivity
  field_simp
  ring

theorem tendsto_impactPrimitive_atTop (ha : 0 < a) :
    Tendsto (impactPrimitive a) atTop (𝓝 0) := by
  have h1 : Tendsto (fun ρ : ℝ => a / ρ ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)
  have h2 : Tendsto (fun ρ : ℝ => a ^ 2 / ρ ^ 3 + 1 / ρ) atTop (𝓝 (0 + 0)) :=
    (tendsto_const_nhds.div_atTop (tendsto_pow_atTop three_ne_zero)).add
      (tendsto_const_nhds.div_atTop tendsto_id)
  have h3 : Tendsto (fun ρ : ℝ => Real.arctan (ρ / a)) atTop (𝓝 (π / 2)) :=
    (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
      (tendsto_id.atTop_div_const ha)
  have h4 := h1.sub ((h2.mul h3))
  rw [add_zero, zero_mul, sub_zero] at h4
  refine h4.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hx0 := hx.ne'
  simp only [impactPrimitive, hx0, ↓reduceIte]
  field_simp

theorem tendsto_impactPrimitive_zero (ha : 0 < a) :
    Tendsto (impactPrimitive a) (𝓝[>] 0) (𝓝 (-(2 / (3 * a)))) := by
  have ha0 := ha.ne'
  -- bounds through `x = ρ/a`
  have hlow : ∀ ρ ∈ Ioi (0 : ℝ),
      -(2 / (3 * a)) + 2 * ρ ^ 2 / (15 * a ^ 3) - ρ ^ 4 / (5 * a ^ 5) ≤ impactPrimitive a ρ := by
    intro ρ hρ
    have hρ0 : ρ ≠ 0 := (mem_Ioi.mp hρ).ne'
    have hx : 0 ≤ ρ / a := div_nonneg (mem_Ioi.mp hρ).le ha.le
    have hu := arctan_upper (ρ / a) hx
    simp only [impactPrimitive, hρ0, ↓reduceIte]
    have hpos : 0 < (a ^ 2 + ρ ^ 2) / ρ ^ 3 := by
      have := mem_Ioi.mp hρ
      positivity
    have key : (a ^ 2 + ρ ^ 2) * Real.arctan (ρ / a) / ρ ^ 3 ≤
        (a ^ 2 + ρ ^ 2) / ρ ^ 3 * (ρ / a - (ρ / a) ^ 3 / 3 + (ρ / a) ^ 5 / 5) := by
      rw [mul_comm (a ^ 2 + ρ ^ 2), mul_div_assoc, mul_comm]
      exact mul_le_mul_of_nonneg_left hu hpos.le
    have e : a / ρ ^ 2 - (a ^ 2 + ρ ^ 2) / ρ ^ 3 * (ρ / a - (ρ / a) ^ 3 / 3 + (ρ / a) ^ 5 / 5) =
        -(2 / (3 * a)) + 2 * ρ ^ 2 / (15 * a ^ 3) - ρ ^ 4 / (5 * a ^ 5) := by
      field_simp
      ring
    linarith
  have hup : ∀ ρ ∈ Ioi (0 : ℝ), impactPrimitive a ρ ≤ -(2 / (3 * a)) + ρ ^ 2 / (3 * a ^ 3) := by
    intro ρ hρ
    have hρ0 : ρ ≠ 0 := (mem_Ioi.mp hρ).ne'
    have hx : 0 ≤ ρ / a := div_nonneg (mem_Ioi.mp hρ).le ha.le
    have hl := arctan_lower (ρ / a) hx
    simp only [impactPrimitive, hρ0, ↓reduceIte]
    have hpos : 0 < (a ^ 2 + ρ ^ 2) / ρ ^ 3 := by
      have := mem_Ioi.mp hρ
      positivity
    have key : (a ^ 2 + ρ ^ 2) / ρ ^ 3 * (ρ / a - (ρ / a) ^ 3 / 3) ≤
        (a ^ 2 + ρ ^ 2) * Real.arctan (ρ / a) / ρ ^ 3 := by
      rw [mul_comm (a ^ 2 + ρ ^ 2), mul_div_assoc, mul_comm (Real.arctan (ρ / a))]
      exact mul_le_mul_of_nonneg_left hl hpos.le
    have e : a / ρ ^ 2 - (a ^ 2 + ρ ^ 2) / ρ ^ 3 * (ρ / a - (ρ / a) ^ 3 / 3) =
        -(2 / (3 * a)) + ρ ^ 2 / (3 * a ^ 3) := by
      field_simp
      ring
    linarith
  have hc1 : Tendsto (fun ρ : ℝ => -(2 / (3 * a)) + 2 * ρ ^ 2 / (15 * a ^ 3) -
      ρ ^ 4 / (5 * a ^ 5)) (𝓝[>] 0) (𝓝 (-(2 / (3 * a)))) := by
    have : Continuous fun ρ : ℝ => -(2 / (3 * a)) + 2 * ρ ^ 2 / (15 * a ^ 3) -
        ρ ^ 4 / (5 * a ^ 5) := by fun_prop
    have h := (this.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using h
  have hc2 : Tendsto (fun ρ : ℝ => -(2 / (3 * a)) + ρ ^ 2 / (3 * a ^ 3)) (𝓝[>] 0)
      (𝓝 (-(2 / (3 * a)))) := by
    have : Continuous fun ρ : ℝ => -(2 / (3 * a)) + ρ ^ 2 / (3 * a ^ 3) := by fun_prop
    have h := (this.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hc1 hc2
    (eventually_nhdsWithin_of_forall hlow) (eventually_nhdsWithin_of_forall hup)

/-- A problem of Landau–Lifshitz §70: the effective radiation in a repulsive Coulomb field
converges and is `κ = (2/9) e² v∞³ a = (2/9) e² v∞ α/m`, i.e. `(8π/9)(e²/4π)(α/m) v∞`. -/
theorem effectiveRadiation_repulsive (e : ℝ) (ha : 0 < a) (hv : 0 < vinf) :
    IsEffectiveFinite e a vinf ∧ effectiveRadiation e a vinf = 2 / 9 * e ^ 2 * vinf ^ 3 * a := by
  set C := 1 / 3 * e ^ 2 * vinf ^ 3 * a ^ 2 with hC
  have hval : ∀ ρ ∈ Ioi (0 : ℝ), totalEnergy e a ρ vinf * (2 * π * ρ) =
      C * (((3 * a ^ 2 + ρ ^ 2) * Real.arctan (ρ / a) - 3 * a * ρ) / ρ ^ 4) := by
    intro ρ hρ
    have hρ0 : 0 < ρ := hρ
    rw [totalEnergy_hyperbolic e a hρ0 hv, asymptoteAngle_eq_arctan ha hρ0, hC]
    have := hρ0.ne'
    field_simp
    ring
  have hcont : ContinuousWithinAt (impactPrimitive a) (Ici 0) 0 := by
    rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt]
    have h := tendsto_impactPrimitive_zero ha
    simpa [impactPrimitive] using h
  have hderiv : ∀ ρ ∈ Ioi (0 : ℝ), HasDerivAt (impactPrimitive a)
      (((3 * a ^ 2 + ρ ^ 2) * Real.arctan (ρ / a) - 3 * a * ρ) / ρ ^ 4) ρ :=
    fun ρ hρ => hasDerivAt_impactPrimitive ha hρ
  have hnn : ∀ ρ ∈ Ioi (0 : ℝ),
      0 ≤ ((3 * a ^ 2 + ρ ^ 2) * Real.arctan (ρ / a) - 3 * a * ρ) / ρ ^ 4 := by
    intro ρ hρ
    have hρ0 : 0 < ρ := hρ
    have h := radiationBracket_nonneg a hρ0
    rw [asymptoteAngle_eq_arctan ha hρ0] at h
    positivity
  have hlim := tendsto_impactPrimitive_atTop ha
  have hint := integrableOn_Ioi_deriv_of_nonneg hcont hderiv hnn hlim
  have hI := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  have h2 : IntegrableOn
      (fun ρ => C * (((3 * a ^ 2 + ρ ^ 2) * Real.arctan (ρ / a) - 3 * a * ρ) / ρ ^ 4))
      (Ioi 0) := hint.const_mul C
  have hfin : IsEffectiveFinite e a vinf :=
    h2.congr_fun (fun ρ hρ => (hval ρ hρ).symm) measurableSet_Ioi
  refine ⟨hfin, ?_⟩
  rw [effectiveRadiation, setIntegral_congr_fun measurableSet_Ioi hval, integral_const_mul, hI]
  simp only [impactPrimitive, ↓reduceIte]
  rw [hC]
  have := ha.ne'
  field_simp
  ring

/-- For an attractive field the effective radiation diverges: `ΔE(ρ) 2πρ ≥ (π/2) e² v∞³ a⁴/ρ⁴`,
because the orbits of small impact parameter turn round the centre at small distances. -/
theorem not_isEffectiveFinite_attractive {e : ℝ} (he : e ≠ 0) (ha : a < 0) (hv : 0 < vinf) :
    ¬ IsEffectiveFinite e a vinf := by
  intro h
  have ha0 := ha.ne
  set c := π / 2 * e ^ 2 * vinf ^ 3 * a ^ 4 with hc
  have hc0 : 0 < c := by positivity
  have hlow : ∀ ρ ∈ Ioo (0 : ℝ) 1,
      c * (ρ ^ 4)⁻¹ ≤ totalEnergy e a ρ vinf * (2 * π * ρ) := by
    intro ρ hρ
    have hρ0 : 0 < ρ := hρ.1
    have hφ : π / 2 ≤ asymptoteAngle a ρ :=
      Real.pi_div_two_le_arccos.mpr (div_nonpos_of_nonpos_of_nonneg ha.le (hyp_pos a hρ0).le)
    have hB : 3 * a ^ 2 * (π / 2) ≤ (3 * a ^ 2 + ρ ^ 2) * asymptoteAngle a ρ - 3 * a * ρ := by
      have h1 : 0 ≤ ρ ^ 2 * asymptoteAngle a ρ :=
        mul_nonneg (sq_nonneg ρ) (Real.arccos_nonneg _)
      have h2 : 0 ≤ -(3 * a * ρ) := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hφ (by positivity : (0 : ℝ) ≤ 3 * a ^ 2)]
    have e1 : totalEnergy e a ρ vinf * (2 * π * ρ) = 1 / 3 * e ^ 2 * vinf ^ 3 * a ^ 2 *
        ((3 * a ^ 2 + ρ ^ 2) * asymptoteAngle a ρ - 3 * a * ρ) * (ρ ^ 4)⁻¹ := by
      rw [totalEnergy_hyperbolic e a hρ0 hv]
      have := hρ0.ne'
      field_simp
      ring
    rw [e1, hc]
    have hk : 0 ≤ 1 / 3 * e ^ 2 * vinf ^ 3 * a ^ 2 * (ρ ^ 4)⁻¹ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hB hk]
  have h1 : IntegrableOn (fun ρ => totalEnergy e a ρ vinf * (2 * π * ρ)) (Ioo 0 1) :=
    h.mono_set Ioo_subset_Ioi_self
  have hcont : ContinuousOn (fun ρ : ℝ => c * (ρ ^ 4)⁻¹) (Ioo 0 1) :=
    continuousOn_const.mul ((continuous_pow 4).continuousOn.inv₀ fun ρ hρ =>
      pow_ne_zero 4 (mem_Ioo.mp hρ).1.ne')
  have h2 : IntegrableOn (fun ρ : ℝ => c * (ρ ^ 4)⁻¹) (Ioo 0 1) := by
    refine h1.mono' (hcont.aestronglyMeasurable measurableSet_Ioo) ?_
    refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun ρ hρ => ?_)
    have : 0 < ρ := hρ.1
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact hlow ρ hρ
  have h2' : IntegrableOn (fun ρ : ℝ => c⁻¹ * (c * (ρ ^ 4)⁻¹)) (Ioo 0 1) := h2.const_mul c⁻¹
  have h3 : IntegrableOn (fun ρ : ℝ => ρ ^ (-4 : ℝ)) (Ioo 0 1) := by
    refine h2'.congr_fun (fun ρ hρ => ?_) measurableSet_Ioo
    have : 0 < ρ := hρ.1
    rw [Real.rpow_neg this.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  have h4 := (intervalIntegral.integrableOn_Ioo_rpow_iff (s := (-4 : ℝ)) zero_lt_one).mp h3
  norm_num at h4

/-! ### The spectrum of a hyperbolic collision -/

/-- The time `t(φ) = ∫₀^φ ρ⁴ dψ/(ρ v∞ (√(a² + ρ²) cos ψ − a)²)` at which the orbit reaches the
angle `φ ∈ (−φ₀, φ₀)`: `dt = r² dφ/ℓ` with `1/r = (√(a² + ρ²) cos φ − a)/ρ²`. -/
def timeOfAngle (a ρ vinf φ : ℝ) : ℝ :=
  ∫ ψ in (0 : ℝ)..φ, ρ ^ 4 / (ρ * vinf * (hyp a ρ * Real.cos ψ - a) ^ 2)

theorem timeOfAngle_orbitAngle (hρ : 0 < ρ) (hv : 0 < vinf) (t : ℝ) :
    timeOfAngle a ρ vinf (orbitAngle a ρ vinf t) = t := by
  have hderiv : ∀ s ∈ uIcc 0 t, HasDerivAt (orbitAngle a ρ vinf)
      (ρ * vinf / orbitRadius a ρ vinf s ^ 2) s := fun s _ => hasDerivAt_orbitAngle hρ hv s
  have hcont' : ContinuousOn (fun s => ρ * vinf / orbitRadius a ρ vinf s ^ 2) (uIcc 0 t) :=
    ((isFactor a hρ hv).continuous_angleRate (closest_pos a hρ) _).continuousOn
  have hg : ContinuousOn (fun ψ => ρ ^ 4 / (ρ * vinf * (hyp a ρ * Real.cos ψ - a) ^ 2))
      (orbitAngle a ρ vinf '' uIcc 0 t) := by
    refine continuousOn_const.div ((continuous_const.mul
      (((continuous_const.mul Real.continuous_cos).sub continuous_const).pow 2)).continuousOn)
      ?_
    rintro _ ⟨s, _, rfl⟩
    rw [cos_orbitAngle hρ hv s]
    have := orbitRadius_pos (a := a) hρ vinf s
    positivity
  have h := intervalIntegral.integral_comp_mul_deriv' hderiv hcont' hg
  rw [orbitAngle_zero] at h
  rw [timeOfAngle, ← h]
  have e : ∀ s : ℝ, ((fun ψ => ρ ^ 4 / (ρ * vinf * (hyp a ρ * Real.cos ψ - a) ^ 2)) ∘
      orbitAngle a ρ vinf) s * (ρ * vinf / orbitRadius a ρ vinf s ^ 2) = 1 := by
    intro s
    simp only [Function.comp_apply]
    rw [cos_orbitAngle hρ hv s]
    have := (orbitRadius_pos (a := a) hρ vinf s).ne'
    have := hρ.ne'
    have := hv.ne'
    field_simp
  rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) (fun s _ => e s)]
  simp

/-- The angle describes `(−φ₀, φ₀)`. -/
theorem range_orbitAngle (hρ : 0 < ρ) (hv : 0 < vinf) :
    range (orbitAngle a ρ vinf) = Ioo (-asymptoteAngle a ρ) (asymptoteAngle a ρ) := by
  have hmono : StrictMono (orbitAngle a ρ vinf) := strictMono_of_deriv_pos fun t => by
    rw [(hasDerivAt_orbitAngle hρ hv t).deriv]
    have := orbitRadius_pos (a := a) hρ vinf t
    positivity
  have htop := tendsto_orbitAngle_atTop (a := a) hρ hv
  have hbot := tendsto_orbitAngle_atBot (a := a) hρ hv
  apply Subset.antisymm
  · rintro _ ⟨t, rfl⟩
    exact ⟨(hmono.monotone.le_of_tendsto hbot (t - 1)).trans_lt (hmono (by linarith)),
      (hmono (by linarith : t < t + 1)).trans_le (hmono.monotone.ge_of_tendsto htop (t + 1))⟩
  · intro y hy
    obtain ⟨T₂, hT₂⟩ := (htop.eventually (eventually_gt_nhds hy.2)).exists
    obtain ⟨T₁, hT₁⟩ := (hbot.eventually (eventually_lt_nhds hy.1)).exists
    have hle : T₁ ≤ T₂ := by
      by_contra h
      exact absurd (hmono (not_le.mp h)) (not_lt.mpr (hT₁.trans hT₂).le)
    obtain ⟨t, _, ht⟩ := intermediate_value_Icc hle
      (continuous_orbitAngle (a := a) hρ hv).continuousOn ⟨hT₁.le, hT₂.le⟩
    exact ⟨t, ht⟩

theorem strictMono_orbitAngle (hρ : 0 < ρ) (hv : 0 < vinf) : StrictMono (orbitAngle a ρ vinf) :=
  strictMono_of_deriv_pos fun t => by
    rw [(hasDerivAt_orbitAngle hρ hv t).deriv]
    have := orbitRadius_pos (a := a) hρ vinf t
    positivity

/-- A Fourier transform along the orbit as an integral over the angle: for `f(t) =
e (v∞² a/r²) n(φ(t))`, `𝓕f(ν) = (e v∞ a/ρ) ∫_{−φ₀}^{φ₀} e^{−2πiν t(φ)} n(φ) dφ`, because
`dt/r² = dφ/ℓ`. -/
theorem fourier_orbit (e a : ℝ) (hρ : 0 < ρ) (hv : 0 < vinf) (n : ℝ → ℝ) (ν : ℝ) :
    𝓕 (fun t => ((e * (vinf ^ 2 * a / orbitRadius a ρ vinf t ^ 2) *
        n (orbitAngle a ρ vinf t) : ℝ) : ℂ)) ν =
      ((e * (vinf * a / ρ) : ℝ) : ℂ) * ∫ φ in Ioo (-asymptoteAngle a ρ) (asymptoteAngle a ρ),
        Complex.exp (↑(-2 * π * timeOfAngle a ρ vinf φ * ν) * Complex.I) * (n φ : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul, ← range_orbitAngle hρ hv,
    ← image_univ, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
      (fun t _ => (hasDerivAt_orbitAngle hρ hv t).hasDerivWithinAt)
      (strictMono_orbitAngle hρ hv).injective.injOn, Measure.restrict_univ]
  congr 1
  funext t
  have hr := (orbitRadius_pos (a := a) hρ vinf t).ne'
  have hρ0 := hρ.ne'
  have hr' : (orbitRadius a ρ vinf t : ℂ) ≠ 0 := by exact_mod_cast hr
  have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ0
  rw [timeOfAngle_orbitAngle hρ hv t, abs_of_pos (by positivity), Complex.real_smul,
    smul_eq_mul]
  push_cast
  field_simp

theorem fst_smul_acceleration (e a ρ vinf t : ℝ) :
    (e • acceleration a ρ vinf t).1 =
      e * (vinf ^ 2 * a / orbitRadius a ρ vinf t ^ 2) * Real.cos (orbitAngle a ρ vinf t) := by
  simp [acceleration, mul_assoc]

theorem snd_smul_acceleration (e a ρ vinf t : ℝ) :
    (e • acceleration a ρ vinf t).2 =
      e * (vinf ^ 2 * a / orbitRadius a ρ vinf t ^ 2) * Real.sin (orbitAngle a ρ vinf t) := by
  simp [acceleration, mul_assoc]

/-- The Fourier transform of the first component of `𝐝̈ = e 𝐫̈`, along the axis of the closest
approach. -/
theorem fourier_acceleration_fst (e a : ℝ) (hρ : 0 < ρ) (hv : 0 < vinf) (ν : ℝ) :
    𝓕 (fun t => ((e • acceleration a ρ vinf t).1 : ℂ)) ν =
      ((e * (vinf * a / ρ) : ℝ) : ℂ) * ∫ φ in Ioo (-asymptoteAngle a ρ) (asymptoteAngle a ρ),
        Complex.exp (↑(-2 * π * timeOfAngle a ρ vinf φ * ν) * Complex.I) * (Real.cos φ : ℂ) := by
  simp only [fst_smul_acceleration]
  exact fourier_orbit e a hρ hv Real.cos ν

/-- The Fourier transform of the second component of `𝐝̈ = e 𝐫̈`. -/
theorem fourier_acceleration_snd (e a : ℝ) (hρ : 0 < ρ) (hv : 0 < vinf) (ν : ℝ) :
    𝓕 (fun t => ((e • acceleration a ρ vinf t).2 : ℂ)) ν =
      ((e * (vinf * a / ρ) : ℝ) : ℂ) * ∫ φ in Ioo (-asymptoteAngle a ρ) (asymptoteAngle a ρ),
        Complex.exp (↑(-2 * π * timeOfAngle a ρ vinf φ * ν) * Complex.I) * (Real.sin φ : ℂ) := by
  simp only [snd_smul_acceleration]
  exact fourier_orbit e a hρ hv Real.sin ν

/-- Landau–Lifshitz §70: the spectral distribution `dE_ν = (2/3)(1/4π)|𝓕𝐝̈(ν)|² dν` of the
radiation in a hyperbolic collision, as integrals over the angle of the orbit. -/
theorem spectrum_hyperbolic (e a : ℝ) (hρ : 0 < ρ) (hv : 0 < vinf) (ν : ℝ) :
    spectralDensity (fun t => e • acceleration a ρ vinf t) ν =
      2 / 3 * (4 * π)⁻¹ * (e * (vinf * a / ρ)) ^ 2 *
        (‖∫ φ in Ioo (-asymptoteAngle a ρ) (asymptoteAngle a ρ),
            Complex.exp (↑(-2 * π * timeOfAngle a ρ vinf φ * ν) * Complex.I) *
              (Real.cos φ : ℂ)‖ ^ 2 +
          ‖∫ φ in Ioo (-asymptoteAngle a ρ) (asymptoteAngle a ρ),
            Complex.exp (↑(-2 * π * timeOfAngle a ρ vinf φ * ν) * Complex.I) *
              (Real.sin φ : ℂ)‖ ^ 2) := by
  rw [spectralDensity, fourier_acceleration_fst e a hρ hv, fourier_acceleration_snd e a hρ hv,
    norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs]
  ring

/-! ### Two integrals over a period -/

variable {ε : ℝ}

theorem one_add_mul_cos_pos (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) (φ : ℝ) : 0 < 1 + ε * Real.cos φ := by
  have := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos φ) hε₀
  linarith

/-- The primitive `(2/√(1 − ε²)) arctan (√(1 − ε²)/(1 + ε) · tan (φ/2))` of `1/(1 + ε cos φ)` on
`(−π, π)`. -/
theorem hasDerivAt_arctan_tan_half (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) {φ : ℝ} (hφ : φ ∈ Ioo (-π) π) :
    HasDerivAt (fun φ => 2 / √(1 - ε ^ 2) *
      Real.arctan (√(1 - ε ^ 2) / (1 + ε) * Real.tan (φ / 2))) (1 + ε * Real.cos φ)⁻¹ φ := by
  set s := √(1 - ε ^ 2) with hs
  have hs2 : s ^ 2 = 1 - ε ^ 2 := Real.sq_sqrt (by nlinarith)
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by nlinarith)
  have hε1 : 0 < 1 + ε := by linarith
  set c := s / (1 + ε) with hc
  have hC : 0 < Real.cos (φ / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hφ.1], by linarith [hφ.2]⟩
  have hd : HasDerivAt (fun φ : ℝ => φ / 2) (1 / 2) φ := (hasDerivAt_id φ).div_const 2
  have ht := HasDerivAt.comp (h₂ := Real.tan) φ (Real.hasDerivAt_tan hC.ne') hd
  have hat := HasDerivAt.comp (h₂ := Real.arctan) φ (Real.hasDerivAt_arctan _) (ht.const_mul c)
  refine (hat.const_mul (2 / s)).congr_deriv ?_
  simp only [Function.comp_apply]
  have hpy := Real.sin_sq_add_cos_sq (φ / 2)
  have hcos : Real.cos φ = Real.cos (φ / 2) ^ 2 - Real.sin (φ / 2) ^ 2 := by
    have h2 := Real.cos_two_mul (φ / 2)
    rw [show 2 * (φ / 2) = φ by ring] at h2
    linarith
  rw [Real.tan_eq_sin_div_cos, hcos, hc]
  have hD : 0 < 1 + ε * (Real.cos (φ / 2) ^ 2 - Real.sin (φ / 2) ^ 2) := by
    rw [← hcos]
    exact one_add_mul_cos_pos hε₀ hε₁ φ
  field_simp
  linear_combination (-(1 + ε)) * hpy + (-(Real.sin (φ / 2) ^ 2)) * hs2

/-- `(ε sin φ/(1 + ε cos φ))′ = 1/(1 + ε cos φ) − (1 − ε²)/(1 + ε cos φ)²`. -/
theorem hasDerivAt_sin_div (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) (φ : ℝ) :
    HasDerivAt (fun φ => ε * Real.sin φ / (1 + ε * Real.cos φ))
      ((1 + ε * Real.cos φ)⁻¹ - (1 - ε ^ 2) * ((1 + ε * Real.cos φ) ^ 2)⁻¹) φ := by
  have hD := one_add_mul_cos_pos hε₀ hε₁ φ
  have h1 := ((Real.hasDerivAt_sin φ).const_mul ε).div
    (((Real.hasDerivAt_cos φ).const_mul ε).const_add 1) hD.ne'
  refine h1.congr_deriv ?_
  have h := Real.sin_sq_add_cos_sq φ
  field_simp
  linear_combination ε ^ 2 * h

theorem tendsto_half_nhdsLT_pi :
    Tendsto (fun φ : ℝ => φ / 2) (𝓝[<] π) (𝓝[<] (π / 2)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    ((continuous_id.div_const 2).tendsto' π (π / 2) rfl |>.mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [self_mem_nhdsWithin] with φ hφ
  exact mem_Iio.mpr (by linarith [mem_Iio.mp hφ])

theorem tendsto_half_nhdsGT_neg_pi :
    Tendsto (fun φ : ℝ => φ / 2) (𝓝[>] (-π)) (𝓝[>] (-(π / 2))) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    ((continuous_id.div_const 2).tendsto' (-π) (-(π / 2)) (by simp; ring)
      |>.mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [self_mem_nhdsWithin] with φ hφ
  exact mem_Ioi.mpr (by linarith [mem_Ioi.mp hφ])

/-- `∫₀^{2π} dφ/(1 + ε cos φ)² = 2π/(1 − ε²)^{3/2}`. -/
theorem integral_inv_one_add_mul_cos_sq (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) :
    ∫ φ in (0 : ℝ)..2 * π, ((1 + ε * Real.cos φ) ^ 2)⁻¹ =
      2 * π / ((1 - ε ^ 2) * √(1 - ε ^ 2)) := by
  set s := √(1 - ε ^ 2) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by nlinarith)
  have hq : 0 < 1 - ε ^ 2 := by nlinarith
  have hε1 : 0 < 1 + ε := by linarith
  set G : ℝ → ℝ := fun φ => (1 - ε ^ 2)⁻¹ * (2 / s * Real.arctan (s / (1 + ε) * Real.tan (φ / 2)) -
    ε * Real.sin φ / (1 + ε * Real.cos φ)) with hG
  have hderiv : ∀ φ ∈ Ioo (-π) π, HasDerivAt G (((1 + ε * Real.cos φ) ^ 2)⁻¹) φ := by
    intro φ hφ
    have h := ((hasDerivAt_arctan_tan_half hε₀ hε₁ hφ).sub
      (hasDerivAt_sin_div hε₀ hε₁ φ)).const_mul (1 - ε ^ 2)⁻¹
    refine h.congr_deriv ?_
    field_simp
    ring
  have hcont : Continuous fun φ : ℝ => ((1 + ε * Real.cos φ) ^ 2)⁻¹ :=
    ((continuous_const.add (continuous_const.mul Real.continuous_cos)).pow 2).inv₀
      fun φ => pow_ne_zero 2 (one_add_mul_cos_pos hε₀ hε₁ φ).ne'
  have hQ : Continuous fun φ : ℝ => ε * Real.sin φ / (1 + ε * Real.cos φ) :=
    (continuous_const.mul Real.continuous_sin).div
      (continuous_const.add (continuous_const.mul Real.continuous_cos))
      fun φ => (one_add_mul_cos_pos hε₀ hε₁ φ).ne'
  have hc0 : 0 < s / (1 + ε) := div_pos hs0 hε1
  have hb : Tendsto G (𝓝[<] π) (𝓝 ((1 - ε ^ 2)⁻¹ * (2 / s * (π / 2) - 0))) := by
    have h1 : Tendsto (fun φ : ℝ => Real.arctan (s / (1 + ε) * Real.tan (φ / 2))) (𝓝[<] π)
        (𝓝 (π / 2)) :=
      (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
        ((Real.tendsto_tan_pi_div_two.comp tendsto_half_nhdsLT_pi).const_mul_atTop hc0)
    have h2 : Tendsto (fun φ : ℝ => ε * Real.sin φ / (1 + ε * Real.cos φ)) (𝓝[<] π) (𝓝 0) := by
      have := (hQ.tendsto π).mono_left (nhdsWithin_le_nhds (s := Iio π))
      simpa using this
    exact ((h1.const_mul (2 / s)).sub h2).const_mul _
  have ha : Tendsto G (𝓝[>] (-π)) (𝓝 ((1 - ε ^ 2)⁻¹ * (2 / s * (-(π / 2)) - 0))) := by
    have h1 : Tendsto (fun φ : ℝ => Real.arctan (s / (1 + ε) * Real.tan (φ / 2))) (𝓝[>] (-π))
        (𝓝 (-(π / 2))) :=
      (Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp
        ((Real.tendsto_tan_neg_pi_div_two.comp tendsto_half_nhdsGT_neg_pi).const_mul_atBot hc0)
    have h2 : Tendsto (fun φ : ℝ => ε * Real.sin φ / (1 + ε * Real.cos φ)) (𝓝[>] (-π))
        (𝓝 0) := by
      have := (hQ.tendsto (-π)).mono_left (nhdsWithin_le_nhds (s := Ioi (-π)))
      simpa using this
    exact ((h1.const_mul (2 / s)).sub h2).const_mul _
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (by linarith [Real.pi_pos])
    hderiv (hcont.intervalIntegrable _ _) ha hb
  have hper : Function.Periodic (fun φ : ℝ => ((1 + ε * Real.cos φ) ^ 2)⁻¹) (2 * π) :=
    fun φ => by simp only [Real.cos_add_two_pi]
  have hshift := hper.intervalIntegral_add_eq (-π) 0
  rw [show -π + 2 * π = π by ring, zero_add] at hshift
  rw [← hshift, hI]
  field_simp
  ring

/-! ### The Kepler ellipse -/

variable {k ℓ : ℝ}

/-- The field `φ̇ = (k²/ℓ³)(1 + ε cos φ)²` of the polar angle on the Kepler ellipse: it is `ℓ/r²`
for `r = p/(1 + ε cos φ)` and `p = ℓ²/k`. -/
def angleField (k ℓ ε φ : ℝ) : ℝ := k ^ 2 / ℓ ^ 3 * (1 + ε * Real.cos φ) ^ 2

/-- The polar angle on the Kepler ellipse, with the perihelion on the first axis at `t = 0`. -/
def keplerAngle (k ℓ ε t : ℝ) : ℝ := SmoothGeometry.NonlinearODE.flow (angleField k ℓ ε) (t, 0)

/-- The parameter `p = ℓ²/k` of the ellipse. -/
def semiLatus (k ℓ : ℝ) : ℝ := ℓ ^ 2 / k

/-- The radius `r = p/(1 + ε cos φ)`. -/
def keplerRadius (k ℓ ε t : ℝ) : ℝ := semiLatus k ℓ / (1 + ε * Real.cos (keplerAngle k ℓ ε t))

/-- The position `r (cos φ, sin φ)`. -/
def keplerPosition (k ℓ ε t : ℝ) : ℝ × ℝ :=
  (keplerRadius k ℓ ε t * Real.cos (keplerAngle k ℓ ε t),
    keplerRadius k ℓ ε t * Real.sin (keplerAngle k ℓ ε t))

/-- The velocity `(k/ℓ)(−sin φ, ε + cos φ)`. -/
def keplerVelocity (k ℓ ε t : ℝ) : ℝ × ℝ :=
  (-(k / ℓ) * Real.sin (keplerAngle k ℓ ε t), k / ℓ * (ε + Real.cos (keplerAngle k ℓ ε t)))

/-- The acceleration `−(k/r²)(cos φ, sin φ)`. -/
def keplerAcceleration (k ℓ ε t : ℝ) : ℝ × ℝ :=
  (-(k / keplerRadius k ℓ ε t ^ 2) * Real.cos (keplerAngle k ℓ ε t),
    -(k / keplerRadius k ℓ ε t ^ 2) * Real.sin (keplerAngle k ℓ ε t))

/-- The period `T = ∫₀^{2π} dφ/φ̇`, the time in which the angle advances by `2π`. -/
def keplerPeriod (k ℓ ε : ℝ) : ℝ :=
  SmoothGeometry.NonlinearODE.scalarTime (angleField k ℓ ε) (2 * π)

theorem angleField_pos (hk : 0 < k) (hℓ : 0 < ℓ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) (φ : ℝ) :
    0 < angleField k ℓ ε φ := by
  have := one_add_mul_cos_pos hε₀ hε₁ φ
  rw [angleField]
  positivity

theorem contDiff_angleField (k ℓ ε : ℝ) : ContDiff ℝ ∞ (angleField k ℓ ε) := by
  unfold angleField
  exact contDiff_const.mul ((contDiff_const.add (contDiff_const.mul Real.contDiff_cos)).pow 2)

theorem abs_angleField_le (hk : 0 < k) (hℓ : 0 < ℓ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) (φ : ℝ) :
    |angleField k ℓ ε φ| ≤ k ^ 2 / ℓ ^ 3 * (1 + ε) ^ 2 := by
  have h0 := one_add_mul_cos_pos hε₀ hε₁ φ
  have h1 : 1 + ε * Real.cos φ ≤ 1 + ε := by
    have := mul_le_mul_of_nonneg_left (Real.cos_le_one φ) hε₀
    linarith
  rw [abs_of_pos (angleField_pos hk hℓ hε₀ hε₁ φ), angleField]
  gcongr

theorem angleField_add_two_pi (k ℓ ε φ : ℝ) :
    angleField k ℓ ε (φ + 2 * π) = angleField k ℓ ε φ := by
  rw [angleField, angleField, Real.cos_add_two_pi]

theorem hasDerivAt_keplerAngle (hk : 0 < k) (hℓ : 0 < ℓ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) (t : ℝ) :
    HasDerivAt (keplerAngle k ℓ ε) (angleField k ℓ ε (keplerAngle k ℓ ε t)) t :=
  SmoothGeometry.NonlinearODE.hasDerivAt_flow_zero (contDiff_angleField k ℓ ε)
    (abs_angleField_le hk hℓ hε₀ hε₁) t

theorem continuous_keplerAngle (hk : 0 < k) (hℓ : 0 < ℓ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) :
    Continuous (keplerAngle k ℓ ε) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_keplerAngle hk hℓ hε₀ hε₁ t).continuousAt

theorem keplerAngle_zero (k ℓ ε : ℝ) : keplerAngle k ℓ ε 0 = 0 :=
  SmoothGeometry.NonlinearODE.flow_zero _ _

/-- The angle advances by `2π` in each period. -/
theorem keplerAngle_add_period (hk : 0 < k) (hℓ : 0 < ℓ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) (t : ℝ) :
    keplerAngle k ℓ ε (t + keplerPeriod k ℓ ε) = keplerAngle k ℓ ε t + 2 * π :=
  SmoothGeometry.NonlinearODE.flow_add_scalarTime_of_periodic (contDiff_angleField k ℓ ε)
    (angleField_pos hk hℓ hε₀ hε₁) (abs_angleField_le hk hℓ hε₀ hε₁)
    (angleField_add_two_pi k ℓ ε) t

theorem keplerAngle_keplerPeriod (hk : 0 < k) (hℓ : 0 < ℓ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) :
    keplerAngle k ℓ ε (keplerPeriod k ℓ ε) = 2 * π := by
  have h := keplerAngle_add_period hk hℓ hε₀ hε₁ 0
  rwa [zero_add, keplerAngle_zero, zero_add] at h

/-- The period of the ellipse, `T = 2πℓ³/(k²(1 − ε²)^{3/2})`. -/
theorem keplerPeriod_eq (hk : 0 < k) (hℓ : 0 < ℓ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) :
    keplerPeriod k ℓ ε = 2 * π * ℓ ^ 3 / (k ^ 2 * ((1 - ε ^ 2) * √(1 - ε ^ 2))) := by
  have e : (fun φ => (angleField k ℓ ε φ)⁻¹) =
      fun φ => ℓ ^ 3 / k ^ 2 * ((1 + ε * Real.cos φ) ^ 2)⁻¹ := by
    funext φ
    rw [angleField, mul_inv, inv_div]
  rw [keplerPeriod, SmoothGeometry.NonlinearODE.scalarTime, e, intervalIntegral.integral_const_mul,
    integral_inv_one_add_mul_cos_sq hε₀ hε₁]
  field_simp

/-- Kepler's third law (*Mechanics* (15.8)): `T = 2π √(A³/k)` with the semi-major axis
`A = p/(1 − ε²)`. -/
theorem keplerPeriod_eq_semiMajor (hk : 0 < k) (hℓ : 0 < ℓ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) :
    keplerPeriod k ℓ ε = 2 * π * √((semiLatus k ℓ / (1 - ε ^ 2)) ^ 3 / k) := by
  have hq : 0 < 1 - ε ^ 2 := by nlinarith
  have hs0 : 0 < √(1 - ε ^ 2) := Real.sqrt_pos.mpr hq
  have hs2 : √(1 - ε ^ 2) ^ 2 = 1 - ε ^ 2 := Real.sq_sqrt hq.le
  have e : (semiLatus k ℓ / (1 - ε ^ 2)) ^ 3 / k =
      (ℓ ^ 3 / (k ^ 2 * ((1 - ε ^ 2) * √(1 - ε ^ 2)))) ^ 2 := by
    rw [semiLatus]
    field_simp
    exact hs2
  rw [keplerPeriod_eq hk hℓ hε₀ hε₁, e, Real.sqrt_sq (by positivity)]
  ring

theorem hasDerivAt_keplerRadius (hk : 0 < k) (hℓ : 0 < ℓ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) (t : ℝ) :
    HasDerivAt (keplerRadius k ℓ ε) (k / ℓ * ε * Real.sin (keplerAngle k ℓ ε t)) t := by
  have hθ := hasDerivAt_keplerAngle hk hℓ hε₀ hε₁ t
  have hD := one_add_mul_cos_pos hε₀ hε₁ (keplerAngle k ℓ ε t)
  have hc := (Real.hasDerivAt_cos (keplerAngle k ℓ ε t)).comp t hθ
  have h1 := (hasDerivAt_const t (semiLatus k ℓ)).div ((hc.const_mul ε).const_add 1) hD.ne'
  refine h1.congr_deriv ?_
  simp only [Function.comp_apply]
  rw [semiLatus, angleField]
  have := hk.ne'
  have := hℓ.ne'
  field_simp
  ring

/-- The velocity of the ellipse. -/
theorem hasDerivAt_keplerPosition (hk : 0 < k) (hℓ : 0 < ℓ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1)
    (t : ℝ) : HasDerivAt (keplerPosition k ℓ ε) (keplerVelocity k ℓ ε t) t := by
  have hθ := hasDerivAt_keplerAngle hk hℓ hε₀ hε₁ t
  have hr := hasDerivAt_keplerRadius hk hℓ hε₀ hε₁ t
  have hD := one_add_mul_cos_pos hε₀ hε₁ (keplerAngle k ℓ ε t)
  have hc := (Real.hasDerivAt_cos (keplerAngle k ℓ ε t)).comp t hθ
  have hs := (Real.hasDerivAt_sin (keplerAngle k ℓ ε t)).comp t hθ
  have h := (hr.fun_mul hc).prodMk (hr.fun_mul hs)
  refine h.congr_deriv (Prod.ext ?_ ?_)
  · simp only [keplerVelocity, keplerRadius, semiLatus, angleField, Function.comp_apply]
    have := hk.ne'
    have := hℓ.ne'
    field_simp
    ring
  · simp only [keplerVelocity, keplerRadius, semiLatus, angleField, Function.comp_apply]
    have := hk.ne'
    have := hℓ.ne'
    have h := Real.sin_sq_add_cos_sq (keplerAngle k ℓ ε t)
    field_simp
    linear_combination ε * h

/-- Newton's equation of the ellipse: the derivative of the velocity is the acceleration
`−k 𝐫/r³` of the attraction `α/r²` with `k = α/m` (`keplerAcceleration_eq_smul`). -/
theorem hasDerivAt_keplerVelocity (hk : 0 < k) (hℓ : 0 < ℓ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1)
    (t : ℝ) : HasDerivAt (keplerVelocity k ℓ ε) (keplerAcceleration k ℓ ε t) t := by
  have hθ := hasDerivAt_keplerAngle hk hℓ hε₀ hε₁ t
  have hD := one_add_mul_cos_pos hε₀ hε₁ (keplerAngle k ℓ ε t)
  have hc := (Real.hasDerivAt_cos (keplerAngle k ℓ ε t)).comp t hθ
  have hs := (Real.hasDerivAt_sin (keplerAngle k ℓ ε t)).comp t hθ
  have h := (hs.const_mul (-(k / ℓ))).prodMk ((hc.const_add ε).const_mul (k / ℓ))
  refine h.congr_deriv (Prod.ext ?_ ?_)
  · simp only [keplerAcceleration, keplerRadius, semiLatus, angleField]
    have := hk.ne'
    have := hℓ.ne'
    field_simp
  · simp only [keplerAcceleration, keplerRadius, semiLatus, angleField]
    have := hk.ne'
    have := hℓ.ne'
    field_simp

theorem keplerRadius_pos (hk : 0 < k) (hℓ : 0 < ℓ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) (t : ℝ) :
    0 < keplerRadius k ℓ ε t := by
  have := one_add_mul_cos_pos hε₀ hε₁ (keplerAngle k ℓ ε t)
  rw [keplerRadius, semiLatus]
  positivity

/-- The acceleration is `−k 𝐫/r³`. -/
theorem keplerAcceleration_eq_smul (hk : 0 < k) (hℓ : 0 < ℓ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1)
    (t : ℝ) : keplerAcceleration k ℓ ε t =
      (-(k / keplerRadius k ℓ ε t ^ 3)) • keplerPosition k ℓ ε t := by
  have hr := (keplerRadius_pos hk hℓ hε₀ hε₁ t).ne'
  simp only [keplerAcceleration, keplerPosition, Prod.smul_mk, smul_eq_mul]
  refine Prod.ext ?_ ?_ <;> (simp only; field_simp)

/-- The moment of the velocity is `ℓ` (Kepler's second law). -/
theorem keplerPosition_cross_velocity (hk : 0 < k) (hℓ : 0 < ℓ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1)
    (t : ℝ) : (keplerPosition k ℓ ε t).1 * (keplerVelocity k ℓ ε t).2 -
      (keplerPosition k ℓ ε t).2 * (keplerVelocity k ℓ ε t).1 = ℓ := by
  have hD := one_add_mul_cos_pos hε₀ hε₁ (keplerAngle k ℓ ε t)
  have h := Real.sin_sq_add_cos_sq (keplerAngle k ℓ ε t)
  simp only [keplerPosition, keplerVelocity, keplerRadius, semiLatus]
  have := hk.ne'
  have := hℓ.ne'
  field_simp
  linear_combination h

/-- The acceleration has the period `T`. -/
theorem keplerAcceleration_add_period (hk : 0 < k) (hℓ : 0 < ℓ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1)
    (t : ℝ) : keplerAcceleration k ℓ ε (t + keplerPeriod k ℓ ε) = keplerAcceleration k ℓ ε t := by
  simp only [keplerAcceleration, keplerRadius, keplerAngle_add_period hk hℓ hε₀ hε₁,
    Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem continuous_keplerAcceleration (hk : 0 < k) (hℓ : 0 < ℓ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) :
    Continuous (keplerAcceleration k ℓ ε) := by
  have hθ := continuous_keplerAngle hk hℓ hε₀ hε₁
  have hr : Continuous (keplerRadius k ℓ ε) :=
    continuous_const.div (continuous_const.add (continuous_const.mul (Real.continuous_cos.comp hθ)))
      fun t => (one_add_mul_cos_pos hε₀ hε₁ _).ne'
  have hq : Continuous fun t => -(k / keplerRadius k ℓ ε t ^ 2) :=
    (continuous_const.div (hr.pow 2) fun t =>
      pow_ne_zero 2 (keplerRadius_pos hk hℓ hε₀ hε₁ t).ne').neg
  exact (hq.mul (Real.continuous_cos.comp hθ)).prodMk (hq.mul (Real.continuous_sin.comp hθ))

/-! ### The mean power on the ellipse -/

/-- `∫ (1 + ε cos φ)² dφ`, divided by `ℓ⁵/k²`: the primitive of `(1 + ε cos φ)⁴/p⁴` in time. -/
def meanPrimitive (k ℓ ε φ : ℝ) : ℝ :=
  k ^ 2 / ℓ ^ 5 * (φ + 2 * ε * Real.sin φ + ε ^ 2 * (φ + Real.sin φ * Real.cos φ) / 2)

theorem dipolePower_smul_keplerAcceleration (hk : 0 < k) (hℓ : 0 < ℓ) (hε₀ : 0 ≤ ε)
    (hε₁ : ε < 1) (e t : ℝ) :
    dipolePower (e • keplerAcceleration k ℓ ε t) =
      2 / 3 * (4 * π)⁻¹ * e ^ 2 * k ^ 2 *
        (k ^ 4 / ℓ ^ 8 * (1 + ε * Real.cos (keplerAngle k ℓ ε t)) ^ 4) := by
  have hD := one_add_mul_cos_pos hε₀ hε₁ (keplerAngle k ℓ ε t)
  have h := Real.sin_sq_add_cos_sq (keplerAngle k ℓ ε t)
  simp only [dipolePower, keplerAcceleration, Prod.smul_mk, smul_eq_mul]
  have e1 : (e * (-(k / keplerRadius k ℓ ε t ^ 2) * Real.cos (keplerAngle k ℓ ε t))) ^ 2 +
      (e * (-(k / keplerRadius k ℓ ε t ^ 2) * Real.sin (keplerAngle k ℓ ε t))) ^ 2 =
        (e * (k / keplerRadius k ℓ ε t ^ 2)) ^ 2 := by
    linear_combination (e * (k / keplerRadius k ℓ ε t ^ 2)) ^ 2 * h
  rw [e1, keplerRadius, semiLatus]
  have := hk.ne'
  have := hℓ.ne'
  field_simp

theorem hasDerivAt_meanPrimitive (hk : 0 < k) (hℓ : 0 < ℓ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1)
    (t : ℝ) : HasDerivAt (fun t => meanPrimitive k ℓ ε (keplerAngle k ℓ ε t))
      (k ^ 4 / ℓ ^ 8 * (1 + ε * Real.cos (keplerAngle k ℓ ε t)) ^ 4) t := by
  have hθ := hasDerivAt_keplerAngle hk hℓ hε₀ hε₁ t
  set φ := keplerAngle k ℓ ε t
  have hs := Real.hasDerivAt_sin φ
  have hc := Real.hasDerivAt_cos φ
  have h1 : HasDerivAt (meanPrimitive k ℓ ε)
      (k ^ 2 / ℓ ^ 5 * (1 + 2 * ε * Real.cos φ +
        ε ^ 2 * (1 + (Real.cos φ * Real.cos φ + Real.sin φ * -Real.sin φ)) / 2)) φ :=
    ((((hasDerivAt_id φ).add (hs.const_mul (2 * ε))).add
      ((((hasDerivAt_id φ).add (hs.mul hc)).const_mul (ε ^ 2)).div_const 2)).const_mul
        (k ^ 2 / ℓ ^ 5))
  refine (h1.comp t hθ).congr_deriv ?_
  have h := Real.sin_sq_add_cos_sq φ
  have hD2 : 1 + 2 * ε * Real.cos φ +
      ε ^ 2 * (1 + (Real.cos φ * Real.cos φ + Real.sin φ * -Real.sin φ)) / 2 =
        (1 + ε * Real.cos φ) ^ 2 := by
    linear_combination (-(ε ^ 2) / 2) * h
  rw [hD2, angleField]
  have := hℓ.ne'
  field_simp

/-- A problem of Landau–Lifshitz §70: the mean power radiated on the Kepler ellipse is
`(2/3)(1/4π) e² k⁶ (2 + ε²)(1 − ε²)^{3/2}/(2ℓ⁸)`; with `ℓ² = kA(1 − ε²)` it is
`(2/3)(1/4π) e² k² (2 + ε²)/(2A⁴(1 − ε²)^{5/2})` (`average_dipolePower_kepler_semiMajor`). -/
theorem average_dipolePower_kepler (e : ℝ) (hk : 0 < k) (hℓ : 0 < ℓ) (hε₀ : 0 ≤ ε)
    (hε₁ : ε < 1) :
    (keplerPeriod k ℓ ε)⁻¹ *
        ∫ t in (0 : ℝ)..keplerPeriod k ℓ ε, dipolePower (e • keplerAcceleration k ℓ ε t) =
      2 / 3 * (4 * π)⁻¹ * e ^ 2 * k ^ 6 * (2 + ε ^ 2) * ((1 - ε ^ 2) * √(1 - ε ^ 2)) /
        (2 * ℓ ^ 8) := by
  have hcont : Continuous fun t =>
      k ^ 4 / ℓ ^ 8 * (1 + ε * Real.cos (keplerAngle k ℓ ε t)) ^ 4 :=
    continuous_const.mul ((continuous_const.add (continuous_const.mul
      (Real.continuous_cos.comp (continuous_keplerAngle hk hℓ hε₀ hε₁)))).pow 4)
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_meanPrimitive hk hℓ hε₀ hε₁ t) (hcont.intervalIntegrable 0
      (keplerPeriod k ℓ ε))
  simp only [dipolePower_smul_keplerAcceleration hk hℓ hε₀ hε₁]
  rw [intervalIntegral.integral_const_mul, hI, keplerAngle_keplerPeriod hk hℓ hε₀ hε₁,
    keplerAngle_zero, keplerPeriod_eq hk hℓ hε₀ hε₁]
  simp only [meanPrimitive, Real.sin_two_pi, Real.cos_two_pi, Real.sin_zero, Real.cos_zero]
  have hq : 0 < 1 - ε ^ 2 := by nlinarith
  have hs0 : 0 < √(1 - ε ^ 2) := Real.sqrt_pos.mpr hq
  have := hk.ne'
  have := hℓ.ne'
  field_simp
  ring

/-- The mean power in terms of the semi-major axis `A = p/(1 − ε²)`. -/
theorem average_dipolePower_kepler_semiMajor (e : ℝ) (hk : 0 < k) (hℓ : 0 < ℓ) (hε₀ : 0 ≤ ε)
    (hε₁ : ε < 1) :
    (keplerPeriod k ℓ ε)⁻¹ *
        ∫ t in (0 : ℝ)..keplerPeriod k ℓ ε, dipolePower (e • keplerAcceleration k ℓ ε t) =
      2 / 3 * (4 * π)⁻¹ * e ^ 2 * k ^ 2 * (2 + ε ^ 2) /
        (2 * (semiLatus k ℓ / (1 - ε ^ 2)) ^ 4 * ((1 - ε ^ 2) ^ 2 * √(1 - ε ^ 2))) := by
  rw [average_dipolePower_kepler e hk hℓ hε₀ hε₁, semiLatus]
  have hq : 0 < 1 - ε ^ 2 := by nlinarith
  have hs0 : 0 < √(1 - ε ^ 2) := Real.sqrt_pos.mpr hq
  have hs2 : √(1 - ε ^ 2) ^ 2 = 1 - ε ^ 2 := Real.sq_sqrt hq.le
  have := hk.ne'
  have := hℓ.ne'
  have := hq.ne'
  field_simp
  rw [show √(1 - ε ^ 2) ^ 2 = 1 - ε ^ 2 from hs2]

/-! ### The harmonics of the elliptic motion -/

/-- The Fourier coefficient `c_n = (1/T) ∫₀ᵀ e^{−2πint/T} w(t) dt` of a function of the period
`T`. -/
def harmonicCoeff (w : ℝ → ℝ) (T : ℝ) (n : ℤ) : ℂ :=
  (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T, Complex.exp (-(2 * π * Complex.I * n * t / T)) * (w t : ℂ)

theorem harmonicCoeff_eq_fourierCoeffOn (w : ℝ → ℝ) {T : ℝ} (hT : 0 < T) (n : ℤ) :
    harmonicCoeff w T n = fourierCoeffOn hT (fun t => (w t : ℂ)) n := by
  rw [fourierCoeffOn_eq_integral, harmonicCoeff]
  simp only [fourier_coe_apply, smul_eq_mul, sub_zero]
  rw [Complex.real_smul]
  push_cast
  congr 1
  · ring
  · refine intervalIntegral.integral_congr fun t _ => ?_
    congr 2
    ring

/-- Parseval's identity on the ellipse (Landau–Lifshitz §70): `𝐝̈ = e 𝐫̈` has the period `T`, and
the mean power is the sum `Σ_n (2/3)(1/4π)|c_n|²` over the harmonics `n ω₀`, `ω₀ = 2π/T`, of the
components of `𝐝̈`. -/
theorem harmonic_decomposition (e : ℝ) (hk : 0 < k) (hℓ : 0 < ℓ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) :
    HasSum (fun n : ℤ => 2 / 3 * (4 * π)⁻¹ *
        (‖harmonicCoeff (fun t => (e • keplerAcceleration k ℓ ε t).1) (keplerPeriod k ℓ ε) n‖ ^ 2 +
          ‖harmonicCoeff (fun t => (e • keplerAcceleration k ℓ ε t).2) (keplerPeriod k ℓ ε) n‖ ^ 2))
      ((keplerPeriod k ℓ ε)⁻¹ *
        ∫ t in (0 : ℝ)..keplerPeriod k ℓ ε, dipolePower (e • keplerAcceleration k ℓ ε t)) := by
  have hT : 0 < keplerPeriod k ℓ ε := by
    rw [keplerPeriod_eq hk hℓ hε₀ hε₁]
    have hq : 0 < 1 - ε ^ 2 := by nlinarith
    have hs0 : 0 < √(1 - ε ^ 2) := Real.sqrt_pos.mpr hq
    positivity
  have hw := (continuous_keplerAcceleration hk hℓ hε₀ hε₁).const_smul e
  have hw1 : Continuous fun t => (e • keplerAcceleration k ℓ ε t).1 := continuous_fst.comp hw
  have hw2 : Continuous fun t => (e • keplerAcceleration k ℓ ε t).2 := continuous_snd.comp hw
  have hL2 : ∀ {f : ℝ → ℝ}, Continuous f →
      MemLp (fun t => (f t : ℂ)) 2 (volume.restrict (Ioc 0 (keplerPeriod k ℓ ε))) := by
    intro f hf
    have hfc : Continuous fun t => (f t : ℂ) := Complex.continuous_ofReal.comp hf
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (hfc.continuousOn (s := Icc 0 (keplerPeriod k ℓ ε)))
    refine MemLp.of_bound hfc.aestronglyMeasurable C ?_
    exact (ae_restrict_iff' measurableSet_Ioc).mpr
      (Eventually.of_forall fun t ht => hC t (Ioc_subset_Icc_self ht))
  have h1 := hasSum_sq_fourierCoeffOn hT (hL2 hw1)
  have h2 := hasSum_sq_fourierCoeffOn hT (hL2 hw2)
  simp only [← harmonicCoeff_eq_fourierCoeffOn _ hT] at h1 h2
  have h := (h1.add h2).mul_left (2 / 3 * (4 * π)⁻¹)
  convert h using 1
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, sub_zero, smul_eq_mul, dipolePower]
  have i1 : IntervalIntegrable (fun t => (e • keplerAcceleration k ℓ ε t).1 ^ 2) volume 0
      (keplerPeriod k ℓ ε) := (hw1.pow 2).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun t => (e • keplerAcceleration k ℓ ε t).2 ^ 2) volume 0
      (keplerPeriod k ℓ ε) := (hw2.pow 2).intervalIntegrable _ _
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add i1 i2]
  ring

/-- The sum over the harmonics in closed form. -/
theorem tsum_harmonic (e : ℝ) (hk : 0 < k) (hℓ : 0 < ℓ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) :
    ∑' n : ℤ, 2 / 3 * (4 * π)⁻¹ *
        (‖harmonicCoeff (fun t => (e • keplerAcceleration k ℓ ε t).1) (keplerPeriod k ℓ ε) n‖ ^ 2 +
          ‖harmonicCoeff (fun t => (e • keplerAcceleration k ℓ ε t).2)
            (keplerPeriod k ℓ ε) n‖ ^ 2) =
      2 / 3 * (4 * π)⁻¹ * e ^ 2 * k ^ 6 * (2 + ε ^ 2) * ((1 - ε ^ 2) * √(1 - ε ^ 2)) /
        (2 * ℓ ^ 8) :=
  (harmonic_decomposition e hk hℓ hε₀ hε₁).tsum_eq.trans
    (average_dipolePower_kepler e hk hℓ hε₀ hε₁)

end ProjectAinos.Electrodynamics.Radiation.CoulombRadiation
