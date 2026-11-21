/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Mechanics.Scattering.Coulomb
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-!
# Dipole radiation during collisions

Landau–Lifshitz, *The Classical Theory of Fields*, §68. The units have `c = 1` and `div E = k⁰`,
so that the power (67.8) radiated by a dipole is `(2/3)(1/4π)|𝐝̈|² = |𝐝̈|²/(6π)`
(`dipolePower`; `Radiation.dipolePower_sub_le` proves it for a slow localized source). The
emission during a collision is this power along a given orbit: the statements of this file are
about the dipole `𝐝 = e 𝐫` of the relative motion of the Coulomb scattering of
`Mechanics.Scattering.Coulomb`, with the speed `v∞` at infinity, the impact parameter `ρ` and
`a = α/m v∞²`. For two charges `e₁, e₂` of masses `m₁, m₂` the dipole in the frame of the centre
of mass is `μ (e₁/m₁ − e₂/m₂) 𝐫` with the reduced mass `μ` (`dipole_eq_reducedCharge_smul`), so
that `e` is `reducedCharge m₁ m₂ e₁ e₂`.

* `acceleration a ρ v∞ t = (v∞² a/r²) 𝐧` is the relative acceleration `α 𝐧/m r²`
  (`hasDerivAt_velocity_coulomb`), and `dipolePower_smul_acceleration`: the power is
  `(2/3)(1/4π) e² (v∞² a/r²)²`.
* `integrable_dipoleAcceleration_coulomb`: `𝐝̈ = e 𝐫̈` is integrable and square integrable on the
  line. Since `φ̇ = ℓ/r²` with `ℓ = ρ v∞`, `∫ dt/r² = 2φ₀/ℓ` is the total angle described
  (`integral_inv_orbitRadius_sq`), with `φ₀ = arccos (a/√(a² + ρ²))` (`asymptoteAngle`).
* `integral_dipolePower_eq`: the energy radiated in the collision (`totalEnergy`) is the radial
  quadrature `2 ∫_{r₀}^∞ P(r) dr/√(v∞²(1 − 2a/r − ρ²/r²))` over the two branches of the orbit,
  by `dt = dr/ṙ` (`integral_Ioi_div_sqrt_speedSq`).
* `integral_norm_sq_fourier` (Plancherel): for `f ∈ L¹ ∩ L²`, `∫ |𝓕f|² = ∫ |f|²` with the
  Fourier integral `𝓕f(ν) = ∫ e^{−2πiνt} f(t) dt`. `spectral_eq`, `spectral_eq_coulomb`: the
  energy is `∫ dE_ν` over all frequencies `ν ∈ ℝ`, with the spectral density
  `(2/3)(1/4π)|𝓕𝐝̈(ν)|²` (`spectralDensity`); the density at `−ν` is that at `ν`, so
  `dE_ν` over `ν > 0` is twice it.
* `effectiveRadiation e a v∞ = ∫ ΔE(ρ) 2πρ dρ`, the effective radiation of a beam, is a
  Bochner integral: it is the effective radiation when `IsEffectiveFinite e a v∞` holds. It does
  for a repulsive field (`CoulombRadiation.effectiveRadiation_repulsive`).

The plane of the orbit carries the Euclidean square `w₁² + w₂²`; the norm of `ℝ × ℝ` is the
maximum norm and is used only for integrability.
-/

@[expose] public section
noncomputable section

open Set Filter MeasureTheory
open scoped Real Topology FourierTransform SchwartzMap ContDiff

namespace ProjectAinos.Electrodynamics.Radiation.Collision

open Mechanics.Scattering Mechanics.Scattering.Coulomb

/-! ### The power of a dipole -/

/-- The power `(2/3)(1/4π)|𝐝̈|² = |𝐝̈|²/(6π)` (Landau–Lifshitz (67.8)) radiated by a dipole whose
second derivative is the plane vector `w`, with the Euclidean square `w₁² + w₂²`. -/
def dipolePower (w : ℝ × ℝ) : ℝ := 2 / 3 * (4 * π)⁻¹ * (w.1 ^ 2 + w.2 ^ 2)

theorem dipolePower_nonneg (w : ℝ × ℝ) : 0 ≤ dipolePower w := by
  rw [dipolePower]
  positivity

/-- The coefficient `μ (e₁/m₁ − e₂/m₂)`, `μ = m₁m₂/(m₁ + m₂)`, of the dipole moment of two
charges in the frame of their centre of mass (Landau–Lifshitz (70.1)). -/
def reducedCharge (m₁ m₂ e₁ e₂ : ℝ) : ℝ := m₁ * m₂ / (m₁ + m₂) * (e₁ / m₁ - e₂ / m₂)

/-- In the frame of the centre of mass, `𝐫₁ = m₂ 𝐫/(m₁ + m₂)` and `𝐫₂ = −m₁ 𝐫/(m₁ + m₂)`, and
the dipole moment `e₁𝐫₁ + e₂𝐫₂` is `μ (e₁/m₁ − e₂/m₂) 𝐫`. -/
theorem dipole_eq_reducedCharge_smul {m₁ m₂ : ℝ} (h₁ : m₁ ≠ 0) (h₂ : m₂ ≠ 0)
    (h : m₁ + m₂ ≠ 0) (e₁ e₂ : ℝ) (r : ℝ × ℝ) :
    e₁ • ((m₂ / (m₁ + m₂)) • r) + e₂ • ((-(m₁ / (m₁ + m₂))) • r) =
      reducedCharge m₁ m₂ e₁ e₂ • r := by
  rw [smul_smul, smul_smul, ← add_smul, reducedCharge]
  congr 1
  field_simp
  ring

/-! ### The Coulomb scattering orbit -/

variable {a ρ vinf : ℝ}

/-- The distance `r(t)` on the Coulomb scattering orbit, with the closest approach at `t = 0`. -/
def orbitRadius (a ρ vinf t : ℝ) : ℝ := radius (factor a ρ vinf) (closest a ρ) t

/-- The polar angle `φ(t)` on the Coulomb scattering orbit, counted from the direction of the
closest approach, for the angular momentum `m ρ v∞`. -/
def orbitAngle (a ρ vinf t : ℝ) : ℝ := angle (factor a ρ vinf) (closest a ρ) (ρ * vinf) t

/-- The angle `φ₀ = arccos (a/√(a² + ρ²))` between the direction of the closest approach and an
asymptote (Landau–Lifshitz (18.4)). -/
def asymptoteAngle (a ρ : ℝ) : ℝ := Real.arccos (a / hyp a ρ)

/-- The relative acceleration `(v∞² a/r²) 𝐧`, which is `α 𝐧/m r²` for `a = α/m v∞²`. -/
def acceleration (a ρ vinf t : ℝ) : ℝ × ℝ :=
  (vinf ^ 2 * a / orbitRadius a ρ vinf t ^ 2) •
    (Real.cos (orbitAngle a ρ vinf t), Real.sin (orbitAngle a ρ vinf t))

theorem closest_le_orbitRadius (a ρ vinf t : ℝ) : closest a ρ ≤ orbitRadius a ρ vinf t :=
  le_radius _ _ t

theorem orbitRadius_pos (hρ : 0 < ρ) (vinf t : ℝ) : 0 < orbitRadius a ρ vinf t :=
  (closest_pos a hρ).trans_le (closest_le_orbitRadius a ρ vinf t)

theorem orbitRadius_neg (hρ : 0 < ρ) (hv : 0 < vinf) (t : ℝ) :
    orbitRadius a ρ vinf (-t) = orbitRadius a ρ vinf t :=
  (isFactor a hρ hv).radius_neg t

theorem orbitAngle_neg (hρ : 0 < ρ) (hv : 0 < vinf) (t : ℝ) :
    orbitAngle a ρ vinf (-t) = -orbitAngle a ρ vinf t :=
  (isFactor a hρ hv).angle_neg _ t

theorem orbitAngle_zero (a ρ vinf : ℝ) : orbitAngle a ρ vinf 0 = 0 := angle_zero _ _ _

theorem continuous_orbitRadius (hρ : 0 < ρ) (hv : 0 < vinf) :
    Continuous (orbitRadius a ρ vinf) :=
  (isFactor a hρ hv).contDiff_radius.continuous

theorem hasDerivAt_orbitRadius (hρ : 0 < ρ) (hv : 0 < vinf) (t : ℝ) :
    HasDerivAt (orbitRadius a ρ vinf) (radialVelocity (factor a ρ vinf) (closest a ρ) t) t :=
  (isFactor a hρ hv).hasDerivAt_radius t

theorem hasDerivAt_orbitAngle (hρ : 0 < ρ) (hv : 0 < vinf) (t : ℝ) :
    HasDerivAt (orbitAngle a ρ vinf) (ρ * vinf / orbitRadius a ρ vinf t ^ 2) t :=
  (isFactor a hρ hv).hasDerivAt_angle (closest_pos a hρ) _ t

theorem continuous_orbitAngle (hρ : 0 < ρ) (hv : 0 < vinf) :
    Continuous (orbitAngle a ρ vinf) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_orbitAngle hρ hv t).continuousAt

theorem tendsto_orbitAngle_atTop (hρ : 0 < ρ) (hv : 0 < vinf) :
    Tendsto (orbitAngle a ρ vinf) atTop (𝓝 (asymptoteAngle a ρ)) :=
  Coulomb.tendsto_angle_atTop a hρ hv

theorem tendsto_orbitAngle_atBot (hρ : 0 < ρ) (hv : 0 < vinf) :
    Tendsto (orbitAngle a ρ vinf) atBot (𝓝 (-asymptoteAngle a ρ)) := by
  have h := ((tendsto_orbitAngle_atTop (a := a) hρ hv).comp tendsto_neg_atBot_atTop).neg
  refine h.congr fun t => ?_
  rw [Function.comp_apply, orbitAngle_neg hρ hv, neg_neg]

/-- Newton's equation: the derivative of the velocity of `Scattering.Coulomb` is
`acceleration`. -/
theorem hasDerivAt_velocity_coulomb (a : ℝ) (hρ : 0 < ρ) (hv : 0 < vinf) (t : ℝ) :
    HasDerivAt (velocity (factor a ρ vinf) (closest a ρ) (ρ * vinf)) (acceleration a ρ vinf t) t :=
  Coulomb.hasDerivAt_velocity a hρ hv t

theorem continuous_acceleration (hρ : 0 < ρ) (hv : 0 < vinf) :
    Continuous (acceleration a ρ vinf) := by
  have hr := continuous_orbitRadius (a := a) hρ hv
  have hφ := continuous_orbitAngle (a := a) hρ hv
  have hc : Continuous fun t => vinf ^ 2 * a / orbitRadius a ρ vinf t ^ 2 :=
    continuous_const.div (hr.pow 2) fun t => pow_ne_zero 2 (orbitRadius_pos hρ vinf t).ne'
  unfold acceleration
  exact hc.smul ((Real.continuous_cos.comp hφ).prodMk (Real.continuous_sin.comp hφ))

/-- The power radiated along the orbit is `(2/3)(1/4π) e² (v∞² a/r²)²`. -/
theorem dipolePower_smul_acceleration (e a ρ vinf t : ℝ) :
    dipolePower (e • acceleration a ρ vinf t) =
      2 / 3 * (4 * π)⁻¹ * (e * (vinf ^ 2 * a / orbitRadius a ρ vinf t ^ 2)) ^ 2 := by
  have h := Real.sin_sq_add_cos_sq (orbitAngle a ρ vinf t)
  simp only [dipolePower, acceleration, Prod.smul_mk, smul_eq_mul]
  linear_combination 2 / 3 * (4 * π)⁻¹ *
    (e * (vinf ^ 2 * a / orbitRadius a ρ vinf t ^ 2)) ^ 2 * h

/-! ### Integrability -/

/-- An even function integrable on `(0, ∞)` is integrable, with twice the integral. -/
theorem integrable_and_integral_of_even {f : ℝ → ℝ} (hf : ∀ t, f (-t) = f t)
    (h : IntegrableOn f (Ioi 0)) :
    Integrable f ∧ ∫ t, f t = 2 * ∫ t in Ioi 0, f t := by
  have h1 : IntegrableOn f (Iio 0) := by
    have := h.comp_neg
    rw [neg_Ioi, neg_zero] at this
    simpa only [hf] using this
  have h2 : IntegrableOn f (Iic 0) := (integrableOn_Iic_iff_integrableOn_Iio).mpr h1
  have hint : Integrable f := by
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
    exact h2.union h
  refine ⟨hint, ?_⟩
  rw [← integral_add_compl (measurableSet_Ioi (a := (0 : ℝ))) hint, compl_Ioi,
    ← neg_zero, ← integral_comp_neg_Ioi, neg_zero]
  simp only [hf]
  ring

/-- `∫₀^∞ ℓ dt/r² = φ₀`: the angle described after the closest approach. -/
theorem integrableOn_Ioi_angleRate (hρ : 0 < ρ) (hv : 0 < vinf) :
    IntegrableOn (fun t => ρ * vinf / orbitRadius a ρ vinf t ^ 2) (Ioi 0) ∧
      ∫ t in Ioi 0, ρ * vinf / orbitRadius a ρ vinf t ^ 2 = asymptoteAngle a ρ := by
  have hcont : ContinuousWithinAt (orbitAngle a ρ vinf) (Ici 0) 0 :=
    (hasDerivAt_orbitAngle hρ hv 0).continuousAt.continuousWithinAt
  have hderiv : ∀ t ∈ Ioi (0 : ℝ),
      HasDerivAt (orbitAngle a ρ vinf) (ρ * vinf / orbitRadius a ρ vinf t ^ 2) t :=
    fun t _ => hasDerivAt_orbitAngle hρ hv t
  have hnn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ ρ * vinf / orbitRadius a ρ vinf t ^ 2 := fun t _ => by
    positivity
  have hint := integrableOn_Ioi_deriv_of_nonneg hcont hderiv hnn (tendsto_orbitAngle_atTop hρ hv)
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint (tendsto_orbitAngle_atTop hρ hv),
    orbitAngle_zero, sub_zero]

/-- `∫ dt/r² = 2φ₀/ℓ` over the whole orbit, with `ℓ = ρ v∞`. -/
theorem integral_inv_orbitRadius_sq (hρ : 0 < ρ) (hv : 0 < vinf) :
    Integrable (fun t => (orbitRadius a ρ vinf t ^ 2)⁻¹) ∧
      ∫ t, (orbitRadius a ρ vinf t ^ 2)⁻¹ = 2 * asymptoteAngle a ρ / (ρ * vinf) := by
  obtain ⟨h1, h2⟩ := integrableOn_Ioi_angleRate (a := a) hρ hv
  obtain ⟨h3, h4⟩ := integrable_and_integral_of_even
    (f := fun t => ρ * vinf / orbitRadius a ρ vinf t ^ 2)
    (fun _ => by rw [orbitRadius_neg hρ hv]) h1
  have hℓ : ρ * vinf ≠ 0 := (mul_pos hρ hv).ne'
  have e : (fun t => (orbitRadius a ρ vinf t ^ 2)⁻¹) =
      fun t => (ρ * vinf)⁻¹ * (ρ * vinf / orbitRadius a ρ vinf t ^ 2) := by
    funext t
    field_simp
  rw [e]
  refine ⟨h3.const_mul _, ?_⟩
  rw [integral_const_mul, h4, h2]
  field_simp

theorem integrable_inv_orbitRadius_pow_four (hρ : 0 < ρ) (hv : 0 < vinf) :
    Integrable (fun t => (orbitRadius a ρ vinf t ^ 4)⁻¹) := by
  have h0 := closest_pos a hρ
  refine ((integral_inv_orbitRadius_sq (a := a) hρ hv).1.const_mul (closest a ρ ^ 2)⁻¹).mono' ?_
    (Eventually.of_forall fun t => ?_)
  · exact ((continuous_orbitRadius hρ hv).pow 4).inv₀
      (fun t => pow_ne_zero 4 (orbitRadius_pos hρ vinf t).ne') |>.aestronglyMeasurable
  · have hr := closest_le_orbitRadius a ρ vinf t
    have hr0 := orbitRadius_pos (a := a) hρ vinf t
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [show orbitRadius a ρ vinf t ^ 4 = orbitRadius a ρ vinf t ^ 2 * orbitRadius a ρ vinf t ^ 2
      by ring, mul_inv]
    gcongr

theorem norm_smul_acceleration_le (e a ρ vinf t : ℝ) :
    ‖e • acceleration a ρ vinf t‖ ≤ |e * (vinf ^ 2 * a)| * (orbitRadius a ρ vinf t ^ 2)⁻¹ := by
  rw [acceleration, smul_smul, norm_smul, Real.norm_eq_abs]
  have hn : ‖(Real.cos (orbitAngle a ρ vinf t), Real.sin (orbitAngle a ρ vinf t))‖ ≤ 1 := by
    rw [Prod.norm_def]
    simp only [Real.norm_eq_abs]
    exact max_le (Real.abs_cos_le_one _) (Real.abs_sin_le_one _)
  have e1 : |e * (vinf ^ 2 * a / orbitRadius a ρ vinf t ^ 2)| =
      |e * (vinf ^ 2 * a)| * (orbitRadius a ρ vinf t ^ 2)⁻¹ := by
    simp only [abs_mul, abs_div, abs_of_nonneg (sq_nonneg (orbitRadius a ρ vinf t))]
    ring
  calc _ ≤ |e * (vinf ^ 2 * a / orbitRadius a ρ vinf t ^ 2)| * 1 := by gcongr
    _ = _ := by rw [mul_one, e1]

/-- `𝐝̈ = e 𝐫̈` is integrable and square integrable on the line: `|𝐫̈| = v∞²|a|/r²` and
`∫ dt/r² < ∞`. -/
theorem integrable_dipoleAcceleration_coulomb (e a : ℝ) (hρ : 0 < ρ) (hv : 0 < vinf) :
    Integrable (fun t => e • acceleration a ρ vinf t) ∧
      MemLp (fun t => e • acceleration a ρ vinf t) 2 := by
  have hmeas : AEStronglyMeasurable (fun t => e • acceleration a ρ vinf t) :=
    ((continuous_acceleration hρ hv).const_smul e).aestronglyMeasurable
  have h1 := (integral_inv_orbitRadius_sq (a := a) hρ hv).1
  have h2 := integrable_inv_orbitRadius_pow_four (a := a) hρ hv
  refine ⟨(h1.const_mul |e * (vinf ^ 2 * a)|).mono' hmeas
    (Eventually.of_forall fun t => norm_smul_acceleration_le e a ρ vinf t), ?_⟩
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  refine (h2.const_mul (|e * (vinf ^ 2 * a)| ^ 2)).mono'
    (hmeas.norm.pow 2) (Eventually.of_forall fun t => ?_)
  have h := norm_smul_acceleration_le e a ρ vinf t
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖e • acceleration a ρ vinf t‖ ^ 2 ≤
      (|e * (vinf ^ 2 * a)| * (orbitRadius a ρ vinf t ^ 2)⁻¹) ^ 2 := by gcongr
    _ = _ := by ring

/-- The power radiated along the orbit is integrable. -/
theorem integrable_dipolePower (e a : ℝ) (hρ : 0 < ρ) (hv : 0 < vinf) :
    Integrable fun t => dipolePower (e • acceleration a ρ vinf t) := by
  have h := (integrable_inv_orbitRadius_pow_four (a := a) hρ hv).const_mul
    (2 / 3 * (4 * π)⁻¹ * (e * (vinf ^ 2 * a)) ^ 2)
  refine h.congr (Eventually.of_forall fun t => ?_)
  have hr := (orbitRadius_pos (a := a) hρ vinf t).ne'
  simp only [dipolePower_smul_acceleration]
  field_simp

/-! ### The energy radiated as a radial quadrature -/

/-- The energy radiated during the collision, `ΔE = ∫ (2/3)(1/4π)|𝐝̈|² dt`. -/
def totalEnergy (e a ρ vinf : ℝ) : ℝ := ∫ t, dipolePower (e • acceleration a ρ vinf t)

theorem totalEnergy_nonneg (e a ρ vinf : ℝ) : 0 ≤ totalEnergy e a ρ vinf :=
  integral_nonneg fun _ => dipolePower_nonneg _

/-- The radius maps the times after the closest approach onto `(r₀, ∞)`. -/
theorem image_orbitRadius_Ioi (hρ : 0 < ρ) (hv : 0 < vinf) :
    orbitRadius a ρ vinf '' Ioi 0 = Ioi (closest a ρ) := by
  have hF := isFactor a hρ hv
  apply Subset.antisymm
  · rintro _ ⟨t, ht, rfl⟩
    have h := hF.strictMonoOn_radius (mem_Ici.mpr (le_refl (0 : ℝ))) (mem_Ici.mpr (le_of_lt ht)) ht
    rw [radius_zero] at h
    exact h
  · intro y hy
    obtain ⟨T, hT, hT0⟩ := ((hF.tendsto_radius_atTop.eventually (eventually_gt_atTop y)).and
      (eventually_gt_atTop 0)).exists
    have hsub := intermediate_value_Icc hT0.le (continuous_orbitRadius (a := a) hρ hv).continuousOn
    have hy' : y ∈ Icc (orbitRadius a ρ vinf 0) (orbitRadius a ρ vinf T) := by
      rw [orbitRadius, radius_zero]
      exact ⟨le_of_lt hy, le_of_lt hT⟩
    obtain ⟨t, ht, rfl⟩ := hsub hy'
    refine ⟨t, lt_of_le_of_ne ht.1 fun h0 => ?_, rfl⟩
    rw [← h0, orbitRadius, radius_zero] at hy
    exact lt_irrefl _ hy

/-- After the closest approach `ṙ = √(v∞²(1 − 2a/r − ρ²/r²))`. -/
theorem radialVelocity_eq_sqrt (hρ : 0 < ρ) (hv : 0 < vinf) {t : ℝ} (ht : 0 < t) :
    radialVelocity (factor a ρ vinf) (closest a ρ) t =
      √(speedSq a ρ vinf (orbitRadius a ρ vinf t)) := by
  have hF := isFactor a hρ hv
  rw [orbitRadius, speedSq_eq hρ vinf (le_radius _ _ t), ← hF.radialVelocity_sq,
    Real.sqrt_sq (hF.radialVelocity_pos ht).le]

/-- The change of variables `dt = dr/ṙ` on the outgoing branch:
`∫_{r₀}^∞ g(r) dr/√(v∞²(1 − 2a/r − ρ²/r²)) = ∫₀^∞ g(r(t)) dt`. -/
theorem integral_Ioi_div_sqrt_speedSq (hρ : 0 < ρ) (hv : 0 < vinf) (g : ℝ → ℝ) :
    ∫ r in Ioi (closest a ρ), g r / √(speedSq a ρ vinf r) =
      ∫ t in Ioi 0, g (orbitRadius a ρ vinf t) := by
  have hF := isFactor a hρ hv
  have hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivWithinAt (orbitRadius a ρ vinf)
      (radialVelocity (factor a ρ vinf) (closest a ρ) t) (Ioi 0) t :=
    fun t _ => (hasDerivAt_orbitRadius hρ hv t).hasDerivWithinAt
  have hinj : InjOn (orbitRadius a ρ vinf) (Ioi 0) :=
    hF.strictMonoOn_radius.injOn.mono Ioi_subset_Ici_self
  rw [← image_orbitRadius_Ioi hρ hv,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have hpos := hF.radialVelocity_pos ht
  rw [smul_eq_mul, abs_of_pos hpos, ← radialVelocity_eq_sqrt hρ hv ht]
  field_simp

/-- The integrability on the outgoing branch, under `dt = dr/ṙ`. -/
theorem integrableOn_Ioi_div_sqrt_speedSq_iff (hρ : 0 < ρ) (hv : 0 < vinf) (g : ℝ → ℝ) :
    IntegrableOn (fun r => g r / √(speedSq a ρ vinf r)) (Ioi (closest a ρ)) ↔
      IntegrableOn (fun t => g (orbitRadius a ρ vinf t)) (Ioi 0) := by
  have hF := isFactor a hρ hv
  have hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivWithinAt (orbitRadius a ρ vinf)
      (radialVelocity (factor a ρ vinf) (closest a ρ) t) (Ioi 0) t :=
    fun t _ => (hasDerivAt_orbitRadius hρ hv t).hasDerivWithinAt
  have hinj : InjOn (orbitRadius a ρ vinf) (Ioi 0) :=
    hF.strictMonoOn_radius.injOn.mono Ioi_subset_Ici_self
  rw [← image_orbitRadius_Ioi hρ hv,
    integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv hinj]
  refine integrableOn_congr_fun (fun t ht => ?_) measurableSet_Ioi
  have hpos := hF.radialVelocity_pos ht
  simp only [smul_eq_mul]
  rw [abs_of_pos hpos, ← radialVelocity_eq_sqrt hρ hv ht]
  field_simp

/-- Landau–Lifshitz §68 for the Coulomb collision: the energy radiated is the radial quadrature
`ΔE = 2 ∫_{r₀}^∞ (2/3)(1/4π) e² (v∞² a/r²)² dr/√(v∞²(1 − 2a/r − ρ²/r²))` over the incoming and the
outgoing branch of the orbit. -/
theorem integral_dipolePower_eq (e a : ℝ) (hρ : 0 < ρ) (hv : 0 < vinf) :
    totalEnergy e a ρ vinf =
      2 * ∫ r in Ioi (closest a ρ),
        2 / 3 * (4 * π)⁻¹ * (e * (vinf ^ 2 * a / r ^ 2)) ^ 2 / √(speedSq a ρ vinf r) := by
  have heven : ∀ t, dipolePower (e • acceleration a ρ vinf (-t)) =
      dipolePower (e • acceleration a ρ vinf t) := fun t => by
    rw [dipolePower_smul_acceleration, dipolePower_smul_acceleration, orbitRadius_neg hρ hv]
  have h := (integrable_and_integral_of_even heven
    (integrable_dipolePower e a hρ hv).integrableOn).2
  rw [totalEnergy, h, integral_Ioi_div_sqrt_speedSq hρ hv]
  simp only [dipolePower_smul_acceleration]

/-! ### Plancherel's theorem and the spectral distribution -/

/-- The squared `L²` norm is the integral of the squared modulus. -/
theorem norm_sq_eq_integral (u : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖u‖ ^ 2 = ∫ x, ‖(u : ℝ → ℂ) x‖ ^ 2 := by
  have H := congr(RCLike.re $(L2.inner_def (𝕜 := ℂ) u u))
  rw [← integral_re (L2.integrable_inner u u)] at H
  simp only [← norm_sq_eq_re_inner] at H
  exact H

/-- Plancherel's theorem for the Fourier integral `𝓕f(ν) = ∫ e^{−2πiνt} f(t) dt` of a function in
`L¹ ∩ L²`: `𝓕f` is square integrable and `∫ |𝓕f|² = ∫ |f|²`. -/
theorem integral_norm_sq_fourier {f : ℝ → ℂ} (hf : Integrable f) (hf2 : MemLp f 2) :
    MemLp (𝓕 f) 2 ∧ ∫ ν, ‖𝓕 f ν‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 := by
  set F : Lp ℂ 2 (volume : Measure ℝ) := 𝓕 (hf2.toLp f) with hFdef
  have hpair : ∀ g : 𝓢(ℝ, ℂ), ∫ x, g x • (F : ℝ → ℂ) x = ∫ x, g x • 𝓕 f x := by
    intro g
    have h1 := congrArg (fun T : 𝓢'(ℝ, ℂ) => T g)
      (Lp.fourier_toTemperedDistribution_eq (hf2.toLp f))
    simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at h1
    rw [hFdef, ← h1]
    have h2 : ∫ x, (𝓕 g) x • (hf2.toLp f : ℝ → ℂ) x = ∫ x, (𝓕 g) x • f x :=
      integral_congr_ae (by filter_upwards [hf2.coeFn_toLp] with x hx; rw [hx])
    rw [h2]
    simpa using! VectorFourier.integral_bilin_fourierIntegral_eq_flip (.lsmul ℂ ℂ)
      (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner g.integrable hf
  have hcont : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hf
  have hlocF : LocallyIntegrable (F : ℝ → ℂ) volume := (Lp.memLp F).locallyIntegrable (by norm_num)
  have hae : (F : ℝ → ℂ) =ᵐ[volume] 𝓕 f := by
    have hloc : LocallyIntegrable (fun x => (F : ℝ → ℂ) x - 𝓕 f x) volume :=
      hlocF.sub (hcont.locallyIntegrable (μ := volume))
    have h0 := ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun g hg hgc => by
      have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
      have hg₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := Complex.ofRealCLM.contDiff.comp hg
      have key := hpair (hg₁.toSchwartzMap hg₂)
      have i1 := hlocF.integrable_smul_left_of_hasCompactSupport hg.continuous hgc
      have i2 := (hcont.locallyIntegrable (μ := volume)).integrable_smul_left_of_hasCompactSupport
        hg.continuous hgc
      simp only [smul_sub]
      rw [integral_sub i1 i2, sub_eq_zero]
      simpa [Complex.real_smul] using key
    filter_upwards [h0] with x hx using sub_eq_zero.mp hx
  refine ⟨(Lp.memLp F).ae_eq hae, ?_⟩
  have h1 : ∫ ν, ‖𝓕 f ν‖ ^ 2 = ‖F‖ ^ 2 := by
    rw [norm_sq_eq_integral]
    exact integral_congr_ae (by filter_upwards [hae] with x hx; rw [hx])
  have h2 : ∫ t, ‖f t‖ ^ 2 = ‖hf2.toLp f‖ ^ 2 := by
    rw [norm_sq_eq_integral]
    exact integral_congr_ae (by filter_upwards [hf2.coeFn_toLp] with x hx; rw [hx])
  rw [h1, h2, hFdef, Lp.norm_fourier_eq]

/-- The spectral density `dE_ν/dν = (2/3)(1/4π)|𝓕𝐝̈(ν)|²` of the radiation of a dipole with the
second derivative `w`, over all frequencies `ν ∈ ℝ`: `𝓕` is taken of each component. -/
def spectralDensity (w : ℝ → ℝ × ℝ) (ν : ℝ) : ℝ :=
  2 / 3 * (4 * π)⁻¹ *
    (‖𝓕 (fun t => ((w t).1 : ℂ)) ν‖ ^ 2 + ‖𝓕 (fun t => ((w t).2 : ℂ)) ν‖ ^ 2)

/-- The radiated energy is the integral of the spectral density (Landau–Lifshitz §68), for
a second derivative `𝐝̈` in `L¹ ∩ L²`. -/
theorem spectral_eq {w : ℝ → ℝ × ℝ} (hw : Integrable w) (hw2 : MemLp w 2) :
    Integrable (spectralDensity w) ∧ ∫ t, dipolePower (w t) = ∫ ν, spectralDensity w ν := by
  have hc1 : Integrable fun t => ((w t).1 : ℂ) := hw.fst.ofReal
  have hc2 : Integrable fun t => ((w t).2 : ℂ) := hw.snd.ofReal
  have hm1 : MemLp (fun t => (w t).1) 2 := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp_memLp' hw2
  have hm2 : MemLp (fun t => (w t).2) 2 := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp_memLp' hw2
  obtain ⟨hF1, hP1⟩ := integral_norm_sq_fourier hc1 hm1.ofReal
  obtain ⟨hF2, hP2⟩ := integral_norm_sq_fourier hc2 hm2.ofReal
  have hi1 := hF1.integrable_norm_pow two_ne_zero
  have hi2 := hF2.integrable_norm_pow two_ne_zero
  refine ⟨(hi1.add hi2).const_mul _, ?_⟩
  have hs1 := hm1.integrable_sq
  have hs2 := hm2.integrable_sq
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at hP1 hP2
  simp only [dipolePower, spectralDensity]
  rw [integral_const_mul, integral_const_mul, integral_add hs1 hs2, integral_add hi1 hi2, hP1,
    hP2]

/-- The energy radiated in the Coulomb collision is the integral of its spectral distribution. -/
theorem spectral_eq_coulomb (e a : ℝ) (hρ : 0 < ρ) (hv : 0 < vinf) :
    Integrable (spectralDensity fun t => e • acceleration a ρ vinf t) ∧
      totalEnergy e a ρ vinf = ∫ ν, spectralDensity (fun t => e • acceleration a ρ vinf t) ν :=
  spectral_eq (integrable_dipoleAcceleration_coulomb e a hρ hv).1
    (integrable_dipoleAcceleration_coulomb e a hρ hv).2

/-! ### The effective radiation -/

/-- The effective radiation `κ = ∫ ΔE(ρ) 2πρ dρ` (Landau–Lifshitz §68) of a beam of unit flux
density scattered by the Coulomb field, as a Bochner integral over the impact parameters. -/
def effectiveRadiation (e a vinf : ℝ) : ℝ :=
  ∫ ρ in Ioi 0, totalEnergy e a ρ vinf * (2 * π * ρ)

/-- The integral defining the effective radiation converges. -/
def IsEffectiveFinite (e a vinf : ℝ) : Prop :=
  IntegrableOn (fun ρ => totalEnergy e a ρ vinf * (2 * π * ρ)) (Ioi 0)

theorem effectiveRadiation_nonneg (e a vinf : ℝ) : 0 ≤ effectiveRadiation e a vinf :=
  setIntegral_nonneg measurableSet_Ioi fun ρ hρ =>
    mul_nonneg (totalEnergy_nonneg _ _ _ _) (by have := mem_Ioi.mp hρ; positivity)

end ProjectAinos.Electrodynamics.Radiation.Collision
