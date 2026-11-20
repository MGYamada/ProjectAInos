/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.Radiation.Relativistic
import Mathlib.Tactic

/-!
# Synchrotron radiation

The radiation of a charge `e` on the circular orbit `r(t) = R (cos Ωt, sin Ωt, 0)`
(`SubluminalWorldline.circular R Ω h` with `|RΩ| < 1`; Landau–Lifshitz, *The Classical Theory
of Fields*, §74; units with `c = 1`), with the speed `v = |RΩ|` and `γ = 1/√(1 − v²)` (`gamma`).

* The velocity `ṙ = RΩ (−sin Ωt, cos Ωt, 0)` (`deriv_circular`) is orthogonal to the
  acceleration `r̈ = −Ω² r` (`deriv_deriv_circular`, `inner_deriv_deriv_circular`), and
  `|r̈| = |Ω| v` (`norm_deriv_deriv_circular`).
* `integral_angularPower_circular`: the power per unit retarded time is
  `synchrotronPower e R Ω = (2/3)(e²/4π) γ⁴ v² Ω²` (`synchrotronPower_eq_gamma`), the formula of
  Liénard with `γ⁶ (v̇² − (v × v̇)²) = γ⁴ v̇²`; it is the limit of the energy radiated through the
  spheres of the light cone (`tendsto_integral_power_lightCone_circular`). The angular
  distribution is `(e² Ω⁴/16π²)(R²/(1 − n·v)³ − (1 − v²)(n·r)²/(1 − n·v)⁵)`
  (`angularPower_circular`).
* `lossPerTurn e R Ω`, the power times the period `2π/|Ω|`, is the energy radiated in one
  revolution (`integral_integral_angularPower_circular`), `(4π/3)(e²/4π) γ⁴ v² |Ω|`
  (`lossPerTurn_eq`). Its ratio to the energy `mγ` is `(4π/3)(e²/4π) γ³ v² |Ω|/m`
  (`lossPerTurn_div_energy`), and if `N` times this ratio is at most `ε`, the energy radiated in
  `N` revolutions of the prescribed orbit is at most `ε mγ` (`mul_lossPerTurn_le`): the condition
  under which the reaction of the radiation on the orbit is negligible.
* `hasDerivAt_momentum_circular`: the orbit solves `d(mγ ṙ)/dt = e ṙ × B` in the uniform
  magnetic field `B` along the third axis when `mγΩ = −eB` (§21; such a field exists for `e ≠ 0`,
  `exists_magnetic_circular`); the power is then `(2/3)(e²/4π) e²B² γ² v²/m²`
  (`synchrotronPower_eq_magnetic`).

The orbit is prescribed: it is not compared with the four-dimensional motion `ConstantField.motion`
in a constant field, whose magnetic case turns in the plane of the second and third axes. Not
formalized: the decomposition of the radiation into the harmonics of `Ω` and their intensities
in terms of Bessel functions, and the spectrum of §74.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric Real Filter
open scoped Topology

namespace ProjectAinos.Electrodynamics.Radiation.Synchrotron

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.Sphere SpecialRelativity
  Relativistic SubluminalWorldline

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### The circular orbit -/

/-- The velocity of the circular orbit, `ṙ(t) = RΩ (−sin Ωt, cos Ωt, 0)`. -/
theorem deriv_circular (R Ω : ℝ) (h : |R * Ω| < 1) (t : ℝ) :
    deriv (circular R Ω h).r t =
      (-(R * Ω) * Real.sin (Ω * t)) • EuclideanSpace.single 0 1 +
        (R * Ω * Real.cos (Ω * t)) • EuclideanSpace.single 1 1 :=
  (hasDerivAt_circularPath R Ω t).deriv

/-- The acceleration of the circular orbit is centripetal, `r̈(t) = −Ω² r(t)`. -/
theorem deriv_deriv_circular (R Ω : ℝ) (h : |R * Ω| < 1) (t : ℝ) :
    deriv (deriv (circular R Ω h).r) t = (-Ω ^ 2) • circularPath R Ω t := by
  have hd : deriv (circular R Ω h).r = fun t =>
      (-(R * Ω) * Real.sin (Ω * t)) • (EuclideanSpace.single 0 1 : E3) +
        (R * Ω * Real.cos (Ω * t)) • EuclideanSpace.single 1 1 :=
    funext (deriv_circular R Ω h)
  have hs := ((hasDerivAt_id' t).const_mul Ω).sin
  have hc := ((hasDerivAt_id' t).const_mul Ω).cos
  have hD : HasDerivAt (fun t =>
      (-(R * Ω) * Real.sin (Ω * t)) • (EuclideanSpace.single 0 1 : E3) +
        (R * Ω * Real.cos (Ω * t)) • EuclideanSpace.single 1 1)
      ((-(R * Ω) * (Real.cos (Ω * t) * (Ω * 1))) • (EuclideanSpace.single 0 1 : E3) +
        (R * Ω * (-Real.sin (Ω * t) * (Ω * 1))) • EuclideanSpace.single 1 1) t :=
    ((hs.const_mul (-(R * Ω))).smul_const (EuclideanSpace.single 0 1 : E3)).add
      ((hc.const_mul (R * Ω)).smul_const (EuclideanSpace.single 1 1 : E3))
  rw [hd, hD.deriv, circularPath]
  ext i
  fin_cases i <;> simp <;> ring

/-- `|ṙ|² = (RΩ)²`. -/
theorem norm_sq_deriv_circular (R Ω : ℝ) (h : |R * Ω| < 1) (t : ℝ) :
    ‖deriv (circular R Ω h).r t‖ ^ 2 = (R * Ω) ^ 2 := by
  rw [show (circular R Ω h).r = circularPath R Ω from rfl, norm_deriv_circularPath, sq_abs]

/-- `|r|² = R²`. -/
theorem norm_sq_circularPath (R Ω t : ℝ) : ‖circularPath R Ω t‖ ^ 2 = R ^ 2 := by
  rw [LienardWiechert.norm_sq_eq_sum, circularPath]
  simp
  linear_combination R ^ 2 * Real.sin_sq_add_cos_sq (Ω * t)

/-- `|r̈|² = R²Ω⁴`. -/
theorem norm_sq_deriv_deriv_circular (R Ω : ℝ) (h : |R * Ω| < 1) (t : ℝ) :
    ‖deriv (deriv (circular R Ω h).r) t‖ ^ 2 = R ^ 2 * Ω ^ 4 := by
  rw [deriv_deriv_circular, norm_smul, mul_pow, norm_sq_circularPath, Real.norm_eq_abs, sq_abs]
  ring

/-- **The kinematic relation of the circular orbit**: `|v̇| = |Ω| v` with the speed `v = |RΩ|`. -/
theorem norm_deriv_deriv_circular (R Ω : ℝ) (h : |R * Ω| < 1) (t : ℝ) :
    ‖deriv (deriv (circular R Ω h).r) t‖ = |Ω| * ‖deriv (circular R Ω h).r t‖ := by
  rw [show (circular R Ω h).r = circularPath R Ω from rfl, norm_deriv_circularPath]
  have h1 := norm_sq_deriv_deriv_circular R Ω h t
  rw [show (circular R Ω h).r = circularPath R Ω from rfl] at h1
  refine (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
  rw [h1, mul_pow, sq_abs, sq_abs]
  ring

/-- The velocity of the circular orbit is orthogonal to its acceleration. -/
theorem inner_deriv_deriv_circular (R Ω : ℝ) (h : |R * Ω| < 1) (t : ℝ) :
    inner ℝ (deriv (circular R Ω h).r t) (deriv (deriv (circular R Ω h).r) t) = 0 := by
  rw [deriv_deriv_circular, deriv_circular, LienardWiechert.inner_eq_sum, circularPath]
  simp
  ring

/-! ### The power -/

/-- The Lorentz factor `γ = 1/√(1 − v²)` of the circular orbit with the speed `v = |RΩ|`. -/
def gamma (R Ω : ℝ) : ℝ := (√(1 - (R * Ω) ^ 2))⁻¹

/-- `γ > 0`. -/
theorem gamma_pos {R Ω : ℝ} (h : |R * Ω| < 1) : 0 < gamma R Ω := by
  have : 0 < 1 - (R * Ω) ^ 2 := by
    have := sq_lt_one_iff_abs_lt_one (R * Ω) |>.mpr h
    linarith
  exact inv_pos.mpr (Real.sqrt_pos.mpr this)

/-- `γ² = 1/(1 − v²)`. -/
theorem gamma_sq {R Ω : ℝ} (h : |R * Ω| < 1) : gamma R Ω ^ 2 = (1 - (R * Ω) ^ 2)⁻¹ := by
  have : 0 ≤ 1 - (R * Ω) ^ 2 := by
    have := sq_lt_one_iff_abs_lt_one (R * Ω) |>.mpr h
    linarith
  rw [gamma, inv_pow, Real.sq_sqrt this]

/-- The power `(2/3)(e²/4π) γ⁴ v² Ω²` of the synchrotron radiation of the circular orbit, with
`γ⁴ = 1/(1 − v²)²` and `v = |RΩ|`. -/
def synchrotronPower (e R Ω : ℝ) : ℝ :=
  2 / 3 * (e ^ 2 / (4 * π)) * ((1 - (R * Ω) ^ 2)⁻¹) ^ 2 * (R * Ω) ^ 2 * Ω ^ 2

/-- The power is `(2/3)(e²/4π) γ⁴ v² Ω²`. -/
theorem synchrotronPower_eq_gamma (e : ℝ) {R Ω : ℝ} (h : |R * Ω| < 1) :
    synchrotronPower e R Ω = 2 / 3 * (e ^ 2 / (4 * π)) * gamma R Ω ^ 4 * (R * Ω) ^ 2 * Ω ^ 2 := by
  rw [synchrotronPower, show gamma R Ω ^ 4 = (gamma R Ω ^ 2) ^ 2 by ring, gamma_sq h]

private theorem one_sub_sq_ne_zero {R Ω : ℝ} (h : |R * Ω| < 1) : 1 - (R * Ω) ^ 2 ≠ 0 := by
  have := sq_lt_one_iff_abs_lt_one (R * Ω) |>.mpr h
  linarith

/-- **The power of the synchrotron radiation** (Landau–Lifshitz §74): the energy radiated per
unit retarded time by the charge `e` on the circular orbit of the radius `R` and the angular
velocity `Ω` is `(2/3)(e²/4π) γ⁴ v² Ω²`, by the formula of Liénard with `v ⊥ v̇`, where
`γ⁶ (v̇² − (v × v̇)²) = γ⁶ v̇² (1 − v²) = γ⁴ v̇²` and `|v̇| = |Ω| v`. -/
theorem integral_angularPower_circular (e R Ω : ℝ) (h : |R * Ω| < 1) (τ : ℝ) :
    ∫ n : sphere (0 : E3) 1, angularPower e (deriv (circular R Ω h).r τ)
        (deriv (deriv (circular R Ω h).r) τ) n ∂sphereMeasure = synchrotronPower e R Ω := by
  have hv : ‖deriv (circular R Ω h).r τ‖ < 1 := by
    rw [show (circular R Ω h).r = circularPath R Ω from rfl, norm_deriv_circularPath]
    exact h
  rw [integral_angularPower e hv, norm_cross_sq, norm_sq_deriv_circular,
    norm_sq_deriv_deriv_circular, inner_deriv_deriv_circular, synchrotronPower,
    show R ^ 2 * Ω ^ 4 = (R * Ω) ^ 2 * Ω ^ 2 by ring]
  have := one_sub_sq_ne_zero h
  generalize (R * Ω) ^ 2 = u at this ⊢
  field_simp
  ring

/-- **The radiation zone of the circular orbit**: the energy radiated through the sphere of the
light cone of `r(τ)`, per unit retarded time, tends to `(2/3)(e²/4π) γ⁴ v² Ω²`. -/
theorem tendsto_integral_power_lightCone_circular (e R Ω : ℝ) (h : |R * Ω| < 1) (τ : ℝ) :
    Tendsto (fun ρ => ∫ n : sphere (0 : E3) 1, ρ ^ 2 * (∑ i : Fin 3,
        poyntingVector (fieldTensor (lienardWiechert e (circular R Ω h))) i
          (Minkowski.vector (τ + ρ) ((circular R Ω h).r τ + ρ • (n : E3))) * (n : E3) i) *
        (1 - inner ℝ (n : E3) (deriv (circular R Ω h).r τ)) ∂sphereMeasure) atTop
      (𝓝 (synchrotronPower e R Ω)) := by
  have hv : ‖deriv (circular R Ω h).r τ‖ < 1 := by
    rw [show (circular R Ω h).r = circularPath R Ω from rfl, norm_deriv_circularPath]
    exact h
  rw [← integral_angularPower_circular e R Ω h τ, integral_angularPower e hv]
  exact tendsto_integral_power_lightCone (circular R Ω h) e τ

/-- **The angular distribution of the synchrotron radiation**: with the velocity
`v = ṙ(τ)` and the radius vector `r(τ)` of the orbit, `v̇ = −Ω² r(τ)` and
`dI/dΩ = (e² Ω⁴/16π²)(R²/(1 − n·v)³ − (1 − v²)(n·r)²/(1 − n·v)⁵)`. -/
theorem angularPower_circular (e R Ω : ℝ) (h : |R * Ω| < 1) (τ : ℝ) {n : E3} (hn : ‖n‖ = 1) :
    angularPower e (deriv (circular R Ω h).r τ) (deriv (deriv (circular R Ω h).r) τ) n =
      e ^ 2 * Ω ^ 4 / (16 * π ^ 2) *
        (R ^ 2 / (1 - inner ℝ n (deriv (circular R Ω h).r τ)) ^ 3 -
          (1 - (R * Ω) ^ 2) * inner ℝ n (circularPath R Ω τ) ^ 2 /
            (1 - inner ℝ n (deriv (circular R Ω h).r τ)) ^ 5) := by
  have hv : ‖deriv (circular R Ω h).r τ‖ < 1 := by
    rw [show (circular R Ω h).r = circularPath R Ω from rfl, norm_deriv_circularPath]
    exact h
  rw [angularPower_of_inner_eq_zero e hv (inner_deriv_deriv_circular R Ω h τ) hn,
    norm_sq_deriv_deriv_circular, norm_sq_deriv_circular]
  conv_lhs => rw [deriv_deriv_circular, real_inner_smul_right]
  ring

/-! ### The energy lost per revolution -/

/-- The energy `(2π/|Ω|) × (2/3)(e²/4π) γ⁴ v² Ω²` radiated during one revolution. -/
def lossPerTurn (e R Ω : ℝ) : ℝ := 2 * π / |Ω| * synchrotronPower e R Ω

/-- **The energy radiated in one revolution** is the integral of the power over one period
`2π/|Ω|` of the retarded time. -/
theorem integral_integral_angularPower_circular (e R Ω : ℝ) (h : |R * Ω| < 1) (τ : ℝ) :
    ∫ t in τ..τ + 2 * π / |Ω|, (∫ n : sphere (0 : E3) 1, angularPower e
        (deriv (circular R Ω h).r t) (deriv (deriv (circular R Ω h).r) t) n ∂sphereMeasure) =
      lossPerTurn e R Ω := by
  simp only [integral_angularPower_circular e R Ω h, intervalIntegral.integral_const,
    smul_eq_mul, lossPerTurn]
  ring

/-- `ΔE = (4π/3)(e²/4π) γ⁴ v² |Ω|` per revolution. -/
theorem lossPerTurn_eq (e R : ℝ) {Ω : ℝ} (hΩ : Ω ≠ 0) :
    lossPerTurn e R Ω =
      4 * π / 3 * (e ^ 2 / (4 * π)) * ((1 - (R * Ω) ^ 2)⁻¹) ^ 2 * (R * Ω) ^ 2 * |Ω| := by
  have habs : 0 < |Ω| := abs_pos.mpr hΩ
  rw [lossPerTurn, synchrotronPower, ← sq_abs Ω]
  field_simp
  ring

/-- **The fraction of the energy lost per revolution** (Landau–Lifshitz §74): the energy
radiated in one revolution divided by the energy `mγ` of the charge is
`(4π/3)(e²/4π) γ³ v² |Ω|/m`. -/
theorem lossPerTurn_div_energy (e m : ℝ) {R Ω : ℝ} (h : |R * Ω| < 1) (hm : m ≠ 0)
    (hΩ : Ω ≠ 0) :
    lossPerTurn e R Ω / (m * gamma R Ω) =
      4 * π / 3 * (e ^ 2 / (4 * π)) * gamma R Ω ^ 3 * (R * Ω) ^ 2 * |Ω| / m := by
  have hγ := (gamma_pos h).ne'
  rw [lossPerTurn_eq e R hΩ, ← gamma_sq h]
  field_simp

/-- **When the reaction of the radiation is negligible**: if `N` times the fraction
`(4π/3)(e²/4π) γ³ v² |Ω|/m` is at most `ε`, the energy radiated in `N` revolutions of the
prescribed orbit is at most `ε` times the energy `mγ` of the charge. -/
theorem mul_lossPerTurn_le (e : ℝ) {m R Ω : ℝ} (h : |R * Ω| < 1) (hm : 0 < m) (hΩ : Ω ≠ 0)
    {N ε : ℝ}
    (hN : N * (4 * π / 3 * (e ^ 2 / (4 * π)) * gamma R Ω ^ 3 * (R * Ω) ^ 2 * |Ω| / m) ≤ ε) :
    N * lossPerTurn e R Ω ≤ ε * (m * gamma R Ω) := by
  have hE : 0 < m * gamma R Ω := mul_pos hm (gamma_pos h)
  have hl : lossPerTurn e R Ω =
      (4 * π / 3 * (e ^ 2 / (4 * π)) * gamma R Ω ^ 3 * (R * Ω) ^ 2 * |Ω| / m) *
        (m * gamma R Ω) := by
    rw [← lossPerTurn_div_energy e m h hm.ne' hΩ, div_mul_cancel₀ _ hE.ne']
  rw [hl, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hN hE.le

/-! ### The motion in a uniform magnetic field -/

/-- **The circular orbit is the motion in a uniform magnetic field** (Landau–Lifshitz §21): with
the momentum `p = mγ ṙ`, the orbit of the radius `R` and the angular velocity `Ω` satisfies
`dp/dt = e ṙ × B` in the field `B` along the third axis when `mγΩ = −eB`, that is for the
frequency `|Ω| = |eB|/(mγ)`. -/
theorem hasDerivAt_momentum_circular {m e B R Ω : ℝ} (h : |R * Ω| < 1)
    (hB : m * gamma R Ω * Ω = -(e * B)) (t : ℝ) :
    HasDerivAt (fun t => (m * (√(1 - ‖deriv (circular R Ω h).r t‖ ^ 2))⁻¹) •
        deriv (circular R Ω h).r t)
      (e • cross (deriv (circular R Ω h).r t) (B • EuclideanSpace.single 2 1)) t := by
  have hfun : (fun t => (m * (√(1 - ‖deriv (circular R Ω h).r t‖ ^ 2))⁻¹) •
      deriv (circular R Ω h).r t) = fun t => (m * gamma R Ω) • deriv (circular R Ω h).r t := by
    funext t
    rw [norm_sq_deriv_circular, gamma]
  rw [hfun]
  have hd : HasDerivAt (deriv (circular R Ω h).r) (deriv (deriv (circular R Ω h).r) t) t :=
    ((circular R Ω h).contDiff_deriv.differentiable (by simp)).differentiableAt.hasDerivAt
  convert hd.const_smul (m * gamma R Ω) using 1
  rw [deriv_deriv_circular, deriv_circular, circularPath]
  ext i
  fin_cases i
  · simp [cross, cross_apply]
    linear_combination (R * Ω * Real.cos (Ω * t)) * hB
  · simp [cross, cross_apply]
    linear_combination (R * Ω * Real.sin (Ω * t)) * hB
  · simp [cross, cross_apply]

/-- For `e ≠ 0` there is a field `B` with `mγΩ = −eB`. -/
theorem exists_magnetic_circular (m : ℝ) {e : ℝ} (he : e ≠ 0) (R Ω : ℝ) :
    ∃ B : ℝ, m * gamma R Ω * Ω = -(e * B) :=
  ⟨-(m * gamma R Ω * Ω) / e, by field_simp⟩

/-- **The power in terms of the magnetic field** (Landau–Lifshitz §74): for `mγΩ = −eB`, the
power is `(2/3)(e²/4π) e² B² γ² v²/m²`. -/
theorem synchrotronPower_eq_magnetic {m e B R Ω : ℝ} (h : |R * Ω| < 1) (hm : m ≠ 0)
    (hB : m * gamma R Ω * Ω = -(e * B)) :
    synchrotronPower e R Ω =
      2 / 3 * (e ^ 2 / (4 * π)) * (e * B) ^ 2 * gamma R Ω ^ 2 * (R * Ω) ^ 2 / m ^ 2 := by
  have hγ := (gamma_pos h).ne'
  have hΩ : Ω ^ 2 = (e * B) ^ 2 / (m * gamma R Ω) ^ 2 := by
    rw [show e * B = -(m * gamma R Ω * Ω) by linarith]
    field_simp
  rw [synchrotronPower_eq_gamma e h, hΩ]
  field_simp

end ProjectAinos.Electrodynamics.Radiation.Synchrotron
