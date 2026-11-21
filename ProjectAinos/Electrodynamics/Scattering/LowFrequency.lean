/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.Scattering.Thomson
public import ProjectAinos.Mechanics.Oscillations.Forced
public import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Tactic

/-!
# Scattering of low-frequency waves

Landau–Lifshitz, *The Classical Theory of Fields*, §79, in units with `c = 1` and `div E = k⁰`.

**The bound charge.** A charge bound by the elastic force `−m ω₀² x`, with the friction
`−2mγ ẋ`, in the plane wave `E₀ cos ωt` of `incidentPotential` at `x₀ = 0` has the steady state
`boundResponse`, `x = (A cos ωt + B sin ωt)(e/m) E₀` with the coefficients `steadyCos` and
`steadySin` of the forced oscillator (Landau–Lifshitz, *Mechanics*, §26):
`hasDerivAt_boundResponse`, `hasDerivAt_boundVelocity` (`ẍ = −ω² x`) and
`boundResponse_equation` (`ẍ + 2γ ẋ + ω₀² x = (e/m) E₀ cos ωt`).

* `crossSection_oscillator`: the cross section of the steady state is
  `σ(ω) = σ_T ω⁴/((ω₀² − ω²)² + 4γ²ω²)` (`oscillatorCrossSection`), since
  `A² + B² = 1/((ω₀² − ω²)² + 4γ²ω²)` (`steadyCos_sq_add_steadySin_sq`).
* `abs_crossSection_sub_le`: **Rayleigh's law** with a remainder: for `ω ≤ ω₀/2` and `|γ| ≤ ω₀`,
  `|σ/σ_T − (ω/ω₀)⁴| ≤ 12 (ω/ω₀)⁶`.

**A polarizable system.** At low frequencies a system acquires the dipole `d = α E` with its
polarizability `α`, and `polarizabilityCrossSection ω α ê = (2/3)(1/4π) ω⁴ |α ê|²` is its cross
section for the polarization `ê` (`crossSection_polarizable`, from the plane wave).

* `orientationAverage`: for a symmetric `α`, the mean of `|α ê|²` over the directions `ê` of the
  polarization is `tr(α²)/3`, by the second moment of the sphere; since the surface measure is
  invariant under rotations, this is also the mean over the orientations of the system for a fixed
  polarization. The mean cross section is `(2/3)(1/4π) ω⁴ tr(α²)/3`
  (`orientationAverage_polarizabilityCrossSection`).
* Instances: the isotropic polarizability `c · 1` (`isSymmetric_smul_id`, `trace_smul_id_comp`),
  and the static polarizability `e²/(m ω₀²)` of the bound charge, whose cross section is Rayleigh's
  leading term `σ_T (ω/ω₀)⁴` (`polarizabilityCrossSection_bound`).

The friction `γ` is a given constant. For the damping by the reaction of the radiation (§75) the
steady state is the same with `2γ = τ ω²`, `τ = (2/3)(e²/4πm)` (`boundResponse_radiationReaction`,
`responseDenominator_radiationReaction`). The polarizability of a general system is a given
tensor.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric Real Filter
open scoped Topology

namespace ProjectAinos.Electrodynamics.Scattering.LowFrequency

open SmoothGeometry SmoothGeometry.Sphere Thomson
open ProjectAinos.Mechanics (steadyCos steadySin responseDenominator)

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### The bound charge -/

/-- The steady state `x(t) = (A cos ωt + B sin ωt) f` of a charge bound by the elastic force
`−m ω₀² x` with the friction `−2mγ ẋ`, driven by the force `m f cos ωt`; `A` and `B` are the
coefficients `steadyCos`, `steadySin` of the forced oscillator (Landau–Lifshitz §26) for the force
`cos ωt`. -/
def boundResponse (γ ω₀ ω : ℝ) (f : E3) (t : ℝ) : E3 :=
  (steadyCos γ ω₀ 1 ω * Real.cos (ω * t) + steadySin γ ω₀ 1 ω * Real.sin (ω * t)) • f

/-- The velocity of the steady state, `ω (B cos ωt − A sin ωt) f`. -/
def boundVelocity (γ ω₀ ω : ℝ) (f : E3) (t : ℝ) : E3 :=
  (ω * (steadySin γ ω₀ 1 ω * Real.cos (ω * t) - steadyCos γ ω₀ 1 ω * Real.sin (ω * t))) • f

/-- The velocity of the steady state is its derivative. -/
theorem hasDerivAt_boundResponse (γ ω₀ ω : ℝ) (f : E3) (t : ℝ) :
    HasDerivAt (boundResponse γ ω₀ ω f) (boundVelocity γ ω₀ ω f t) t := by
  have h1 : HasDerivAt (fun t => ω * t) ω t := by
    simpa using (hasDerivAt_id t).const_mul ω
  have h := ((h1.cos.const_mul (steadyCos γ ω₀ 1 ω)).fun_add
    (h1.sin.const_mul (steadySin γ ω₀ 1 ω))).smul_const f
  refine h.congr_deriv ?_
  rw [boundVelocity]
  congr 1
  ring

/-- The acceleration of the steady state is `−ω² x`. -/
theorem hasDerivAt_boundVelocity (γ ω₀ ω : ℝ) (f : E3) (t : ℝ) :
    HasDerivAt (boundVelocity γ ω₀ ω f) (-(ω ^ 2) • boundResponse γ ω₀ ω f t) t := by
  have h1 : HasDerivAt (fun t => ω * t) ω t := by
    simpa using (hasDerivAt_id t).const_mul ω
  have h := (((h1.cos.const_mul (steadySin γ ω₀ 1 ω)).fun_sub
    (h1.sin.const_mul (steadyCos γ ω₀ 1 ω))).const_mul ω).smul_const f
  refine h.congr_deriv ?_
  rw [boundResponse, smul_smul]
  congr 1
  ring

/-- **The equation of motion of the bound charge**: for `(ω₀² − ω²)² + 4γ²ω² ≠ 0` the steady state
solves `ẍ + 2γ ẋ + ω₀² x = f cos ωt`. -/
theorem boundResponse_equation {γ ω₀ ω : ℝ} (hD : responseDenominator γ ω₀ ω ≠ 0) (f : E3)
    (t : ℝ) :
    -(ω ^ 2) • boundResponse γ ω₀ ω f t = Real.cos (ω * t) • f -
      (2 * γ) • boundVelocity γ ω₀ ω f t - ω₀ ^ 2 • boundResponse γ ω₀ ω f t := by
  have hA := Mechanics.steadyCos_mul_add_steadySin_mul hD 1
  have hB := Mechanics.steadySin_mul_eq_steadyCos_mul γ ω₀ 1 ω
  simp only [boundResponse, boundVelocity, smul_smul, ← sub_smul]
  congr 1
  linear_combination Real.cos (ω * t) * hA + Real.sin (ω * t) * hB

/-- `A² + B² = 1/((ω₀² − ω²)² + 4γ²ω²)`. -/
theorem steadyCos_sq_add_steadySin_sq (γ ω₀ ω : ℝ) :
    steadyCos γ ω₀ 1 ω ^ 2 + steadySin γ ω₀ 1 ω ^ 2 = 1 / responseDenominator γ ω₀ ω := by
  by_cases hD : responseDenominator γ ω₀ ω = 0
  · simp [Mechanics.steadyCos, Mechanics.steadySin, hD]
  · simp only [Mechanics.steadyCos, Mechanics.steadySin]
    field_simp
    unfold responseDenominator
    ring

/-- The cross section `σ_T ω⁴/((ω₀² − ω²)² + 4γ²ω²)` of the damped bound charge. -/
def oscillatorCrossSection (e m γ ω₀ ω : ℝ) : ℝ :=
  thomsonCrossSection e m * ω ^ 4 / responseDenominator γ ω₀ ω

/-- **The cross section of a bound charge** (Landau–Lifshitz §79, with a friction of the
coefficient `2γ`): the steady state of `ẍ + 2γ ẋ + ω₀² x = (e/m) E₀ cos ωt` in the plane wave
of `incidentPotential` (at `x₀ = 0`) has the acceleration `−ω² x`, and its averaged power of
Larmor divided by the averaged incident flux is `σ = σ_T ω⁴/((ω₀² − ω²)² + 4γ²ω²)`. -/
theorem crossSection_oscillator (e m γ ω₀ : ℝ) {ω : ℝ} (hω : ω ≠ 0) {u E₀ : E3} (hu : ‖u‖ = 1)
    (huE : inner ℝ u E₀ = 0) (hE₀ : E₀ ≠ 0) :
    crossSection e ω (fun t => -(ω ^ 2) • boundResponse γ ω₀ ω ((e / m) • E₀) t)
        (incidentFlux ω u E₀ 0) = oscillatorCrossSection e m γ ω₀ ω := by
  set A := steadyCos γ ω₀ 1 ω
  set B := steadySin γ ω₀ 1 ω
  have h : (fun t => 2 / 3 * (e ^ 2 / (4 * π)) *
      ‖-(ω ^ 2) • boundResponse γ ω₀ ω ((e / m) • E₀) t‖ ^ 2) =
      fun t => 2 / 3 * (e ^ 2 / (4 * π)) * ω ^ 4 * (e / m) ^ 2 * ‖E₀‖ ^ 2 *
        Mechanics.amplitude A B ^ 2 * Real.cos (ω * t + Mechanics.phase A B) ^ 2 := by
    funext t
    rw [boundResponse, ← Mechanics.amplitude_mul_cos_add, norm_smul, norm_smul, norm_smul,
      Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, mul_pow, sq_abs,
      sq_abs, sq_abs, mul_pow]
    ring
  have hE : ‖E₀‖ ≠ 0 := norm_ne_zero_iff.mpr hE₀
  have hR : Mechanics.amplitude A B ^ 2 = 1 / responseDenominator γ ω₀ ω := by
    rw [Mechanics.amplitude_sq, steadyCos_sq_add_steadySin_sq]
  rw [crossSection, incidentFlux_eq hω hu huE, h, periodAverage_const_mul,
    periodAverage_cos_sq hω, hR, oscillatorCrossSection, thomsonCrossSection]
  field_simp
  ring

/-- The third derivative of the steady state: `x⃛ = −ω² ẋ`. -/
theorem hasDerivAt_boundAcceleration (γ ω₀ ω : ℝ) (f : E3) (t : ℝ) :
    HasDerivAt (fun t => -(ω ^ 2) • boundResponse γ ω₀ ω f t)
      (-(ω ^ 2) • boundVelocity γ ω₀ ω f t) t :=
  (hasDerivAt_boundResponse γ ω₀ ω f t).const_smul (-(ω ^ 2))

/-- **The damping by the radiation** (Landau–Lifshitz §79, with the reaction force of §75): for
the friction `2γ = τ ω²`, `τ = (2/3)(e²/4πm)`, the steady state also solves the equation
`ẍ + ω₀² x = f cos ωt + τ x⃛` with the force of the radiation reaction, since `x⃛ = −ω² ẋ`
(`hasDerivAt_boundAcceleration`). Its cross section is `crossSection_oscillator` with this `γ`. -/
theorem boundResponse_radiationReaction {τ ω₀ ω : ℝ}
    (hD : responseDenominator (τ * ω ^ 2 / 2) ω₀ ω ≠ 0) (f : E3) (t : ℝ) :
    -(ω ^ 2) • boundResponse (τ * ω ^ 2 / 2) ω₀ ω f t = Real.cos (ω * t) • f +
      τ • (-(ω ^ 2) • boundVelocity (τ * ω ^ 2 / 2) ω₀ ω f t) -
        ω₀ ^ 2 • boundResponse (τ * ω ^ 2 / 2) ω₀ ω f t := by
  rw [boundResponse_equation hD f t, smul_smul]
  congr 1
  rw [sub_eq_add_neg, ← neg_smul]
  congr 2
  ring

/-- With the damping by the radiation the denominator is `(ω₀² − ω²)² + τ²ω⁶`, the cross section
of Landau–Lifshitz §79 `σ = σ_T ω⁴/((ω₀² − ω²)² + τ²ω⁶)`. -/
theorem responseDenominator_radiationReaction (τ ω₀ ω : ℝ) :
    responseDenominator (τ * ω ^ 2 / 2) ω₀ ω = (ω₀ ^ 2 - ω ^ 2) ^ 2 + τ ^ 2 * ω ^ 6 := by
  unfold responseDenominator
  ring

/-- **Rayleigh's law** (Landau–Lifshitz §79): at low frequencies, `ω ≤ ω₀/2`, and for a
friction `|γ| ≤ ω₀`, the cross section of the bound charge is `σ_T (ω/ω₀)⁴` up to
`12 σ_T (ω/ω₀)⁶`: `|σ/σ_T − (ω/ω₀)⁴| ≤ 12 (ω/ω₀)⁶`. -/
theorem abs_crossSection_sub_le {e m : ℝ} (he : e ≠ 0) (hm : m ≠ 0) {γ ω₀ ω : ℝ}
    (hω₀ : ω₀ ≠ 0) (hω : 4 * ω ^ 2 ≤ ω₀ ^ 2) (hγ : γ ^ 2 ≤ ω₀ ^ 2) :
    |oscillatorCrossSection e m γ ω₀ ω / thomsonCrossSection e m - (ω / ω₀) ^ 4| ≤
      12 * (ω / ω₀) ^ 6 := by
  have hT : thomsonCrossSection e m ≠ 0 := by
    unfold thomsonCrossSection
    have : 0 < π := pi_pos
    positivity
  have hw : 0 < ω₀ ^ 2 := by positivity
  have hu : 0 ≤ ω ^ 2 := sq_nonneg ω
  have hc : 0 ≤ γ ^ 2 := sq_nonneg γ
  have hD : responseDenominator γ ω₀ ω = (ω₀ ^ 2 - ω ^ 2) ^ 2 + 4 * γ ^ 2 * ω ^ 2 := rfl
  have hDlow : 9 * (ω₀ ^ 2) ^ 2 / 16 ≤ responseDenominator γ ω₀ ω := by
    rw [hD]
    nlinarith [mul_nonneg hc hu]
  have hDpos : 0 < responseDenominator γ ω₀ ω := lt_of_lt_of_le (by positivity) hDlow
  have hratio : oscillatorCrossSection e m γ ω₀ ω / thomsonCrossSection e m =
      (ω ^ 2) ^ 2 / responseDenominator γ ω₀ ω := by
    rw [oscillatorCrossSection]
    field_simp
  have h4 : (ω / ω₀) ^ 4 = (ω ^ 2) ^ 2 / (ω₀ ^ 2) ^ 2 := by
    rw [div_pow]
    ring
  have h6 : (ω / ω₀) ^ 6 = (ω ^ 2) ^ 3 / (ω₀ ^ 2) ^ 3 := by
    rw [div_pow]
    ring
  rw [hratio, h4, h6]
  set u := ω ^ 2
  set w := ω₀ ^ 2
  set D := responseDenominator γ ω₀ ω
  have key : u ^ 2 / D - u ^ 2 / w ^ 2 = u ^ 2 * (w ^ 2 - D) / (D * w ^ 2) := by
    field_simp
  have hnum : |w ^ 2 - D| ≤ 25 / 4 * w * u := by
    rw [hD, abs_le]
    constructor <;> nlinarith [mul_nonneg hc hu, mul_nonneg hu hu]
  rw [key, abs_div, abs_mul, abs_of_nonneg (sq_nonneg u),
    abs_of_pos (mul_pos hDpos (by positivity)), div_le_iff₀ (by positivity)]
  have h12 : 12 * (u ^ 3 / w ^ 3) * (D * w ^ 2) = 12 * u ^ 3 * D / w := by
    field_simp
  rw [h12, le_div_iff₀ hw]
  have hu3 : 0 ≤ u ^ 3 := by positivity
  calc u ^ 2 * |w ^ 2 - D| * w ≤ u ^ 2 * (25 / 4 * w * u) * w := by gcongr
    _ = 25 / 4 * u ^ 3 * w ^ 2 := by ring
    _ ≤ 12 * u ^ 3 * D := by nlinarith [mul_le_mul_of_nonneg_left hDlow hu3]

/-! ### A polarizable system -/

/-- The cross section of a system with the polarizability `α`, the dipole `d = α E` induced by the
field, for the polarization `ê` of a wave of the frequency `ω`:
`σ = (2/3)(1/4π) ω⁴ |α ê|²` (Landau–Lifshitz §79). -/
def polarizabilityCrossSection (ω : ℝ) (α : E3 →ₗ[ℝ] E3) (ê : E3) : ℝ :=
  2 / 3 * (1 / (4 * π)) * ω ^ 4 * ‖α ê‖ ^ 2

/-- The dipole `d(t) = α E(t, 0)` induced by the plane wave of `incidentPotential` has
`d̈ = −ω² d`; its averaged power of Larmor `⟨(2/3)(1/4π)|d̈|²⟩` (`crossSection` with the charge
`1` and the acceleration `d̈`) divided by the averaged incident flux is
`polarizabilityCrossSection ω α (E₀/|E₀|)`. -/
theorem crossSection_polarizable {ω : ℝ} (hω : ω ≠ 0) {u E₀ : E3} (hu : ‖u‖ = 1)
    (huE : inner ℝ u E₀ = 0) (hE₀ : E₀ ≠ 0) (α : E3 →ₗ[ℝ] E3) :
    crossSection 1 ω (fun t => -(ω ^ 2) • α (waveElectric ω u E₀ t 0)) (incidentFlux ω u E₀ 0) =
      polarizabilityCrossSection ω α (‖E₀‖⁻¹ • E₀) := by
  have h : (fun t => 2 / 3 * ((1 : ℝ) ^ 2 / (4 * π)) *
      ‖-(ω ^ 2) • α (waveElectric ω u E₀ t 0)‖ ^ 2) =
      fun t => 2 / 3 * (1 / (4 * π)) * ω ^ 4 * ‖α E₀‖ ^ 2 * Real.cos (ω * t + 0) ^ 2 := by
    funext t
    rw [waveElectric, inner_zero_right, sub_zero, map_smul, norm_smul, norm_smul,
      Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs, add_zero]
    ring
  have hE : ‖E₀‖ ≠ 0 := norm_ne_zero_iff.mpr hE₀
  rw [crossSection, incidentFlux_eq hω hu huE, h, periodAverage_const_mul,
    periodAverage_cos_sq hω, polarizabilityCrossSection, map_smul, norm_smul, norm_inv,
    norm_norm]
  field_simp

/-- **The average over orientations** (Landau–Lifshitz §79): for a symmetric polarizability `α`,
the mean of `|α ê|²` over the directions `ê` of the polarization is `tr(α²)/3`. For a fixed
polarization it is also the mean over the orientations of the system, since the surface measure
of the sphere is invariant under rotations (`integral_comp_linearIsometryEquiv`). The proof
expands `|α ê|² = Σᵢ ⟨ê, α eᵢ⟩²` in an orthonormal basis and uses the second moment
`∫ ⟨ê, a⟩² dσ = (4π/3)|a|²`. -/
theorem orientationAverage (α : E3 →ₗ[ℝ] E3) (hα : α.IsSymmetric) :
    (4 * π)⁻¹ * ∫ ê : sphere (0 : E3) 1, ‖α ê‖ ^ 2 ∂sphereMeasure =
      LinearMap.trace ℝ E3 (α ∘ₗ α) / 3 := by
  set b := EuclideanSpace.basisFun (Fin 3) ℝ
  have h1 : ∀ ê : E3, ‖α ê‖ ^ 2 = ∑ i, inner ℝ ê (α (b i)) ^ 2 := by
    intro ê
    rw [← b.sum_sq_norm_inner_right (α ê)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.norm_eq_abs, sq_abs, ← hα (b i) ê, real_inner_comm]
  have h2 : LinearMap.trace ℝ E3 (α ∘ₗ α) = ∑ i, ‖α (b i)‖ ^ 2 := by
    rw [LinearMap.trace_eq_sum_inner _ b]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.comp_apply, ← hα, real_inner_self_eq_norm_sq]
  simp_rw [h1]
  rw [integral_finsetSum _ (fun i _ => integrable_of_continuous (by fun_prop))]
  simp_rw [integral_inner_sq]
  rw [h2, ← Finset.mul_sum]
  field_simp

/-- The average of the cross section over orientations:
`⟨σ⟩ = (2/3)(1/4π) ω⁴ tr(α²)/3`. -/
theorem orientationAverage_polarizabilityCrossSection (ω : ℝ) (α : E3 →ₗ[ℝ] E3)
    (hα : α.IsSymmetric) :
    (4 * π)⁻¹ * ∫ ê : sphere (0 : E3) 1, polarizabilityCrossSection ω α ê ∂sphereMeasure =
      2 / 3 * (1 / (4 * π)) * ω ^ 4 * (LinearMap.trace ℝ E3 (α ∘ₗ α) / 3) := by
  simp only [polarizabilityCrossSection]
  rw [integral_const_mul, ← orientationAverage α hα]
  ring

/-- An isotropic polarizability `c · 1` is symmetric. -/
theorem isSymmetric_smul_id (c : ℝ) : (c • LinearMap.id : E3 →ₗ[ℝ] E3).IsSymmetric := by
  intro x y
  simp [real_inner_smul_left, real_inner_smul_right]

/-- For an isotropic polarizability `c · 1`, `tr(α²)/3 = c²`. -/
theorem trace_smul_id_comp (c : ℝ) :
    LinearMap.trace ℝ E3 ((c • LinearMap.id) ∘ₗ (c • LinearMap.id)) / 3 = c ^ 2 := by
  rw [LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.id_comp, smul_smul, map_smul,
    LinearMap.trace_id, finrank_euclideanSpace_fin]
  simp only [smul_eq_mul, Nat.cast_ofNat]
  ring

/-- **The static polarizability of the bound charge** `α = e²/(m ω₀²)` gives Rayleigh's leading
term: `σ = σ_T (ω/ω₀)⁴` for every unit polarization. -/
theorem polarizabilityCrossSection_bound (e m ω₀ ω : ℝ) {ê : E3} (hê : ‖ê‖ = 1) :
    polarizabilityCrossSection ω ((e ^ 2 / (m * ω₀ ^ 2)) • LinearMap.id) ê =
      thomsonCrossSection e m * (ω / ω₀) ^ 4 := by
  rw [polarizabilityCrossSection, LinearMap.smul_apply, LinearMap.id_apply, norm_smul, hê,
    mul_one, Real.norm_eq_abs, sq_abs, thomsonCrossSection]
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne ω₀ 0 with rfl | hω₀
  · simp
  field_simp
  ring

end ProjectAinos.Electrodynamics.Scattering.LowFrequency
