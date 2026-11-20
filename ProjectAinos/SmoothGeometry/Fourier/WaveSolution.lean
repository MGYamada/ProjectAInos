/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Tactic

/-!
# The Fourier solution of the wave equation

Space is `EuclideanSpace ℝ (Fin 3)`. The Fourier transform has Mathlib's normalization
`𝓕 f(ξ) = ∫ e^{−2πi⟪x, ξ⟫} f(x) dx`, so that a frequency `ξ` has the angular frequency
`2π‖ξ‖` in the wave equation `∂ₜ²u = Δu`. For Schwartz data `u₀, u₁`,

`waveSolution u₀ u₁ t x = ∫ (cos(2π‖ξ‖t) 𝓕u₀(ξ) + sin(2π‖ξ‖t)/(2π‖ξ‖) 𝓕u₁(ξ)) e^{2πi⟪x, ξ⟫} dξ`.

* `sinPropagator t ξ = sin(2π‖ξ‖t)/(2π‖ξ‖)`, with the value `t` at `ξ = 0`, is `t sinc(2π‖ξ‖t)`.
* `waveSolution_eq_fourierIntegral`: the solution is the Fourier integral of the density
  `coneDensity u₀ u₁` with respect to `coneMeasure`, the image of Lebesgue measure on the two
  sheets `s = ±‖ξ‖` of the light cone in `ℝ × ℝ³`.
* `contDiff_waveSolution`: the solution is smooth in `(t, x)`.
* `wave_iteratedFDeriv_waveSolution` and `wave_waveSolution`: `−∂ₜ²u + Δₓu = 0` on `ℝ × ℝ³`;
  the second derivatives are the Fourier integrals of `(2πi s)²` and `(2πiηⱼ)²` times the
  density, which cancel on the cone `s² = ‖η‖²`.
* `waveSolution_zero` and `deriv_waveSolution_zero`: the initial data are `u₀` and `u₁`, by the
  Fourier inversion on the Schwartz space; `hasDerivAt_waveSolution` gives the velocity at every
  time.
* `fourierEnergy_waveSolution`: for each frequency the energy `|∂ₜû|² + (2π‖ξ‖)² |û|²` of the
  amplitude `û(t, ξ)` is conserved.
* `im_waveSolution`: for real data the solution is real.

Whether the solution is a Schwartz function at each time is not proved.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Real
open scoped FourierTransform RealInnerProductSpace Laplacian ContDiff Topology SchwartzMap

namespace ProjectAinos.SmoothGeometry.Fourier

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### The propagators -/

/-- The propagator `sin(2π‖ξ‖t)/(2π‖ξ‖)` of the initial velocity, written `t sinc(2π‖ξ‖t)`; its
value at `ξ = 0` is `t`. -/
def sinPropagator (t : ℝ) (ξ : E3) : ℝ := t * Real.sinc (2 * π * ‖ξ‖ * t)

/-- Away from `ξ = 0`, the propagator is `sin(2π‖ξ‖t)/(2π‖ξ‖)`. -/
theorem sinPropagator_of_ne_zero {ξ : E3} (hξ : ξ ≠ 0) (t : ℝ) :
    sinPropagator t ξ = Real.sin (2 * π * ‖ξ‖ * t) / (2 * π * ‖ξ‖) := by
  have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
  rcases eq_or_ne t 0 with rfl | ht
  · simp [sinPropagator]
  · rw [sinPropagator, Real.sinc_of_ne_zero (by positivity)]
    field_simp

/-- At `ξ = 0` the propagator is `t`. -/
@[simp] theorem sinPropagator_zero_right (t : ℝ) : sinPropagator t 0 = t := by
  simp [sinPropagator]

/-- At `t = 0` the propagator vanishes. -/
@[simp] theorem sinPropagator_zero_left (ξ : E3) : sinPropagator 0 ξ = 0 := by
  simp [sinPropagator]

/-- `2π‖ξ‖ · sinPropagator t ξ = sin(2π‖ξ‖t)`, also at `ξ = 0`. -/
theorem mul_sinPropagator (t : ℝ) (ξ : E3) :
    2 * π * ‖ξ‖ * sinPropagator t ξ = Real.sin (2 * π * ‖ξ‖ * t) := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp
  · have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
    rw [sinPropagator_of_ne_zero hξ]
    field_simp

/-- The propagator is bounded by `|t|`. -/
theorem abs_sinPropagator_le (t : ℝ) (ξ : E3) : |sinPropagator t ξ| ≤ |t| := by
  rw [sinPropagator, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg t) (Real.abs_sinc_le_one _)

/-- The propagator is continuous in `(t, ξ)`. -/
theorem continuous_sinPropagator : Continuous fun p : ℝ × E3 => sinPropagator p.1 p.2 := by
  unfold sinPropagator
  fun_prop

/-- The time derivative of the propagator is `cos(2π‖ξ‖t)`. -/
theorem hasDerivAt_sinPropagator (t : ℝ) (ξ : E3) :
    HasDerivAt (fun s => sinPropagator s ξ) (Real.cos (2 * π * ‖ξ‖ * t)) t := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simpa using hasDerivAt_id' t
  · have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
    have hk : 2 * π * ‖ξ‖ ≠ 0 := by positivity
    have h := ((hasDerivAt_id t).const_mul (2 * π * ‖ξ‖)).sin.div_const (2 * π * ‖ξ‖)
    simp only [mul_one, id] at h
    rw [mul_div_cancel_right₀ _ hk] at h
    convert h using 1
    funext s
    exact sinPropagator_of_ne_zero hξ s

/-! ### The amplitudes on the Fourier side -/

/-- The amplitude `û(t, ξ) = cos(2π‖ξ‖t) 𝓕u₀(ξ) + sin(2π‖ξ‖t)/(2π‖ξ‖) 𝓕u₁(ξ)` of the
solution. -/
def waveAmplitude (u₀ u₁ : 𝓢(E3, ℂ)) (t : ℝ) (ξ : E3) : ℂ :=
  (Real.cos (2 * π * ‖ξ‖ * t) : ℂ) * 𝓕 u₀ ξ + (sinPropagator t ξ : ℂ) * 𝓕 u₁ ξ

/-- The velocity amplitude `∂ₜû(t, ξ) = −2π‖ξ‖ sin(2π‖ξ‖t) 𝓕u₀(ξ) + cos(2π‖ξ‖t) 𝓕u₁(ξ)`. -/
def waveVelocity (u₀ u₁ : 𝓢(E3, ℂ)) (t : ℝ) (ξ : E3) : ℂ :=
  ((-(2 * π * ‖ξ‖ * Real.sin (2 * π * ‖ξ‖ * t)) : ℝ) : ℂ) * 𝓕 u₀ ξ +
    (Real.cos (2 * π * ‖ξ‖ * t) : ℂ) * 𝓕 u₁ ξ

/-- The time derivative of the amplitude is the velocity amplitude. -/
theorem hasDerivAt_waveAmplitude (u₀ u₁ : 𝓢(E3, ℂ)) (t : ℝ) (ξ : E3) :
    HasDerivAt (fun s => waveAmplitude u₀ u₁ s ξ) (waveVelocity u₀ u₁ t ξ) t := by
  have hc : HasDerivAt (fun s => Real.cos (2 * π * ‖ξ‖ * s))
      (-Real.sin (2 * π * ‖ξ‖ * t) * (2 * π * ‖ξ‖)) t := by
    simpa using ((hasDerivAt_id t).const_mul (2 * π * ‖ξ‖)).cos
  have h := ((hc.ofReal_comp).mul_const (𝓕 u₀ ξ)).add
    ((hasDerivAt_sinPropagator t ξ).ofReal_comp.mul_const (𝓕 u₁ ξ))
  unfold waveAmplitude
  convert h using 1
  rw [waveVelocity]
  push_cast
  ring

/-- **Conservation of the energy of each frequency**: `|∂ₜû|² + (2π‖ξ‖)² |û|²` does not depend on
the time. -/
theorem fourierEnergy_waveSolution (u₀ u₁ : 𝓢(E3, ℂ)) (t : ℝ) (ξ : E3) :
    ‖waveVelocity u₀ u₁ t ξ‖ ^ 2 + (2 * π * ‖ξ‖) ^ 2 * ‖waveAmplitude u₀ u₁ t ξ‖ ^ 2 =
      ‖𝓕 u₁ ξ‖ ^ 2 + (2 * π * ‖ξ‖) ^ 2 * ‖𝓕 u₀ ξ‖ ^ 2 := by
  have hS := mul_sinPropagator t ξ
  have hcs := Real.sin_sq_add_cos_sq (2 * π * ‖ξ‖ * t)
  have key (a b : ℝ) (A B : ℂ) : ‖(a : ℂ) * A + (b : ℂ) * B‖ ^ 2 =
      a ^ 2 * (A.re ^ 2 + A.im ^ 2) + 2 * a * b * (A.re * B.re + A.im * B.im) +
        b ^ 2 * (B.re ^ 2 + B.im ^ 2) := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have h1 : (2 * π * ‖ξ‖) ^ 2 * ‖waveAmplitude u₀ u₁ t ξ‖ ^ 2 =
      ‖((2 * π * ‖ξ‖ * Real.cos (2 * π * ‖ξ‖ * t) : ℝ) : ℂ) * 𝓕 u₀ ξ +
        ((2 * π * ‖ξ‖ * sinPropagator t ξ : ℝ) : ℂ) * 𝓕 u₁ ξ‖ ^ 2 := by
    rw [show ((2 * π * ‖ξ‖ * Real.cos (2 * π * ‖ξ‖ * t) : ℝ) : ℂ) * 𝓕 u₀ ξ +
        ((2 * π * ‖ξ‖ * sinPropagator t ξ : ℝ) : ℂ) * 𝓕 u₁ ξ =
        ((2 * π * ‖ξ‖ : ℝ) : ℂ) * waveAmplitude u₀ u₁ t ξ by rw [waveAmplitude]; push_cast; ring]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * π * ‖ξ‖)]
    ring
  rw [h1, hS, waveVelocity, key, key, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
    Complex.normSq_apply]
  linear_combination ((2 * π * ‖ξ‖) ^ 2 * ((𝓕 u₀ ξ).re ^ 2 + (𝓕 u₀ ξ).im ^ 2) +
    ((𝓕 u₁ ξ).re ^ 2 + (𝓕 u₁ ξ).im ^ 2)) * hcs

/-! ### The solution formula -/

/-- **The Fourier solution of the wave equation** with the initial value `u₀` and the initial
velocity `u₁`:
`u(t, x) = ∫ (cos(2π‖ξ‖t) 𝓕u₀(ξ) + sin(2π‖ξ‖t)/(2π‖ξ‖) 𝓕u₁(ξ)) e^{2πi⟪x, ξ⟫} dξ`. -/
def waveSolution (u₀ u₁ : 𝓢(E3, ℂ)) (t : ℝ) (x : E3) : ℂ :=
  ∫ ξ : E3, waveAmplitude u₀ u₁ t ξ * 𝐞 ⟪x, ξ⟫

/-- The solution at time `t` is the inverse Fourier transform of the amplitude. -/
theorem waveSolution_eq_fourierInv (u₀ u₁ : 𝓢(E3, ℂ)) (t : ℝ) :
    waveSolution u₀ u₁ t = 𝓕⁻ (waveAmplitude u₀ u₁ t) := by
  funext x
  rw [waveSolution, Real.fourierInv_eq]
  congr 1
  funext ξ
  rw [Circle.smul_def, smul_eq_mul, mul_comm, real_inner_comm]

/-! ### The light cone -/

/-- The pairing `−(s t + ⟪η, x⟫)` of a point `(s, η)` of the cone with a point `(t, x)`, so that
`𝐞(−conePairing v w)` is the plane wave `e^{2πi(st + ⟪η, x⟫)}`. -/
def conePairing : (ℝ × E3) →L[ℝ] (ℝ × E3) →L[ℝ] ℝ :=
  -((ContinuousLinearMap.mul ℝ ℝ).bilinearComp (ContinuousLinearMap.fst ℝ ℝ E3)
      (ContinuousLinearMap.fst ℝ ℝ E3) +
    ((innerSL ℝ (E := E3)).bilinearComp (ContinuousLinearMap.snd ℝ ℝ E3)
      (ContinuousLinearMap.snd ℝ ℝ E3) : (ℝ × E3) →L[ℝ] (ℝ × E3) →L[ℝ] ℝ))

/-- The pairing in co-ordinates. -/
@[simp] theorem conePairing_apply (v w : ℝ × E3) :
    conePairing v w = -(v.1 * w.1 + ⟪v.2, w.2⟫) := by
  simp [conePairing]

/-- The measure on the light cone `s² = ‖η‖²` of `ℝ × ℝ³`: the sum of the images of Lebesgue
measure under `ξ ↦ (‖ξ‖, ξ)` and `ξ ↦ (−‖ξ‖, ξ)`. -/
def coneMeasure : Measure (ℝ × E3) :=
  Measure.map (fun ξ : E3 => (‖ξ‖, ξ)) volume + Measure.map (fun ξ : E3 => (-‖ξ‖, ξ)) volume

/-- The density `𝓕u₀(η)/2 + 𝓕u₁(η)/(4πis)` on the cone; its value at `s = 0` is `𝓕u₀(η)/2`. -/
def coneDensity (u₀ u₁ : 𝓢(E3, ℂ)) (v : ℝ × E3) : ℂ :=
  2⁻¹ * 𝓕 u₀ v.2 + (4 * π * Complex.I * v.1)⁻¹ * 𝓕 u₁ v.2

/-- The lift `ξ ↦ (‖ξ‖, ξ)` to the upper sheet is measurable. -/
private theorem aemeasurable_liftPlus : AEMeasurable (fun ξ : E3 => (‖ξ‖, ξ)) volume :=
  (by fun_prop : Continuous fun ξ : E3 => (‖ξ‖, ξ)).measurable.aemeasurable

/-- The lift `ξ ↦ (−‖ξ‖, ξ)` to the lower sheet is measurable. -/
private theorem aemeasurable_liftMinus : AEMeasurable (fun ξ : E3 => (-‖ξ‖, ξ)) volume :=
  (by fun_prop : Continuous fun ξ : E3 => (-‖ξ‖, ξ)).measurable.aemeasurable

/-- Almost every point of the cone measure lies on the cone `s² = ‖η‖²`. -/
theorem ae_coneMeasure : ∀ᵐ v ∂coneMeasure, v.1 ^ 2 = ‖v.2‖ ^ 2 := by
  have hs : MeasurableSet {v : ℝ × E3 | v.1 ^ 2 = ‖v.2‖ ^ 2} :=
    (isClosed_eq (by fun_prop) (by fun_prop)).measurableSet
  rw [coneMeasure, ae_add_measure_iff, ae_map_iff aemeasurable_liftPlus hs,
    ae_map_iff aemeasurable_liftMinus hs]
  exact ⟨Eventually.of_forall fun ξ => by simp, Eventually.of_forall fun ξ => by simp⟩

/-- A function is integrable for the cone measure if it is integrable on both sheets. -/
theorem integrable_coneMeasure {G : Type*} [NormedAddCommGroup G] {h : ℝ × E3 → G}
    (hm : AEStronglyMeasurable h coneMeasure) (hp : Integrable fun ξ : E3 => h (‖ξ‖, ξ))
    (hn : Integrable fun ξ : E3 => h (-‖ξ‖, ξ)) : Integrable h coneMeasure := by
  rw [coneMeasure, aestronglyMeasurable_add_measure_iff] at hm
  rw [coneMeasure]
  exact ((integrable_map_measure hm.1 aemeasurable_liftPlus).2 hp).add_measure
    ((integrable_map_measure hm.2 aemeasurable_liftMinus).2 hn)

/-- The integral for the cone measure is the integral over `ℝ³` of the sum of the values on the
two sheets. -/
theorem integral_coneMeasure {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {h : ℝ × E3 → G} (hh : Integrable h coneMeasure) :
    ∫ v, h v ∂coneMeasure = ∫ ξ : E3, (h (‖ξ‖, ξ) + h (-‖ξ‖, ξ)) := by
  have h₁ : Integrable h (Measure.map (fun ξ : E3 => (‖ξ‖, ξ)) volume) :=
    hh.mono_measure (Measure.le_add_right le_rfl)
  have h₂ : Integrable h (Measure.map (fun ξ : E3 => (-‖ξ‖, ξ)) volume) :=
    hh.mono_measure (Measure.le_add_left le_rfl)
  rw [coneMeasure, integral_add_measure h₁ h₂, integral_map aemeasurable_liftPlus
    h₁.aestronglyMeasurable, integral_map aemeasurable_liftMinus h₂.aestronglyMeasurable]
  exact (integral_add ((integrable_map_measure h₁.aestronglyMeasurable aemeasurable_liftPlus).1 h₁)
      ((integrable_map_measure h₂.aestronglyMeasurable aemeasurable_liftMinus).1 h₂)).symm

/-! ### Integrability of the density -/

/-- `‖ξ‖⁻¹ ‖g(ξ)‖` is integrable on `ℝ³` for a Schwartz function `g`. -/
private theorem integrable_norm_inv_mul (g : 𝓢(E3, ℂ)) :
    Integrable fun ξ : E3 => ‖ξ‖⁻¹ * ‖g ξ‖ := by
  have hloc : LocallyIntegrable (fun ξ : E3 => ‖ξ‖⁻¹) volume := by
    refine locallyIntegrable_of_norm_le_rpow (by simp) (α := 1) (C := 1) (by simp)
      (Eventually.of_forall fun x => ?_) measurable_norm.inv.aestronglyMeasurable
    simp [Real.rpow_neg_one]
  have hball : IntegrableOn (fun ξ : E3 => ‖ξ‖⁻¹) (Metric.closedBall 0 1) :=
    hloc.integrableOn_isCompact (isCompact_closedBall 0 1)
  set C := SchwartzMap.seminorm ℝ 0 0 g
  have hb (ξ : E3) : ‖g ξ‖ ≤ C := SchwartzMap.norm_le_seminorm ℝ g ξ
  refine (((hball.integrable_indicator Metric.isClosed_closedBall.measurableSet).const_mul
    C).add g.integrable.norm).mono' ?_ (Eventually.of_forall fun ξ => ?_)
  · exact (measurable_norm.inv.mul g.continuous.norm.measurable).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity)]
    have h0 := norm_nonneg (g ξ)
    have h1 := inv_nonneg.2 (norm_nonneg ξ)
    simp only [Pi.add_apply, indicator, Metric.mem_closedBall, dist_zero_right]
    split_ifs with hξ
    · have := mul_le_mul_of_nonneg_left (hb ξ) h1
      nlinarith
    · have : ‖ξ‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (le_of_lt (not_le.1 hξ))
      nlinarith

/-- `‖ξ‖ⁿ ‖ξ‖⁻¹ ‖g(ξ)‖` is integrable on `ℝ³` for a Schwartz function `g`. -/
private theorem integrable_pow_mul_norm_inv_mul (g : 𝓢(E3, ℂ)) (n : ℕ) :
    Integrable fun ξ : E3 => ‖ξ‖ ^ n * (‖ξ‖⁻¹ * ‖g ξ‖) := by
  rcases n with _ | m
  · simpa using integrable_norm_inv_mul g
  · refine (g.integrable_pow_mul volume m).mono' (by fun_prop) (Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_of_nonneg (by positivity), ← mul_assoc]
    gcongr
    rcases eq_or_ne ξ 0 with rfl | hξ
    · simp
    · rw [pow_succ, mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hξ), mul_one]

/-- The density is measurable. -/
private theorem measurable_coneDensity (u₀ u₁ : 𝓢(E3, ℂ)) : Measurable (coneDensity u₀ u₁) := by
  unfold coneDensity
  have h₀ := (𝓕 u₀).continuous.measurable
  have h₁ := (𝓕 u₁).continuous.measurable
  fun_prop

/-- On the sheet `s = σ‖ξ‖` with `|σ| = 1`, `|f| ≤ |𝓕u₀|/2 + |𝓕u₁|/(4π‖ξ‖)`. -/
private theorem norm_coneDensity_le (u₀ u₁ : 𝓢(E3, ℂ)) (σ : ℝ) (hσ : |σ| = 1) (ξ : E3) :
    ‖coneDensity u₀ u₁ (σ * ‖ξ‖, ξ)‖ ≤ 2⁻¹ * ‖𝓕 u₀ ξ‖ + (4 * π)⁻¹ * (‖ξ‖⁻¹ * ‖𝓕 u₁ ξ‖) := by
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  simp only [norm_mul, norm_inv, Complex.norm_I, Complex.norm_real, Complex.norm_ofNat,
    Real.norm_eq_abs, hσ, abs_norm, abs_of_pos pi_pos]
  ring

/-- The norm of `(σ‖ξ‖, ξ)` in `ℝ × ℝ³` is `‖ξ‖` when `|σ| = 1`. -/
private theorem norm_lift (σ : ℝ) (hσ : |σ| = 1) (ξ : E3) : ‖((σ * ‖ξ‖, ξ) : ℝ × E3)‖ = ‖ξ‖ := by
  simp [Prod.norm_def, hσ]

/-- The moments `‖v‖ⁿ ‖coneDensity u₀ u₁ v‖` are integrable for the cone measure. -/
theorem integrable_pow_mul_coneDensity (u₀ u₁ : 𝓢(E3, ℂ)) (n : ℕ) :
    Integrable (fun v : ℝ × E3 => ‖v‖ ^ n * ‖coneDensity u₀ u₁ v‖) coneMeasure := by
  have hbound : Integrable fun ξ : E3 =>
      2⁻¹ * (‖ξ‖ ^ n * ‖𝓕 u₀ ξ‖) + (4 * π)⁻¹ * (‖ξ‖ ^ n * (‖ξ‖⁻¹ * ‖𝓕 u₁ ξ‖)) :=
    (((𝓕 u₀).integrable_pow_mul volume n).const_mul _).add
      ((integrable_pow_mul_norm_inv_mul (𝓕 u₁) n).const_mul _)
  have hsheet (σ : ℝ) (hσ : |σ| = 1) :
      Integrable fun ξ : E3 => ‖((σ * ‖ξ‖, ξ) : ℝ × E3)‖ ^ n *
        ‖coneDensity u₀ u₁ (σ * ‖ξ‖, ξ)‖ := by
    refine hbound.mono' ?_ (Eventually.of_forall fun ξ => ?_)
    · exact ((by fun_prop : Continuous fun ξ : E3 => ((σ * ‖ξ‖, ξ) : ℝ × E3)).norm.pow n
        |>.aestronglyMeasurable).mul ((measurable_coneDensity u₀ u₁).comp
          (by fun_prop : Continuous fun ξ : E3 => ((σ * ‖ξ‖, ξ) : ℝ × E3)).measurable
            |>.norm.aestronglyMeasurable)
    · rw [Real.norm_of_nonneg (by positivity), norm_lift σ hσ]
      calc ‖ξ‖ ^ n * ‖coneDensity u₀ u₁ (σ * ‖ξ‖, ξ)‖
          ≤ ‖ξ‖ ^ n * (2⁻¹ * ‖𝓕 u₀ ξ‖ + (4 * π)⁻¹ * (‖ξ‖⁻¹ * ‖𝓕 u₁ ξ‖)) := by
            gcongr
            exact norm_coneDensity_le u₀ u₁ σ hσ ξ
        _ = _ := by ring
  refine integrable_coneMeasure ((continuous_norm.pow n).aestronglyMeasurable.mul
    (measurable_coneDensity u₀ u₁).norm.aestronglyMeasurable) ?_ ?_
  · simpa using hsheet 1 (by simp)
  · simpa using hsheet (-1) (by simp)

/-- The density is integrable for the cone measure. -/
theorem integrable_coneDensity (u₀ u₁ : 𝓢(E3, ℂ)) : Integrable (coneDensity u₀ u₁) coneMeasure :=
  (integrable_norm_iff (measurable_coneDensity u₀ u₁).aestronglyMeasurable).1
    (by simpa using integrable_pow_mul_coneDensity u₀ u₁ 0)

/-! ### The solution as a Fourier integral on the cone -/

/-- `𝐞(at) = cos(2πat) + i sin(2πat)`. -/
private theorem coe_fourierChar_mul (a t : ℝ) :
    ((𝐞 (a * t) : Circle) : ℂ) =
      (Real.cos (2 * π * a * t) : ℂ) + (Real.sin (2 * π * a * t) : ℂ) * Complex.I := by
  have h : (2 * π * (a * t) : ℝ) = 2 * π * a * t := by ring
  rw [Real.fourierChar_apply, h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- `𝐞(−at) = cos(2πat) − i sin(2πat)`. -/
private theorem coe_fourierChar_neg_mul (a t : ℝ) :
    ((𝐞 (-(a * t)) : Circle) : ℂ) =
      (Real.cos (2 * π * a * t) : ℂ) - (Real.sin (2 * π * a * t) : ℂ) * Complex.I := by
  have h : (2 * π * -(a * t) : ℝ) = -(2 * π * a * t) := by ring
  rw [Real.fourierChar_apply, h, Complex.ofReal_neg, Complex.exp_mul_I, Complex.cos_neg,
    Complex.sin_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring

/-- Away from `ξ = 0`, the integrand of the solution is the sum of the integrands of the Fourier
integral on the two sheets of the cone. -/
private theorem waveIntegrand_eq (u₀ u₁ : 𝓢(E3, ℂ)) (t : ℝ) (x : E3) {ξ : E3} (hξ : ξ ≠ 0) :
    waveAmplitude u₀ u₁ t ξ * 𝐞 ⟪x, ξ⟫ =
      𝐞 (-conePairing (‖ξ‖, ξ) (t, x)) • coneDensity u₀ u₁ (‖ξ‖, ξ) +
        𝐞 (-conePairing (-‖ξ‖, ξ) (t, x)) • coneDensity u₀ u₁ (-‖ξ‖, ξ) := by
  have hn : (‖ξ‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hξ
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
  simp only [conePairing_apply, neg_neg, neg_mul, Circle.smul_def, smul_eq_mul,
    AddChar.map_add_eq_mul, Circle.coe_mul, coe_fourierChar_mul, coe_fourierChar_neg_mul]
  rw [waveAmplitude, coneDensity, coneDensity, sinPropagator_of_ne_zero hξ, real_inner_comm]
  push_cast
  field_simp
  ring

/-- **The solution formula on the cone**: `u(t, x) = ∫ e^{2πi(st + ⟪η, x⟫)} f(s, η) dμ(s, η)`,
the Fourier integral of the density `f = coneDensity u₀ u₁` for the cone measure `μ`. -/
theorem uncurry_waveSolution (u₀ u₁ : 𝓢(E3, ℂ)) :
    Function.uncurry (waveSolution u₀ u₁) = VectorFourier.fourierIntegral 𝐞 coneMeasure
      conePairing.toLinearMap₁₂ (coneDensity u₀ u₁) := by
  funext p
  have hint : Integrable (fun v => 𝐞 (-conePairing.toLinearMap₁₂ v p) • coneDensity u₀ u₁ v)
      coneMeasure :=
    (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar
      (by exact conePairing.continuous₂) p).2 (integrable_coneDensity u₀ u₁)
  rw [VectorFourier.fourierIntegral, integral_coneMeasure hint]
  refine integral_congr_ae ?_
  filter_upwards [Measure.ae_ne volume (0 : E3)] with ξ hξ
  simpa using waveIntegrand_eq u₀ u₁ p.1 p.2 hξ

/-- The solution formula on the cone at a point `(t, x)`. -/
theorem waveSolution_eq_fourierIntegral (u₀ u₁ : 𝓢(E3, ℂ)) (t : ℝ) (x : E3) :
    waveSolution u₀ u₁ t x = VectorFourier.fourierIntegral 𝐞 coneMeasure
      conePairing.toLinearMap₁₂ (coneDensity u₀ u₁) (t, x) := by
  rw [← uncurry_waveSolution]
  rfl

/-- The solution is smooth in `(t, x)`. -/
theorem contDiff_waveSolution (u₀ u₁ : 𝓢(E3, ℂ)) {n : ℕ∞} :
    ContDiff ℝ n (Function.uncurry (waveSolution u₀ u₁)) := by
  rw [uncurry_waveSolution]
  exact VectorFourier.contDiff_fourierIntegral conePairing fun k _ =>
    integrable_pow_mul_coneDensity u₀ u₁ k

/-- The derivatives of the solution are the Fourier integrals of the moments of the density. -/
theorem iteratedFDeriv_waveSolution (u₀ u₁ : 𝓢(E3, ℂ)) (k : ℕ) :
    iteratedFDeriv ℝ k (Function.uncurry (waveSolution u₀ u₁)) =
      VectorFourier.fourierIntegral 𝐞 coneMeasure conePairing.toLinearMap₁₂
        (fun v => VectorFourier.fourierPowSMulRight conePairing (coneDensity u₀ u₁) v k) := by
  rw [uncurry_waveSolution]
  exact VectorFourier.iteratedFDeriv_fourierIntegral conePairing (N := ⊤)
    (fun k _ => integrable_pow_mul_coneDensity u₀ u₁ k)
    (measurable_coneDensity u₀ u₁).aestronglyMeasurable le_top

/-- **The wave equation for the second derivatives**: `−∂ₜ²u + Σⱼ ∂ⱼ²u = 0` at every point of
`ℝ × ℝ³`, written with the second derivative of `(t, x) ↦ u(t, x)`. -/
theorem wave_iteratedFDeriv_waveSolution (u₀ u₁ : 𝓢(E3, ℂ)) (p : ℝ × E3) :
    -iteratedFDeriv ℝ 2 (Function.uncurry (waveSolution u₀ u₁)) p (fun _ => (1, 0)) +
      ∑ i : Fin 3, iteratedFDeriv ℝ 2 (Function.uncurry (waveSolution u₀ u₁)) p
        (fun _ => (0, EuclideanSpace.single i 1)) = 0 := by
  have hg : Integrable (fun v => VectorFourier.fourierPowSMulRight conePairing
      (coneDensity u₀ u₁) v 2) coneMeasure :=
    VectorFourier.integrable_fourierPowSMulRight conePairing
      (integrable_pow_mul_coneDensity u₀ u₁ 2) (measurable_coneDensity u₀ u₁).aestronglyMeasurable
  have hgm (m : ℝ × E3) : Integrable (fun v => 𝐞 (-conePairing.toLinearMap₁₂ v p) •
      VectorFourier.fourierPowSMulRight conePairing (coneDensity u₀ u₁) v 2 (fun _ => m))
      coneMeasure :=
    (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar
      (by exact conePairing.continuous₂) p).2
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℝ × E3) ℂ
        (fun _ => m)).integrable_comp hg)
  rw [iteratedFDeriv_waveSolution]
  simp only [Real.fourierIntegral_continuousMultilinearMap_apply' hg]
  simp only [VectorFourier.fourierIntegral]
  rw [← integral_neg, ← integral_finsetSum _ (fun i _ => hgm _), ← integral_add]
  rotate_left
  · exact (hgm _).neg
  · exact integrable_finsetSum _ fun i _ => hgm _
  refine integral_eq_zero_of_ae ?_
  filter_upwards [ae_coneMeasure] with v hv
  simp only [VectorFourier.fourierPowSMulRight_apply, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply, conePairing_apply,
    mul_one, mul_zero, inner_zero_right, add_zero, zero_add, EuclideanSpace.inner_single_right,
    one_mul, conj_trivial, neg_sq]
  have h : ∑ i : Fin 3, v.2 i ^ 2 = v.1 ^ 2 := by rw [hv, EuclideanSpace.real_norm_sq_eq]
  rw [← Finset.smul_sum, ← Finset.smul_sum, ← Finset.sum_smul, h, neg_add_cancel, Pi.zero_apply]

/-! ### The wave equation in the variables `t` and `x` -/

/-- The second derivative of `z ↦ U(a + g z)` for a linear map `g`. -/
private theorem iteratedFDeriv_two_comp_affine {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {U : ℝ × E3 → ℂ} (hU : ContDiff ℝ 2 U) (a : ℝ × E3)
    (g : G →L[ℝ] ℝ × E3) (y : G) (m : Fin 2 → G) :
    iteratedFDeriv ℝ 2 (fun z => U (a + g z)) y m =
      iteratedFDeriv ℝ 2 U (a + g y) (fun j => g (m j)) := by
  have h : (fun z => U (a + g z)) = (fun q => U (a + q)) ∘ g := rfl
  have hc : ContDiff ℝ 2 fun q => U (a + q) := hU.comp (contDiff_const.add contDiff_id)
  rw [h, g.iteratedFDeriv_comp_right hc y le_rfl,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_comp_add_left]

/-- The second time derivative is the second derivative along `(1, 0)`. -/
theorem deriv_deriv_waveSolution (u₀ u₁ : 𝓢(E3, ℂ)) (t : ℝ) (x : E3) :
    deriv (fun s => deriv (fun r => waveSolution u₀ u₁ r x) s) t =
      iteratedFDeriv ℝ 2 (Function.uncurry (waveSolution u₀ u₁)) (t, x) (fun _ => (1, 0)) := by
  have h : (fun r => waveSolution u₀ u₁ r x) = fun r =>
      Function.uncurry (waveSolution u₀ u₁) ((0, x) + ContinuousLinearMap.inl ℝ ℝ E3 r) := by
    funext r
    simp
  have h2 : deriv (fun s => deriv (fun r => waveSolution u₀ u₁ r x) s) t =
      iteratedDeriv 2 (fun r => waveSolution u₀ u₁ r x) t := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2, iteratedDeriv_eq_iteratedFDeriv, h, iteratedFDeriv_two_comp_affine
    (contDiff_waveSolution u₀ u₁)]
  simp

/-- The spatial Laplacian is the sum of the second derivatives along `(0, eⱼ)`. -/
theorem laplacian_waveSolution (u₀ u₁ : 𝓢(E3, ℂ)) (t : ℝ) (x : E3) :
    Δ (waveSolution u₀ u₁ t) x = ∑ i : Fin 3, iteratedFDeriv ℝ 2
      (Function.uncurry (waveSolution u₀ u₁)) (t, x) (fun _ => (0, EuclideanSpace.single i 1)) := by
  have h : waveSolution u₀ u₁ t = fun y =>
      Function.uncurry (waveSolution u₀ u₁) ((t, 0) + ContinuousLinearMap.inr ℝ ℝ E3 y) := by
    funext y
    simp
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
    (EuclideanSpace.basisFun (Fin 3) ℝ), h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_two_comp_affine (contDiff_waveSolution u₀ u₁)]
  congr 1
  · simp
  · funext j
    fin_cases j <;> simp

/-- **The wave equation** `−∂ₜ²u + Δₓu = 0` on `ℝ × ℝ³`. -/
theorem wave_waveSolution (u₀ u₁ : 𝓢(E3, ℂ)) (t : ℝ) (x : E3) :
    -deriv (fun s => deriv (fun r => waveSolution u₀ u₁ r x) s) t +
      Δ (waveSolution u₀ u₁ t) x = 0 := by
  rw [deriv_deriv_waveSolution, laplacian_waveSolution]
  exact wave_iteratedFDeriv_waveSolution u₀ u₁ (t, x)

/-! ### The initial data -/

/-- Away from `ξ = 0`, the integrand of the velocity is the sum of the integrands of the time
derivative of the Fourier integral on the two sheets of the cone. -/
private theorem velocityIntegrand_eq (u₀ u₁ : 𝓢(E3, ℂ)) (t : ℝ) (x : E3) {ξ : E3}
    (hξ : ξ ≠ 0) :
    waveVelocity u₀ u₁ t ξ * 𝐞 ⟪x, ξ⟫ =
      𝐞 (-conePairing (‖ξ‖, ξ) (t, x)) • VectorFourier.fourierSMulRight conePairing
          (coneDensity u₀ u₁) (‖ξ‖, ξ) (1, 0) +
        𝐞 (-conePairing (-‖ξ‖, ξ) (t, x)) • VectorFourier.fourierSMulRight conePairing
          (coneDensity u₀ u₁) (-‖ξ‖, ξ) (1, 0) := by
  have hn : (‖ξ‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hξ
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
  simp only [VectorFourier.fourierSMulRight_apply, conePairing_apply, neg_neg, neg_mul,
    Circle.smul_def, smul_eq_mul, Complex.real_smul, AddChar.map_add_eq_mul, Circle.coe_mul,
    coe_fourierChar_mul, coe_fourierChar_neg_mul, mul_one, inner_zero_right, add_zero]
  rw [waveVelocity, coneDensity, coneDensity, real_inner_comm]
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The time derivative of the solution is `∫ ∂ₜû(t, ξ) e^{2πi⟪x, ξ⟫} dξ`. -/
theorem hasDerivAt_waveSolution (u₀ u₁ : 𝓢(E3, ℂ)) (t : ℝ) (x : E3) :
    HasDerivAt (fun s => waveSolution u₀ u₁ s x)
      (∫ ξ : E3, waveVelocity u₀ u₁ t ξ * 𝐞 ⟪x, ξ⟫) t := by
  have hf1 : Integrable (fun v : ℝ × E3 => ‖v‖ * ‖coneDensity u₀ u₁ v‖) coneMeasure := by
    simpa using integrable_pow_mul_coneDensity u₀ u₁ 1
  have hS : Integrable (VectorFourier.fourierSMulRight conePairing (coneDensity u₀ u₁))
      coneMeasure :=
    (hf1.const_mul (2 * π * ‖conePairing‖)).mono'
      (measurable_coneDensity u₀ u₁).aestronglyMeasurable.fourierSMulRight
      (Eventually.of_forall fun v =>
        (VectorFourier.norm_fourierSMulRight_le _ _ v).trans (le_of_eq (by ring)))
  have hU := VectorFourier.hasFDerivAt_fourierIntegral conePairing
    (integrable_coneDensity u₀ u₁) hf1 (t, x)
  have hline : HasDerivAt (fun r : ℝ => ((r, x) : ℝ × E3)) (1, 0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  have h := hU.comp_hasDerivAt t hline
  rw [← uncurry_waveSolution] at h
  refine HasDerivAt.congr_deriv h ?_
  have hint : Integrable (fun v => 𝐞 (-conePairing.toLinearMap₁₂ v (t, x)) •
      VectorFourier.fourierSMulRight conePairing (coneDensity u₀ u₁) v (1, 0)) coneMeasure :=
    (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar
      (by exact conePairing.continuous₂) (t, x)).2
      ((ContinuousLinearMap.apply ℝ ℂ ((1, 0) : ℝ × E3)).integrable_comp hS)
  rw [Real.fourierIntegral_continuousLinearMap_apply' hS, VectorFourier.fourierIntegral,
    integral_coneMeasure hint]
  refine integral_congr_ae ?_
  filter_upwards [Measure.ae_ne volume (0 : E3)] with ξ hξ
  simpa using (velocityIntegrand_eq u₀ u₁ t x hξ).symm

/-- The initial value of the solution is `u₀`. -/
theorem waveSolution_zero (u₀ u₁ : 𝓢(E3, ℂ)) (x : E3) : waveSolution u₀ u₁ 0 x = u₀ x := by
  have h : waveAmplitude u₀ u₁ 0 = ⇑(𝓕 u₀ : 𝓢(E3, ℂ)) := by
    funext ξ
    simp [waveAmplitude]
  rw [waveSolution_eq_fourierInv, h, ← SchwartzMap.fourierInv_coe,
    FourierTransform.fourierInv_fourier_eq]

/-- The initial velocity of the solution is `u₁`. -/
theorem deriv_waveSolution_zero (u₀ u₁ : 𝓢(E3, ℂ)) (x : E3) :
    deriv (fun t => waveSolution u₀ u₁ t x) 0 = u₁ x := by
  have h : waveVelocity u₀ u₁ 0 = ⇑(𝓕 u₁ : 𝓢(E3, ℂ)) := by
    funext ξ
    simp [waveVelocity]
  rw [(hasDerivAt_waveSolution u₀ u₁ 0 x).deriv, h]
  have h3 : (𝓕⁻ (𝓕 u₁ : 𝓢(E3, ℂ)) : 𝓢(E3, ℂ)) x = u₁ x := by
    rw [FourierTransform.fourierInv_fourier_eq]
  rw [← h3, SchwartzMap.fourierInv_coe, Real.fourierInv_eq]
  congr 1
  funext ξ
  rw [Circle.smul_def, smul_eq_mul, mul_comm, real_inner_comm]

/-! ### Real data -/

/-- For a real function `u`, `𝓕u(−ξ)` is the conjugate of `𝓕u(ξ)`. -/
private theorem fourier_neg_eq_conj_of_im_eq_zero (u : 𝓢(E3, ℂ)) (hu : ∀ x, (u x).im = 0)
    (ξ : E3) : 𝓕 u (-ξ) = starRingEnd ℂ (𝓕 u ξ) := by
  rw [SchwartzMap.fourier_coe, Real.fourier_eq, Real.fourier_eq, ← integral_conj]
  congr 1
  funext y
  rw [Circle.smul_def, Circle.smul_def, smul_eq_mul, smul_eq_mul, map_mul,
    Complex.conj_eq_iff_im.mpr (hu y), ← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv,
    inner_neg_right, neg_neg]

/-- For real data, the amplitude at `−ξ` is the conjugate of the amplitude at `ξ`. -/
theorem waveAmplitude_neg (u₀ u₁ : 𝓢(E3, ℂ)) (h₀ : ∀ x, (u₀ x).im = 0)
    (h₁ : ∀ x, (u₁ x).im = 0) (t : ℝ) (ξ : E3) :
    waveAmplitude u₀ u₁ t (-ξ) = starRingEnd ℂ (waveAmplitude u₀ u₁ t ξ) := by
  have hS : sinPropagator t (-ξ) = sinPropagator t ξ := by simp [sinPropagator]
  rw [waveAmplitude, waveAmplitude, norm_neg, hS, fourier_neg_eq_conj_of_im_eq_zero u₀ h₀,
    fourier_neg_eq_conj_of_im_eq_zero u₁ h₁, map_add, map_mul, map_mul, Complex.conj_ofReal,
    Complex.conj_ofReal]

/-- **For real data the solution is real.** -/
theorem im_waveSolution (u₀ u₁ : 𝓢(E3, ℂ)) (h₀ : ∀ x, (u₀ x).im = 0)
    (h₁ : ∀ x, (u₁ x).im = 0) (t : ℝ) (x : E3) : (waveSolution u₀ u₁ t x).im = 0 := by
  rw [← Complex.conj_eq_iff_im, waveSolution, ← integral_conj,
    ← integral_neg_eq_self (fun ξ => waveAmplitude u₀ u₁ t ξ * 𝐞 ⟪x, ξ⟫)]
  congr 1
  funext ξ
  rw [map_mul, waveAmplitude_neg u₀ u₁ h₀ h₁, ← Circle.coe_inv_eq_conj,
    ← AddChar.map_neg_eq_inv, inner_neg_right]

end ProjectAinos.SmoothGeometry.Fourier
