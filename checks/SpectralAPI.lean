/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.SmoothGeometry.Fourier.WaveSolution
import ProjectAinos.Electrodynamics.Spectral

/-! Public consumers of the spectral resolution (Landau–Lifshitz §49): the Fourier solution of
the wave equation for Schwartz data as a Fourier integral on the light cone, smooth in time and
space, with its initial data, the conservation at each frequency and real solutions; and the
temporal Fourier components with the inversion formula, Plancherel and (49.8).
Default elaborator options are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/

noncomputable section

section WaveSolution

open MeasureTheory Filter Set Real

open scoped FourierTransform RealInnerProductSpace Laplacian ContDiff Topology SchwartzMap

namespace ProjectAinos.SmoothGeometry.Fourier

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example (t : ℝ) (ξ : E3) :
    ℝ :=
  sinPropagator t ξ

example {ξ : E3} (hξ : ξ ≠ 0) (t : ℝ) :
    sinPropagator t ξ = Real.sin (2 * π * ‖ξ‖ * t) / (2 * π * ‖ξ‖) :=
  sinPropagator_of_ne_zero hξ t

example (t : ℝ) :
    sinPropagator t 0 = t :=
  sinPropagator_zero_right t

example (ξ : E3) :
    sinPropagator 0 ξ = 0 :=
  sinPropagator_zero_left ξ

example (t : ℝ) (ξ : E3) :
    2 * π * ‖ξ‖ * sinPropagator t ξ = Real.sin (2 * π * ‖ξ‖ * t) :=
  mul_sinPropagator t ξ

example (t : ℝ) (ξ : E3) :
    |sinPropagator t ξ| ≤ |t| :=
  abs_sinPropagator_le t ξ

example :
    Continuous fun p : ℝ × E3 => sinPropagator p.1 p.2 :=
  continuous_sinPropagator

example (t : ℝ) (ξ : E3) :
    HasDerivAt (fun s => sinPropagator s ξ) (Real.cos (2 * π * ‖ξ‖ * t)) t :=
  hasDerivAt_sinPropagator t ξ

example (u₀ u₁ : 𝓢(E3, ℂ)) (t : ℝ) (ξ : E3) :
    ℂ :=
  waveAmplitude u₀ u₁ t ξ

example (u₀ u₁ : 𝓢(E3, ℂ)) (t : ℝ) (ξ : E3) :
    ℂ :=
  waveVelocity u₀ u₁ t ξ

example (u₀ u₁ : 𝓢(E3, ℂ)) (t : ℝ) (ξ : E3) :
    HasDerivAt (fun s => waveAmplitude u₀ u₁ s ξ) (waveVelocity u₀ u₁ t ξ) t :=
  hasDerivAt_waveAmplitude u₀ u₁ t ξ

example (u₀ u₁ : 𝓢(E3, ℂ)) (t : ℝ) (ξ : E3) :
    ‖waveVelocity u₀ u₁ t ξ‖ ^ 2 + (2 * π * ‖ξ‖) ^ 2 * ‖waveAmplitude u₀ u₁ t ξ‖ ^ 2 =
      ‖𝓕 u₁ ξ‖ ^ 2 + (2 * π * ‖ξ‖) ^ 2 * ‖𝓕 u₀ ξ‖ ^ 2 :=
  fourierEnergy_waveSolution u₀ u₁ t ξ

example (u₀ u₁ : 𝓢(E3, ℂ)) (t : ℝ) (x : E3) :
    ℂ :=
  waveSolution u₀ u₁ t x

example (u₀ u₁ : 𝓢(E3, ℂ)) (t : ℝ) :
    waveSolution u₀ u₁ t = 𝓕⁻ (waveAmplitude u₀ u₁ t) :=
  waveSolution_eq_fourierInv u₀ u₁ t

example :
    (ℝ × E3) →L[ℝ] (ℝ × E3) →L[ℝ] ℝ :=
  conePairing

example (v w : ℝ × E3) :
    conePairing v w = -(v.1 * w.1 + ⟪v.2, w.2⟫) :=
  conePairing_apply v w

example :
    Measure (ℝ × E3) :=
  coneMeasure

example (u₀ u₁ : 𝓢(E3, ℂ)) (v : ℝ × E3) :
    ℂ :=
  coneDensity u₀ u₁ v

example :
    ∀ᵐ v ∂coneMeasure, v.1 ^ 2 = ‖v.2‖ ^ 2 :=
  ae_coneMeasure

example {G : Type*} [NormedAddCommGroup G] {h : ℝ × E3 → G}
    (hm : AEStronglyMeasurable h coneMeasure) (hp : Integrable fun ξ : E3 => h (‖ξ‖, ξ))
    (hn : Integrable fun ξ : E3 => h (-‖ξ‖, ξ)) :
    Integrable h coneMeasure :=
  integrable_coneMeasure hm hp hn

example {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {h : ℝ × E3 → G}
    (hh : Integrable h coneMeasure) :
    ∫ v, h v ∂coneMeasure = ∫ ξ : E3, (h (‖ξ‖, ξ) + h (-‖ξ‖, ξ)) :=
  integral_coneMeasure hh

example (u₀ u₁ : 𝓢(E3, ℂ)) (n : ℕ) :
    Integrable (fun v : ℝ × E3 => ‖v‖ ^ n * ‖coneDensity u₀ u₁ v‖) coneMeasure :=
  integrable_pow_mul_coneDensity u₀ u₁ n

example (u₀ u₁ : 𝓢(E3, ℂ)) :
    Integrable (coneDensity u₀ u₁) coneMeasure :=
  integrable_coneDensity u₀ u₁

example (u₀ u₁ : 𝓢(E3, ℂ)) :
    Function.uncurry (waveSolution u₀ u₁) = VectorFourier.fourierIntegral 𝐞 coneMeasure
      conePairing.toLinearMap₁₂ (coneDensity u₀ u₁) :=
  uncurry_waveSolution u₀ u₁

example (u₀ u₁ : 𝓢(E3, ℂ)) (t : ℝ) (x : E3) :
    waveSolution u₀ u₁ t x = VectorFourier.fourierIntegral 𝐞 coneMeasure
      conePairing.toLinearMap₁₂ (coneDensity u₀ u₁) (t, x) :=
  waveSolution_eq_fourierIntegral u₀ u₁ t x

example (u₀ u₁ : 𝓢(E3, ℂ)) {n : ℕ∞} :
    ContDiff ℝ n (Function.uncurry (waveSolution u₀ u₁)) :=
  contDiff_waveSolution u₀ u₁

example (u₀ u₁ : 𝓢(E3, ℂ)) (k : ℕ) :
    iteratedFDeriv ℝ k (Function.uncurry (waveSolution u₀ u₁)) =
      VectorFourier.fourierIntegral 𝐞 coneMeasure conePairing.toLinearMap₁₂
        (fun v => VectorFourier.fourierPowSMulRight conePairing (coneDensity u₀ u₁) v k) :=
  iteratedFDeriv_waveSolution u₀ u₁ k

example (u₀ u₁ : 𝓢(E3, ℂ)) (p : ℝ × E3) :
    -iteratedFDeriv ℝ 2 (Function.uncurry (waveSolution u₀ u₁)) p (fun _ => (1, 0)) +
      ∑ i : Fin 3, iteratedFDeriv ℝ 2 (Function.uncurry (waveSolution u₀ u₁)) p
        (fun _ => (0, EuclideanSpace.single i 1)) = 0 :=
  wave_iteratedFDeriv_waveSolution u₀ u₁ p

example (u₀ u₁ : 𝓢(E3, ℂ)) (t : ℝ) (x : E3) :
    deriv (fun s => deriv (fun r => waveSolution u₀ u₁ r x) s) t =
      iteratedFDeriv ℝ 2 (Function.uncurry (waveSolution u₀ u₁)) (t, x) (fun _ => (1, 0)) :=
  deriv_deriv_waveSolution u₀ u₁ t x

example (u₀ u₁ : 𝓢(E3, ℂ)) (t : ℝ) (x : E3) :
    Δ (waveSolution u₀ u₁ t) x = ∑ i : Fin 3, iteratedFDeriv ℝ 2
      (Function.uncurry (waveSolution u₀ u₁)) (t, x) (fun _ => (0, EuclideanSpace.single i 1)) :=
  laplacian_waveSolution u₀ u₁ t x

example (u₀ u₁ : 𝓢(E3, ℂ)) (t : ℝ) (x : E3) :
    -deriv (fun s => deriv (fun r => waveSolution u₀ u₁ r x) s) t +
      Δ (waveSolution u₀ u₁ t) x = 0 :=
  wave_waveSolution u₀ u₁ t x

example (u₀ u₁ : 𝓢(E3, ℂ)) (t : ℝ) (x : E3) :
    HasDerivAt (fun s => waveSolution u₀ u₁ s x)
      (∫ ξ : E3, waveVelocity u₀ u₁ t ξ * 𝐞 ⟪x, ξ⟫) t :=
  hasDerivAt_waveSolution u₀ u₁ t x

example (u₀ u₁ : 𝓢(E3, ℂ)) (x : E3) :
    waveSolution u₀ u₁ 0 x = u₀ x :=
  waveSolution_zero u₀ u₁ x

example (u₀ u₁ : 𝓢(E3, ℂ)) (x : E3) :
    deriv (fun t => waveSolution u₀ u₁ t x) 0 = u₁ x :=
  deriv_waveSolution_zero u₀ u₁ x

example (u₀ u₁ : 𝓢(E3, ℂ)) (h₀ : ∀ x, (u₀ x).im = 0) (h₁ : ∀ x, (u₁ x).im = 0) (t : ℝ) (ξ : E3) :
    waveAmplitude u₀ u₁ t (-ξ) = starRingEnd ℂ (waveAmplitude u₀ u₁ t ξ) :=
  waveAmplitude_neg u₀ u₁ h₀ h₁ t ξ

example (u₀ u₁ : 𝓢(E3, ℂ)) (h₀ : ∀ x, (u₀ x).im = 0) (h₁ : ∀ x, (u₁ x).im = 0) (t : ℝ) (x : E3) :
    (waveSolution u₀ u₁ t x).im = 0 :=
  im_waveSolution u₀ u₁ h₀ h₁ t x

end ProjectAinos.SmoothGeometry.Fourier

end WaveSolution

section Spectral

open MeasureTheory Filter Set Real ComplexConjugate

open scoped FourierTransform RealInnerProductSpace ContDiff SchwartzMap

namespace ProjectAinos.Electrodynamics.Spectral

open SmoothGeometry SmoothGeometry.Minkowski SpecialRelativity SmoothGeometry.Fourier

example (f : 𝓢(ℝ, ℂ)) (w : ℝ) :
    ℂ :=
  fourierComponent f w

example (f : 𝓢(ℝ, ℂ)) (w : ℝ) :
    fourierComponent f w = 𝓕 f (-(w / (2 * π))) :=
  fourierComponent_eq_fourier f w

example (f : 𝓢(ℝ, ℂ)) (t : ℝ) :
    f t = ∫ ν : ℝ, 𝐞 (ν * t) • 𝓕 f ν :=
  eq_integral_fourier f t

example (f : 𝓢(ℝ, ℂ)) (t : ℝ) :
    f t = (2 * π)⁻¹ * ∫ w : ℝ, fourierComponent f w * Complex.exp (-(w * t) * Complex.I) :=
  eq_integral_fourierComponent f t

example (f : 𝓢(ℝ, ℂ)) :
    ∫ t, ‖f t‖ ^ 2 = ∫ ν, ‖𝓕 f ν‖ ^ 2 :=
  integral_sq_eq_integral_sq_fourier f

example (f : 𝓢(ℝ, ℂ)) (hf : ∀ t, (f t).im = 0) (ν : ℝ) :
    𝓕 f (-ν) = conj (𝓕 f ν) :=
  fourier_neg_eq_conj f hf ν

example (f : 𝓢(ℝ, ℂ)) (hf : ∀ t, (f t).im = 0) (ν : ℝ) :
    ‖𝓕 f (-ν)‖ = ‖𝓕 f ν‖ :=
  norm_fourier_neg f hf ν

example (f : 𝓢(ℝ, ℂ)) (hf : ∀ t, (f t).im = 0) :
    ∫ t, ‖f t‖ ^ 2 = 2 * ∫ ν in Ioi 0, ‖𝓕 f ν‖ ^ 2 :=
  integral_sq_eq_two_integral_Ioi f hf

example (f : 𝓢(ℝ, ℂ)) (hf : ∀ t, (f t).im = 0) :
    ∫ t, ‖f t‖ ^ 2 = π⁻¹ * ∫ w in Ioi 0, ‖fourierComponent f w‖ ^ 2 :=
  integral_sq_eq_integral_Ioi_fourierComponent f hf

example (u₀ u₁ : 𝓢(Minkowski.Space 3, ℂ)) {n : ℕ∞} :
    ContDiff ℝ n fun y : Spacetime => (waveSolution u₀ u₁ (y 0) (Minkowski.space y)).re :=
  contDiff_re_waveSolution u₀ u₁

example (u₀ u₁ : 𝓢(Minkowski.Space 3, ℂ)) (y : Spacetime) :
    box (fun z => (waveSolution u₀ u₁ (z 0) (Minkowski.space z)).re) y = 0 :=
  box_re_waveSolution u₀ u₁ y

example (u₀ u₁ : 𝓢(Minkowski.Space 3, ℂ)) (x : Minkowski.Space 3) :
    (waveSolution u₀ u₁ 0 x).re = (u₀ x).re :=
  re_waveSolution_zero u₀ u₁ x

example (u₀ u₁ : 𝓢(Minkowski.Space 3, ℂ)) (x : Minkowski.Space 3) :
    HasDerivAt (fun t => (waveSolution u₀ u₁ t x).re) (u₁ x).re 0 :=
  hasDerivAt_re_waveSolution_zero u₀ u₁ x

example (u₀ u₁ : 𝓢(Minkowski.Space 3, ℂ)) (h₀ : ∀ x, (u₀ x).im = 0) (h₁ : ∀ x, (u₁ x).im = 0)
    (y : Spacetime) :
    ((waveSolution u₀ u₁ (y 0) (Minkowski.space y)).re : ℂ) =
      waveSolution u₀ u₁ (y 0) (Minkowski.space y) :=
  ofReal_re_waveSolution u₀ u₁ h₀ h₁ y

end ProjectAinos.Electrodynamics.Spectral

end Spectral
