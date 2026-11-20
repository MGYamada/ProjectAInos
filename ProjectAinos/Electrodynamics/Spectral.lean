/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Fourier.WaveSolution
public import ProjectAinos.Electrodynamics.WaveEquation
import Mathlib.Tactic

/-!
# Spectral resolution

Landau–Lifshitz, *The Classical Theory of Fields*, §49. The Fourier transform has Mathlib's
normalization `𝓕f(ν) = ∫ e^{−2πiνt} f(t) dt` in the frequency `ν = ω/2π`. The Fourier component
of Landau–Lifshitz is `fourierComponent f ω = f_ω = ∫ f(t) e^{iωt} dt` (49.2), which is
`𝓕f(−ω/2π)`. The signals are Schwartz functions `f ∈ 𝓢(ℝ, ℂ)`; a real signal is one with
`(f t).im = 0` for every `t`.

* `eq_integral_fourier`, `eq_integral_fourierComponent`: the spectral resolution
  `f(t) = ∫ 𝓕f(ν) e^{2πiνt} dν = ∫ f_ω e^{−iωt} dω/2π` (49.1).
* `integral_sq_eq_integral_sq_fourier`: Plancherel's theorem `∫ |f|² dt = ∫ |𝓕f|² dν`.
* `fourier_neg_eq_conj`: for a real signal, `𝓕f(−ν)` is the conjugate of `𝓕f(ν)`.
* `integral_sq_eq_two_integral_Ioi`: for a real signal, `∫ f² dt = 2 ∫_{ν>0} |𝓕f(ν)|² dν`,
  and `integral_sq_eq_integral_Ioi_fourierComponent`: `∫ f² dt = ∫_{ω>0} |f_ω|² dω/π`, the
  energy spectrum (49.8).
* `box_re_waveSolution`: the real part of the Fourier solution
  `SmoothGeometry.Fourier.waveSolution` of the wave equation, as a function on space-time, solves
  `box u = 0`; `re_waveSolution_zero` and `hasDerivAt_re_waveSolution_zero` give its initial data.
  The data need not be real. For real data the solution is real (`im_waveSolution`), so
  `ofReal_re_waveSolution`: it is its real part, and `box_re_waveSolution` is the wave equation
  for the solution itself.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Real ComplexConjugate
open scoped FourierTransform RealInnerProductSpace ContDiff SchwartzMap

namespace ProjectAinos.Electrodynamics.Spectral

open SmoothGeometry SmoothGeometry.Minkowski SpecialRelativity SmoothGeometry.Fourier

/-! ### The spectral resolution of a signal -/

/-- The Fourier component `f_ω = ∫ f(t) e^{iωt} dt` of a signal (Landau–Lifshitz (49.2)). -/
def fourierComponent (f : 𝓢(ℝ, ℂ)) (w : ℝ) : ℂ :=
  ∫ t : ℝ, Complex.exp (w * t * Complex.I) * f t

/-- The Fourier component at the angular frequency `ω` is the Fourier transform at
`ν = −ω/2π`. -/
theorem fourierComponent_eq_fourier (f : 𝓢(ℝ, ℂ)) (w : ℝ) :
    fourierComponent f w = 𝓕 f (-(w / (2 * π))) := by
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul, fourierComponent]
  congr 1
  funext t
  rw [smul_eq_mul]
  congr 2
  push_cast
  field_simp

/-- **The spectral resolution** `f(t) = ∫ 𝓕f(ν) e^{2πiνt} dν`. -/
theorem eq_integral_fourier (f : 𝓢(ℝ, ℂ)) (t : ℝ) :
    f t = ∫ ν : ℝ, 𝐞 (ν * t) • 𝓕 f ν := by
  have h : (𝓕⁻ (𝓕 f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ)) t = f t := by
    rw [FourierTransform.fourierInv_fourier_eq]
  rw [← h, SchwartzMap.fourierInv_coe, Real.fourierInv_eq]
  simp [mul_comm]

/-- **The spectral resolution** in the angular frequency,
`f(t) = ∫ f_ω e^{−iωt} dω/2π` (Landau–Lifshitz (49.1)). -/
theorem eq_integral_fourierComponent (f : 𝓢(ℝ, ℂ)) (t : ℝ) :
    f t = (2 * π)⁻¹ * ∫ w : ℝ, fourierComponent f w * Complex.exp (-(w * t) * Complex.I) := by
  have hπ : (0 : ℝ) < 2 * π := by positivity
  set g : ℝ → ℂ := fun w => fourierComponent f w * Complex.exp (-(w * t) * Complex.I) with hg
  have h := Measure.integral_comp_mul_left g (-(2 * π))
  rw [abs_inv, abs_neg, abs_of_pos hπ] at h
  have h' : ∫ w, g w = ((2 * π : ℝ) : ℂ) * ∫ x, g (-(2 * π) * x) := by
    rw [h, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hπ.ne',
      Complex.ofReal_one, one_mul]
  change f t = (2 * π)⁻¹ * ∫ w, g w
  rw [h', ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hπ.ne', Complex.ofReal_one, one_mul,
    eq_integral_fourier f t]
  congr 1
  funext ν
  simp only [hg, fourierComponent_eq_fourier]
  rw [show -(-(2 * π) * ν / (2 * π)) = ν by field_simp, Circle.smul_def, Real.fourierChar_apply,
    smul_eq_mul, mul_comm]
  congr 2
  push_cast
  ring

/-! ### Plancherel's theorem and the energy spectrum -/

/-- **Plancherel's theorem** for a signal: `∫ |f(t)|² dt = ∫ |𝓕f(ν)|² dν`. -/
theorem integral_sq_eq_integral_sq_fourier (f : 𝓢(ℝ, ℂ)) :
    ∫ t, ‖f t‖ ^ 2 = ∫ ν, ‖𝓕 f ν‖ ^ 2 :=
  (SchwartzMap.integral_norm_sq_fourier f).symm

/-- For a real signal, `𝓕f(−ν)` is the conjugate of `𝓕f(ν)`. -/
theorem fourier_neg_eq_conj (f : 𝓢(ℝ, ℂ)) (hf : ∀ t, (f t).im = 0) (ν : ℝ) :
    𝓕 f (-ν) = conj (𝓕 f ν) := by
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq, Real.fourier_real_eq, ← integral_conj]
  congr 1
  funext t
  rw [Circle.smul_def, Circle.smul_def, smul_eq_mul, smul_eq_mul, map_mul,
    Complex.conj_eq_iff_im.mpr (hf t), ← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv]
  congr 3
  ring

/-- For a real signal, `|𝓕f(−ν)| = |𝓕f(ν)|`. -/
theorem norm_fourier_neg (f : 𝓢(ℝ, ℂ)) (hf : ∀ t, (f t).im = 0) (ν : ℝ) :
    ‖𝓕 f (-ν)‖ = ‖𝓕 f ν‖ := by
  rw [fourier_neg_eq_conj f hf, Complex.norm_conj]

/-- **The energy spectrum** of a real signal, Landau–Lifshitz (49.8) in the frequency `ν`:
`∫ f² dt = 2 ∫_{ν>0} |𝓕f(ν)|² dν`. -/
theorem integral_sq_eq_two_integral_Ioi (f : 𝓢(ℝ, ℂ)) (hf : ∀ t, (f t).im = 0) :
    ∫ t, ‖f t‖ ^ 2 = 2 * ∫ ν in Ioi 0, ‖𝓕 f ν‖ ^ 2 := by
  have hint : Integrable fun ν => ‖𝓕 f ν‖ ^ 2 :=
    ((𝓕 f : 𝓢(ℝ, ℂ)).memLp 2).integrable_norm_pow two_ne_zero
  have hneg : ∫ ν in Iic 0, ‖𝓕 f ν‖ ^ 2 = ∫ ν in Ioi 0, ‖𝓕 f ν‖ ^ 2 := by
    rw [← neg_zero, ← integral_comp_neg_Ioi, neg_zero]
    simp only [norm_fourier_neg f hf]
  rw [integral_sq_eq_integral_sq_fourier, ← integral_add_compl measurableSet_Ioi hint, compl_Ioi,
    hneg]
  ring

/-- **The energy spectrum** of a real signal, Landau–Lifshitz (49.8):
`∫ f² dt = ∫_{ω>0} |f_ω|² dω/π`. -/
theorem integral_sq_eq_integral_Ioi_fourierComponent (f : 𝓢(ℝ, ℂ)) (hf : ∀ t, (f t).im = 0) :
    ∫ t, ‖f t‖ ^ 2 = π⁻¹ * ∫ w in Ioi 0, ‖fourierComponent f w‖ ^ 2 := by
  have hπ : (0 : ℝ) < 2 * π := by positivity
  have h := integral_comp_mul_left_Ioi (fun w => ‖fourierComponent f w‖ ^ 2) 0 hπ
  have h2 (ν : ℝ) : ‖fourierComponent f (2 * π * ν)‖ ^ 2 = ‖𝓕 f ν‖ ^ 2 := by
    rw [fourierComponent_eq_fourier, mul_div_cancel_left₀ _ hπ.ne', norm_fourier_neg f hf]
  simp only [h2, mul_zero, smul_eq_mul] at h
  rw [integral_sq_eq_two_integral_Ioi f hf, h]
  field_simp

/-! ### The real solution of the wave equation on space-time -/

/-- The co-ordinates `(t, x)` of a point of space-time. -/
private def timeSpace : Spacetime →L[ℝ] ℝ × Minkowski.Space 3 :=
  (Minkowski.time : Spacetime →L[ℝ] ℝ).prod Minkowski.space

/-- The co-ordinates of `y` are `(y⁰, 𝐲)`. -/
private theorem timeSpace_apply (y : Spacetime) : timeSpace y = (y 0, Minkowski.space y) := rfl

/-- The unit vector of `x⁰` has the co-ordinates `(1, 0)`. -/
private theorem timeSpace_single_zero : timeSpace (Pi.single 0 1) = (1, 0) := by
  rw [timeSpace_apply]
  ext i
  · simp
  · simp [Minkowski.space_apply, Fin.succ_ne_zero]

/-- The unit vector of `xⁱ⁺¹` has the co-ordinates `(0, eᵢ)`. -/
private theorem timeSpace_single_succ (i : Fin 3) :
    timeSpace (Pi.single i.succ 1) = (0, EuclideanSpace.single i 1) := by
  rw [timeSpace_apply]
  ext j
  · simp [(Fin.succ_ne_zero i).symm]
  · simp [Minkowski.space_apply, Pi.single_apply, Fin.succ_inj]

/-- For a `C²` function, `∂_μ∂_μ f` is the second derivative along the unit vector of `x^μ`. -/
private theorem partialAt_partialAt_eq {f : Spacetime → ℝ} (hf : ContDiff ℝ 2 f) (μ : Fin 4)
    (y : Spacetime) :
    partialAt (partialAt f μ) μ y = iteratedFDeriv ℝ 2 f y (fun _ => Pi.single μ 1) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) y :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) y
  rw [iteratedFDeriv_two_apply, partialAt]
  change fderiv ℝ (fun z => fderiv ℝ f z (Pi.single μ 1)) y (Pi.single μ 1) = _
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp

/-- The real part of the solution, as a function on space-time, is smooth. -/
theorem contDiff_re_waveSolution (u₀ u₁ : 𝓢(Minkowski.Space 3, ℂ)) {n : ℕ∞} :
    ContDiff ℝ n fun y : Spacetime => (waveSolution u₀ u₁ (y 0) (Minkowski.space y)).re := by
  have h : (fun y : Spacetime => (waveSolution u₀ u₁ (y 0) (Minkowski.space y)).re) =
      Complex.reCLM ∘ (Function.uncurry (waveSolution u₀ u₁) ∘ timeSpace) := rfl
  rw [h]
  exact Complex.reCLM.contDiff.comp ((contDiff_waveSolution u₀ u₁).comp timeSpace.contDiff)

/-- **The real solution of the wave equation**: the real part of the Fourier solution, as a
function on space-time, solves `box u = 0`. -/
theorem box_re_waveSolution (u₀ u₁ : 𝓢(Minkowski.Space 3, ℂ)) (y : Spacetime) :
    box (fun z => (waveSolution u₀ u₁ (z 0) (Minkowski.space z)).re) y = 0 := by
  set U := Function.uncurry (waveSolution u₀ u₁)
  have hU : ContDiff ℝ 2 U := contDiff_waveSolution u₀ u₁
  have hf : (fun z : Spacetime => (waveSolution u₀ u₁ (z 0) (Minkowski.space z)).re) =
      Complex.reCLM ∘ (U ∘ timeSpace) := rfl
  have hsecond (μ : Fin 4) :
      partialAt (partialAt (fun z : Spacetime =>
        (waveSolution u₀ u₁ (z 0) (Minkowski.space z)).re) μ) μ y =
        (iteratedFDeriv ℝ 2 U (timeSpace y) (fun _ => timeSpace (Pi.single μ 1))).re := by
    rw [partialAt_partialAt_eq (contDiff_re_waveSolution u₀ u₁) μ y, hf,
      Complex.reCLM.iteratedFDeriv_comp_left (hU.comp timeSpace.contDiff).contDiffAt le_rfl,
      timeSpace.iteratedFDeriv_comp_right hU y le_rfl]
    simp
  have hwave := wave_iteratedFDeriv_waveSolution u₀ u₁ (timeSpace y)
  rw [box, hsecond, timeSpace_single_zero]
  simp only [hsecond, timeSpace_single_succ]
  have := congrArg Complex.re hwave
  simpa [Complex.re_sum] using this

/-- The real part of the solution has the initial value `re u₀`. -/
theorem re_waveSolution_zero (u₀ u₁ : 𝓢(Minkowski.Space 3, ℂ)) (x : Minkowski.Space 3) :
    (waveSolution u₀ u₁ 0 x).re = (u₀ x).re := by
  rw [waveSolution_zero]

/-- The real part of the solution has the initial velocity `re u₁`. -/
theorem hasDerivAt_re_waveSolution_zero (u₀ u₁ : 𝓢(Minkowski.Space 3, ℂ))
    (x : Minkowski.Space 3) :
    HasDerivAt (fun t => (waveSolution u₀ u₁ t x).re) (u₁ x).re 0 := by
  have h := (hasDerivAt_waveSolution u₀ u₁ 0 x)
  rw [← (h.deriv), deriv_waveSolution_zero] at h
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 h

/-- For real data the solution on space-time is its real part. -/
theorem ofReal_re_waveSolution (u₀ u₁ : 𝓢(Minkowski.Space 3, ℂ)) (h₀ : ∀ x, (u₀ x).im = 0)
    (h₁ : ∀ x, (u₁ x).im = 0) (y : Spacetime) :
    ((waveSolution u₀ u₁ (y 0) (Minkowski.space y)).re : ℂ) =
      waveSolution u₀ u₁ (y 0) (Minkowski.space y) :=
  Complex.ext (by simp) (by simp [im_waveSolution u₀ u₁ h₀ h₁])

end ProjectAinos.Electrodynamics.Spectral
