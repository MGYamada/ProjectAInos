/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAInos.Mechanics.Oscillations.AdiabaticAccuracyExample

/-! Typed contracts for the accuracy of the conservation of the adiabatic
invariant: Gronwall's inequality with an integrable coefficient, the
propagator of a coefficient that is deformed along a complex direction, the
amplitude system of an oscillator and its coefficient along the lines parallel
to the real axis, the estimate of the propagator on the real line, the
symmetries on the real line, the amplitude of an oscillator whose frequency
depends on the slow phase, the limits of the action and their exponentially
small difference, and the Lorentzian frequency as an instance. These examples
use default elaborator options. -/

open ProjectAInos ProjectAInos.Mechanics ProjectAInos.Mechanics.AdiabaticAmplitude
open ProjectAInos.SmoothGeometry.LinearODE
open ProjectAInos.Mechanics.AdiabaticOscillator (action)
open Complex (I)
open Set Filter
open scoped Topology ComplexConjugate Real

noncomputable section

section PropagatorBound

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

example {f f' : ℝ → E} {a : ℝ → ℝ} {s t : ℝ}
    (hst : s ≤ t) (ha : Continuous a) (hf : ∀ r ∈ Icc s t, HasDerivAt f (f' r) r)
    (hbound : ∀ r ∈ Icc s t, ‖f' r‖ ≤ a r * ‖f r‖) :
    ‖f t‖ ≤ ‖f s‖ * Real.exp (∫ r in s..t, a r) :=
  norm_le_mul_exp_integral_of_norm_deriv_le hst ha hf hbound

example (A : C(ℝ, E →L[ℝ] E)) {s t : ℝ} (hst : s ≤ t)
    (y : E) :
    ‖propagator A t s y‖ ≤ ‖y‖ * Real.exp (∫ r in s..t, ‖A r‖) :=
  norm_propagator_apply_le_exp_integral A hst y

example (A : C(ℝ, E →L[ℝ] E)) (T : E →L[ℝ] E)
    (hT : ∀ (r : ℝ) (y : E), A r (T y) = T (A r y)) (t s : ℝ) (y : E) :
    propagator A t s (T y) = T (propagator A t s y) :=
  propagator_apply_comm A T hT t s y

end PropagatorBound

section PropagatorDeformation

open scoped ContDiff

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

example {F : ℝ × ℝ → G} {p s : ℝ} (h : DifferentiableAt ℝ F (p, s)) :
    HasDerivAt (fun p' => F (p', s)) (fderiv ℝ F (p, s) (1, 0)) p :=
  hasDerivAt_fst_line h

example {F : ℝ × ℝ → G} {p s : ℝ} (h : DifferentiableAt ℝ F (p, s)) :
    HasDerivAt (fun s' => F (p, s')) (fderiv ℝ F (p, s) (0, 1)) s :=
  hasDerivAt_snd_line h

example (A : ℝ × ℝ → V →L[ℝ] V) (hA : Continuous A) (s₀ : ℝ) (y₀ : V) (q : ℝ × ℝ) :
    paramSolution A hA s₀ y₀ q = propagator (coefficientCurve A hA q.1) q.2 s₀ y₀ := rfl

example {A : ℝ × ℝ → V →L[ℝ] V} (hA : ContDiff ℝ ∞ A) (s₀ : ℝ)
    (y₀ : V) :
    ContDiff ℝ ∞ (paramSolution A hA.continuous s₀ y₀) :=
  contDiff_paramSolution hA s₀ y₀

example (A : ℝ × ℝ → V →L[ℝ] V) (hA : Continuous A) (s₀ : ℝ)
    (y₀ : V) (p s : ℝ) :
    HasDerivAt (fun s' => paramSolution A hA s₀ y₀ (p, s'))
      (A (p, s) (paramSolution A hA s₀ y₀ (p, s))) s :=
  hasDerivAt_paramSolution A hA s₀ y₀ p s

example (A : ℝ × ℝ → V →L[ℝ] V) (hA : Continuous A) (s₀ : ℝ) (y₀ : V)
    (p : ℝ) :
    paramSolution A hA s₀ y₀ (p, s₀) = y₀ :=
  paramSolution_self A hA s₀ y₀ p

example {A : ℝ × ℝ → V →L[ℝ] V} (hA : ContDiff ℝ ∞ A) (s₀ : ℝ)
    (y₀ : V) (p s : ℝ) :
    fderiv ℝ (paramSolution A hA.continuous s₀ y₀) (p, s) (0, 1) =
      A (p, s) (paramSolution A hA.continuous s₀ y₀ (p, s)) :=
  fderiv_paramSolution_time hA s₀ y₀ p s

example {A : ℝ × ℝ → V →L[ℝ] V} (hA : ContDiff ℝ ∞ A)
    (s₀ : ℝ) (y₀ : V) (p s : ℝ) :
    HasDerivAt (fun s' => fderiv ℝ (paramSolution A hA.continuous s₀ y₀) (p, s') (1, 0))
      (fderiv ℝ A (p, s) (1, 0) (paramSolution A hA.continuous s₀ y₀ (p, s)) +
        A (p, s) (fderiv ℝ (paramSolution A hA.continuous s₀ y₀) (p, s) (1, 0))) s :=
  hasDerivAt_fderiv_paramSolution hA s₀ y₀ p s

example {A : ℝ × ℝ → V →L[ℝ] V} (hA : ContDiff ℝ ∞ A)
    (J : V →L[ℝ] V) (c : ℝ → ℝ) (hJ : ∀ (q : ℝ × ℝ) (v : V), A q (J v) = J (A q v))
    (hCR : ∀ (q : ℝ × ℝ) (v : V),
      fderiv ℝ A q (1, 0) v = c q.1 • J (fderiv ℝ A q (0, 1) v))
    (p s₀ s₁ : ℝ) (y₀ : V) :
    HasDerivAt (fun p' => propagator (coefficientCurve A hA.continuous p') s₁ s₀ y₀)
      (c p • J (A (p, s₁) (propagator (coefficientCurve A hA.continuous p) s₁ s₀ y₀) -
        propagator (coefficientCurve A hA.continuous p) s₁ s₀ (A (p, s₀) y₀))) p :=
  hasDerivAt_propagator_apply_param hA J c hJ hCR p s₀ s₁ y₀

example {A : ℝ × ℝ → V →L[ℝ] V}
    (hA : ContDiff ℝ ∞ A) (J : V →L[ℝ] V) (c : ℝ → ℝ)
    (hJ : ∀ (q : ℝ × ℝ) (v : V), A q (J v) = J (A q v))
    (hCR : ∀ (q : ℝ × ℝ) (v : V),
      fderiv ℝ A q (1, 0) v = c q.1 • J (fderiv ℝ A q (0, 1) v))
    {p₀ p₁ s₀ s₁ C K M₀ M₁ : ℝ} (hp : p₀ ≤ p₁) (hK0 : 0 ≤ K) (hJn : ∀ v : V, ‖J v‖ ≤ ‖v‖)
    (hc : ∀ p ∈ Icc p₀ p₁, |c p| ≤ C)
    (hK : ∀ p ∈ Icc p₀ p₁, ∀ y : V,
      ‖propagator (coefficientCurve A hA.continuous p) s₁ s₀ y‖ ≤ K * ‖y‖)
    (hM₀ : ∀ p ∈ Icc p₀ p₁, ‖A (p, s₀)‖ ≤ M₀) (hM₁ : ∀ p ∈ Icc p₀ p₁, ‖A (p, s₁)‖ ≤ M₁)
    (y₀ : V) :
    ‖propagator (coefficientCurve A hA.continuous p₁) s₁ s₀ y₀ -
        propagator (coefficientCurve A hA.continuous p₀) s₁ s₀ y₀‖ ≤
      C * (K * (M₁ + M₀) * ‖y₀‖) * (p₁ - p₀) :=
  norm_propagator_apply_sub_le_of_deformation hA J c hJ hCR hp hK0 hJn hc hK hM₀ hM₁ y₀

end PropagatorDeformation

section AmplitudeSystem

open scoped ContDiff

variable {g : ℂ → ℂ} {U : Set ℂ} {σ ε : ℝ}

example (a b : ℂ) (y : ℂ × ℂ) : offDiag a b y = (a * y.2, b * y.1) := rfl

example (a b : ℂ) (y : ℂ × ℂ) :
    offDiag a b y = (a * y.2, b * y.1) :=
  offDiag_apply a b y

example (a b : ℂ) {M : ℝ} (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) :
    ‖offDiag a b‖ ≤ M :=
  norm_offDiag_le a b ha hb

example (y : ℂ × ℂ) : mulI y = (I * y.1, I * y.2) := rfl

example (y : ℂ × ℂ) :
    mulI y = (I * y.1, I * y.2) :=
  mulI_apply y

example (y : ℂ × ℂ) :
    ‖mulI y‖ ≤ ‖y‖ :=
  norm_mulI_le y

example (a b : ℂ) (y : ℂ × ℂ) :
    offDiag a b (mulI y) = mulI (offDiag a b y) :=
  offDiag_mulI a b y

example (g : ℂ → ℂ) (ε : ℝ) (z : ℂ) :
    coeffPlus g ε z = g z * Complex.exp (((2 / ε : ℝ) : ℂ) * (I * z)) := rfl

example (g : ℂ → ℂ) (ε : ℝ) (z : ℂ) :
    coeffMinus g ε z = g z * Complex.exp (-(((2 / ε : ℝ) : ℂ) * (I * z))) := rfl

example (g : ℂ → ℂ) (ε : ℝ) (z : ℂ) :
    coeff g ε z = offDiag (coeffPlus g ε z) (coeffMinus g ε z) := rfl

example (g : ℂ → ℂ) (ε : ℝ) (z : ℂ) :
    ‖coeffPlus g ε z‖ = ‖g z‖ * Real.exp (-(2 / ε * z.im)) :=
  norm_coeffPlus g ε z

example (g : ℂ → ℂ) (ε : ℝ) (z : ℂ) :
    ‖coeffMinus g ε z‖ = ‖g z‖ * Real.exp (2 / ε * z.im) :=
  norm_coeffMinus g ε z

example (g : ℂ → ℂ) {ε σ : ℝ} (hε : 0 < ε) {z : ℂ} (h0 : 0 ≤ z.im)
    (hσ : z.im ≤ σ) :
    ‖coeff g ε z‖ ≤ ‖g z‖ * Real.exp (2 / ε * σ) :=
  norm_coeff_le g hε h0 hσ

example (g : ℂ → ℂ) (ε : ℝ) (z : ℂ) (y : ℂ × ℂ) :
    coeff g ε z (mulI y) = mulI (coeff g ε z y) :=
  coeff_mulI g ε z y

example (σ : ℝ) (q : ℝ × ℝ) :
    path σ q = (q.2 : ℂ) + ((σ * Real.smoothTransition q.1 : ℝ) : ℂ) * I := rfl

example (σ : ℝ) (q : ℝ × ℝ) :
    (path σ q).re = q.2 :=
  path_re σ q

example (σ : ℝ) (q : ℝ × ℝ) :
    (path σ q).im = σ * Real.smoothTransition q.1 :=
  path_im σ q

example (σ s : ℝ) :
    path σ (0, s) = (s : ℂ) :=
  path_zero σ s

example (σ s : ℝ) :
    path σ (1, s) = (s : ℂ) + (σ : ℂ) * I :=
  path_one σ s

example {σ : ℝ} (hσ : 0 ≤ σ) (q : ℝ × ℝ) :
    0 ≤ (path σ q).im :=
  path_im_nonneg hσ q

example {σ : ℝ} (hσ : 0 ≤ σ) (q : ℝ × ℝ) :
    (path σ q).im ≤ σ :=
  path_im_le hσ q

example (σ : ℝ) :
    ContDiff ℝ ∞ (path σ) :=
  contDiff_path σ

example (σ p : ℝ) : pathSpeed σ p = σ * deriv Real.smoothTransition p := rfl

example (σ p s : ℝ) :
    HasDerivAt (fun p' => path σ (p', s)) ((pathSpeed σ p : ℂ) * I) p :=
  hasDerivAt_path_fst σ p s

example (σ p s : ℝ) :
    HasDerivAt (fun s' => path σ (p, s')) 1 s :=
  hasDerivAt_path_snd σ p s

example (g : ℂ → ℂ) (ε σ : ℝ) (q : ℝ × ℝ) :
    family g ε σ q = coeff g ε (path σ q) := rfl

example (hg : DifferentiableOn ℂ g U) (ε : ℝ) :
    DifferentiableOn ℂ (coeffPlus g ε) U :=
  differentiableOn_coeffPlus hg ε

example (hg : DifferentiableOn ℂ g U) (ε : ℝ) :
    DifferentiableOn ℂ (coeffMinus g ε) U :=
  differentiableOn_coeffMinus hg ε

example {c : ℂ → ℂ} (hU : IsOpen U) (hc : DifferentiableOn ℂ c U)
    (hmem : ∀ q, path σ q ∈ U) :
    ContDiff ℝ ∞ fun q => c (path σ q) :=
  contDiff_comp_path hU hc hmem

example (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
    (hmem : ∀ q, path σ q ∈ U) (ε : ℝ) :
    ContDiff ℝ ∞ (family g ε σ) :=
  contDiff_family hU hg hmem ε

example {c : ℂ → ℂ} (hU : IsOpen U) (hc : DifferentiableOn ℂ c U)
    (hmem : ∀ q, path σ q ∈ U) (q : ℝ × ℝ) :
    fderiv ℝ (fun q => c (path σ q)) q (1, 0) =
      (pathSpeed σ q.1 : ℂ) * (I * fderiv ℝ (fun q => c (path σ q)) q (0, 1)) :=
  fderiv_comp_path_one_zero hU hc hmem q

example (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
    (hmem : ∀ q, path σ q ∈ U) (ε : ℝ) (q w : ℝ × ℝ) (y : ℂ × ℂ) :
    fderiv ℝ (family g ε σ) q w y =
      (fderiv ℝ (fun q => coeffPlus g ε (path σ q)) q w * y.2,
        fderiv ℝ (fun q => coeffMinus g ε (path σ q)) q w * y.1) :=
  fderiv_family_apply hU hg hmem ε q w y

example (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
    (hmem : ∀ q, path σ q ∈ U) (ε : ℝ) (q : ℝ × ℝ) (y : ℂ × ℂ) :
    fderiv ℝ (family g ε σ) q (1, 0) y =
      pathSpeed σ q.1 • mulI (fderiv ℝ (family g ε σ) q (0, 1) y) :=
  fderiv_family_one_zero hU hg hmem ε q y

example (g : ℂ → ℂ) (ε σ : ℝ) (q : ℝ × ℝ) (y : ℂ × ℂ) :
    family g ε σ q (mulI y) = mulI (family g ε σ q y) :=
  family_mulI g ε σ q y

example (σ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ Icc (0 : ℝ) 1, |pathSpeed σ p| ≤ C :=
  exists_abs_pathSpeed_le σ

example {a b : ℝ → ℂ} (ha : Continuous a) (hb : Continuous b) :
    Continuous fun s => offDiag (a s) (b s) :=
  continuous_offDiag ha hb

example (a b : ℝ → ℂ) (ha : Continuous a) (hb : Continuous b) (s : ℝ) :
    offDiagCurve a b ha hb s = offDiag (a s) (b s) := rfl

example (a b : ℝ → ℂ) (ha : Continuous a) (hb : Continuous b) (s : ℝ) :
    offDiagCurve a b ha hb s = offDiag (a s) (b s) :=
  offDiagCurve_apply a b ha hb s

example (κ : ℂ) (y : ℂ × ℂ) : scaleFst κ y = (κ * y.1, y.2) := rfl

example (κ : ℂ) (y : ℂ × ℂ) :
    scaleFst κ y = (κ * y.1, y.2) :=
  scaleFst_apply κ y

example {κ : ℂ} (hκ : κ ≠ 0) (a b : ℂ) (y : ℂ × ℂ) :
    offDiag a b (scaleFst κ y) = scaleFst κ (offDiag (κ⁻¹ * a) (κ * b) y) :=
  offDiag_scaleFst hκ a b y

example {κ : ℂ} (hκ : κ ≠ 0) {a b : ℝ → ℂ} (ha : Continuous a)
    (hb : Continuous b) (ha' : Continuous fun s => κ⁻¹ * a s)
    (hb' : Continuous fun s => κ * b s) (s₁ s₀ : ℝ) (y₀ : ℂ × ℂ) :
    propagator (offDiagCurve a b ha hb) s₁ s₀ (scaleFst κ y₀) =
      scaleFst κ (propagator
        (offDiagCurve (fun s => κ⁻¹ * a s) (fun s => κ * b s) ha' hb') s₁ s₀ y₀) :=
  propagator_scaleFst hκ ha hb ha' hb' s₁ s₀ y₀

example {a b : ℝ → ℂ} (ha : Continuous a) (hb : Continuous b)
    {m : ℝ → ℝ} (hm : Continuous m) (ham : ∀ s, ‖a s‖ ≤ m s) (hbm : ∀ s, ‖b s‖ ≤ m s)
    {G : ℝ} (hG : ∀ s₀ s₁ : ℝ, s₀ ≤ s₁ → ∫ r in s₀..s₁, m r ≤ G) {s₀ s₁ : ℝ} (hs : s₀ ≤ s₁)
    (y : ℂ × ℂ) :
    ‖propagator (offDiagCurve a b ha hb) s₁ s₀ y‖ ≤ Real.exp G * ‖y‖ :=
  norm_propagator_offDiagCurve_le ha hb hm ham hbm hG hs y

example (hc : Continuous (family g ε σ)) (p : ℝ)
    (hp : Continuous fun s : ℝ => coeffPlus g ε (path σ (p, s)))
    (hm : Continuous fun s : ℝ => coeffMinus g ε (path σ (p, s))) :
    coefficientCurve (family g ε σ) hc p =
      offDiagCurve (fun s => coeffPlus g ε (path σ (p, s)))
        (fun s => coeffMinus g ε (path σ (p, s))) hp hm :=
  coefficientCurve_family hc p hp hm

example (hc : Continuous (family g ε σ))
    (hcp : Continuous fun q => coeffPlus g ε (path σ q))
    (hcm : Continuous fun q => coeffMinus g ε (path σ q)) {m : ℝ → ℝ} (hm : Continuous m)
    (hbound : ∀ q : ℝ × ℝ, ‖g (path σ q)‖ ≤ m q.2) {G : ℝ}
    (hG : ∀ s₀ s₁ : ℝ, s₀ ≤ s₁ → ∫ r in s₀..s₁, m r ≤ G) {s₀ s₁ : ℝ} (hs : s₀ ≤ s₁) :
    ‖(propagator (coefficientCurve (family g ε σ) hc 1) s₁ s₀ (0, 1)).1‖ ≤
      Real.exp G * (Real.exp (2 / ε * σ))⁻¹ :=
  norm_fst_propagator_top_le hc hcp hcm hm hbound hG hs

example (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
    (hσ : 0 ≤ σ) (hmem : ∀ q, path σ q ∈ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ) (_ : 0 < ε) (m : ℝ → ℝ), Continuous m →
      (∀ q : ℝ × ℝ, ‖g (path σ q)‖ ≤ m q.2) → ∀ G : ℝ,
      (∀ s₀ s₁ : ℝ, s₀ ≤ s₁ → ∫ r in s₀..s₁, m r ≤ G) → ∀ s₀ s₁ : ℝ, s₀ ≤ s₁ →
      ‖(propagator (coefficientCurve (family g ε σ)
          (contDiff_family hU hg hmem ε).continuous 0) s₁ s₀ (0, 1)).1‖ ≤
        Real.exp G * (Real.exp (2 / ε * σ))⁻¹ +
          C * (Real.exp (Real.exp (2 / ε * σ) * G) *
            (Real.exp (2 / ε * σ) * (m s₁ + m s₀))) :=
  exists_norm_fst_propagator_le hU hg hσ hmem

end AmplitudeSystem

section AmplitudeReal

variable {a : ℝ → ℂ} (ha : Continuous a) (hb : Continuous fun s => conj (a s))

example (c : ℂ) (y : ℂ × ℂ) : cmul c y = (c * y.1, c * y.2) := rfl

example (c : ℂ) (y : ℂ × ℂ) :
    cmul c y = (c * y.1, c * y.2) :=
  cmul_apply c y

example (a b c : ℂ) (y : ℂ × ℂ) :
    offDiag a b (cmul c y) = cmul c (offDiag a b y) :=
  offDiag_cmul a b c y

example (y : ℂ × ℂ) : swapConj y = (conj y.2, conj y.1) := rfl

example (y : ℂ × ℂ) :
    swapConj y = (conj y.2, conj y.1) :=
  swapConj_apply y

example (a : ℂ) (y : ℂ × ℂ) :
    offDiag a (conj a) (swapConj y) = swapConj (offDiag a (conj a) y) :=
  offDiag_swapConj a y

example {b : ℝ → ℂ} (hb' : Continuous b) (c : ℂ) (s₁ s₀ : ℝ) (y : ℂ × ℂ) :
    propagator (offDiagCurve a b ha hb') s₁ s₀ (cmul c y) =
      cmul c (propagator (offDiagCurve a b ha hb') s₁ s₀ y) :=
  propagator_cmul ha hb' c s₁ s₀ y

example (s₁ s₀ : ℝ) (y : ℂ × ℂ) :
    propagator (offDiagCurve a (fun s => conj (a s)) ha hb) s₁ s₀ (swapConj y) =
      swapConj (propagator (offDiagCurve a (fun s => conj (a s)) ha hb) s₁ s₀ y) :=
  propagator_swapConj ha hb s₁ s₀ y

example (s₁ s₀ : ℝ) (y : ℂ × ℂ) :
    Complex.normSq (propagator (offDiagCurve a (fun s => conj (a s)) ha hb) s₁ s₀ y).1 -
        Complex.normSq (propagator (offDiagCurve a (fun s => conj (a s)) ha hb) s₁ s₀ y).2 =
      Complex.normSq y.1 - Complex.normSq y.2 :=
  normSq_sub_normSq_propagator ha hb s₁ s₀ y

example {n₁ n₀ A c : ℝ} (hn₁ : 0 ≤ n₁) (hn₀ : 0 ≤ n₀) (hA : 0 ≤ A)
    (hc : 0 ≤ c) (hsq : A ^ 2 - c ^ 2 = 1) (h1 : n₁ ≤ n₀ * A + n₀ * c)
    (h2 : n₀ * A ≤ n₁ + n₀ * c) :
    |n₁ ^ 2 - n₀ ^ 2| ≤ n₀ ^ 2 * (c * (4 * c + 2)) :=
  abs_sq_sub_sq_le hn₁ hn₀ hA hc hsq h1 h2

example (s₁ s₀ : ℝ) (B₀ : ℂ) :
    |Complex.normSq (propagator (offDiagCurve a (fun s => conj (a s)) ha hb) s₁ s₀
          (B₀, conj B₀)).1 - Complex.normSq B₀| ≤
      Complex.normSq B₀ *
        (‖(propagator (offDiagCurve a (fun s => conj (a s)) ha hb) s₁ s₀ (0, 1)).1‖ *
          (4 * ‖(propagator (offDiagCurve a (fun s => conj (a s)) ha hb) s₁ s₀ (0, 1)).1‖ +
            2)) :=
  abs_normSq_fst_propagator_sub_le ha hb s₁ s₀ B₀

end AmplitudeReal

section Oscillator

variable {g : ℂ → ℂ} {σ G : ℝ} {m : ℝ → ℝ} {U : Set ℂ} {q : ℝ → ℝ} {ε : ℝ}
  {ω θ x v : ℝ → ℝ}

example (h : IsStripProfile g σ m G U) : 0 < σ := h.pos

example (h : IsStripProfile g σ m G U) : IsOpen U := h.isOpen

example (h : IsStripProfile g σ m G U) {z : ℂ} (h0 : 0 ≤ z.im) (h1 : z.im ≤ σ) : z ∈ U :=
  h.mem z h0 h1

example (h : IsStripProfile g σ m G U) : DifferentiableOn ℂ g U := h.differentiableOn

example (h : IsStripProfile g σ m G U) (s : ℝ) : (g s).im = 0 := h.real s

example (h : IsStripProfile g σ m G U) {z : ℂ} (h0 : 0 ≤ z.im) (h1 : z.im ≤ σ) :
    ‖g z‖ ≤ m z.re := h.bound z h0 h1

example (h : IsStripProfile g σ m G U) : Continuous m := h.continuous

example (h : IsStripProfile g σ m G U) {s₀ s₁ : ℝ} (hs : s₀ ≤ s₁) :
    ∫ r in s₀..s₁, m r ≤ G := h.integral_le s₀ s₁ hs

example (h : IsStripProfile g σ m G U) : Tendsto m atTop (𝓝 0) := h.tendsto_atTop

example (h : IsStripProfile g σ m G U) : Tendsto m atBot (𝓝 0) := h.tendsto_atBot

example (h : IsStripProfile g σ m G U) (q : ℝ × ℝ) :
    path σ q ∈ U :=
  IsStripProfile.path_mem h q

example (h : IsStripProfile g σ m G U) (q : ℝ × ℝ) :
    ‖g (path σ q)‖ ≤ m q.2 :=
  IsStripProfile.norm_path_le h q

example (h : IsStripProfile g σ m G U) (s : ℝ) :
    (s : ℂ) ∈ U :=
  IsStripProfile.ofReal_mem h s

example (h : IsStripProfile g σ m G U) (s : ℝ) :
    ‖g s‖ ≤ m s :=
  IsStripProfile.norm_ofReal_le h s

example (h : IsStripProfile g σ m G U) (s : ℝ) :
    0 ≤ m s :=
  IsStripProfile.nonneg h s

example (h : IsStripProfile g σ m G U) (s : ℝ) :
    g s = (((g s).re : ℝ) : ℂ) :=
  IsStripProfile.eq_ofReal_re h s

example (h : IsStripProfile g σ m G U) (s : ℝ) :
    conj (g s) = g s :=
  IsStripProfile.conj_eq h s

example (h : IsStripProfile g σ m G U) (ε : ℝ) :
    Continuous fun s : ℝ => coeffPlus g ε (s : ℂ) :=
  IsStripProfile.continuous_coeffPlus h ε

example (h : IsStripProfile g σ m G U) (ε s : ℝ) :
    coeffMinus g ε (s : ℂ) = conj (coeffPlus g ε (s : ℂ)) :=
  IsStripProfile.coeffMinus_ofReal h ε s

example (g : ℂ → ℂ) (ε s : ℝ) :
    ‖coeffPlus g ε (s : ℂ)‖ = ‖g s‖ :=
  IsStripProfile.norm_coeffPlus_ofReal g ε s

example (h : IsStripProfile g σ m G U) (ε s : ℝ) (y : ℂ × ℂ) :
    h.realCurve ε s y =
      (coeffPlus g ε (s : ℂ) * y.2, conj (coeffPlus g ε (s : ℂ)) * y.1) := rfl

example (h : IsStripProfile g σ m G U) (ε s : ℝ) (y : ℂ × ℂ) :
    h.realCurve ε s y =
      (coeffPlus g ε (s : ℂ) * y.2, conj (coeffPlus g ε (s : ℂ)) * y.1) :=
  IsStripProfile.realCurve_apply h ε s y

example (h : IsStripProfile g σ m G U) (ε : ℝ)
    (hc : Continuous (family g ε σ)) :
    coefficientCurve (family g ε σ) hc 0 = h.realCurve ε :=
  IsStripProfile.coefficientCurve_zero h ε hc

example (h : IsStripProfile g σ m G U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ) (_ : 0 < ε) (s₀ s₁ : ℝ), s₀ ≤ s₁ →
      ‖(propagator (h.realCurve ε) s₁ s₀ (0, 1)).1‖ ≤
        Real.exp G * (Real.exp (2 / ε * σ))⁻¹ +
          C * (Real.exp (Real.exp (2 / ε * σ) * G) *
            (Real.exp (2 / ε * σ) * (m s₁ + m s₀))) :=
  IsStripProfile.exists_norm_fst_realCurve_le h

example (h : IsSlowOscillator g q ε ω θ x v) : 0 < ε := h.pos

example (h : IsSlowOscillator g q ε ω θ x v) (s : ℝ) : HasDerivAt q (2 * (g s).re) s :=
  h.hasDerivAt_log s

example (h : IsSlowOscillator g q ε ω θ x v) (t : ℝ) : ω t = Real.exp (q (ε * θ t)) :=
  h.frequency t

example (h : IsSlowOscillator g q ε ω θ x v) (t : ℝ) : HasDerivAt θ (ω t) t := h.hasDerivAt_phase t

example (h : IsSlowOscillator g q ε ω θ x v) (t : ℝ) : HasDerivAt x (v t) t :=
  h.hasDerivAt_position t

example (h : IsSlowOscillator g q ε ω θ x v) (t : ℝ) : HasDerivAt v (-(ω t) ^ 2 * x t) t :=
  h.hasDerivAt_velocity t

example (q : ℝ → ℝ) (ε : ℝ) (ω θ x v : ℝ → ℝ) (t : ℝ) :
    amplitude q ε ω θ x v t =
      (((ω t * x t : ℝ) : ℂ) + ((v t : ℝ) : ℂ) * I) * Complex.exp (((θ t : ℝ) : ℂ) * I) *
        ((Real.exp (-(q (ε * θ t) / 2)) : ℝ) : ℂ) := rfl

example (q : ℝ → ℝ) (ε : ℝ) (ω θ x v : ℝ → ℝ) (t : ℝ) :
    amplitudePair q ε ω θ x v t =
      (amplitude q ε ω θ x v t, conj (amplitude q ε ω θ x v t)) := rfl

example (ho : IsSlowOscillator g q ε ω θ x v) (t : ℝ) :
    0 < ω t :=
  IsSlowOscillator.frequency_pos ho t

example (ho : IsSlowOscillator g q ε ω θ x v) (t : ℝ) :
    Complex.normSq (amplitude q ε ω θ x v t) = 2 * action (ω t) (x t) (v t) :=
  IsSlowOscillator.normSq_amplitude ho t

example (ho : IsSlowOscillator g q ε ω θ x v) (t : ℝ) :
    HasDerivAt ω (2 * (g (ε * θ t : ℝ)).re * (ε * ω t) * ω t) t :=
  IsSlowOscillator.hasDerivAt_frequency ho t

example (ho : IsSlowOscillator g q ε ω θ x v) (t : ℝ) :
    HasDerivAt (amplitude q ε ω θ x v)
      (((ε * ω t * (g (ε * θ t : ℝ)).re : ℝ) : ℂ) *
        ((((ω t * x t : ℝ) : ℂ) - ((v t : ℝ) : ℂ) * I) * Complex.exp (((θ t : ℝ) : ℂ) * I) *
          ((Real.exp (-(q (ε * θ t) / 2)) : ℝ) : ℂ))) t :=
  IsSlowOscillator.hasDerivAt_amplitude ho t

example {σ G : ℝ} {m : ℝ → ℝ} {U : Set ℂ}
    (hp : IsStripProfile g σ m G U) (ho : IsSlowOscillator g q ε ω θ x v) (t : ℝ) :
    coeffPlus g ε ((ε * θ t : ℝ) : ℂ) * conj (amplitude q ε ω θ x v t) =
      (((g (ε * θ t : ℝ)).re : ℝ) : ℂ) *
        ((((ω t * x t : ℝ) : ℂ) - ((v t : ℝ) : ℂ) * I) * Complex.exp (((θ t : ℝ) : ℂ) * I) *
          ((Real.exp (-(q (ε * θ t) / 2)) : ℝ) : ℂ)) :=
  coeffPlus_mul_conj_amplitude hp ho t

example {σ G : ℝ} {m : ℝ → ℝ} {U : Set ℂ}
    (hp : IsStripProfile g σ m G U) (ho : IsSlowOscillator g q ε ω θ x v) (t : ℝ) :
    HasDerivAt (amplitudePair q ε ω θ x v)
      ((ε * ω t) • hp.realCurve ε (ε * θ t) (amplitudePair q ε ω θ x v t)) t :=
  hasDerivAt_amplitudePair hp ho t

example (ho : IsSlowOscillator g q ε ω θ x v) :
    Continuous θ :=
  IsSlowOscillator.continuous_phase ho

example (ho : IsSlowOscillator g q ε ω θ x v) :
    Continuous ω :=
  IsSlowOscillator.continuous_frequency ho

example {σ G : ℝ} {m : ℝ → ℝ} {U : Set ℂ}
    (hp : IsStripProfile g σ m G U) (ho : IsSlowOscillator g q ε ω θ x v) (t₀ t : ℝ) :
    amplitudePair q ε ω θ x v t =
      propagator (hp.realCurve ε) (ε * θ t) (ε * θ t₀) (amplitudePair q ε ω θ x v t₀) :=
  amplitudePair_eq_propagator hp ho t₀ t

example {σ G : ℝ} {m : ℝ → ℝ} {U : Set ℂ} (hp : IsStripProfile g σ m G U)
    (ho : IsSlowOscillator g q ε ω θ x v) (t₀ t₁ : ℝ) :
    |action (ω t₁) (x t₁) (v t₁) - action (ω t₀) (x t₀) (v t₀)| ≤
      action (ω t₀) (x t₀) (v t₀) *
        (‖(propagator (hp.realCurve ε) (ε * θ t₁) (ε * θ t₀) (0, 1)).1‖ *
          (4 * ‖(propagator (hp.realCurve ε) (ε * θ t₁) (ε * θ t₀) (0, 1)).1‖ + 2)) :=
  abs_action_sub_le hp ho t₀ t₁

example (m : ℝ → ℝ) (s : ℝ) : boundIntegral m s = ∫ r in (0 : ℝ)..s, m r := rfl

example (hp : IsStripProfile g σ m G U) (s : ℝ) :
    HasDerivAt (boundIntegral m) (m s) s :=
  IsStripProfile.hasDerivAt_boundIntegral hp s

example (hp : IsStripProfile g σ m G U) (s : ℝ) :
    |boundIntegral m s| ≤ G :=
  IsStripProfile.abs_boundIntegral_le hp s

example (hp : IsStripProfile g σ m G U) (s : ℝ) :
    |(g s).re| ≤ m s :=
  IsStripProfile.abs_re_le hp s

example (hp : IsStripProfile g σ m G U)
    (hq : ∀ s : ℝ, HasDerivAt q (2 * (g s).re) s) (s : ℝ) :
    |q s - q 0| ≤ 2 * G :=
  IsStripProfile.abs_log_sub_le hp hq s

example (hp : IsStripProfile g σ m G U)
    (hq : ∀ s : ℝ, HasDerivAt q (2 * (g s).re) s) (s : ℝ) :
    q 0 - 2 * G ≤ q s :=
  IsStripProfile.log_ge hp hq s

example (hp : IsStripProfile g σ m G U)
    (hq : ∀ s : ℝ, HasDerivAt q (2 * (g s).re) s) (s : ℝ) :
    q s ≤ q 0 + 2 * G :=
  IsStripProfile.log_le hp hq s

example (ho : IsSlowOscillator g q ε ω θ x v)
    (hp : IsStripProfile g σ m G U) (t : ℝ) :
    Real.exp (q 0 - 2 * G) ≤ ω t :=
  IsSlowOscillator.frequency_ge ho hp t

example (ho : IsSlowOscillator g q ε ω θ x v) :
    Monotone θ :=
  IsSlowOscillator.monotone_phase ho

example (ho : IsSlowOscillator g q ε ω θ x v)
    (hp : IsStripProfile g σ m G U) :
    Monotone fun t => θ t - Real.exp (q 0 - 2 * G) * t :=
  IsSlowOscillator.monotone_phase_sub ho hp

example (ho : IsSlowOscillator g q ε ω θ x v)
    (hp : IsStripProfile g σ m G U) :
    Tendsto θ atTop atTop :=
  IsSlowOscillator.tendsto_phase_atTop ho hp

example (ho : IsSlowOscillator g q ε ω θ x v)
    (hp : IsStripProfile g σ m G U) :
    Tendsto θ atBot atBot :=
  IsSlowOscillator.tendsto_phase_atBot ho hp

example {N W N' W' : ℝ → ℝ} {G : ℝ}
    (hN : ∀ t, HasDerivAt N (N' t) t) (hW : ∀ t, HasDerivAt W (W' t) t) (hN0 : ∀ t, 0 ≤ N t)
    (hW0 : ∀ t, 0 ≤ W' t) (hbound : ∀ t, |N' t| ≤ 2 * W' t * N t) (hG : ∀ t, |W t| ≤ G) :
    ∃ L₀ L₁ : ℝ, Tendsto N atBot (𝓝 L₀) ∧ Tendsto N atTop (𝓝 L₁) :=
  exists_tendsto_of_abs_deriv_le hN hW hN0 hW0 hbound hG

example {B : ℝ → ℂ} {B' : ℂ} {t : ℝ} (h : HasDerivAt B B' t) :
    HasDerivAt (fun t => Complex.normSq (B t)) (2 * (conj (B t) * B').re) t :=
  hasDerivAt_normSq h

example (ho : IsSlowOscillator g q ε ω θ x v)
    (hp : IsStripProfile g σ m G U) :
    ∃ I₀ I₁ : ℝ, Tendsto (fun t => action (ω t) (x t) (v t)) atBot (𝓝 I₀) ∧
      Tendsto (fun t => action (ω t) (x t) (v t)) atTop (𝓝 I₁) :=
  IsSlowOscillator.exists_tendsto_action ho hp

example (hp : IsStripProfile g σ m G U)
    (ho : IsSlowOscillator g q ε ω θ x v) {I₀ I₁ : ℝ}
    (h₀ : Tendsto (fun t => action (ω t) (x t) (v t)) atBot (𝓝 I₀))
    (h₁ : Tendsto (fun t => action (ω t) (x t) (v t)) atTop (𝓝 I₁)) :
    |I₁ - I₀| ≤ Real.exp G * (4 * Real.exp G + 2) * Real.exp (-(2 * σ / ε)) * I₀ :=
  abs_action_limit_sub_le hp ho h₀ h₁

example (hp : IsStripProfile g σ m G U)
    (ho : IsSlowOscillator g q ε ω θ x v) :
    ∃ I₀ I₁ : ℝ, Tendsto (fun t => action (ω t) (x t) (v t)) atBot (𝓝 I₀) ∧
      Tendsto (fun t => action (ω t) (x t) (v t)) atTop (𝓝 I₁) ∧
      |I₁ - I₀| ≤ Real.exp G * (4 * Real.exp G + 2) * Real.exp (-(2 * σ / ε)) * I₀ :=
  exists_tendsto_action_and_abs_sub_le hp ho

example (hp : IsStripProfile g σ m G U)
    (hq : ∀ s : ℝ, HasDerivAt q (2 * (g s).re) s) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) q :=
  IsStripProfile.contDiff_log hp hq

example (hp : IsStripProfile g σ m G U)
    (hq : ∀ s : ℝ, HasDerivAt q (2 * (g s).re) s) (ε : ℝ) :
    ∃ θ : ℝ → ℝ, θ 0 = 0 ∧ ∀ t, HasDerivAt θ (Real.exp (q (ε * θ t))) t :=
  IsStripProfile.exists_phase hp hq ε

example (hp : IsStripProfile g σ m G U)
    (hq : ∀ s : ℝ, HasDerivAt q (2 * (g s).re) s) {ε : ℝ} (hε : 0 < ε) (x₀ v₀ : ℝ) :
    ∃ ω θ x v : ℝ → ℝ, IsSlowOscillator g q ε ω θ x v ∧ x 0 = x₀ ∧ v 0 = v₀ :=
  IsStripProfile.exists_isSlowOscillator hp hq hε x₀ v₀

example (a : ℝ) (z : ℂ) : lorentzProfile a z = (a : ℂ) * z / (1 + z ^ 2) ^ 2 := rfl

example (a s : ℝ) : lorentzLog a s = -a / (1 + s ^ 2) := rfl

example (a s : ℝ) :
    lorentzProfile a (s : ℂ) = ((a * s / (1 + s ^ 2) ^ 2 : ℝ) : ℂ) :=
  lorentzProfile_ofReal a s

example (a s : ℝ) :
    HasDerivAt (lorentzLog a) (2 * (lorentzProfile a (s : ℂ)).re) s :=
  hasDerivAt_lorentzLog a s

example {z : ℂ} (hz : |z.im| < 1) :
    0 < (1 + z ^ 2).re :=
  one_add_sq_re_pos hz

example (a : ℝ) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    IsStripProfile (lorentzProfile a) σ
      (fun s => 2 * |a| / (1 - σ ^ 2) ^ 2 * (1 + s ^ 2)⁻¹) (2 * |a| / (1 - σ ^ 2) ^ 2 * π)
      {z : ℂ | |z.im| < 1} :=
  isStripProfile_lorentz a hσ0 hσ1

example (a : ℝ) {σ ε : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hε : 0 < ε)
    (x₀ v₀ : ℝ) :
    ∃ ω θ x v : ℝ → ℝ, IsSlowOscillator (lorentzProfile a) (lorentzLog a) ε ω θ x v ∧
      x 0 = x₀ ∧ v 0 = v₀ ∧
      ∃ I₀ I₁ : ℝ, Tendsto (fun t => action (ω t) (x t) (v t)) atBot (𝓝 I₀) ∧
        Tendsto (fun t => action (ω t) (x t) (v t)) atTop (𝓝 I₁) ∧
        |I₁ - I₀| ≤ Real.exp (2 * |a| / (1 - σ ^ 2) ^ 2 * π) *
          (4 * Real.exp (2 * |a| / (1 - σ ^ 2) ^ 2 * π) + 2) * Real.exp (-(2 * σ / ε)) * I₀ :=
  exists_lorentz_oscillator a hσ0 hσ1 hε x₀ v₀

end Oscillator
