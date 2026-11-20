/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.SmoothGeometry.Wave.RetardedIntegral
import ProjectAinos.Electrodynamics.RetardedPotential
import ProjectAinos.Electrodynamics.RetardedSpectrum

/-! Public consumers of the retarded potentials (Landau–Lifshitz §§62, 64): the flat retarded
integral with the identity `∫ (□f)(t − |y|, x − y)/(4π|y|) dy = f(t, x)`, its smoothness, the wave
equation, causal support and finite speed, and the transport to space-time; the retarded
potentials of a conserved current with the Lorenz condition, Maxwell's equations, causality,
uniqueness and the circulating-current instance; and their time Fourier transform with the
Helmholtz equation. Default elaborator options are intentional: these checks must not rely on the
implementation's transparency settings. Every statement is pinned with its type. -/

noncomputable section

section RetardedIntegral

open MeasureTheory Filter Set Metric Real

open scoped Topology ContDiff

namespace ProjectAinos.SmoothGeometry.Wave

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example (f : ℝ × E3 → ℝ) (p : ℝ × E3) :
    ℝ :=
  timeDeriv f p

example (i : Fin 3) (f : ℝ × E3 → ℝ) (p : ℝ × E3) :
    ℝ :=
  spaceDeriv i f p

example (f : ℝ × E3 → ℝ) (p : ℝ × E3) :
    ℝ :=
  waveOperator f p

example {y : E3} (hy : y ≠ 0) :
    HasFDerivAt (fun z : E3 => ‖z‖) (‖y‖⁻¹ • innerSL ℝ y) y :=
  hasFDerivAt_norm_of_ne_zero hy

example (y : E3) :
    E3 →L[ℝ] ℝ × E3 :=
  retardedDeriv y

example (t : ℝ) (x : E3) {y : E3} (hy : y ≠ 0) :
    HasFDerivAt (fun z : E3 => (t - ‖z‖, x - z)) (retardedDeriv y) y :=
  hasFDerivAt_retarded t x hy

example (b : ℝ × E3 → ℝ) (q : ℝ × E3) (y : E3) (i : Fin 3) :
    (fderiv ℝ b q).comp (retardedDeriv y) (EuclideanSpace.single i 1) =
      -(y i / ‖y‖) * timeDeriv b q - spaceDeriv i b q :=
  fderiv_retardedDeriv_single b q y i

example {b : ℝ × E3 → ℝ} (t : ℝ) (x : E3) {y : E3} (hy : y ≠ 0)
    (hb : DifferentiableAt ℝ b (t - ‖y‖, x - y)) :
    HasFDerivAt (fun z : E3 => b (t - ‖z‖, x - z))
      ((fderiv ℝ b (t - ‖y‖, x - y)).comp (retardedDeriv y)) y :=
  hasFDerivAt_comp_retarded t x hy hb

example {f : ℝ × E3 → ℝ} {q : ℝ × E3} (hf : ContDiffAt ℝ 2 f q) (v w : ℝ × E3) :
    fderiv ℝ (fun p => fderiv ℝ f p w) q v = fderiv ℝ (fderiv ℝ f) q v w :=
  fderiv_fderiv_apply_eq hf v w

example {f : ℝ × E3 → ℝ} {q : ℝ × E3} (hf : ContDiffAt ℝ 2 f q) (i : Fin 3) :
    timeDeriv (spaceDeriv i f) q = spaceDeriv i (timeDeriv f) q :=
  timeDeriv_spaceDeriv hf i

example (f : ℝ × E3 → ℝ) (t : ℝ) (x : E3) (i : Fin 3) (y : E3) :
    ℝ :=
  retardedField f t x i y

example {n : ℕ∞ω} {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ (n + 1) f) :
    ContDiff ℝ n (timeDeriv f) :=
  contDiff_timeDeriv hf

example {n : ℕ∞ω} {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ (n + 1) f) (i : Fin 3) :
    ContDiff ℝ n (spaceDeriv i f) :=
  contDiff_spaceDeriv hf i

example {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ 2 f) (t : ℝ) (x : E3) {y : E3} (hy : y ≠ 0) (i : Fin 3) :
    fderiv ℝ (retardedField f t x i) y (EuclideanSpace.single i 1) =
      (-(y i / ‖y‖) * timeDeriv (spaceDeriv i f) (t - ‖y‖, x - y) -
          spaceDeriv i (spaceDeriv i f) (t - ‖y‖, x - y)) * ‖y‖⁻¹ -
        spaceDeriv i f (t - ‖y‖, x - y) * (y i / ‖y‖ ^ 3) -
        ((-(y i / ‖y‖) * timeDeriv (timeDeriv f) (t - ‖y‖, x - y) -
          spaceDeriv i (timeDeriv f) (t - ‖y‖, x - y)) * (y i / ‖y‖ ^ 2) +
          timeDeriv f (t - ‖y‖, x - y) * (1 / ‖y‖ ^ 2 - 2 * y i ^ 2 / ‖y‖ ^ 4)) -
        ((-(y i / ‖y‖) * timeDeriv f (t - ‖y‖, x - y) - spaceDeriv i f (t - ‖y‖, x - y)) *
            (y i / ‖y‖ ^ 3) +
          f (t - ‖y‖, x - y) * (1 / ‖y‖ ^ 3 - 3 * y i ^ 2 / ‖y‖ ^ 5)) :=
  fderiv_retardedField_single hf t x hy i

example {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ 2 f) (t : ℝ) (x : E3) {y : E3} (hy : y ≠ 0) :
    ∑ i, fderiv ℝ (retardedField f t x i) y (EuclideanSpace.single i 1) =
      waveOperator f (t - ‖y‖, x - y) / ‖y‖ :=
  sum_fderiv_retardedField hf t x hy

example (f : ℝ × E3 → ℝ) :
    tsupport (timeDeriv f) ⊆ tsupport f :=
  tsupport_timeDeriv_subset f

example (i : Fin 3) (f : ℝ × E3 → ℝ) :
    tsupport (spaceDeriv i f) ⊆ tsupport f :=
  tsupport_spaceDeriv_subset i f

example {f : ℝ × E3 → ℝ} {q : ℝ × E3} (hq : q ∉ tsupport f) :
    timeDeriv f q = 0 :=
  timeDeriv_eq_zero_of_notMem hq

example {f : ℝ × E3 → ℝ} {q : ℝ × E3} (hq : q ∉ tsupport f) (i : Fin 3) :
    spaceDeriv i f q = 0 :=
  spaceDeriv_eq_zero_of_notMem hq i

example {f : ℝ × E3 → ℝ} {q : ℝ × E3} (hq : q ∉ tsupport f) :
    waveOperator f q = 0 :=
  waveOperator_eq_zero_of_notMem hq

example (s : ℝ) :
    HasDerivAt smoothTransition (deriv smoothTransition s) s :=
  hasDerivAt_smoothTransition s

example (s : ℝ) :
    0 ≤ deriv smoothTransition s :=
  deriv_smoothTransition_nonneg s

example {s : ℝ} (hs : s < 0) :
    deriv smoothTransition s = 0 :=
  deriv_smoothTransition_of_neg hs

example {s : ℝ} (hs : 1 < s) :
    deriv smoothTransition s = 0 :=
  deriv_smoothTransition_of_one_lt hs

example :
    ∫ r in Ioi (0 : ℝ), deriv smoothTransition (r - 1) = 1 :=
  integral_Ioi_deriv_smoothTransition

example (z : E3) :
    ℝ :=
  shellKernel z

example (z : E3) :
    0 ≤ shellKernel z :=
  shellKernel_nonneg z

example :
    ∫ z, shellKernel z = 1 :=
  integral_shellKernel

example {z : E3} (hz : 2 < ‖z‖) :
    shellKernel z = 0 :=
  shellKernel_eq_zero_of_two_lt hz

example :
    Tendsto (fun z : E3 => ‖z‖ ^ Module.finrank ℝ E3 * shellKernel z) (Bornology.cobounded E3)
      (𝓝 0) :=
  tendsto_norm_pow_mul_shellKernel

example (ε : ℝ) (y : E3) :
    ℝ :=
  cutoff ε y

example {ε : ℝ} (hε : 0 < ε) {y : E3} (hy : ‖y‖ ≤ ε) :
    cutoff ε y = 0 :=
  cutoff_eq_zero hε hy

example {ε : ℝ} (hε : 0 < ε) {y : E3} (hy : 2 * ε ≤ ‖y‖) :
    cutoff ε y = 1 :=
  cutoff_eq_one hε hy

example {ε : ℝ} (hε : 0 < ε) :
    cutoff ε =ᶠ[𝓝 0] fun _ => 0 :=
  cutoff_eventuallyEq_zero hε

example (ε : ℝ) {y : E3} (hy : y ≠ 0) :
    HasFDerivAt (cutoff ε)
      (deriv smoothTransition (‖y‖ / ε - 1) • (ε⁻¹ • (‖y‖⁻¹ • innerSL ℝ y))) y :=
  hasFDerivAt_cutoff ε hy

example {ε : ℝ} (hε : 0 < ε) {n : ℕ∞} :
    ContDiff ℝ n (cutoff ε) :=
  contDiff_cutoff hε

example (ε : ℝ) (y : E3) :
    cutoff ε y ∈ Icc (0 : ℝ) 1 :=
  cutoff_mem_Icc ε y

example (f : ℝ × E3 → ℝ) (t : ℝ) (x : E3) (y : E3) :
    ℝ :=
  fluxDensity f t x y

example {f : ℝ × E3 → ℝ} (t : ℝ) (x : E3) {y : E3} (hy : y ≠ 0) :
    ∑ i, retardedField f t x i y * y i = -fluxDensity f t x y / ‖y‖ :=
  sum_retardedField_mul t x hy

example {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ 2 f) (t : ℝ) (x : E3) {y : E3} (hy : y ≠ 0) (i : Fin 3) :
    ContDiffAt ℝ 1 (retardedField f t x i) y :=
  contDiffAt_retardedField hf t x hy i

example {f : ℝ × E3 → ℝ} {t : ℝ} {x y : E3} (hy : (t - ‖y‖, x - y) ∉ tsupport f) (i : Fin 3) :
    retardedField f t x i y = 0 :=
  retardedField_eq_zero hy i

example {f : ℝ × E3 → ℝ} {t : ℝ} {x y : E3} (hy : (t - ‖y‖, x - y) ∉ tsupport f) :
    fluxDensity f t x y = 0 :=
  fluxDensity_eq_zero hy

example {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ 1 f) (t : ℝ) (x : E3) :
    Continuous (fluxDensity f t x) :=
  continuous_fluxDensity hf t x

example (f : ℝ × E3 → ℝ) (t : ℝ) (x : E3) :
    fluxDensity f t x 0 = f (t, x) :=
  fluxDensity_zero f t x

example {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (waveOperator f) :=
  continuous_waveOperator hf

example {W : E3 → ℝ} (hW : ContDiff ℝ 1 W) (hc : HasCompactSupport W) (v : E3) :
    ∫ y, fderiv ℝ W y v = 0 :=
  integral_fderiv_eq_zero hW hc v

example {f : ℝ × E3 → ℝ} {t : ℝ} {x : E3} {L : ℝ}
    (hL : ∀ y : E3, L ≤ ‖y‖ → (t - ‖y‖, x - y) ∉ tsupport f) :
    HasCompactSupport fun y : E3 => waveOperator f (t - ‖y‖, x - y) :=
  hasCompactSupport_waveOperator_retarded hL

example {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ 2 f) {t : ℝ} {x : E3} {L : ℝ}
    (hL : ∀ y : E3, L ≤ ‖y‖ → (t - ‖y‖, x - y) ∉ tsupport f) :
    Integrable fun y : E3 => waveOperator f (t - ‖y‖, x - y) / ‖y‖ :=
  integrable_wave_div_norm hf hL

example {ε : ℝ} (hε : 0 < ε) (y : E3) :
    4 * π * (ε⁻¹ ^ 3 * shellKernel (ε⁻¹ • y)) =
      deriv smoothTransition (‖y‖ / ε - 1) * (ε⁻¹ * ‖y‖⁻¹) * ‖y‖⁻¹ :=
  shellKernel_smul hε y

example {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ 2 f) (t : ℝ) (x : E3) {L : ℝ}
    (hL : ∀ y : E3, L ≤ ‖y‖ → (t - ‖y‖, x - y) ∉ tsupport f) {ε : ℝ} (hε : 0 < ε) :
    ∫ y, waveOperator f (t - ‖y‖, x - y) / ‖y‖ * cutoff ε y =
      4 * π * ∫ y, ε⁻¹ ^ 3 * shellKernel (ε⁻¹ • y) * fluxDensity f t x y :=
  integral_wave_mul_cutoff hf t x hL hε

example {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ 2 f) (t : ℝ) (x : E3) {L : ℝ}
    (hL : ∀ y : E3, L ≤ ‖y‖ → (t - ‖y‖, x - y) ∉ tsupport f) :
    ∫ y, waveOperator f (t - ‖y‖, x - y) / ‖y‖ = 4 * π * f (t, x) :=
  integral_wave_div_norm_eq_mul hf t x hL

example {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ 2 f) (t : ℝ) (x : E3) {L : ℝ}
    (hL : ∀ y : E3, L ≤ ‖y‖ → (t - ‖y‖, x - y) ∉ tsupport f) :
    ∫ y, waveOperator f (t - ‖y‖, x - y) / (4 * π * ‖y‖) = f (t, x) :=
  integral_wave_div_norm hf t x hL

section RetardedIntegral

variable {G : Type*} [NormedAddCommGroup G]

example {G' : Type*} [NormedAddCommGroup G'] {R v₀ : ℝ} {f : ℝ × E3 → G} {g : ℝ × E3 → G'}
    (hf : SubluminalSupport R v₀ f) (hg : tsupport g ⊆ tsupport f) :
    SubluminalSupport R v₀ g :=
  SubluminalSupport.mono hf hg

example {f : ℝ × E3 → G} (hf : HasCompactSupport f) :
    ∃ R, SubluminalSupport R 0 f :=
  exists_subluminalSupport_of_hasCompactSupport hf

example (R v₀ : ℝ) (p₀ : ℝ × E3) :
    ℝ :=
  pastRadius R v₀ p₀

example {R v₀ : ℝ} {f : ℝ × E3 → G} (hf : SubluminalSupport R v₀ f) {p₀ p : ℝ × E3}
    (hp : dist p p₀ < 1) {y : E3} (hy : pastRadius R v₀ p₀ ≤ ‖y‖) :
    p - (‖y‖, y) ∉ tsupport f :=
  SubluminalSupport.notMem_tsupport hf hp hy

example {R v₀ : ℝ} {f : ℝ × E3 → G} (hf : SubluminalSupport R v₀ f) (p : ℝ × E3) :
    HasCompactSupport fun y : E3 => f (p - (‖y‖, y)) :=
  SubluminalSupport.hasCompactSupport_comp hf p

variable [NormedSpace ℝ G]

example {R v₀ : ℝ} {f : ℝ × E3 → G} (hf : SubluminalSupport R v₀ f) :
    SubluminalSupport R v₀ (fderiv ℝ f) :=
  SubluminalSupport.fderiv hf

example (f : ℝ × E3 → G) (p : ℝ × E3) :
    G :=
  retardedIntegral f p

example (f : ℝ × E3 → ℝ) (t : ℝ) (x : E3) :
    retardedIntegral f (t, x) = ∫ y, f (t - ‖y‖, x - y) / (4 * π * ‖y‖) :=
  retardedIntegral_apply f t x

example {R v₀ : ℝ} {f : ℝ × E3 → G} (hf : SubluminalSupport R v₀ f) (hc : Continuous f)
    (p : ℝ × E3) :
    Integrable fun y : E3 => (4 * π * ‖y‖)⁻¹ • f (p - (‖y‖, y)) :=
  SubluminalSupport.integrable hf hc p

example {R v₀ : ℝ} {f : ℝ × E3 → G} (hf : SubluminalSupport R v₀ f) (hc : Continuous f)
    (p₀ : ℝ × E3) :
    ∃ C, ∀ p ∈ ball p₀ 1, ∀ y : E3, ‖(4 * π * ‖y‖)⁻¹ • f (p - (‖y‖, y))‖ ≤
      (closedBall (0 : E3) (pastRadius R v₀ p₀)).indicator
        (fun y => C * Potential.newtonKernel y) y :=
  SubluminalSupport.exists_bound hf hc p₀

example (C ρ : ℝ) :
    Integrable ((closedBall (0 : E3) ρ).indicator fun y => C * Potential.newtonKernel y) :=
  integrable_indicator_newtonKernel C ρ

example {R v₀ : ℝ} {f : ℝ × E3 → G} (hc : Continuous f) (hf : SubluminalSupport R v₀ f) :
    Continuous (retardedIntegral f) :=
  continuous_retardedIntegral hc hf

example [CompleteSpace G] {R v₀ : ℝ} {f : ℝ × E3 → G} (hc : ContDiff ℝ 1 f)
    (hf : SubluminalSupport R v₀ f) (p₀ : ℝ × E3) :
    HasFDerivAt (retardedIntegral f) (retardedIntegral (fderiv ℝ f) p₀) p₀ :=
  hasFDerivAt_retardedIntegral hc hf p₀

example [CompleteSpace G] {R v₀ : ℝ} {f : ℝ × E3 → G} (hc : ContDiff ℝ 1 f)
    (hf : SubluminalSupport R v₀ f) :
    fderiv ℝ (retardedIntegral f) = retardedIntegral (fderiv ℝ f) :=
  fderiv_retardedIntegral hc hf

example [CompleteSpace G] {R v₀ : ℝ} {F : ℝ × E3 → ℝ × E3 →L[ℝ] G} (hc : Continuous F)
    (hF : SubluminalSupport R v₀ F) (p : ℝ × E3) (v : ℝ × E3) :
    retardedIntegral F p v = retardedIntegral (fun q => F q v) p :=
  retardedIntegral_apply_clm hc hF p v

example [CompleteSpace G] {R v₀ : ℝ} (n : ℕ) {f : ℝ × E3 → G} (hc : ContDiff ℝ n f)
    (hf : SubluminalSupport R v₀ f) :
    ContDiff ℝ n (retardedIntegral f) :=
  contDiff_retardedIntegral_nat n hc hf

example [CompleteSpace G] {R v₀ : ℝ} {n : ℕ∞} {f : ℝ × E3 → G} (hc : ContDiff ℝ n f)
    (hf : SubluminalSupport R v₀ f) :
    ContDiff ℝ n (retardedIntegral f) :=
  contDiff_retardedIntegral hc hf

example {f g : ℝ × E3 → G} {p : ℝ × E3}
    (hf : Integrable fun y : E3 => (4 * π * ‖y‖)⁻¹ • f (p - (‖y‖, y)))
    (hg : Integrable fun y : E3 => (4 * π * ‖y‖)⁻¹ • g (p - (‖y‖, y))) :
    retardedIntegral (fun q => f q + g q) p = retardedIntegral f p + retardedIntegral g p :=
  retardedIntegral_add hf hg

example {ι : Type*} (s : Finset ι) {f : ι → ℝ × E3 → G} {p : ℝ × E3}
    (hf : ∀ i ∈ s, Integrable fun y : E3 => (4 * π * ‖y‖)⁻¹ • f i (p - (‖y‖, y))) :
    retardedIntegral (fun q => ∑ i ∈ s, f i q) p = ∑ i ∈ s, retardedIntegral (f i) p :=
  retardedIntegral_finsetSum s hf

example (p : ℝ × E3) :
    retardedIntegral (fun _ => (0 : G)) p = 0 :=
  retardedIntegral_zero p

example {χ : E3 → G} {R : ℝ} (hχ : tsupport χ ⊆ closedBall 0 R) {w : E3} (hw : ‖w‖ < 1) :
    SubluminalSupport R ‖w‖ fun p : ℝ × E3 => χ (p.2 - p.1 • w) :=
  subluminalSupport_moving hχ hw

example :
    ContDiffBump (0 : E3) :=
  spaceBump

example :
    SubluminalSupport 2 (1 / 2) fun p : ℝ × E3 =>
      spaceBump (p.2 - p.1 • ((1 / 2 : ℝ) • EuclideanSpace.single 0 1)) :=
  subluminalSupport_movingBump

end RetardedIntegral

example {R v₀ : ℝ} {f : ℝ × E3 → ℝ} (hc : ContDiff ℝ 2 f) (hf : SubluminalSupport R v₀ f) (t : ℝ)
    (x : E3) :
    ∫ y, waveOperator f (t - ‖y‖, x - y) / (4 * π * ‖y‖) = f (t, x) :=
  integral_wave_div_norm_of_subluminalSupport hc hf t x

example {R v₀ : ℝ} {f : ℝ × E3 → ℝ} (hf : SubluminalSupport R v₀ f) :
    SubluminalSupport R v₀ (timeDeriv f) :=
  SubluminalSupport.timeDeriv hf

example {R v₀ : ℝ} {f : ℝ × E3 → ℝ} (hf : SubluminalSupport R v₀ f) (i : Fin 3) :
    SubluminalSupport R v₀ (spaceDeriv i f) :=
  SubluminalSupport.spaceDeriv hf i

example {R v₀ : ℝ} {f : ℝ × E3 → ℝ} (hf : SubluminalSupport R v₀ f) :
    SubluminalSupport R v₀ (waveOperator f) :=
  SubluminalSupport.waveOperator hf

example {R v₀ : ℝ} {f : ℝ × E3 → ℝ} (hc : ContDiff ℝ 1 f) (hf : SubluminalSupport R v₀ f) :
    timeDeriv (retardedIntegral f) = retardedIntegral (timeDeriv f) :=
  timeDeriv_retardedIntegral hc hf

example {R v₀ : ℝ} {f : ℝ × E3 → ℝ} (hc : ContDiff ℝ 1 f) (hf : SubluminalSupport R v₀ f)
    (i : Fin 3) :
    spaceDeriv i (retardedIntegral f) = retardedIntegral (spaceDeriv i f) :=
  spaceDeriv_retardedIntegral hc hf i

example {R v₀ : ℝ} {f : ℝ × E3 → ℝ} (hc : ContDiff ℝ 2 f) (hf : SubluminalSupport R v₀ f) :
    waveOperator (retardedIntegral f) = retardedIntegral (waveOperator f) :=
  waveOperator_retardedIntegral hc hf

example {R v₀ : ℝ} {f : ℝ × E3 → ℝ} (hc : ContDiff ℝ 2 f) (hf : SubluminalSupport R v₀ f)
    (p : ℝ × E3) :
    waveOperator (retardedIntegral f) p = f p :=
  wave_retardedIntegral hc hf p

example (p : ℝ × E3) :
    Set (ℝ × E3) :=
  pastCone p

example (p : ℝ × E3) (y : E3) :
    p - (‖y‖, y) ∈ pastCone p :=
  sub_mem_pastCone p y

example {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {f : ℝ × E3 → G} {p : ℝ × E3}
    (h : Disjoint (pastCone p) (Function.support f)) :
    retardedIntegral f p = 0 :=
  retardedIntegral_eq_zero_of_support h

example {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {f : ℝ × E3 → G} {T : ℝ}
    (hT : ∀ q : ℝ × E3, q.1 ≤ T → f q = 0) {p : ℝ × E3} (hp : p.1 ≤ T) :
    retardedIntegral f p = 0 :=
  retardedIntegral_eq_zero_of_le hT hp

example {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {f : ℝ × E3 → G} {T ρ : ℝ}
    (hsupp : ∀ q : ℝ × E3, f q ≠ 0 → T ≤ q.1 ∧ ‖q.2‖ ≤ ρ) {p : ℝ × E3}
    (hp : ρ + (p.1 - T) < ‖p.2‖) :
    retardedIntegral f p = 0 :=
  retardedIntegral_eq_zero_of_far hsupp hp

example {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {R v₀ : ℝ} {f : ℝ × E3 → G}
    (hf : SubluminalSupport R v₀ f) {T₀ T : ℝ} (hpast : ∀ q : ℝ × E3, f q ≠ 0 → T₀ ≤ q.1)
    {p : ℝ × E3} (hpT : p.1 ≤ T) (hne : retardedIntegral f p ≠ 0) :
    ‖p.2‖ ≤ R + v₀ * (|T₀| + |T|) + (T - T₀) :=
  norm_le_of_retardedIntegral_ne_zero hf hpast hpT hne

example :
    MinkowskiModel 3 ≃L[ℝ] ℝ × E3 :=
  timeSpaceEquiv

example (v : MinkowskiModel 3) :
    timeSpaceEquiv v = (v 0, Minkowski.space v) :=
  timeSpaceEquiv_apply v

example (p : ℝ × E3) :
    timeSpaceEquiv.symm p = Minkowski.vector p.1 p.2 :=
  timeSpaceEquiv_symm_apply p

example :
    timeSpaceEquiv (Pi.single 0 1) = ((1 : ℝ), (0 : E3)) :=
  timeSpaceEquiv_single_zero

example (i : Fin 3) :
    timeSpaceEquiv (Pi.single i.succ 1) = ((0 : ℝ), EuclideanSpace.single i 1) :=
  timeSpaceEquiv_single_succ i

example {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {u : ℝ × E3 → G}
    {v : MinkowskiModel 3} (hu : DifferentiableAt ℝ u (timeSpaceEquiv v)) (w : MinkowskiModel 3) :
    fderiv ℝ (fun z => u (timeSpaceEquiv z)) v w =
      fderiv ℝ u (timeSpaceEquiv v) (timeSpaceEquiv w) :=
  fderiv_comp_timeSpaceEquiv hu w

example {u : ℝ × E3 → ℝ} (hu : Differentiable ℝ u) :
    (fun v => fderiv ℝ (fun z => u (timeSpaceEquiv z)) v (Pi.single 0 1)) =
      fun v => timeDeriv u (timeSpaceEquiv v) :=
  fderiv_comp_timeSpaceEquiv_zero hu

example {u : ℝ × E3 → ℝ} (hu : Differentiable ℝ u) (i : Fin 3) :
    (fun v => fderiv ℝ (fun z => u (timeSpaceEquiv z)) v (Pi.single i.succ 1)) =
      fun v => spaceDeriv i u (timeSpaceEquiv v) :=
  fderiv_comp_timeSpaceEquiv_succ hu i

example {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (k : MinkowskiModel 3 → G)
    (v : MinkowskiModel 3) :
    retardedIntegral (fun p => k (timeSpaceEquiv.symm p)) (timeSpaceEquiv v) =
      ∫ y, (4 * π * ‖y‖)⁻¹ • k (v - Minkowski.vector ‖y‖ y) :=
  retardedIntegral_comp_symm k v

end ProjectAinos.SmoothGeometry.Wave

end RetardedIntegral

section RetardedPotential

open MeasureTheory Filter Set Metric

open scoped Topology ContDiff

namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example {u : ℝ × E3 → ℝ} (hu : ContDiff ℝ 2 u) (v : Spacetime) :
    box (fun w => u (Wave.timeSpaceEquiv w)) v =
      -Wave.waveOperator u (Wave.timeSpaceEquiv v) :=
  box_comp_timeSpaceEquiv hu v

example (g : Spacetime → ℝ) (v : Spacetime) :
    ℝ :=
  retardedScalar g v

example (g : Spacetime → ℝ) (v : Spacetime) :
    retardedScalar g v = ∫ y : E3, g (v - Minkowski.vector ‖y‖ y) / (4 * Real.pi * ‖y‖) :=
  retardedScalar_eq g v

example {g : Spacetime → ℝ} (hg : Differentiable ℝ g) (p w : ℝ × E3) :
    fderiv ℝ (fun q => g (Wave.timeSpaceEquiv.symm q)) p w =
      fderiv ℝ g (Wave.timeSpaceEquiv.symm p) (Wave.timeSpaceEquiv.symm w) :=
  fderiv_comp_timeSpaceEquiv_symm hg p w

example {n : ℕ∞} {g : Spacetime → ℝ} (hg : ContDiff ℝ n g) {R v₀ : ℝ}
    (hs : Wave.SubluminalSupport R v₀ fun p => g (Wave.timeSpaceEquiv.symm p)) :
    ContDiff ℝ n (retardedScalar g) :=
  contDiff_retardedScalar hg hs

example {g : Spacetime → ℝ} (hg : ContDiff ℝ 2 g) {R v₀ : ℝ}
    (hs : Wave.SubluminalSupport R v₀ fun p => g (Wave.timeSpaceEquiv.symm p)) :
    ContDiff ℝ 2 (retardedScalar g) :=
  contDiff_two_retardedScalar hg hs

example {g : Spacetime → ℝ} (hg : ContDiff ℝ 2 g) {R v₀ : ℝ}
    (hs : Wave.SubluminalSupport R v₀ fun p => g (Wave.timeSpaceEquiv.symm p)) (v : Spacetime) :
    box (retardedScalar g) v = -g v :=
  box_retardedScalar hg hs v

example {g : Spacetime → ℝ} (hg : ContDiff ℝ 1 g) {R v₀ : ℝ}
    (hs : Wave.SubluminalSupport R v₀ fun p => g (Wave.timeSpaceEquiv.symm p)) (μ : Fin 4) :
    partialAt (retardedScalar g) μ = retardedScalar (partialAt g μ) :=
  partialAt_retardedScalar hg hs μ

example {g : Spacetime → ℝ} {T : ℝ} (hpast : ∀ v : Spacetime, v 0 ≤ T → g v = 0) {v : Spacetime}
    (hv : v 0 ≤ T) :
    retardedScalar g v = 0 :=
  retardedScalar_eq_zero_of_le hpast hv

example {k : Spacetime → Spacetime} {R v₀ : ℝ}
    (hs : Wave.SubluminalSupport R v₀ fun p => k (Wave.timeSpaceEquiv.symm p)) (μ : Fin 4) :
    Wave.SubluminalSupport R v₀ fun p => k (Wave.timeSpaceEquiv.symm p) μ :=
  subluminalSupport_component hs μ

example (k : Spacetime → Spacetime) :
    Potential :=
  retardedPotential k

example (k : Spacetime → Spacetime) :
    potentialComponent (retardedPotential k) 0 = fun v => -retardedScalar (fun w => k w 0) v :=
  potentialComponent_retardedPotential_zero k

example (k : Spacetime → Spacetime) (i : Fin 3) :
    potentialComponent (retardedPotential k) i.succ = retardedScalar fun w => k w i.succ :=
  potentialComponent_retardedPotential_succ k i

example {k : Spacetime → Spacetime} (hk : ContDiff ℝ 2 k) {R v₀ : ℝ}
    (hs : Wave.SubluminalSupport R v₀ fun p => k (Wave.timeSpaceEquiv.symm p)) :
    ContDiff ℝ 2 (retardedPotential k) :=
  contDiff_retardedPotential hk hs

example {k : Spacetime → Spacetime} {v : Spacetime} (hk : DifferentiableAt ℝ k v) (μ ν : Fin 4) :
    partialAt (fun w => k w μ) ν v = fderiv ℝ k v (Pi.single ν 1) μ :=
  partialAt_component_eq hk μ ν

example {g : Spacetime → ℝ} (hg : Differentiable ℝ g) {R v₀ : ℝ}
    (hs : Wave.SubluminalSupport R v₀ fun p => g (Wave.timeSpaceEquiv.symm p)) (μ : Fin 4) :
    Wave.SubluminalSupport R v₀ fun p => partialAt g μ (Wave.timeSpaceEquiv.symm p) :=
  subluminalSupport_partialAt hg hs μ

example {ι : Type*} (s : Finset ι) {F : ι → Spacetime → ℝ} (hc : ∀ i ∈ s, Continuous (F i))
    {R v₀ : ℝ}
    (hs : ∀ i ∈ s, Wave.SubluminalSupport R v₀ fun p => F i (Wave.timeSpaceEquiv.symm p))
    (v : Spacetime) :
    retardedScalar (fun w => ∑ i ∈ s, F i w) v = ∑ i ∈ s, retardedScalar (F i) v :=
  retardedScalar_finsetSum s hc hs v

example {k : Spacetime → Spacetime} {v : Spacetime} (hk : DifferentiableAt ℝ k v) :
    divergence4 k v = ∑ μ : Fin 4, partialAt (fun w => k w μ) μ v :=
  divergence4_eq_sum_partialAt hk

example {k : Spacetime → Spacetime} (hk : ContDiff ℝ 2 k) {R v₀ : ℝ}
    (hs : Wave.SubluminalSupport R v₀ fun p => k (Wave.timeSpaceEquiv.symm p))
    (hdiv : ∀ v, divergence4 k v = 0) (v : Spacetime) :
    lorenzDivergence (retardedPotential k) v = 0 :=
  lorenz_retardedPotential hk hs hdiv v

example {k : Spacetime → Spacetime} (hk : ContDiff ℝ 2 k) {R v₀ : ℝ}
    (hs : Wave.SubluminalSupport R v₀ fun p => k (Wave.timeSpaceEquiv.symm p)) (v : Spacetime) :
    box (potentialComponent (retardedPotential k) 0) v = k v 0 ∧
      ∀ i : Fin 3, box (potentialComponent (retardedPotential k) i.succ) v = -k v i.succ :=
  box_retardedPotential hk hs v

example {k : Spacetime → Spacetime} (hk : ContDiff ℝ 2 k) {R v₀ : ℝ}
    (hs : Wave.SubluminalSupport R v₀ fun p => k (Wave.timeSpaceEquiv.symm p))
    (hdiv : ∀ v, divergence4 k v = 0) (y : Spacetime) :
    (divergence3 (magneticField (fieldTensor (retardedPotential k))) y = 0 ∧
        ∀ i, partialAt (magneticField (fieldTensor (retardedPotential k)) i) 0 y +
          curl (electricField (fieldTensor (retardedPotential k))) y i = 0) ∧
      (divergence3 (electricField (fieldTensor (retardedPotential k))) y = k y 0 ∧
        ∀ i, curl (magneticField (fieldTensor (retardedPotential k))) y i -
          partialAt (electricField (fieldTensor (retardedPotential k)) i) 0 y = k y i.succ) :=
  maxwell_retardedPotential hk hs hdiv y

example {k : Spacetime → Spacetime} (hk : ContDiff ℝ 2 k) {R v₀ : ℝ}
    (hs : Wave.SubluminalSupport R v₀ fun p => k (Wave.timeSpaceEquiv.symm p))
    (hdiv : ∀ v, divergence4 k v = 0) (y : Spacetime) :
    exteriorDerivative (fun z => -star (fieldTensor (retardedPotential k) z)) y =
      SourcedAction.matterCurrentForm k y :=
  excitation_retardedPotential hk hs hdiv y

example {k : Spacetime → Spacetime} {T : ℝ} (hpast : ∀ v : Spacetime, v 0 ≤ T → k v = 0)
    {v : Spacetime} (hv : v 0 ≤ T) :
    retardedPotential k v = 0 :=
  retardedPotential_eq_zero_of_le hpast hv

example (f : Spacetime → ℝ) (c : Spacetime) (μ : Fin 4) :
    partialAt (fun z => f (z + c)) μ = fun z => partialAt f μ (z + c) :=
  partialAt_comp_add_right f c μ

example (f : Spacetime → ℝ) (c z : Spacetime) :
    box (fun z => f (z + c)) z = box f (z + c) :=
  box_comp_add_right f c z

example {u : Spacetime → ℝ} (hu : ContDiff ℝ 2 u) {T₀ : ℝ} (hbox : ∀ y, box u y = 0)
    (hpast : ∀ y : Spacetime, y 0 ≤ T₀ → u y = 0)
    (hsupp : ∀ T : ℝ, ∃ ρ : ℝ, ∀ y : Spacetime, T₀ ≤ y 0 → y 0 ≤ T → u y ≠ 0 →
      ∀ i : Fin 3, |y i.succ| < ρ)
    (y : Spacetime) :
    u y = 0 :=
  eq_zero_of_wave_eq_zero hu hbox hpast hsupp y

example {g u : Spacetime → ℝ} (hg : ContDiff ℝ 2 g) {R v₀ : ℝ}
    (hs : Wave.SubluminalSupport R v₀ fun p => g (Wave.timeSpaceEquiv.symm p)) {T₀ : ℝ}
    (hgpast : ∀ y : Spacetime, y 0 ≤ T₀ → g y = 0) (hu : ContDiff ℝ 2 u)
    (hbox : ∀ y, box u y = -g y) (hupast : ∀ y : Spacetime, y 0 ≤ T₀ → u y = 0)
    (husupp : ∀ T : ℝ, ∃ ρ : ℝ, ∀ y : Spacetime, T₀ ≤ y 0 → y 0 ≤ T → u y ≠ 0 →
      ∀ i : Fin 3, |y i.succ| < ρ) :
    u = retardedScalar g :=
  eq_retardedScalar hg hs hgpast hu hbox hupast husupp

example {k : Spacetime → Spacetime} (hk : ContDiff ℝ 2 k) {R v₀ : ℝ}
    (hs : Wave.SubluminalSupport R v₀ fun p => k (Wave.timeSpaceEquiv.symm p)) {T₀ : ℝ}
    (hkpast : ∀ y : Spacetime, y 0 ≤ T₀ → k y = 0) {A : Potential} (hA : ContDiff ℝ 2 A)
    (hbox : ∀ y, box (potentialComponent A 0) y = k y 0 ∧
      ∀ i : Fin 3, box (potentialComponent A i.succ) y = -k y i.succ)
    (hpast : ∀ y : Spacetime, y 0 ≤ T₀ → A y = 0)
    (hsupp : ∀ T : ℝ, ∃ ρ : ℝ, ∀ y : Spacetime, T₀ ≤ y 0 → y 0 ≤ T → A y ≠ 0 →
      ∀ i : Fin 3, |y i.succ| < ρ)
    (ν : Fin 4) :
    potentialComponent A ν = potentialComponent (retardedPotential k) ν :=
  eq_retardedPotential hk hs hkpast hA hbox hpast hsupp ν

example :
    ContDiffBump (0 : Spacetime) :=
  spacetimeBump

example :
    Spacetime → Spacetime :=
  circulatingCurrent

example :
    ContDiff ℝ ∞ circulatingCurrent :=
  contDiff_circulatingCurrent

example :
    HasCompactSupport circulatingCurrent :=
  hasCompactSupport_circulatingCurrent

example (v : Spacetime) :
    circulatingCurrent v 0 = partialAt spacetimeBump 1 v ∧
      circulatingCurrent v 1 = -partialAt spacetimeBump 0 v ∧
      circulatingCurrent v 2 = 0 ∧ circulatingCurrent v 3 = 0 :=
  circulatingCurrent_apply v

example (v : Spacetime) :
    divergence4 circulatingCurrent v = 0 :=
  divergence4_circulatingCurrent v

example :
    circulatingCurrent ≠ 0 :=
  circulatingCurrent_ne_zero

example :
    ∃ R, Wave.SubluminalSupport R 0 fun p => circulatingCurrent (Wave.timeSpaceEquiv.symm p) :=
  exists_subluminalSupport_circulatingCurrent

example (y : Spacetime) :
    (divergence3 (magneticField (fieldTensor (retardedPotential circulatingCurrent))) y = 0 ∧
        ∀ i, partialAt (magneticField (fieldTensor (retardedPotential circulatingCurrent)) i) 0 y +
          curl (electricField (fieldTensor (retardedPotential circulatingCurrent))) y i = 0) ∧
      (divergence3 (electricField (fieldTensor (retardedPotential circulatingCurrent))) y =
          circulatingCurrent y 0 ∧
        ∀ i, curl (magneticField (fieldTensor (retardedPotential circulatingCurrent))) y i -
          partialAt (electricField (fieldTensor (retardedPotential circulatingCurrent)) i) 0 y =
            circulatingCurrent y i.succ) :=
  maxwell_retardedPotential_circulatingCurrent y

end ProjectAinos.Electrodynamics

end RetardedPotential

section RetardedSpectrum

open MeasureTheory Filter Set Metric Real

open scoped Topology ContDiff FourierTransform Laplacian

namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.Minkowski SpecialRelativity

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section TimeFourier

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]

example (g : ℝ × E3 → G) (ν : ℝ) (x : E3) :
    G :=
  timeFourier g ν x

example (g : ℝ × E3 → G) (ν : ℝ) (x : E3) :
    timeFourier g ν x = ∫ t : ℝ, (𝐞 (-(t * ν)) : ℂ) • g (t, x) :=
  timeFourier_eq g ν x

example (ν : ℝ) :
    Continuous fun t : ℝ => (𝐞 (-(t * ν)) : ℂ) :=
  continuous_fourierChar_mul ν

end TimeFourier

section TimeBounded

variable {H : Type*} [NormedAddCommGroup H]

example (a : ℝ) (g : ℝ × E3 → H) :
    Prop :=
  TimeBoundedSupport a g

example {H' : Type*} [NormedAddCommGroup H'] {a : ℝ} {g : ℝ × E3 → H} {g' : ℝ × E3 → H'}
    (hg : TimeBoundedSupport a g) (h : tsupport g' ⊆ tsupport g) :
    TimeBoundedSupport a g' :=
  TimeBoundedSupport.mono hg h

example {a : ℝ} {g : ℝ × E3 → H} (hg : TimeBoundedSupport a g) {t : ℝ} {x : E3}
    (ht : a + ‖x‖ < |t|) :
    g (t, x) = 0 :=
  TimeBoundedSupport.eq_zero hg ht

example {g : ℝ × E3 → H} (hg : HasCompactSupport g) :
    ∃ a, TimeBoundedSupport a g :=
  exists_timeBoundedSupport_of_hasCompactSupport hg

example {a : ℝ} {g : ℝ × E3 → H} (hg : TimeBoundedSupport a g) (x : E3) :
    HasCompactSupport fun t : ℝ => g (t, x) :=
  TimeBoundedSupport.hasCompactSupport_slice hg x

example {a : ℝ} {g : ℝ × E3 → H} (hg : TimeBoundedSupport a g) (hc : Continuous g) (x : E3) :
    Integrable fun t : ℝ => g (t, x) :=
  TimeBoundedSupport.integrable_slice hg hc x

example {H' : Type*} [NormedAddCommGroup H'] [NormedSpace ℝ H'] {a : ℝ} {g : ℝ × E3 → H'}
    (hg : TimeBoundedSupport a g) :
    TimeBoundedSupport a (fderiv ℝ g) :=
  TimeBoundedSupport.fderiv hg

end TimeBounded

section Derivative

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]

example {a : ℝ} {g : ℝ × E3 → G} (hg : TimeBoundedSupport a g) (hc : Continuous g) (ν : ℝ)
    (x : E3) :
    Integrable fun t : ℝ => (𝐞 (-(t * ν)) : ℂ) • g (t, x) :=
  TimeBoundedSupport.integrable_fourier hg hc ν x

example :
    (ℝ × E3 →L[ℝ] G) →L[ℝ] (E3 →L[ℝ] G) :=
  restrictSpace

example (L : ℝ × E3 →L[ℝ] G) :
    restrictSpace L = L.comp (ContinuousLinearMap.inr ℝ ℝ E3) :=
  restrictSpace_apply L

example [CompleteSpace G] {g : ℝ × E3 → G} (hg : ContDiff ℝ 1 g) {a : ℝ}
    (hs : TimeBoundedSupport a g) (ν : ℝ) (x₀ : E3) :
    HasFDerivAt (timeFourier g ν) (restrictSpace (timeFourier (fderiv ℝ g) ν x₀)) x₀ :=
  hasFDerivAt_timeFourier hg hs ν x₀

example [CompleteSpace G] {g : ℝ × E3 → G} (hg : ContDiff ℝ 1 g) {a : ℝ}
    (hs : TimeBoundedSupport a g) (ν : ℝ) :
    fderiv ℝ (timeFourier g ν) = fun x => restrictSpace (timeFourier (fderiv ℝ g) ν x) :=
  fderiv_timeFourier hg hs ν

example [CompleteSpace G] {L : ℝ × E3 → ℝ × E3 →L[ℝ] G} (hc : Continuous L) {a : ℝ}
    (hs : TimeBoundedSupport a L) (ν : ℝ) (x : E3) (v : ℝ × E3) :
    timeFourier L ν x v = timeFourier (fun p => L p v) ν x :=
  timeFourier_apply_clm hc hs ν x v

example [CompleteSpace G] {g : ℝ × E3 → G} (hg : ContDiff ℝ 1 g) {a : ℝ}
    (hs : TimeBoundedSupport a g) (ν : ℝ) (x v : E3) :
    fderiv ℝ (timeFourier g ν) x v = timeFourier (fun p => fderiv ℝ g p (0, v)) ν x :=
  fderiv_timeFourier_apply hg hs ν x v

example [CompleteSpace G] {g : ℝ × E3 → G} (hg : ContDiff ℝ 2 g) {a : ℝ}
    (hs : TimeBoundedSupport a g) (ν : ℝ) (x v w : E3) :
    fderiv ℝ (fderiv ℝ (timeFourier g ν)) x v w =
      timeFourier (fun p => fderiv ℝ (fderiv ℝ g) p (0, v) (0, w)) ν x :=
  fderiv_fderiv_timeFourier_apply hg hs ν x v w

example [CompleteSpace G] {g : ℝ × E3 → G} (hg : ContDiff ℝ 2 g) {a : ℝ}
    (hs : TimeBoundedSupport a g) (ν : ℝ) (x : E3) :
    Δ (timeFourier g ν) x = ∑ i, timeFourier (fun p => fderiv ℝ (fderiv ℝ g) p
      (0, EuclideanSpace.single i 1) (0, EuclideanSpace.single i 1)) ν x :=
  laplacian_timeFourier hg hs ν x

end Derivative

section Real

example {a : ℝ} {u : ℝ × E3 → ℝ} (hs : TimeBoundedSupport a u) :
    TimeBoundedSupport a fun p => (u p : ℂ) :=
  TimeBoundedSupport.ofReal hs

example {u : ℝ × E3 → ℝ} (hu : ContDiff ℝ 2 u) (p v w : ℝ × E3) :
    fderiv ℝ (fderiv ℝ fun q => (u q : ℂ)) p v w = (fderiv ℝ (fderiv ℝ u) p v w : ℂ) :=
  fderiv_fderiv_ofReal hu p v w

example {u : ℝ × E3 → ℝ} (hu : ContDiff ℝ 1 u) {a : ℝ} (hs : TimeBoundedSupport a u) (ν : ℝ)
    (x : E3) :
    timeFourier (fun p => (Wave.timeDeriv u p : ℂ)) ν x =
      2 * π * Complex.I * ν * timeFourier (fun p => (u p : ℂ)) ν x :=
  timeFourier_timeDeriv hu hs ν x

example {a : ℝ} {T : ℝ × E3 → ℂ} {S : Fin 3 → ℝ × E3 → ℂ} (hT : Continuous T)
    (hTs : TimeBoundedSupport a T) (hS : ∀ i, Continuous (S i))
    (hSs : ∀ i, TimeBoundedSupport a (S i)) (ν : ℝ) (x : E3) :
    timeFourier (fun p => T p - ∑ i, S i p) ν x =
      timeFourier T ν x - ∑ i, timeFourier (S i) ν x :=
  timeFourier_sub_sum hT hTs hS hSs ν x

example {u f : ℝ × E3 → ℝ} (hu : ContDiff ℝ 2 u) {a : ℝ} (hs : TimeBoundedSupport a u)
    (hwave : ∀ p, Wave.waveOperator u p = f p) (ν : ℝ) (x : E3) :
    Δ (timeFourier (fun p => (u p : ℂ)) ν) x +
        (2 * π * ν) ^ 2 * timeFourier (fun p => (u p : ℂ)) ν x =
      -timeFourier (fun p => (f p : ℂ)) ν x :=
  helmholtz_timeFourier hu hs hwave ν x

end Real

example {f : ℝ × E3 → ℝ} (hf : HasCompactSupport f) :
    ∃ a, TimeBoundedSupport a (Wave.retardedIntegral f) :=
  exists_timeBoundedSupport_retardedIntegral hf

example {f : ℝ × E3 → ℝ} (hc : Continuous f) (hf : HasCompactSupport f) (ν : ℝ) (x : E3) :
    Integrable (fun q : ℝ × E3 => (𝐞 (-(q.1 * ν)) : ℂ) *
      (((4 * π * ‖q.2‖)⁻¹ * f (q.1 - ‖q.2‖, x - q.2) : ℝ) : ℂ)) (volume.prod volume) :=
  integrable_fourier_retarded hc hf ν x

example {f : ℝ × E3 → ℝ} (hc : Continuous f) (hf : HasCompactSupport f) (ν : ℝ) (x : E3) :
    timeFourier (fun p => ((Wave.retardedIntegral f p : ℝ) : ℂ)) ν x =
      ∫ y : E3, Complex.exp (-(2 * π * ν * ‖y‖) * Complex.I) *
        timeFourier (fun p => (f p : ℂ)) ν (x - y) / (4 * π * ‖y‖) :=
  fourier_retardedIntegral hc hf ν x

example {f : ℝ × E3 → ℝ} (hc : ContDiff ℝ 2 f) (hf : HasCompactSupport f) (ν : ℝ) (x : E3) :
    Δ (timeFourier (fun p => ((Wave.retardedIntegral f p : ℝ) : ℂ)) ν) x +
        (2 * π * ν) ^ 2 * timeFourier (fun p => ((Wave.retardedIntegral f p : ℝ) : ℂ)) ν x =
      -timeFourier (fun p => (f p : ℂ)) ν x :=
  helmholtz_fourier_retardedIntegral hc hf ν x

example (h : Spacetime → ℝ) (ν : ℝ) (x : E3) :
    ℂ :=
  spacetimeFourier h ν x

example (h : Spacetime → ℝ) (ν : ℝ) (x : E3) :
    spacetimeFourier h ν x = ∫ t : ℝ, (𝐞 (-(t * ν)) : ℂ) * h (Minkowski.vector t x) :=
  spacetimeFourier_eq h ν x

example (h : Spacetime → ℝ) (ν : ℝ) :
    spacetimeFourier (fun v => -h v) ν = -spacetimeFourier h ν :=
  spacetimeFourier_neg h ν

example (g : Spacetime → ℝ) (p : ℝ × E3) :
    retardedScalar g (Wave.timeSpaceEquiv.symm p) =
      Wave.retardedIntegral (fun q => g (Wave.timeSpaceEquiv.symm q)) p :=
  retardedScalar_symm g p

example {g : Spacetime → ℝ} (hc : Continuous g) (hg : HasCompactSupport g) (ν : ℝ) (x : E3) :
    spacetimeFourier (retardedScalar g) ν x =
      ∫ y : E3, Complex.exp (-(2 * π * ν * ‖y‖) * Complex.I) *
        spacetimeFourier g ν (x - y) / (4 * π * ‖y‖) :=
  fourier_retardedScalar hc hg ν x

example {g : Spacetime → ℝ} (hc : ContDiff ℝ 2 g) (hg : HasCompactSupport g) (ν : ℝ) (x : E3) :
    Δ (spacetimeFourier (retardedScalar g) ν) x +
        (2 * π * ν) ^ 2 * spacetimeFourier (retardedScalar g) ν x =
      -spacetimeFourier g ν x :=
  helmholtz_fourier_retardedScalar hc hg ν x

example {k : Spacetime → Spacetime} (hk : HasCompactSupport k) (μ : Fin 4) :
    HasCompactSupport fun w => k w μ :=
  hasCompactSupport_spacetimeComponent hk μ

example {k : Spacetime → Spacetime} (hc : Continuous k) (hk : HasCompactSupport k) (ν : ℝ)
    (x : E3) :
    spacetimeFourier (potentialComponent (retardedPotential k) 0) ν x =
        -∫ y : E3, Complex.exp (-(2 * π * ν * ‖y‖) * Complex.I) *
          spacetimeFourier (fun w => k w 0) ν (x - y) / (4 * π * ‖y‖) ∧
      ∀ i : Fin 3, spacetimeFourier (potentialComponent (retardedPotential k) i.succ) ν x =
        ∫ y : E3, Complex.exp (-(2 * π * ν * ‖y‖) * Complex.I) *
          spacetimeFourier (fun w => k w i.succ) ν (x - y) / (4 * π * ‖y‖) :=
  fourier_retardedPotential hc hk ν x

example {k : Spacetime → Spacetime} (hc : ContDiff ℝ 2 k) (hk : HasCompactSupport k) (ν : ℝ)
    (x : E3) :
    Δ (spacetimeFourier (potentialComponent (retardedPotential k) 0) ν) x +
        (2 * π * ν) ^ 2 * spacetimeFourier (potentialComponent (retardedPotential k) 0) ν x =
      spacetimeFourier (fun w => k w 0) ν x ∧
    ∀ i : Fin 3, Δ (spacetimeFourier (potentialComponent (retardedPotential k) i.succ) ν) x +
        (2 * π * ν) ^ 2 * spacetimeFourier (potentialComponent (retardedPotential k) i.succ) ν x =
      -spacetimeFourier (fun w => k w i.succ) ν x :=
  helmholtz_fourier_retardedPotential hc hk ν x

example (ν : ℝ) (x : E3) :
    spacetimeFourier (potentialComponent (retardedPotential circulatingCurrent) 0) ν x =
        -∫ y : E3, Complex.exp (-(2 * π * ν * ‖y‖) * Complex.I) *
          spacetimeFourier (fun w => circulatingCurrent w 0) ν (x - y) / (4 * π * ‖y‖) ∧
      ∀ i : Fin 3,
        spacetimeFourier (potentialComponent (retardedPotential circulatingCurrent) i.succ) ν x =
          ∫ y : E3, Complex.exp (-(2 * π * ν * ‖y‖) * Complex.I) *
            spacetimeFourier (fun w => circulatingCurrent w i.succ) ν (x - y) / (4 * π * ‖y‖) :=
  fourier_retardedPotential_circulatingCurrent ν x

example (ν : ℝ) (x : E3) :
    Δ (spacetimeFourier (potentialComponent (retardedPotential circulatingCurrent) 0) ν) x +
        (2 * π * ν) ^ 2 *
          spacetimeFourier (potentialComponent (retardedPotential circulatingCurrent) 0) ν x =
      spacetimeFourier (fun w => circulatingCurrent w 0) ν x ∧
    ∀ i : Fin 3,
      Δ (spacetimeFourier (potentialComponent (retardedPotential circulatingCurrent) i.succ) ν) x +
          (2 * π * ν) ^ 2 * spacetimeFourier
            (potentialComponent (retardedPotential circulatingCurrent) i.succ) ν x =
        -spacetimeFourier (fun w => circulatingCurrent w i.succ) ν x :=
  helmholtz_fourier_retardedPotential_circulatingCurrent ν x

end ProjectAinos.Electrodynamics

end RetardedSpectrum
