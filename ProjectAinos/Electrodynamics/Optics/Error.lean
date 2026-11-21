/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Wave.Energy
public import ProjectAinos.SmoothGeometry.Wave.HighFrequency
public import ProjectAinos.Electrodynamics.RetardedPotential
import Mathlib.Tactic

/-!
# The limits of geometrical optics: the error of a high-frequency wave

The high-frequency wave `w = a cos(ψ/ε) + b sin(ψ/ε)` (`Wave.highFrequencyWave`) with amplitudes
`a`, `b` and a phase `ψ` on `ℝ × ℝ³` is the wave of geometrical optics when the phase solves the
eikonal equation `⟨dψ, dψ⟩ = 0` on the support of the amplitudes and the amplitudes solve the
transport equations `2⟨da, dψ⟩ + a □ψ = 0` (`IsGeometricalOptics`; Landau–Lifshitz, *The Classical
Theory of Fields*, §53). This file measures how far it is from an exact solution of the wave
equation `□u = 0` (§58).

* `IsGeometricalOptics.waveOperator_eq`: the terms of order `ε⁻²` and `ε⁻¹` of the expansion
  `Wave.waveOperator_highFrequencyWave` cancel, `□w = □a cos(ψ/ε) + □b sin(ψ/ε)`, and
  `IsGeometricalOptics.spatialL2Norm_waveOperator_le`: `‖□w(s, ·)‖_{L²} ≤ (∫ (□a)² + (□b)²)^{1/2}`
  (`amplitudeSource`), for every `ε`.
* `sqrt_energy_sub_le`: **the error of geometrical optics**. For an exact solution `u` with
  support in a ball and the Cauchy data of `w` at `t = 0`, the energy estimate
  `Wave.sqrt_energy_le` gives `√E_{u−w}(t) ≤ ∫₀ᵗ (∫ (□a)² + (□b)²)^{1/2} ds`, and
  `exists_sqrt_energy_sub_le`: `√E_{u−w}(t) ≤ C t` with `C` independent of `ε` and of `u`.
* The energy of `w` is of order `ε⁻²` since `∂w = O(1/ε)`; its leading part
  `½ε⁻² ∫ (b cos − a sin)² |∂ψ|²` oscillates with `ψ/ε`. The shift of the phase by `επ/2` gives
  the partner `w′ = b cos(ψ/ε) − a sin(ψ/ε)` (`highFrequencyWave_add_quarter`), and the pair has
  the energy density `ε⁻² (a² + b²) |∂ψ|² + 2ε⁻¹ (b ∂a − a ∂b) · ∂ψ + |∂a|² + |∂b|²`
  (`gradNormSq_highFrequencyWave_add_shift`) without oscillating terms. Hence
  `sq_mul_energy_add_shift`: `ε² (E_w + E_{w′}) = L + ε M + ε² (E_a + E_b)` exactly, with
  `L = ½ ∫ (a² + b²) |∂ψ|²` (`leadingEnergy`) and `M = ∫ (b ∂a − a ∂b) · ∂ψ` (`crossEnergy`);
  `tendsto_sq_mul_energy_add_shift`: `ε² (E_w + E_{w′}) → L` as `ε → 0`;
  `leadingEnergy_div_two_le`: `ε² (E_w + E_{w′}) ≥ L/2` for `|ε| |M| ≤ L/2`.
* `energy_sub_add_energy_sub_le`: **the relative error is of order `ε`**, the energy of the errors
  of the pair is at most `ε² · 4 (∫₀ᵗ ‖(□a, □b)‖)² / L` times the energy of the pair.
* An instance: the plane phase `t − x₁` (`planePhase`) with profiles carried with the speed of
  light along the first axis, `f(x − t e₁)` (`planeAmplitude`), solves the equations of geometrical
  optics (`isGeometricalOptics_plane`, `waveOperator_plane`); a profile in the ball of radius `r`
  stays in the ball of radius `r + T` (`ballSupportOn_planeAmplitude`), and
  `leadingEnergy_plane`: `L = ∫ (f² + g²)`, positive for the bump `spaceBump`
  (`leadingEnergy_plane_spaceBump_pos`). The source `□a = −(∂₂² + ∂₃²) f` of the error is the
  diffraction of the transverse profile, so that a localized plane wave is never exact.
* An exact instance: the outgoing spherical shell `a = g(t − r)/r` on the phase `t − r`
  (`radialAmplitude`, `radialPhase`) has `□(t − r) = 2/r` (`waveOperator_radialPhase`), solves the
  eikonal and transport equations (`wavePairing_radialPhase`, `transport_radialAmplitude`) and the
  wave equation `□a = 0` (`waveOperator_radialAmplitude`) away from the origin. With the profile
  `g = shellBump` on `[−6, −4]` and a smooth cutoff near the origin, which the shell does not reach
  at the times `t ≥ 0`, it is smooth on `ℝ × ℝ³` (`sphericalAmplitude`, `sphericalPhase`,
  `isGeometricalOptics_spherical`, `ballSupportOn_sphericalAmplitude`), the wave
  `a cos((t − r)/ε) + a sin((t − r)/ε)` and its partner are exact for every `ε`
  (`waveOperator_spherical`, `waveOperator_spherical_shift`), `L > 0` and `M = 0`
  (`leadingEnergy_spherical_pos`, `crossEnergy_self`); `sqrt_energy_sub_le_spherical` and
  `energy_sub_add_energy_sub_le_spherical` are instances of the hypotheses of the error estimates
  with `u = w`. The amplitude `1/r` blows up at the focus `r = 0`.
* The electromagnetic reading: in the gauge of Lorenz and in vacuum each component of the
  potential solves `□A_μ = 0` (`waveOperator_potentialComponent_eq_zero`, from
  `maxwell_iff_box_of_lorenz` and `box_comp_timeSpaceEquiv`), and
  `sqrt_energy_potentialComponent_sub_le` applies the error estimate to each component.

The companion module `SingleWave` proves the short-wavelength limit for one real wave. At a
nonstationary spatial phase the doubled-phase terms average to zero, so the normalized energy
converges to half the leading energy of the pair.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric Real
open scoped Topology ContDiff

namespace ProjectAinos.Electrodynamics.Optics.Limits

open SmoothGeometry SpecialRelativity

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### Linearity of the derivatives -/

private theorem timeDeriv_fun_neg' (f : ℝ × E3 → ℝ) (p : ℝ × E3) :
    Wave.timeDeriv (fun q => -f q) p = -Wave.timeDeriv f p := by
  simp only [Wave.timeDeriv, fderiv_fun_neg, neg_apply]

private theorem spaceDeriv_fun_neg' (f : ℝ × E3 → ℝ) (i : Fin 3) (p : ℝ × E3) :
    Wave.spaceDeriv i (fun q => -f q) p = -Wave.spaceDeriv i f p := by
  simp only [Wave.spaceDeriv, fderiv_fun_neg, neg_apply]

private theorem waveOperator_fun_neg' (f : ℝ × E3 → ℝ) (p : ℝ × E3) :
    Wave.waveOperator (fun q => -f q) p = -Wave.waveOperator f p := by
  have ht : Wave.timeDeriv (fun q => -f q) = fun q => -Wave.timeDeriv f q :=
    funext (timeDeriv_fun_neg' f)
  have hs : ∀ i, Wave.spaceDeriv i (fun q => -f q) = fun q => -Wave.spaceDeriv i f q :=
    fun i => funext (spaceDeriv_fun_neg' f i)
  simp only [Wave.waveOperator, ht, hs, timeDeriv_fun_neg', spaceDeriv_fun_neg',
    Finset.sum_neg_distrib]
  ring

private theorem waveOperator_fun_sub' {f g : ℝ × E3 → ℝ} {p : ℝ × E3} (hf : ContDiffAt ℝ 2 f p)
    (hg : ContDiffAt ℝ 2 g p) :
    Wave.waveOperator (fun q => f q - g q) p = Wave.waveOperator f p - Wave.waveOperator g p := by
  rw [show (fun q => f q - g q) = fun q => f q + -g q from funext fun q => sub_eq_add_neg _ _,
    Wave.waveOperator_fun_add hf hg.neg, waveOperator_fun_neg', sub_eq_add_neg]

/-! ### The equations of geometrical optics -/

/-- The transport operator vanishes off the support of the amplitude. -/
theorem transport_eq_zero_of_notMem {a : ℝ × E3 → ℝ} (ψ : ℝ × E3 → ℝ) {p : ℝ × E3}
    (hp : p ∉ tsupport a) : Wave.transport a ψ p = 0 := by
  simp [Wave.transport, Wave.wavePairing, Wave.timeDeriv_eq_zero_of_notMem hp,
    Wave.spaceDeriv_eq_zero_of_notMem hp, image_eq_zero_of_notMem_tsupport hp]

/-- The amplitudes `a`, `b` and the phase `ψ` satisfy **the equations of geometrical optics** on
the times of `[0, T]` (Landau–Lifshitz §53): the eikonal equation `⟨dψ, dψ⟩ = 0` where `a` or
`b` does not vanish, and the transport equations `2⟨da, dψ⟩ + a □ψ = 0` and
`2⟨db, dψ⟩ + b □ψ = 0` on the supports of `a` and of `b`. -/
structure IsGeometricalOptics (T : ℝ) (a b ψ : ℝ × E3 → ℝ) : Prop where
  eikonal : ∀ p : ℝ × E3, p.1 ∈ Icc 0 T → (a p ≠ 0 ∨ b p ≠ 0) → Wave.wavePairing ψ ψ p = 0
  transport_fst : ∀ p ∈ tsupport a, p.1 ∈ Icc 0 T → Wave.transport a ψ p = 0
  transport_snd : ∀ p ∈ tsupport b, p.1 ∈ Icc 0 T → Wave.transport b ψ p = 0

/-- **The wave operator of a high-frequency wave in geometrical optics**: where the eikonal and
the transport equations hold, the terms of order `ε⁻²` and `ε⁻¹` cancel and
`□(a cos(ψ/ε) + b sin(ψ/ε)) = □a cos(ψ/ε) + □b sin(ψ/ε)`. -/
theorem IsGeometricalOptics.waveOperator_eq {T : ℝ} {a b ψ : ℝ × E3 → ℝ}
    (h : IsGeometricalOptics T a b ψ) (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (hψ : ContDiff ℝ 2 ψ) {ε : ℝ} (hε : ε ≠ 0) {p : ℝ × E3} (hp : p.1 ∈ Icc 0 T) :
    Wave.waveOperator (Wave.highFrequencyWave a b ψ ε) p =
      Wave.waveOperator a p * cos (ψ p / ε) + Wave.waveOperator b p * sin (ψ p / ε) := by
  rw [Wave.waveOperator_highFrequencyWave ha.contDiffAt hb.contDiffAt hψ.contDiffAt hε]
  have h1 : Wave.wavePairing ψ ψ p * (a p * cos (ψ p / ε) + b p * sin (ψ p / ε)) = 0 := by
    by_cases hab : a p ≠ 0 ∨ b p ≠ 0
    · rw [h.eikonal p hp hab, zero_mul]
    · obtain ⟨ha0, hb0⟩ : a p = 0 ∧ b p = 0 := by simpa [not_or] using hab
      rw [ha0, hb0]
      ring
  have h2 : Wave.transport a ψ p = 0 := by
    by_cases hpa : p ∈ tsupport a
    · exact h.transport_fst p hpa hp
    · exact transport_eq_zero_of_notMem ψ hpa
  have h3 : Wave.transport b ψ p = 0 := by
    by_cases hpb : p ∈ tsupport b
    · exact h.transport_snd p hpb hp
    · exact transport_eq_zero_of_notMem ψ hpb
  rw [h2, h3]
  linear_combination (-(ε⁻¹ ^ 2)) * h1

/-- `(x cos θ + y sin θ)² ≤ x² + y²`. -/
theorem sq_mul_cos_add_mul_sin_le (x y θ : ℝ) : (x * cos θ + y * sin θ) ^ 2 ≤ x ^ 2 + y ^ 2 := by
  nlinarith [sq_nonneg (x * sin θ - y * cos θ), sin_sq_add_cos_sq θ]

/-- The norm `(∫ (□a)² + (□b)²)^{1/2}` on the time slice `t`; it bounds the source `□w` of the
error of the high-frequency wave for every `ε`. -/
def amplitudeSource (a b : ℝ × E3 → ℝ) (t : ℝ) : ℝ :=
  √(∫ x, (Wave.waveOperator a (t, x) ^ 2 + Wave.waveOperator b (t, x) ^ 2))

/-- The amplitude source is nonnegative. -/
theorem amplitudeSource_nonneg (a b : ℝ × E3 → ℝ) (t : ℝ) : 0 ≤ amplitudeSource a b t :=
  sqrt_nonneg _

/-- The high-frequency wave of `C²` amplitudes and a `C²` phase is `C²`. -/
theorem contDiff_highFrequencyWave {a b ψ : ℝ × E3 → ℝ} (ha : ContDiff ℝ 2 a)
    (hb : ContDiff ℝ 2 b) (hψ : ContDiff ℝ 2 ψ) (ε : ℝ) :
    ContDiff ℝ 2 (Wave.highFrequencyWave a b ψ ε) :=
  contDiff_iff_contDiffAt.2 fun _ =>
    Wave.contDiffAt_highFrequencyWave ha.contDiffAt hb.contDiffAt hψ.contDiffAt ε

/-- The high-frequency wave vanishes where both amplitudes vanish. -/
theorem ballSupportOn_highFrequencyWave {T R : ℝ} {a b : ℝ × E3 → ℝ}
    (has : Wave.BallSupportOn T R a) (hbs : Wave.BallSupportOn T R b) (ψ : ℝ × E3 → ℝ)
    (ε : ℝ) : Wave.BallSupportOn T R (Wave.highFrequencyWave a b ψ ε) := fun s hs y hy => by
  simp only [Wave.highFrequencyWave, has s hs y hy, hbs s hs y hy, zero_mul, add_zero]

private theorem continuousOn_sqrt_integral {F : ℝ × E3 → ℝ} (hc : Continuous F) {T R : ℝ}
    (h : Wave.BallSupportOn T R F) : ContinuousOn (fun s => √(∫ x, F (s, x))) (Icc 0 T) :=
  (h.continuousOn_integral hc).sqrt

/-- The amplitude source is continuous on `[0, T]`. -/
theorem continuousOn_amplitudeSource {T R : ℝ} {a b : ℝ × E3 → ℝ} (hT : 0 < T)
    (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b) (has : Wave.BallSupportOn T R a)
    (hbs : Wave.BallSupportOn T R b) : ContinuousOn (amplitudeSource a b) (Icc 0 T) :=
  continuousOn_sqrt_integral
    (((Wave.continuous_waveOperator ha).fun_pow 2).fun_add
      ((Wave.continuous_waveOperator hb).fun_pow 2))
    (((has.waveOperator hT ha).pow two_ne_zero).add ((hbs.waveOperator hT hb).pow two_ne_zero))

/-- **The source of the error is bounded independently of `ε`**:
`‖□w(s, ·)‖_{L²} ≤ (∫ (□a)² + (□b)²)^{1/2}` for the high-frequency wave `w` of geometrical
optics, at every time of `[0, T]` and for every `ε ≠ 0`. -/
theorem IsGeometricalOptics.spatialL2Norm_waveOperator_le {T R : ℝ} {a b ψ : ℝ × E3 → ℝ}
    (h : IsGeometricalOptics T a b ψ) (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (hψ : ContDiff ℝ 2 ψ) (hT : 0 < T) (has : Wave.BallSupportOn T R a)
    (hbs : Wave.BallSupportOn T R b) {ε : ℝ} (hε : ε ≠ 0) {s : ℝ} (hs : s ∈ Icc 0 T) :
    Wave.spatialL2Norm (Wave.waveOperator (Wave.highFrequencyWave a b ψ ε)) s ≤
      amplitudeSource a b s := by
  refine sqrt_le_sqrt (integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _)
    ((((has.waveOperator hT ha).pow two_ne_zero).add
      ((hbs.waveOperator hT hb).pow two_ne_zero)).integrable
      (((Wave.continuous_waveOperator ha).fun_pow 2).fun_add
        ((Wave.continuous_waveOperator hb).fun_pow 2)) hs)
    (Eventually.of_forall fun x => ?_))
  simp only
  rw [h.waveOperator_eq ha hb hψ hε hs]
  exact sq_mul_cos_add_mul_sin_le _ _ _

/-! ### The energy of the error -/

/-- A function with the same Cauchy data at `t = 0` as `w` differs from `w` by a function of
zero energy at `t = 0`. -/
theorem energy_sub_eq_zero {u w : ℝ × E3 → ℝ} (hu : Differentiable ℝ u)
    (hw : Differentiable ℝ w) (h0 : ∀ x, u (0, x) = w (0, x))
    (h1 : ∀ x, Wave.timeDeriv u (0, x) = Wave.timeDeriv w (0, x)) :
    Wave.energy (fun p => u p - w p) 0 = 0 := by
  have hslice : (fun z : E3 => u (0, z) - w (0, z)) = fun _ => 0 :=
    funext fun z => by rw [h0 z, sub_self]
  have hg : ∀ x : E3, Wave.gradNormSq (fun p => u p - w p) (0, x) = 0 := by
    intro x
    have ht : Wave.timeDeriv (fun p => u p - w p) (0, x) = 0 := by
      simp only [Wave.timeDeriv, fderiv_fun_sub (hu _) (hw _), sub_apply]
      exact sub_eq_zero.2 (h1 x)
    have hdx : DifferentiableAt ℝ (fun p => u p - w p) (0, x) := (hu _).sub (hw _)
    have hs : ∀ i, Wave.spaceDeriv i (fun p => u p - w p) (0, x) = 0 := fun i => by
      rw [← Wave.fderiv_spaceSlice hdx i, hslice, fderiv_const_apply]
      rfl
    simp [Wave.gradNormSq, ht, hs]
  simp [Wave.energy, hg]

/-- **The error of geometrical optics** (Landau–Lifshitz §58): let `u` be a `C²` solution of the
wave equation `□u = 0` on `[0, T] × ℝ³` with support in a ball, with the same Cauchy data at
`t = 0` as the high-frequency wave `w = a cos(ψ/ε) + b sin(ψ/ε)` whose amplitudes and phase
satisfy the equations of geometrical optics. Then the energy of the error is bounded independently
of `ε`: `√E_{u−w}(t) ≤ ∫₀ᵗ (∫ (□a)² + (□b)²)^{1/2} ds` for `t ∈ [0, T]`. -/
theorem sqrt_energy_sub_le {T R : ℝ} {a b ψ u : ℝ × E3 → ℝ} (ha : ContDiff ℝ 2 a)
    (hb : ContDiff ℝ 2 b) (hψ : ContDiff ℝ 2 ψ) (h : IsGeometricalOptics T a b ψ)
    (has : Wave.BallSupportOn T R a) (hbs : Wave.BallSupportOn T R b) (hu : ContDiff ℝ 2 u)
    (hus : Wave.BallSupportOn T R u)
    (hwave : ∀ p : ℝ × E3, p.1 ∈ Icc 0 T → Wave.waveOperator u p = 0) {ε : ℝ} (hε : ε ≠ 0)
    (h0 : ∀ x, u (0, x) = Wave.highFrequencyWave a b ψ ε (0, x))
    (h1 : ∀ x, Wave.timeDeriv u (0, x) = Wave.timeDeriv (Wave.highFrequencyWave a b ψ ε) (0, x))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    √(Wave.energy (fun p => u p - Wave.highFrequencyWave a b ψ ε p) t) ≤
      ∫ s in 0..t, amplitudeSource a b s := by
  set w := Wave.highFrequencyWave a b ψ ε with hwdef
  have hw : ContDiff ℝ 2 w := contDiff_highFrequencyWave ha hb hψ ε
  have hd : ContDiff ℝ 2 fun p => u p - w p := hu.sub hw
  have hds : Wave.BallSupportOn T R fun p => u p - w p :=
    hus.sub (ballSupportOn_highFrequencyWave has hbs ψ ε)
  have hE0 : Wave.energy (fun p => u p - w p) 0 = 0 :=
    energy_sub_eq_zero (hu.differentiable (by norm_num)) (hw.differentiable (by norm_num)) h0 h1
  rcases ht.1.eq_or_lt with rfl | ht0
  · simp [hE0]
  have hest := Wave.sqrt_energy_le hd hds ht
  rw [hE0, sqrt_zero, zero_add] at hest
  refine hest.trans (intervalIntegral.integral_mono_on ht0.le ?_ ?_ fun s hs => ?_)
  · exact (continuousOn_sqrt_integral ((Wave.continuous_waveOperator hd).fun_pow 2)
      (((hds.mono ht.2 le_rfl).waveOperator ht0 hd).pow two_ne_zero)).intervalIntegrable_of_Icc
        ht0.le
  · exact (continuousOn_amplitudeSource ht0 ha hb (has.mono ht.2 le_rfl)
      (hbs.mono ht.2 le_rfl)).intervalIntegrable_of_Icc ht0.le
  · have hsT : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans ht.2⟩
    have heq : Wave.spatialL2Norm (Wave.waveOperator fun p => u p - w p) s =
        Wave.spatialL2Norm (Wave.waveOperator w) s := by
      simp only [Wave.spatialL2Norm]
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      rw [waveOperator_fun_sub' hu.contDiffAt hw.contDiffAt, hwave (s, x) hsT, zero_sub,
        neg_sq]
    rw [heq]
    exact h.spatialL2Norm_waveOperator_le ha hb hψ (ht0.trans_le ht.2) has hbs hε hsT

/-- **The error of geometrical optics is bounded uniformly in the wavelength**: there is a constant
`C`, which depends on the amplitudes only, such that `√E_{u−w}(t) ≤ C t` for every `ε ≠ 0`, every
exact solution `u` with the Cauchy data of the high-frequency wave `w`, and every `t ∈ [0, T]`. -/
theorem exists_sqrt_energy_sub_le {T R : ℝ} {a b ψ : ℝ × E3 → ℝ} (ha : ContDiff ℝ 2 a)
    (hb : ContDiff ℝ 2 b) (hψ : ContDiff ℝ 2 ψ) (h : IsGeometricalOptics T a b ψ)
    (has : Wave.BallSupportOn T R a) (hbs : Wave.BallSupportOn T R b) :
    ∃ C, ∀ ε ≠ 0, ∀ u : ℝ × E3 → ℝ, ContDiff ℝ 2 u → Wave.BallSupportOn T R u →
      (∀ p : ℝ × E3, p.1 ∈ Icc 0 T → Wave.waveOperator u p = 0) →
      (∀ x, u (0, x) = Wave.highFrequencyWave a b ψ ε (0, x)) →
      (∀ x, Wave.timeDeriv u (0, x) = Wave.timeDeriv (Wave.highFrequencyWave a b ψ ε) (0, x)) →
      ∀ t ∈ Icc 0 T,
        √(Wave.energy (fun p => u p - Wave.highFrequencyWave a b ψ ε p) t) ≤ C * t := by
  rcases le_or_gt T 0 with hT | hT
  · refine ⟨0, fun ε hε u hu hus hwave h0 h1 t ht => ?_⟩
    have ht0 : t = 0 := le_antisymm (ht.2.trans hT) ht.1
    subst ht0
    rw [energy_sub_eq_zero (hu.differentiable (by norm_num))
      ((contDiff_highFrequencyWave ha hb hψ ε).differentiable (by norm_num)) h0 h1]
    simp
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuousOn_amplitudeSource hT ha hb has hbs)
  refine ⟨C, fun ε hε u hu hus hwave h0 h1 t ht => ?_⟩
  refine (sqrt_energy_sub_le ha hb hψ h has hbs hu hus hwave hε h0 h1 ht).trans ?_
  have hle : ∫ s in 0..t, amplitudeSource a b s ≤ ∫ _ in 0..t, C := by
    rcases ht.1.eq_or_lt with rfl | ht0
    · simp
    refine intervalIntegral.integral_mono_on ht.1 ?_ intervalIntegrable_const fun s hs => ?_
    · exact (continuousOn_amplitudeSource ht0 ha hb (has.mono ht.2 le_rfl)
        (hbs.mono ht.2 le_rfl)).intervalIntegrable_of_Icc ht.1
    · have := hC s ⟨hs.1, hs.2.trans ht.2⟩
      rw [norm_of_nonneg (amplitudeSource_nonneg a b s)] at this
      exact this
  simpa [mul_comm] using hle

/-! ### The pair of phases and the energy of the high-frequency wave -/

/-- The shift of the phase by a quarter wavelength `επ/2` turns `a cos + b sin` into
`b cos − a sin`, the high-frequency wave with the amplitudes `(b, −a)`. -/
theorem highFrequencyWave_add_quarter (a b ψ : ℝ × E3 → ℝ) {ε : ℝ} (hε : ε ≠ 0) :
    Wave.highFrequencyWave a b (fun p => ψ p + ε * (π / 2)) ε =
      Wave.highFrequencyWave b (fun p => -a p) ψ ε := by
  funext p
  have h : (ψ p + ε * (π / 2)) / ε = ψ p / ε + π / 2 := by field_simp
  simp only [Wave.highFrequencyWave, h, cos_add_pi_div_two, sin_add_pi_div_two]
  ring

private theorem wavePairing_fun_neg' (f g : ℝ × E3 → ℝ) (p : ℝ × E3) :
    Wave.wavePairing (fun q => -f q) g p = -Wave.wavePairing f g p := by
  simp only [Wave.wavePairing, timeDeriv_fun_neg', spaceDeriv_fun_neg', neg_mul,
    Finset.sum_neg_distrib]
  ring

/-- The transport operator is odd in the amplitude. -/
theorem transport_fun_neg (a ψ : ℝ × E3 → ℝ) (p : ℝ × E3) :
    Wave.transport (fun q => -a q) ψ p = -Wave.transport a ψ p := by
  simp only [Wave.transport, wavePairing_fun_neg']
  ring

/-- The amplitudes `(b, −a)` of the shifted phase satisfy the equations of geometrical optics with
`(a, b)`. -/
theorem IsGeometricalOptics.shift {T : ℝ} {a b ψ : ℝ × E3 → ℝ} (h : IsGeometricalOptics T a b ψ) :
    IsGeometricalOptics T b (fun p => -a p) ψ where
  eikonal p hp hab := h.eikonal p hp (hab.elim Or.inr fun ha => Or.inl (neg_ne_zero.mp ha))
  transport_fst := h.transport_snd
  transport_snd p hp hpT := by
    have hp' : p ∈ tsupport a := by
      rwa [show (fun q => -a q) = -a from rfl, tsupport_neg] at hp
    rw [transport_fun_neg, h.transport_fst p hp' hpT, neg_zero]

/-- The amplitude source of the shifted phase is that of `(a, b)`. -/
theorem amplitudeSource_shift (a b : ℝ × E3 → ℝ) (t : ℝ) :
    amplitudeSource b (fun p => -a p) t = amplitudeSource a b t := by
  simp only [amplitudeSource, waveOperator_fun_neg', neg_sq]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun x => add_comm _ _)

/-- **The energy density of the pair of phases**: the squares of the gradients of
`w = a cos(ψ/ε) + b sin(ψ/ε)` and of `w′ = b cos(ψ/ε) − a sin(ψ/ε)` add up to
`ε⁻² (a² + b²) |∂ψ|² + 2ε⁻¹ (b ∂a − a ∂b) · ∂ψ + |∂a|² + |∂b|²`, without oscillating terms. -/
theorem gradNormSq_highFrequencyWave_add_shift {a b ψ : ℝ × E3 → ℝ} {p : ℝ × E3}
    (ha : DifferentiableAt ℝ a p) (hb : DifferentiableAt ℝ b p) (hψ : DifferentiableAt ℝ ψ p)
    (ε : ℝ) :
    Wave.gradNormSq (Wave.highFrequencyWave a b ψ ε) p +
        Wave.gradNormSq (Wave.highFrequencyWave b (fun q => -a q) ψ ε) p =
      ε⁻¹ ^ 2 * ((a p ^ 2 + b p ^ 2) * Wave.gradNormSq ψ p) +
        2 * ε⁻¹ * (b p * Wave.gradInner a ψ p - a p * Wave.gradInner b ψ p) +
        (Wave.gradNormSq a p + Wave.gradNormSq b p) := by
  have hcs := sin_sq_add_cos_sq (ψ p / ε)
  have hD : ∀ A B P W W' : ℝ,
      W = ε⁻¹ * (P * (b p * cos (ψ p / ε) - a p * sin (ψ p / ε))) +
        (A * cos (ψ p / ε) + B * sin (ψ p / ε)) →
      W' = ε⁻¹ * (P * (-a p * cos (ψ p / ε) - b p * sin (ψ p / ε))) +
        (B * cos (ψ p / ε) + -A * sin (ψ p / ε)) →
      W ^ 2 + W' ^ 2 = ε⁻¹ ^ 2 * ((a p ^ 2 + b p ^ 2) * P ^ 2) +
        2 * ε⁻¹ * (b p * (A * P) - a p * (B * P)) + (A ^ 2 + B ^ 2) := by
    rintro A B P W W' rfl rfl
    linear_combination (ε⁻¹ ^ 2 * (a p ^ 2 + b p ^ 2) * P ^ 2 +
      2 * ε⁻¹ * P * (b p * A - a p * B) + A ^ 2 + B ^ 2) * hcs
  have hna : DifferentiableAt ℝ (fun q => -a q) p := ha.neg
  have ht := hD _ _ _ _ (Wave.timeDeriv (Wave.highFrequencyWave b (fun q => -a q) ψ ε) p)
    (Wave.timeDeriv_highFrequencyWave ha hb hψ ε)
    (by rw [Wave.timeDeriv_highFrequencyWave hb hna hψ ε, timeDeriv_fun_neg'])
  have hs := fun i => hD _ _ _ _
    (Wave.spaceDeriv i (Wave.highFrequencyWave b (fun q => -a q) ψ ε) p)
    (Wave.spaceDeriv_highFrequencyWave ha hb hψ ε i)
    (by rw [Wave.spaceDeriv_highFrequencyWave hb hna hψ ε i, spaceDeriv_fun_neg'])
  simp only [Wave.gradNormSq, Wave.gradInner, Fin.sum_univ_three]
  linear_combination ht + hs 0 + hs 1 + hs 2

/-- The leading coefficient `½ ∫ (a² + b²) |∂ψ|²` of the energy of the pair of phases. -/
def leadingEnergy (a b ψ : ℝ × E3 → ℝ) (t : ℝ) : ℝ :=
  (1 / 2) * ∫ x, (a (t, x) ^ 2 + b (t, x) ^ 2) * Wave.gradNormSq ψ (t, x)

/-- The coefficient `∫ (b ∂a − a ∂b) · ∂ψ` of order `ε⁻¹` of the energy of the pair of phases. -/
def crossEnergy (a b ψ : ℝ × E3 → ℝ) (t : ℝ) : ℝ :=
  ∫ x, (b (t, x) * Wave.gradInner a ψ (t, x) - a (t, x) * Wave.gradInner b ψ (t, x))

/-- The leading coefficient is nonnegative. -/
theorem leadingEnergy_nonneg (a b ψ : ℝ × E3 → ℝ) (t : ℝ) : 0 ≤ leadingEnergy a b ψ t :=
  mul_nonneg (by norm_num) (integral_nonneg fun _ =>
    mul_nonneg (by positivity) (Wave.gradNormSq_nonneg ψ _))

/-- **The energy of the pair of phases** is a polynomial in `ε`:
`ε² (E_w(t) + E_{w′}(t)) = ½ ∫ (a² + b²) |∂ψ|² + ε ∫ (b ∂a − a ∂b) · ∂ψ + ε² (E_a(t) + E_b(t))`
for `w = a cos(ψ/ε) + b sin(ψ/ε)` and `w′ = b cos(ψ/ε) − a sin(ψ/ε)`, the wave with the phase
shifted by `επ/2` (`highFrequencyWave_add_quarter`). -/
theorem sq_mul_energy_add_shift {T R : ℝ} {a b ψ : ℝ × E3 → ℝ} (ha : ContDiff ℝ 2 a)
    (hb : ContDiff ℝ 2 b) (hψ : ContDiff ℝ 2 ψ) (hT : 0 < T) (has : Wave.BallSupportOn T R a)
    (hbs : Wave.BallSupportOn T R b) {t : ℝ} (ht : t ∈ Icc 0 T) {ε : ℝ} (hε : ε ≠ 0) :
    ε ^ 2 * (Wave.energy (Wave.highFrequencyWave a b ψ ε) t +
        Wave.energy (Wave.highFrequencyWave b (fun q => -a q) ψ ε) t) =
      leadingEnergy a b ψ t + ε * crossEnergy a b ψ t +
        ε ^ 2 * (Wave.energy a t + Wave.energy b t) := by
  have ha1 : ContDiff ℝ 1 a := ha.of_le (by norm_num)
  have hb1 : ContDiff ℝ 1 b := hb.of_le (by norm_num)
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
  have hnas : Wave.BallSupportOn T R fun q => -a q := fun s hs y hy => by
    simp only [has s hs y hy, neg_zero]
  have hw1 : ContDiff ℝ 1 (Wave.highFrequencyWave a b ψ ε) :=
    (contDiff_highFrequencyWave ha hb hψ ε).of_le (by norm_num)
  have hw1' : ContDiff ℝ 1 (Wave.highFrequencyWave b (fun q => -a q) ψ ε) :=
    (contDiff_highFrequencyWave hb ha.neg hψ ε).of_le (by norm_num)
  have iw := ((ballSupportOn_highFrequencyWave has hbs ψ ε).gradNormSq hT hw1).integrable
    (Wave.continuous_gradNormSq hw1) ht
  have iw' := ((ballSupportOn_highFrequencyWave hbs hnas ψ ε).gradNormSq hT hw1').integrable
    (Wave.continuous_gradNormSq hw1') ht
  have i1 : Integrable fun x =>
      (a (t, x) ^ 2 + b (t, x) ^ 2) * Wave.gradNormSq ψ (t, x) :=
    (((has.pow two_ne_zero).add (hbs.pow two_ne_zero)).mul_right _).integrable
      (((ha.continuous.fun_pow 2).fun_add (hb.continuous.fun_pow 2)).fun_mul
        (Wave.continuous_gradNormSq hψ1)) ht
  have i2 : Integrable fun x =>
      b (t, x) * Wave.gradInner a ψ (t, x) - a (t, x) * Wave.gradInner b ψ (t, x) :=
    ((hbs.mul_right _).sub (has.mul_right _)).integrable
      ((hb.continuous.fun_mul (Wave.continuous_gradInner ha1 hψ1)).fun_sub
        (ha.continuous.fun_mul (Wave.continuous_gradInner hb1 hψ1))) ht
  have i3 := (has.gradNormSq hT ha1).integrable (Wave.continuous_gradNormSq ha1) ht
  have i4 := (hbs.gradNormSq hT hb1).integrable (Wave.continuous_gradNormSq hb1) ht
  have e : (∫ x, Wave.gradNormSq (Wave.highFrequencyWave a b ψ ε) (t, x)) +
      ∫ x, Wave.gradNormSq (Wave.highFrequencyWave b (fun q => -a q) ψ ε) (t, x) =
      ε⁻¹ ^ 2 * (∫ x, (a (t, x) ^ 2 + b (t, x) ^ 2) * Wave.gradNormSq ψ (t, x)) +
        2 * ε⁻¹ * (∫ x, (b (t, x) * Wave.gradInner a ψ (t, x) -
          a (t, x) * Wave.gradInner b ψ (t, x))) +
        ((∫ x, Wave.gradNormSq a (t, x)) + ∫ x, Wave.gradNormSq b (t, x)) := by
    rw [← integral_add iw iw', integral_congr_ae (Eventually.of_forall fun x =>
      gradNormSq_highFrequencyWave_add_shift ((ha.differentiable (by norm_num)) (t, x))
        ((hb.differentiable (by norm_num)) (t, x)) ((hψ.differentiable (by norm_num)) (t, x)) ε),
      integral_add ((i1.const_mul _).fun_add (i2.const_mul _)) (i3.fun_add i4),
      integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul,
      integral_add i3 i4]
  have hε2 : ε ^ 2 * ε⁻¹ ^ 2 = 1 := by rw [← mul_pow, mul_inv_cancel₀ hε, one_pow]
  have hε1 : ε ^ 2 * ε⁻¹ = ε := by field_simp
  simp only [Wave.energy, leadingEnergy, crossEnergy]
  linear_combination (ε ^ 2 / 2) * e +
    ((1 / 2) * ∫ x, (a (t, x) ^ 2 + b (t, x) ^ 2) * Wave.gradNormSq ψ (t, x)) * hε2 +
    (∫ x, (b (t, x) * Wave.gradInner a ψ (t, x) - a (t, x) * Wave.gradInner b ψ (t, x))) * hε1

/-- **The leading term of the energy**: `ε² (E_w(t) + E_{w′}(t)) → ½ ∫ (a² + b²) |∂ψ|²` as
`ε → 0`. -/
theorem tendsto_sq_mul_energy_add_shift {T R : ℝ} {a b ψ : ℝ × E3 → ℝ} (ha : ContDiff ℝ 2 a)
    (hb : ContDiff ℝ 2 b) (hψ : ContDiff ℝ 2 ψ) (hT : 0 < T) (has : Wave.BallSupportOn T R a)
    (hbs : Wave.BallSupportOn T R b) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Tendsto (fun ε => ε ^ 2 * (Wave.energy (Wave.highFrequencyWave a b ψ ε) t +
        Wave.energy (Wave.highFrequencyWave b (fun q => -a q) ψ ε) t))
      (𝓝[≠] 0) (𝓝 (leadingEnergy a b ψ t)) := by
  have hc : Continuous fun ε : ℝ => leadingEnergy a b ψ t + ε * crossEnergy a b ψ t +
      ε ^ 2 * (Wave.energy a t + Wave.energy b t) := by fun_prop
  have hlim := hc.tendsto 0
  simp only [zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    at hlim
  refine (tendsto_nhdsWithin_of_tendsto_nhds hlim).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (sq_mul_energy_add_shift ha hb hψ hT has hbs ht hε).symm

/-- **The energy of the high-frequency wave is of order `ε⁻²`**: for `|ε| |∫ (b ∂a − a ∂b) · ∂ψ|`
at most half the leading coefficient `L = ½ ∫ (a² + b²) |∂ψ|²`, the pair of phases has the energy
`E_w(t) + E_{w′}(t) ≥ L/(2ε²)`. -/
theorem leadingEnergy_div_two_le {T R : ℝ} {a b ψ : ℝ × E3 → ℝ} (ha : ContDiff ℝ 2 a)
    (hb : ContDiff ℝ 2 b) (hψ : ContDiff ℝ 2 ψ) (hT : 0 < T) (has : Wave.BallSupportOn T R a)
    (hbs : Wave.BallSupportOn T R b) {t : ℝ} (ht : t ∈ Icc 0 T) {ε : ℝ} (hε : ε ≠ 0)
    (hsmall : |ε| * |crossEnergy a b ψ t| ≤ leadingEnergy a b ψ t / 2) :
    leadingEnergy a b ψ t / 2 ≤ ε ^ 2 * (Wave.energy (Wave.highFrequencyWave a b ψ ε) t +
      Wave.energy (Wave.highFrequencyWave b (fun q => -a q) ψ ε) t) := by
  rw [sq_mul_energy_add_shift ha hb hψ hT has hbs ht hε]
  have h1 : -(|ε| * |crossEnergy a b ψ t|) ≤ ε * crossEnergy a b ψ t := by
    rw [← abs_mul]
    exact neg_abs_le _
  have h2 : 0 ≤ ε ^ 2 * (Wave.energy a t + Wave.energy b t) :=
    mul_nonneg (sq_nonneg ε) (add_nonneg (Wave.energy_nonneg a t) (Wave.energy_nonneg b t))
  linarith

/-- **The relative error of geometrical optics is of order `ε`** (Landau–Lifshitz §58): let `u`
and `u′` be exact solutions with the Cauchy data of `w = a cos(ψ/ε) + b sin(ψ/ε)` and of
`w′ = b cos(ψ/ε) − a sin(ψ/ε)`. For `|ε| |∫ (b ∂a − a ∂b) · ∂ψ| ≤ L/2` with
`L = ½ ∫ (a² + b²) |∂ψ|² > 0`, the energy of the errors is at most
`ε² · 4 (∫₀ᵗ ‖□a, □b‖)² / L` times the energy of the waves. -/
theorem energy_sub_add_energy_sub_le {T R : ℝ} {a b ψ u u' : ℝ × E3 → ℝ} (ha : ContDiff ℝ 2 a)
    (hb : ContDiff ℝ 2 b) (hψ : ContDiff ℝ 2 ψ) (h : IsGeometricalOptics T a b ψ) (hT : 0 < T)
    (has : Wave.BallSupportOn T R a) (hbs : Wave.BallSupportOn T R b)
    (hu : ContDiff ℝ 2 u) (hus : Wave.BallSupportOn T R u)
    (hwave : ∀ p : ℝ × E3, p.1 ∈ Icc 0 T → Wave.waveOperator u p = 0)
    (hu' : ContDiff ℝ 2 u') (hus' : Wave.BallSupportOn T R u')
    (hwave' : ∀ p : ℝ × E3, p.1 ∈ Icc 0 T → Wave.waveOperator u' p = 0) {ε : ℝ} (hε : ε ≠ 0)
    (h0 : ∀ x, u (0, x) = Wave.highFrequencyWave a b ψ ε (0, x))
    (h1 : ∀ x, Wave.timeDeriv u (0, x) = Wave.timeDeriv (Wave.highFrequencyWave a b ψ ε) (0, x))
    (h0' : ∀ x, u' (0, x) = Wave.highFrequencyWave b (fun q => -a q) ψ ε (0, x))
    (h1' : ∀ x, Wave.timeDeriv u' (0, x) =
      Wave.timeDeriv (Wave.highFrequencyWave b (fun q => -a q) ψ ε) (0, x))
    {t : ℝ} (ht : t ∈ Icc 0 T) (hL : 0 < leadingEnergy a b ψ t)
    (hsmall : |ε| * |crossEnergy a b ψ t| ≤ leadingEnergy a b ψ t / 2) :
    Wave.energy (fun p => u p - Wave.highFrequencyWave a b ψ ε p) t +
        Wave.energy (fun p => u' p - Wave.highFrequencyWave b (fun q => -a q) ψ ε p) t ≤
      ε ^ 2 * (4 * (∫ s in 0..t, amplitudeSource a b s) ^ 2 / leadingEnergy a b ψ t) *
        (Wave.energy (Wave.highFrequencyWave a b ψ ε) t +
          Wave.energy (Wave.highFrequencyWave b (fun q => -a q) ψ ε) t) := by
  have hnas : Wave.BallSupportOn T R fun q => -a q := fun s hs y hy => by
    simp only [has s hs y hy, neg_zero]
  set I := ∫ s in 0..t, amplitudeSource a b s with hI
  have hI0 : 0 ≤ I := intervalIntegral.integral_nonneg ht.1 fun s _ => amplitudeSource_nonneg a b s
  have hE1 := sqrt_energy_sub_le ha hb hψ h has hbs hu hus hwave hε h0 h1 ht
  have hE2 := sqrt_energy_sub_le hb ha.neg hψ h.shift hbs hnas hu' hus' hwave' hε h0' h1' ht
  simp only [amplitudeSource_shift] at hE2
  have hsq : ∀ E : ℝ, 0 ≤ E → √E ≤ I → E ≤ I ^ 2 := fun E hE hle => by
    have := pow_le_pow_left₀ (sqrt_nonneg E) hle 2
    rwa [sq_sqrt hE] at this
  have hE1' := hsq _ (Wave.energy_nonneg _ t) hE1
  have hE2' := hsq _ (Wave.energy_nonneg _ t) hE2
  have hlow := leadingEnergy_div_two_le ha hb hψ hT has hbs ht hε hsmall
  set S := Wave.energy (Wave.highFrequencyWave a b ψ ε) t +
    Wave.energy (Wave.highFrequencyWave b (fun q => -a q) ψ ε) t with hS
  have hk : 0 ≤ 4 * I ^ 2 / leadingEnergy a b ψ t := by positivity
  have key : 4 * I ^ 2 / leadingEnergy a b ψ t * (leadingEnergy a b ψ t / 2) = 2 * I ^ 2 := by
    field_simp
    ring
  have := mul_le_mul_of_nonneg_left hlow hk
  rw [key] at this
  calc _ ≤ 2 * I ^ 2 := by linarith
    _ ≤ 4 * I ^ 2 / leadingEnergy a b ψ t * (ε ^ 2 * S) := this
    _ = _ := by ring

/-! ### An instance: a plane wave along the first axis -/

/-- The phase `t − x₁` of a plane wave travelling along the first axis. -/
def planePhase (p : ℝ × E3) : ℝ := p.1 - p.2 0

/-- A profile `f` carried with the speed of light along the first axis, `f(x − t e₁)`. -/
def planeAmplitude (f : E3 → ℝ) (p : ℝ × E3) : ℝ := f (p.2 - p.1 • EuclideanSpace.single 0 1)

private def planePhaseCLM : ℝ × E3 →L[ℝ] ℝ :=
  ContinuousLinearMap.fst ℝ ℝ E3 - (EuclideanSpace.proj (0 : Fin 3)).comp
    (ContinuousLinearMap.snd ℝ ℝ E3)

private def planeShiftCLM : ℝ × E3 →L[ℝ] E3 :=
  ContinuousLinearMap.snd ℝ ℝ E3 -
    (ContinuousLinearMap.fst ℝ ℝ E3).smulRight (EuclideanSpace.single 0 1)

private theorem planePhase_eq : planePhase = planePhaseCLM := by
  funext p
  simp [planePhase, planePhaseCLM]

private theorem planeAmplitude_eq (f : E3 → ℝ) : planeAmplitude f = f ∘ planeShiftCLM := by
  funext p
  simp [planeAmplitude, planeShiftCLM]

/-- The plane phase is smooth. -/
theorem contDiff_planePhase {n : ℕ∞} : ContDiff ℝ n planePhase := by
  rw [planePhase_eq]
  exact planePhaseCLM.contDiff

/-- A profile carried along the first axis is as smooth as the profile. -/
theorem contDiff_planeAmplitude {n : ℕ∞} {f : E3 → ℝ} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (planeAmplitude f) := by
  rw [planeAmplitude_eq]
  exact hf.comp planeShiftCLM.contDiff

private theorem fderiv_planePhase (p v : ℝ × E3) : fderiv ℝ planePhase p v = v.1 - v.2 0 := by
  rw [planePhase_eq, ContinuousLinearMap.fderiv]
  simp [planePhaseCLM]

private theorem fderiv_planeAmplitude {f : E3 → ℝ} (hf : Differentiable ℝ f) (p v : ℝ × E3) :
    fderiv ℝ (planeAmplitude f) p v =
      fderiv ℝ f (p.2 - p.1 • EuclideanSpace.single 0 1)
        (v.2 - v.1 • EuclideanSpace.single 0 1) := by
  have h : HasFDerivAt (planeAmplitude f)
      ((fderiv ℝ f (planeShiftCLM p)).comp planeShiftCLM) p := by
    rw [planeAmplitude_eq]
    exact (hf _).hasFDerivAt.comp p planeShiftCLM.hasFDerivAt
  rw [h.fderiv]
  simp [planeShiftCLM]

/-- `∂ₜ(t − x₁) = 1`. -/
theorem timeDeriv_planePhase (p : ℝ × E3) : Wave.timeDeriv planePhase p = 1 := by
  simp [Wave.timeDeriv, fderiv_planePhase]

/-- `∂ᵢ(t − x₁) = −δᵢ₁`. -/
theorem spaceDeriv_planePhase (i : Fin 3) (p : ℝ × E3) :
    Wave.spaceDeriv i planePhase p = -(EuclideanSpace.single i (1 : ℝ)) 0 := by
  simp [Wave.spaceDeriv, fderiv_planePhase]

/-- The phase of the plane wave solves the wave equation, `□(t − x₁) = 0`. -/
theorem waveOperator_planePhase (p : ℝ × E3) : Wave.waveOperator planePhase p = 0 := by
  have ht : Wave.timeDeriv planePhase = fun _ => 1 := funext timeDeriv_planePhase
  have hs : ∀ i, Wave.spaceDeriv i planePhase = fun _ => -(EuclideanSpace.single i (1 : ℝ)) 0 :=
    fun i => funext (spaceDeriv_planePhase i)
  simp [Wave.waveOperator, ht, hs, Wave.timeDeriv, Wave.spaceDeriv]

/-- **The eikonal equation** of the plane wave: `⟨d(t − x₁), d(t − x₁)⟩ = 1 − 1 = 0`. -/
theorem wavePairing_planePhase (p : ℝ × E3) : Wave.wavePairing planePhase planePhase p = 0 := by
  simp [Wave.wavePairing, timeDeriv_planePhase, spaceDeriv_planePhase]

/-- **The transport equation** of the plane wave: a profile carried with the speed of light along
the first axis has `2⟨da, d(t − x₁)⟩ + a □(t − x₁) = 0`. -/
theorem transport_planeAmplitude {f : E3 → ℝ} (hf : Differentiable ℝ f) (p : ℝ × E3) :
    Wave.transport (planeAmplitude f) planePhase p = 0 := by
  have ht : Wave.timeDeriv (planeAmplitude f) p =
      -fderiv ℝ f (p.2 - p.1 • EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1) := by
    rw [Wave.timeDeriv, fderiv_planeAmplitude hf]
    simp
  have hs : ∀ i, Wave.spaceDeriv i (planeAmplitude f) p =
      fderiv ℝ f (p.2 - p.1 • EuclideanSpace.single 0 1) (EuclideanSpace.single i 1) := by
    intro i
    rw [Wave.spaceDeriv, fderiv_planeAmplitude hf]
    simp
  simp [Wave.transport, Wave.wavePairing, waveOperator_planePhase, ht, hs, spaceDeriv_planePhase,
    timeDeriv_planePhase]

/-- **An instance of the equations of geometrical optics**: the plane phase `t − x₁` with two
profiles carried along the first axis. -/
theorem isGeometricalOptics_plane {f g : E3 → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (T : ℝ) :
    IsGeometricalOptics T (planeAmplitude f) (planeAmplitude g) planePhase where
  eikonal p _ _ := wavePairing_planePhase p
  transport_fst p _ _ := transport_planeAmplitude hf p
  transport_snd p _ _ := transport_planeAmplitude hg p

/-- A profile that vanishes outside the ball of radius `r`, carried along the first axis, has
support in the ball of radius `r + T` on `[0, T]`. -/
theorem ballSupportOn_planeAmplitude {f : E3 → ℝ} {r : ℝ} (hf : ∀ y, r < ‖y‖ → f y = 0)
    (T : ℝ) : Wave.BallSupportOn T (r + T) (planeAmplitude f) := by
  intro s hs y hy
  refine hf _ ?_
  have h1 : ‖s • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)‖ = s := by
    rw [norm_smul, PiLp.norm_single, norm_one, mul_one, norm_of_nonneg hs.1]
  have h2 := norm_sub_norm_le y (s • EuclideanSpace.single (0 : Fin 3) (1 : ℝ))
  linarith [hs.2]

/-- The square of the gradient of the plane phase is `|∂(t − x₁)|² = 2`. -/
theorem gradNormSq_planePhase (p : ℝ × E3) : Wave.gradNormSq planePhase p = 2 := by
  simp [Wave.gradNormSq, timeDeriv_planePhase, spaceDeriv_planePhase]
  norm_num

/-- The leading coefficient of the energy of a plane wave is `∫ (f² + g²)` at every time. -/
theorem leadingEnergy_plane (f g : E3 → ℝ) (t : ℝ) :
    leadingEnergy (planeAmplitude f) (planeAmplitude g) planePhase t =
      ∫ x, (f x ^ 2 + g x ^ 2) := by
  simp only [leadingEnergy, gradNormSq_planePhase, planeAmplitude]
  rw [← integral_sub_right_eq_self (fun x => f x ^ 2 + g x ^ 2)
    (t • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)), ← integral_const_mul]
  congr 1
  funext x
  ring

/-- **An instance with a positive leading term**: for the bump `χ = spaceBump` carried along the
first axis, `½ ∫ (a² + b²) |∂ψ|² = ∫ χ² > 0`. -/
theorem leadingEnergy_plane_spaceBump_pos (t : ℝ) :
    0 < leadingEnergy (planeAmplitude Wave.spaceBump) (planeAmplitude fun _ => 0) planePhase t := by
  rw [leadingEnergy_plane]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0)
    (Wave.spaceBump.continuous.fun_pow 2) ?_ (fun x => by positivity)
    (pow_ne_zero 2 (Wave.spaceBump.pos_of_mem_ball (mem_ball_self Wave.spaceBump.rOut_pos)).ne')
  exact HasCompactSupport.intro (isCompact_closedBall 0 2) fun y hy => by
    simp [Wave.spaceBump.zero_of_le_dist (by
      rw [dist_zero_right]; rw [mem_closedBall_zero_iff, not_le] at hy; exact hy.le)]

/-- **An instance of the wave operator in geometrical optics**: for the plane wave
`w = f(x − t e₁) cos((t − x₁)/ε) + g(x − t e₁) sin((t − x₁)/ε)` the terms of order `ε⁻²`
and `ε⁻¹` vanish, `□w = □a cos + □b sin`. -/
theorem waveOperator_plane {f g : E3 → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) {ε : ℝ}
    (hε : ε ≠ 0) {p : ℝ × E3} (hp : 0 ≤ p.1) :
    Wave.waveOperator
        (Wave.highFrequencyWave (planeAmplitude f) (planeAmplitude g) planePhase ε) p =
      Wave.waveOperator (planeAmplitude f) p * cos (planePhase p / ε) +
        Wave.waveOperator (planeAmplitude g) p * sin (planePhase p / ε) :=
  (isGeometricalOptics_plane (hf.differentiable (by norm_num)) (hg.differentiable (by norm_num))
    p.1).waveOperator_eq (contDiff_planeAmplitude hf) (contDiff_planeAmplitude hg)
    contDiff_planePhase hε ⟨hp, le_rfl⟩

/-! ### An exact instance: an outgoing spherical shell -/

private theorem fderiv_apply_of_line {F : ℝ × E3 → ℝ} {q v : ℝ × E3} {d : ℝ}
    (hF : DifferentiableAt ℝ F q) (h : HasDerivAt (fun s : ℝ => F (q + s • v)) d 0) :
    fderiv ℝ F q v = d := by
  have hl : HasDerivAt (fun s : ℝ => q + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add q
  exact (hF.hasFDerivAt.comp_hasDerivAt_of_eq 0 hl (by simp)).unique h

private theorem timeDeriv_eq_of_line {F : ℝ × E3 → ℝ} {q : ℝ × E3} {d : ℝ}
    (hF : DifferentiableAt ℝ F q) (h : HasDerivAt (fun s : ℝ => F (q.1 + s, q.2)) d 0) :
    Wave.timeDeriv F q = d := by
  refine fderiv_apply_of_line hF ?_
  have e : (fun s : ℝ => F (q + s • ((1 : ℝ), (0 : E3)))) = fun s => F (q.1 + s, q.2) := by
    funext s
    congr 1
    exact Prod.ext (by simp) (by simp)
  rw [e]
  exact h

private theorem spaceDeriv_eq_of_line {F : ℝ × E3 → ℝ} {q : ℝ × E3} {d : ℝ}
    (hF : DifferentiableAt ℝ F q) (i : Fin 3)
    (h : HasDerivAt (fun s : ℝ => F (q.1, q.2 + s • EuclideanSpace.single i (1 : ℝ))) d 0) :
    Wave.spaceDeriv i F q = d := by
  refine fderiv_apply_of_line hF ?_
  have e : (fun s : ℝ => F (q + s • ((0 : ℝ), EuclideanSpace.single i (1 : ℝ)))) =
      fun s => F (q.1, q.2 + s • EuclideanSpace.single i (1 : ℝ)) := by
    funext s
    congr 1
    exact Prod.ext (by simp) (by simp)
  rw [e]
  exact h

private theorem hasDerivAt_norm_line {x : E3} (hx : x ≠ 0) (i : Fin 3) :
    HasDerivAt (fun s : ℝ => ‖x + s • EuclideanSpace.single i (1 : ℝ)‖) (x i / ‖x‖) 0 := by
  have hl : HasDerivAt (fun s : ℝ => x + s • EuclideanSpace.single i (1 : ℝ))
      (EuclideanSpace.single i 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single i (1 : ℝ))).const_add x
  have := (Wave.hasFDerivAt_norm_of_ne_zero hx).comp_hasDerivAt_of_eq 0 hl (by simp)
  refine this.congr_deriv ?_
  simp [EuclideanSpace.inner_single_right, div_eq_inv_mul]

private theorem hasDerivAt_coord_line (x : E3) (i : Fin 3) :
    HasDerivAt (fun s : ℝ => (x + s • EuclideanSpace.single i (1 : ℝ)) i) 1 0 := by
  have e : (fun s : ℝ => (x + s • EuclideanSpace.single i (1 : ℝ)) i) = fun s => x i + s := by
    funext s
    simp
  rw [e]
  simpa using (hasDerivAt_id (0 : ℝ)).const_add (x i)

/-- The spherical phase `t − ‖x‖`. -/
def radialPhase (p : ℝ × E3) : ℝ := p.1 - ‖p.2‖

/-- The spherical amplitude `g(t − ‖x‖)/‖x‖`. -/
def radialAmplitude (g : ℝ → ℝ) (p : ℝ × E3) : ℝ := g (p.1 - ‖p.2‖) * ‖p.2‖⁻¹

private theorem differentiableAt_norm_snd {q : ℝ × E3} (hq : q.2 ≠ 0) :
    DifferentiableAt ℝ (fun p : ℝ × E3 => ‖p.2‖) q :=
  ((contDiffAt_norm ℝ (n := 1) hq).differentiableAt one_ne_zero).comp q differentiableAt_snd

private theorem differentiableAt_radialPhase {q : ℝ × E3} (hq : q.2 ≠ 0) :
    DifferentiableAt ℝ radialPhase q :=
  differentiableAt_fst.sub (differentiableAt_norm_snd hq)

private theorem differentiableAt_radialAmplitude {g : ℝ → ℝ} (hg : Differentiable ℝ g) {q : ℝ × E3}
    (hq : q.2 ≠ 0) : DifferentiableAt ℝ (radialAmplitude g) q :=
  ((hg _).comp q (differentiableAt_radialPhase hq)).mul
    ((differentiableAt_norm_snd hq).inv (norm_ne_zero_iff.mpr hq))

/-- `∂ₜ(t − r) = 1` away from the origin. -/
theorem timeDeriv_radialPhase {q : ℝ × E3} (hq : q.2 ≠ 0) : Wave.timeDeriv radialPhase q = 1 :=
  timeDeriv_eq_of_line (differentiableAt_radialPhase hq) (by
    simpa [radialPhase] using ((hasDerivAt_id (0 : ℝ)).const_add q.1).sub_const ‖q.2‖)

/-- `∂ᵢ(t − r) = −xᵢ/r` away from the origin. -/
theorem spaceDeriv_radialPhase {q : ℝ × E3} (hq : q.2 ≠ 0) (i : Fin 3) :
    Wave.spaceDeriv i radialPhase q = -(q.2 i * ‖q.2‖⁻¹) :=
  spaceDeriv_eq_of_line (differentiableAt_radialPhase hq) i (by
    have := (hasDerivAt_norm_line hq i).const_sub q.1
    simpa [radialPhase, div_eq_mul_inv] using this)

private theorem isOpen_snd_ne_zero : IsOpen {p : ℝ × E3 | p.2 ≠ 0} :=
  isOpen_ne_fun continuous_snd continuous_const

/-- `∂ₜ(g(t − r)/r) = g′(t − r)/r` away from the origin. -/
theorem timeDeriv_radialAmplitude {g : ℝ → ℝ} (hg : Differentiable ℝ g) {q : ℝ × E3}
    (hq : q.2 ≠ 0) :
    Wave.timeDeriv (radialAmplitude g) q = radialAmplitude (deriv g) q := by
  refine timeDeriv_eq_of_line (differentiableAt_radialAmplitude hg hq) ?_
  have h1 : HasDerivAt (fun s : ℝ => q.1 + s - ‖q.2‖) 1 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_add q.1).sub_const ‖q.2‖
  have h2 := ((hg (q.1 - ‖q.2‖)).hasDerivAt.comp_of_eq 0 h1 (by simp)).mul_const ‖q.2‖⁻¹
  refine h2.congr_deriv ?_
  simp [radialAmplitude]

/-- `∂ᵢ(g(t − r)/r) = −xᵢ (g′(t − r)/r² + g(t − r)/r³)` away from the origin. -/
theorem spaceDeriv_radialAmplitude {g : ℝ → ℝ} (hg : Differentiable ℝ g) {q : ℝ × E3} (hq : q.2 ≠ 0)
    (i : Fin 3) :
    Wave.spaceDeriv i (radialAmplitude g) q = -(q.2 i * (deriv g (q.1 - ‖q.2‖) * ‖q.2‖⁻¹ ^ 2 +
      g (q.1 - ‖q.2‖) * ‖q.2‖⁻¹ ^ 3)) := by
  refine spaceDeriv_eq_of_line (differentiableAt_radialAmplitude hg hq) i ?_
  have hr := hasDerivAt_norm_line hq i
  have hτ := hr.const_sub q.1
  have hgτ := (hg (q.1 - ‖q.2‖)).hasDerivAt.comp_of_eq 0 hτ (by simp)
  have hι := hr.fun_inv (by simpa using hq)
  refine (hgτ.fun_mul hι).congr_deriv ?_
  have hn : ‖q.2‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  simp only [Function.comp, zero_smul, add_zero]
  field_simp
  ring

private theorem differentiableAt_coord (i : Fin 3) (q : ℝ × E3) :
    DifferentiableAt ℝ (fun p : ℝ × E3 => p.2 i) q :=
  ((EuclideanSpace.proj i).comp (ContinuousLinearMap.snd ℝ ℝ E3)).differentiableAt

private theorem differentiableAt_inv_norm_snd {q : ℝ × E3} (hq : q.2 ≠ 0) :
    DifferentiableAt ℝ (fun p : ℝ × E3 => ‖p.2‖⁻¹) q :=
  (differentiableAt_norm_snd hq).inv (norm_ne_zero_iff.mpr hq)

/-- The closed form of the spatial derivative of the amplitude. -/
private def ampS (g : ℝ → ℝ) (i : Fin 3) (p : ℝ × E3) : ℝ :=
  -(p.2 i * (deriv g (p.1 - ‖p.2‖) * ‖p.2‖⁻¹ ^ 2 + g (p.1 - ‖p.2‖) * ‖p.2‖⁻¹ ^ 3))

/-- The closed form of the spatial derivative of the phase. -/
private def phaseS (i : Fin 3) (p : ℝ × E3) : ℝ := -(p.2 i * ‖p.2‖⁻¹)

private theorem differentiableAt_ampS {g : ℝ → ℝ} (hg : Differentiable ℝ g)
    (hg' : Differentiable ℝ (deriv g)) {q : ℝ × E3} (hq : q.2 ≠ 0) (i : Fin 3) :
    DifferentiableAt ℝ (ampS g i) q :=
  ((differentiableAt_coord i q).mul
    ((((hg' _).comp q (differentiableAt_radialPhase hq)).mul
      ((differentiableAt_inv_norm_snd hq).pow 2)).add
    (((hg _).comp q (differentiableAt_radialPhase hq)).mul
      ((differentiableAt_inv_norm_snd hq).pow 3)))).neg

private theorem differentiableAt_phaseS {q : ℝ × E3} (hq : q.2 ≠ 0) (i : Fin 3) :
    DifferentiableAt ℝ (phaseS i) q :=
  ((differentiableAt_coord i q).mul (differentiableAt_inv_norm_snd hq)).neg

private theorem spaceDeriv_ampS {g : ℝ → ℝ} (hg : Differentiable ℝ g)
    (hg' : Differentiable ℝ (deriv g)) {q : ℝ × E3} (hq : q.2 ≠ 0) (i : Fin 3) :
    Wave.spaceDeriv i (ampS g i) q =
      -(deriv g (q.1 - ‖q.2‖) * ‖q.2‖⁻¹ ^ 2 + g (q.1 - ‖q.2‖) * ‖q.2‖⁻¹ ^ 3) +
        q.2 i ^ 2 * (deriv (deriv g) (q.1 - ‖q.2‖) * ‖q.2‖⁻¹ ^ 3 +
          3 * deriv g (q.1 - ‖q.2‖) * ‖q.2‖⁻¹ ^ 4 + 3 * g (q.1 - ‖q.2‖) * ‖q.2‖⁻¹ ^ 5) := by
  refine spaceDeriv_eq_of_line (differentiableAt_ampS hg hg' hq i) i ?_
  have hr := hasDerivAt_norm_line hq i
  have hτ := hr.const_sub q.1
  have hgτ := (hg (q.1 - ‖q.2‖)).hasDerivAt.comp_of_eq 0 hτ (by simp)
  have hg'τ := (hg' (q.1 - ‖q.2‖)).hasDerivAt.comp_of_eq 0 hτ (by simp)
  have hι := hr.fun_inv (by simpa using hq)
  have hc := hasDerivAt_coord_line q.2 i
  refine ((hc.fun_mul ((hg'τ.fun_mul (hι.fun_pow 2)).fun_add
    (hgτ.fun_mul (hι.fun_pow 3)))).fun_neg).congr_deriv ?_
  have hn : ‖q.2‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  simp only [Function.comp, zero_smul, add_zero, Nat.cast_ofNat, Nat.add_one_sub_one,
    show (3 : ℕ) - 1 = 2 from rfl, pow_one]
  field_simp
  ring

private theorem spaceDeriv_phaseS {q : ℝ × E3} (hq : q.2 ≠ 0) (i : Fin 3) :
    Wave.spaceDeriv i (phaseS i) q = -‖q.2‖⁻¹ + q.2 i ^ 2 * ‖q.2‖⁻¹ ^ 3 := by
  refine spaceDeriv_eq_of_line (differentiableAt_phaseS hq i) i ?_
  have hr := hasDerivAt_norm_line hq i
  have hι := hr.fun_inv (by simpa using hq)
  have hc := hasDerivAt_coord_line q.2 i
  refine (hc.fun_mul hι).fun_neg.congr_deriv ?_
  have hn : ‖q.2‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  simp only [zero_smul, add_zero]
  field_simp
  ring

private theorem timeDeriv_congr {f g : ℝ × E3 → ℝ} {q : ℝ × E3} (h : f =ᶠ[𝓝 q] g) :
    Wave.timeDeriv f q = Wave.timeDeriv g q := by
  simp only [Wave.timeDeriv, h.fderiv_eq]

private theorem spaceDeriv_congr {f g : ℝ × E3 → ℝ} {q : ℝ × E3} (h : f =ᶠ[𝓝 q] g) (i : Fin 3) :
    Wave.spaceDeriv i f q = Wave.spaceDeriv i g q := by
  simp only [Wave.spaceDeriv, h.fderiv_eq]

private theorem sum_sq_coord (x : E3) : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]

/-- **The spherical wave solves the wave equation**: `□(g(t − r)/r) = 0` away from the origin. -/
theorem waveOperator_radialAmplitude {g : ℝ → ℝ} (hg : Differentiable ℝ g)
    (hg' : Differentiable ℝ (deriv g)) {q : ℝ × E3} (hq : q.2 ≠ 0) :
    Wave.waveOperator (radialAmplitude g) q = 0 := by
  have ht : Wave.timeDeriv (radialAmplitude g) =ᶠ[𝓝 q] radialAmplitude (deriv g) :=
    eventually_of_mem (isOpen_snd_ne_zero.mem_nhds hq) fun p hp => timeDeriv_radialAmplitude hg hp
  have hs : ∀ i, Wave.spaceDeriv i (radialAmplitude g) =ᶠ[𝓝 q] ampS g i := fun i =>
    eventually_of_mem (isOpen_snd_ne_zero.mem_nhds hq) fun p hp =>
      spaceDeriv_radialAmplitude hg hp i
  have hn : ‖q.2‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  simp only [Wave.waveOperator, timeDeriv_congr ht, timeDeriv_radialAmplitude hg' hq,
    fun i => spaceDeriv_congr (hs i) i, spaceDeriv_ampS hg hg' hq, Fin.sum_univ_three,
    radialAmplitude]
  have h0 : deriv (deriv g) (q.1 - ‖q.2‖) * ‖q.2‖⁻¹ +
      3 * (deriv g (q.1 - ‖q.2‖) * ‖q.2‖⁻¹ ^ 2 + g (q.1 - ‖q.2‖) * ‖q.2‖⁻¹ ^ 3) -
      ‖q.2‖ ^ 2 * (deriv (deriv g) (q.1 - ‖q.2‖) * ‖q.2‖⁻¹ ^ 3 +
          3 * deriv g (q.1 - ‖q.2‖) * ‖q.2‖⁻¹ ^ 4 + 3 * g (q.1 - ‖q.2‖) * ‖q.2‖⁻¹ ^ 5) = 0 := by
    field_simp
    ring
  linear_combination (-(deriv (deriv g) (q.1 - ‖q.2‖) * ‖q.2‖⁻¹ ^ 3 +
    3 * deriv g (q.1 - ‖q.2‖) * ‖q.2‖⁻¹ ^ 4 + 3 * g (q.1 - ‖q.2‖) * ‖q.2‖⁻¹ ^ 5)) *
    sum_sq_coord q.2 + h0

/-- `□(t − r) = Δr = 2/r` away from the origin. -/
theorem waveOperator_radialPhase {q : ℝ × E3} (hq : q.2 ≠ 0) :
    Wave.waveOperator radialPhase q = 2 * ‖q.2‖⁻¹ := by
  have ht : Wave.timeDeriv radialPhase =ᶠ[𝓝 q] fun _ => 1 :=
    eventually_of_mem (isOpen_snd_ne_zero.mem_nhds hq) fun p hp => timeDeriv_radialPhase hp
  have hs : ∀ i, Wave.spaceDeriv i radialPhase =ᶠ[𝓝 q] phaseS i := fun i =>
    eventually_of_mem (isOpen_snd_ne_zero.mem_nhds hq) fun p hp => spaceDeriv_radialPhase hp i
  have htt : Wave.timeDeriv (fun _ : ℝ × E3 => (1 : ℝ)) q = 0 := by simp [Wave.timeDeriv]
  have hn : ‖q.2‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  simp only [Wave.waveOperator, timeDeriv_congr ht, htt, fun i => spaceDeriv_congr (hs i) i,
    spaceDeriv_phaseS hq, Fin.sum_univ_three]
  have h0 : 3 * ‖q.2‖⁻¹ - ‖q.2‖ ^ 2 * ‖q.2‖⁻¹ ^ 3 - 2 * ‖q.2‖⁻¹ = 0 := by
    field_simp
    ring
  linear_combination (-(‖q.2‖⁻¹ ^ 3)) * sum_sq_coord q.2 + h0

/-- **The eikonal equation** of the spherical phase: `⟨d(t − r), d(t − r)⟩ = 0`. -/
theorem wavePairing_radialPhase {q : ℝ × E3} (hq : q.2 ≠ 0) :
    Wave.wavePairing radialPhase radialPhase q = 0 := by
  have hn : ‖q.2‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  simp only [Wave.wavePairing, timeDeriv_radialPhase hq, spaceDeriv_radialPhase hq,
    Fin.sum_univ_three]
  have h0 : 1 - ‖q.2‖ ^ 2 * ‖q.2‖⁻¹ ^ 2 = 0 := by
    field_simp
    ring
  linear_combination (-(‖q.2‖⁻¹ ^ 2)) * sum_sq_coord q.2 + h0

/-- `|∂(t − r)|² = 2` away from the origin. -/
theorem gradNormSq_radialPhase {q : ℝ × E3} (hq : q.2 ≠ 0) : Wave.gradNormSq radialPhase q = 2 := by
  have hn : ‖q.2‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  simp only [Wave.gradNormSq, timeDeriv_radialPhase hq, spaceDeriv_radialPhase hq,
    Fin.sum_univ_three]
  have h0 : 1 + ‖q.2‖ ^ 2 * ‖q.2‖⁻¹ ^ 2 - 2 = 0 := by
    field_simp
    ring
  linear_combination (‖q.2‖⁻¹ ^ 2) * sum_sq_coord q.2 + h0

/-- **The transport equation** of the spherical wave: `2⟨da, d(t − r)⟩ + a □(t − r) = 0` for
`a = g(t − r)/r`. -/
theorem transport_radialAmplitude {g : ℝ → ℝ} (hg : Differentiable ℝ g) {q : ℝ × E3}
    (hq : q.2 ≠ 0) :
    Wave.transport (radialAmplitude g) radialPhase q = 0 := by
  have hn : ‖q.2‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  simp only [Wave.transport, Wave.wavePairing, timeDeriv_radialAmplitude hg hq,
    timeDeriv_radialPhase hq, spaceDeriv_radialAmplitude hg hq, spaceDeriv_radialPhase hq,
    waveOperator_radialPhase hq, Fin.sum_univ_three,
    radialAmplitude]
  have h0 : 2 * (deriv g (q.1 - ‖q.2‖) * ‖q.2‖⁻¹ - ‖q.2‖ ^ 2 * ‖q.2‖⁻¹ *
      (deriv g (q.1 - ‖q.2‖) * ‖q.2‖⁻¹ ^ 2 + g (q.1 - ‖q.2‖) * ‖q.2‖⁻¹ ^ 3)) +
      g (q.1 - ‖q.2‖) * ‖q.2‖⁻¹ * (2 * ‖q.2‖⁻¹) = 0 := by
    field_simp
    ring
  linear_combination (-(2 * ‖q.2‖⁻¹ * (deriv g (q.1 - ‖q.2‖) * ‖q.2‖⁻¹ ^ 2 +
    g (q.1 - ‖q.2‖) * ‖q.2‖⁻¹ ^ 3))) * sum_sq_coord q.2 + h0

private theorem eqOn_timeDeriv {f g : ℝ × E3 → ℝ} {U : Set (ℝ × E3)} (hU : IsOpen U)
    (h : EqOn f g U) :
    EqOn (Wave.timeDeriv f) (Wave.timeDeriv g) U := fun _ hp =>
  timeDeriv_congr (eventually_of_mem (hU.mem_nhds hp) h)

private theorem eqOn_spaceDeriv {f g : ℝ × E3 → ℝ} {U : Set (ℝ × E3)} (hU : IsOpen U)
    (h : EqOn f g U) (i : Fin 3) : EqOn (Wave.spaceDeriv i f) (Wave.spaceDeriv i g) U := fun _ hp =>
  spaceDeriv_congr (eventually_of_mem (hU.mem_nhds hp) h) i

private theorem eqOn_waveOperator {f g : ℝ × E3 → ℝ} {U : Set (ℝ × E3)} (hU : IsOpen U)
    (h : EqOn f g U) : EqOn (Wave.waveOperator f) (Wave.waveOperator g) U := fun p hp => by
  simp only [Wave.waveOperator, eqOn_timeDeriv hU (eqOn_timeDeriv hU h) hp,
    fun i => eqOn_spaceDeriv hU (eqOn_spaceDeriv hU h i) i hp]

private theorem eqOn_transport {f g ψ φ : ℝ × E3 → ℝ} {U : Set (ℝ × E3)} (hU : IsOpen U)
    (h : EqOn f g U) (hψ : EqOn ψ φ U) {p : ℝ × E3} (hp : p ∈ U) :
    Wave.transport f ψ p = Wave.transport g φ p := by
  simp only [Wave.transport, Wave.wavePairing, eqOn_timeDeriv hU h hp, eqOn_timeDeriv hU hψ hp,
    fun i => eqOn_spaceDeriv hU h i hp, fun i => eqOn_spaceDeriv hU hψ i hp,
    eqOn_waveOperator hU hψ hp, h hp]

private theorem eqOn_wavePairing {ψ φ : ℝ × E3 → ℝ} {U : Set (ℝ × E3)} (hU : IsOpen U)
    (hψ : EqOn ψ φ U) {p : ℝ × E3} (hp : p ∈ U) :
    Wave.wavePairing ψ ψ p = Wave.wavePairing φ φ p := by
  simp only [Wave.wavePairing, eqOn_timeDeriv hU hψ hp, fun i => eqOn_spaceDeriv hU hψ i hp]

private theorem eqOn_gradNormSq {ψ φ : ℝ × E3 → ℝ} {U : Set (ℝ × E3)} (hU : IsOpen U)
    (hψ : EqOn ψ φ U) {p : ℝ × E3} (hp : p ∈ U) :
    Wave.gradNormSq ψ p = Wave.gradNormSq φ p := by
  simp only [Wave.gradNormSq, eqOn_timeDeriv hU hψ hp, fun i => eqOn_spaceDeriv hU hψ i hp]

/-- The smooth radius `χ(x) ‖x‖`, equal to `‖x‖` for `‖x‖ ≥ 1`. -/
def smoothRadius (x : E3) : ℝ := Wave.cutoff (1 / 2) x * ‖x‖

/-- The smooth inverse radius `χ(x) / ‖x‖`, equal to `1/‖x‖` for `‖x‖ ≥ 1`. -/
def smoothInvRadius (x : E3) : ℝ := Wave.cutoff (1 / 2) x * ‖x‖⁻¹

/-- The smooth radius is smooth. -/
theorem contDiff_smoothRadius {n : ℕ∞} : ContDiff ℝ n smoothRadius := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Wave.cutoff_eventuallyEq_zero (ε := 1 / 2) (by norm_num)] with y hy
    simp only [smoothRadius, hy, zero_mul]
  · exact (Wave.contDiff_cutoff (by norm_num)).contDiffAt.mul (contDiffAt_norm ℝ hx)

/-- The smooth inverse radius is smooth. -/
theorem contDiff_smoothInvRadius {n : ℕ∞} : ContDiff ℝ n smoothInvRadius := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Wave.cutoff_eventuallyEq_zero (ε := 1 / 2) (by norm_num)] with y hy
    simp only [smoothInvRadius, hy, zero_mul]
  · exact (Wave.contDiff_cutoff (by norm_num)).contDiffAt.mul
      ((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx))

/-- The smooth radius is the radius for `‖x‖ ≥ 1`. -/
theorem smoothRadius_of_one_le {x : E3} (hx : 1 ≤ ‖x‖) : smoothRadius x = ‖x‖ := by
  rw [smoothRadius, Wave.cutoff_eq_one (by norm_num) (by linarith), one_mul]

/-- The smooth inverse radius is `1/‖x‖` for `‖x‖ ≥ 1`. -/
theorem smoothInvRadius_of_one_le {x : E3} (hx : 1 ≤ ‖x‖) : smoothInvRadius x = ‖x‖⁻¹ := by
  rw [smoothInvRadius, Wave.cutoff_eq_one (by norm_num) (by linarith), one_mul]

private theorem smoothRadius_le (x : E3) : smoothRadius x ≤ ‖x‖ := by
  have h := Wave.cutoff_mem_Icc (1 / 2) x
  rw [smoothRadius]
  nlinarith [norm_nonneg x, h.1, h.2]

/-- The profile of the shell, a bump on `[−6, −4]` with the value `1` at `−5`. -/
def shellBump : ContDiffBump (-5 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- The spherical phase `t − ρ(x)`, equal to `t − ‖x‖` for `‖x‖ ≥ 1`. -/
def sphericalPhase (p : ℝ × E3) : ℝ := p.1 - smoothRadius p.2

/-- The amplitude of an outgoing spherical shell, `g(t − ρ(x)) χ(x)/‖x‖`, equal to
`g(t − ‖x‖)/‖x‖` for `‖x‖ ≥ 1`, with the profile `g = shellBump`. -/
def sphericalAmplitude (p : ℝ × E3) : ℝ := shellBump (p.1 - smoothRadius p.2) * smoothInvRadius p.2

/-- The spherical phase is smooth. -/
theorem contDiff_sphericalPhase {n : ℕ∞} : ContDiff ℝ n sphericalPhase :=
  contDiff_fst.sub (contDiff_smoothRadius.comp contDiff_snd)

/-- The spherical amplitude is smooth. -/
theorem contDiff_sphericalAmplitude {n : ℕ∞} : ContDiff ℝ n sphericalAmplitude :=
  (shellBump.contDiff.comp (contDiff_fst.sub (contDiff_smoothRadius.comp contDiff_snd))).mul
    (contDiff_smoothInvRadius.comp contDiff_snd)

private theorem isOpen_outer : IsOpen {p : ℝ × E3 | 1 < ‖p.2‖} :=
  isOpen_lt continuous_const (continuous_norm.comp continuous_snd)

private theorem isOpen_inner : IsOpen {p : ℝ × E3 | -1 < p.1 ∧ ‖p.2‖ < 2} :=
  (isOpen_lt continuous_const continuous_fst).inter
    (isOpen_lt (continuous_norm.comp continuous_snd) continuous_const)

private theorem eqOn_sphericalPhase : EqOn sphericalPhase radialPhase {p : ℝ × E3 | 1 < ‖p.2‖} :=
  fun p hp => by simp [sphericalPhase, radialPhase, smoothRadius_of_one_le (le_of_lt hp)]

private theorem eqOn_sphericalAmplitude :
    EqOn sphericalAmplitude (radialAmplitude shellBump) {p : ℝ × E3 | 1 < ‖p.2‖} := fun p hp => by
  simp [sphericalAmplitude, radialAmplitude, smoothRadius_of_one_le (le_of_lt hp),
    smoothInvRadius_of_one_le (le_of_lt hp)]

private theorem eqOn_sphericalAmplitude_zero :
    EqOn sphericalAmplitude (fun _ => 0) {p : ℝ × E3 | -1 < p.1 ∧ ‖p.2‖ < 2} := fun p hp => by
  have h1 := smoothRadius_le p.2
  have h2 : 0 ≤ smoothRadius p.2 :=
    mul_nonneg (Wave.cutoff_mem_Icc _ _).1 (norm_nonneg _)
  have hd : shellBump.rOut ≤ dist (p.1 - smoothRadius p.2) (-5) := by
    rw [Real.dist_eq, abs_of_pos (by linarith [hp.1, hp.2])]
    show (1 : ℝ) ≤ _
    linarith [hp.1, hp.2]
  simp [sphericalAmplitude, shellBump.zero_of_le_dist hd]

private theorem shellBump_differentiable : Differentiable ℝ shellBump :=
  shellBump.contDiff.differentiable (n := 1) one_ne_zero

private theorem shellBump_differentiable_deriv : Differentiable ℝ (deriv shellBump) :=
  (shellBump.contDiff (n := 2)).differentiable_deriv_two

private theorem notMem_tsupport_sphericalAmplitude {p : ℝ × E3}
    (hp : p ∈ {p : ℝ × E3 | -1 < p.1 ∧ ‖p.2‖ < 2}) : p ∉ tsupport sphericalAmplitude := by
  rw [notMem_tsupport_iff_eventuallyEq]
  exact eventually_of_mem (isOpen_inner.mem_nhds hp) eqOn_sphericalAmplitude_zero

/-- **The spherical shell solves the wave equation** at the times `t ≥ 0`: near the origin the
amplitude vanishes, and away from it `□(g(t − r)/r) = 0`. -/
theorem waveOperator_sphericalAmplitude {p : ℝ × E3} (hp : 0 ≤ p.1) :
    Wave.waveOperator sphericalAmplitude p = 0 := by
  rcases lt_or_ge ‖p.2‖ 2 with h | h
  · rw [eqOn_waveOperator isOpen_inner eqOn_sphericalAmplitude_zero
      (show -1 < p.1 ∧ ‖p.2‖ < 2 from ⟨by linarith, h⟩)]
    exact Wave.waveOperator_eq_zero_of_notMem (by simp)
  · rw [eqOn_waveOperator isOpen_outer eqOn_sphericalAmplitude
      (show 1 < ‖p.2‖ by linarith)]
    exact waveOperator_radialAmplitude shellBump_differentiable shellBump_differentiable_deriv
      (norm_pos_iff.mp (by linarith))

private theorem two_le_norm_of_mem_tsupport {p : ℝ × E3} (hp : p ∈ tsupport sphericalAmplitude)
    (hp0 : 0 ≤ p.1) : 2 ≤ ‖p.2‖ := by
  by_contra h
  exact notMem_tsupport_sphericalAmplitude ⟨by linarith, not_le.mp h⟩ hp

/-- **An instance of the equations of geometrical optics with an exact wave**: the outgoing
spherical shell `a = g(t − r)/r` on the phase `t − r`, cut off smoothly near the origin, which
the shell does not reach at the times `t ≥ 0`. -/
theorem isGeometricalOptics_spherical (T : ℝ) :
    IsGeometricalOptics T sphericalAmplitude sphericalAmplitude sphericalPhase where
  eikonal p hp hab := by
    have ha : sphericalAmplitude p ≠ 0 := hab.elim id id
    have h2 : 2 ≤ ‖p.2‖ := by
      by_contra h
      exact ha (eqOn_sphericalAmplitude_zero
        (show -1 < p.1 ∧ ‖p.2‖ < 2 from ⟨by linarith [hp.1], not_le.mp h⟩))
    rw [eqOn_wavePairing isOpen_outer eqOn_sphericalPhase (show 1 < ‖p.2‖ by linarith)]
    exact wavePairing_radialPhase (norm_pos_iff.mp (by linarith))
  transport_fst p hp hpT := by
    have h2 := two_le_norm_of_mem_tsupport hp hpT.1
    rw [eqOn_transport isOpen_outer eqOn_sphericalAmplitude eqOn_sphericalPhase
      (show 1 < ‖p.2‖ by linarith)]
    exact transport_radialAmplitude shellBump_differentiable (norm_pos_iff.mp (by linarith))
  transport_snd p hp hpT := by
    have h2 := two_le_norm_of_mem_tsupport hp hpT.1
    rw [eqOn_transport isOpen_outer eqOn_sphericalAmplitude eqOn_sphericalPhase
      (show 1 < ‖p.2‖ by linarith)]
    exact transport_radialAmplitude shellBump_differentiable (norm_pos_iff.mp (by linarith))

/-- The spherical shell has support in the ball of radius `T + 6` on `[0, T]`. -/
theorem ballSupportOn_sphericalAmplitude (T : ℝ) :
    Wave.BallSupportOn T (T + 6) sphericalAmplitude := by
  intro s hs y hy
  have h1 : 1 ≤ ‖y‖ := by linarith [hs.1, hs.2]
  have hd : shellBump.rOut ≤ dist (s - smoothRadius y) (-5) := by
    rw [smoothRadius_of_one_le h1, Real.dist_eq, abs_of_neg (by linarith [hs.2])]
    show (1 : ℝ) ≤ _
    linarith [hs.2]
  simp [sphericalAmplitude, shellBump.zero_of_le_dist hd]

/-- The coefficient of order `ε⁻¹` vanishes for equal amplitudes. -/
theorem crossEnergy_self (a ψ : ℝ × E3 → ℝ) (t : ℝ) : crossEnergy a a ψ t = 0 := by
  simp [crossEnergy]

/-- The leading coefficient of the energy of the spherical shell is positive at the times
`t ≥ 0`. -/
theorem leadingEnergy_spherical_pos {t : ℝ} (ht : 0 ≤ t) :
    0 < leadingEnergy sphericalAmplitude sphericalAmplitude sphericalPhase t := by
  set x₀ : E3 := (t + 5) • EuclideanSpace.single 0 1 with hx₀def
  have hx₀ : ‖x₀‖ = t + 5 := by
    rw [hx₀def, norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
  have h1 : 1 < ‖(t, x₀).2‖ := by simp only; rw [hx₀]; linarith
  have hA : sphericalAmplitude (t, x₀) = (t + 5)⁻¹ := by
    rw [eqOn_sphericalAmplitude h1]
    simp only [radialAmplitude, hx₀, sub_add_cancel_left]
    rw [shellBump.one_of_mem_closedBall (mem_closedBall_self shellBump.rIn_pos.le), one_mul]
  have hG : Wave.gradNormSq sphericalPhase (t, x₀) = 2 := by
    rw [eqOn_gradNormSq isOpen_outer eqOn_sphericalPhase h1]
    exact gradNormSq_radialPhase (norm_pos_iff.mp (by linarith))
  have hpos : 0 < (sphericalAmplitude (t, x₀) ^ 2 + sphericalAmplitude (t, x₀) ^ 2) *
      Wave.gradNormSq sphericalPhase (t, x₀) := by
    rw [hA, hG]
    have : 0 < t + 5 := by linarith
    positivity
  have hc : Continuous fun p : ℝ × E3 =>
      (sphericalAmplitude p ^ 2 + sphericalAmplitude p ^ 2) * Wave.gradNormSq sphericalPhase p :=
    ((contDiff_sphericalAmplitude (n := 0)).continuous.fun_pow 2 |>.fun_add
      ((contDiff_sphericalAmplitude (n := 0)).continuous.fun_pow 2)).fun_mul
      (Wave.continuous_gradNormSq (contDiff_sphericalPhase (n := 1)))
  have hs : Wave.BallSupportOn t (t + 6) fun p : ℝ × E3 =>
      (sphericalAmplitude p ^ 2 + sphericalAmplitude p ^ 2) * Wave.gradNormSq sphericalPhase p :=
    ((((ballSupportOn_sphericalAmplitude t).pow two_ne_zero).add
      ((ballSupportOn_sphericalAmplitude t).pow two_ne_zero)).mul_right _)
  refine mul_pos (by norm_num) (Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (x := x₀) (hc.comp (continuous_const.prodMk continuous_id)) ?_
    (fun x => mul_nonneg (by positivity) (Wave.gradNormSq_nonneg _ _)) hpos.ne')
  exact HasCompactSupport.intro (isCompact_closedBall 0 (t + 6)) fun y hy =>
    hs t ⟨ht, le_rfl⟩ y (by rwa [mem_closedBall_zero_iff, not_le] at hy)

/-- **The spherical shell is an exact high-frequency wave**: for every `ε ≠ 0`,
`w = a cos((t − r)/ε) + a sin((t − r)/ε)` with `a = g(t − r)/r` solves `□w = 0` at the times
`t ≥ 0`. -/
theorem waveOperator_spherical {ε : ℝ} (hε : ε ≠ 0) {p : ℝ × E3} (hp : 0 ≤ p.1) :
    Wave.waveOperator
      (Wave.highFrequencyWave sphericalAmplitude sphericalAmplitude sphericalPhase ε) p = 0 := by
  rw [(isGeometricalOptics_spherical p.1).waveOperator_eq contDiff_sphericalAmplitude
    contDiff_sphericalAmplitude contDiff_sphericalPhase hε ⟨hp, le_rfl⟩,
    waveOperator_sphericalAmplitude hp]
  ring

/-- The partner of the spherical shell with the phase shifted by `επ/2` is exact too. -/
theorem waveOperator_spherical_shift {ε : ℝ} (hε : ε ≠ 0) {p : ℝ × E3} (hp : 0 ≤ p.1) :
    Wave.waveOperator (Wave.highFrequencyWave sphericalAmplitude
      (fun q => -sphericalAmplitude q) sphericalPhase ε) p = 0 := by
  rw [(isGeometricalOptics_spherical p.1).shift.waveOperator_eq contDiff_sphericalAmplitude
    contDiff_sphericalAmplitude.neg contDiff_sphericalPhase hε ⟨hp, le_rfl⟩,
    waveOperator_fun_neg', waveOperator_sphericalAmplitude hp]
  ring

/-- **An instance of the error estimate with a nonzero wave**: the spherical shell is exact, so
it is its own solution `u = w` with its Cauchy data. -/
theorem sqrt_energy_sub_le_spherical (T : ℝ) {ε : ℝ} (hε : ε ≠ 0) {t : ℝ} (ht : t ∈ Icc 0 T) :
    √(Wave.energy (fun p =>
        Wave.highFrequencyWave sphericalAmplitude sphericalAmplitude sphericalPhase ε p -
          Wave.highFrequencyWave sphericalAmplitude sphericalAmplitude sphericalPhase ε p) t) ≤
      ∫ s in 0..t, amplitudeSource sphericalAmplitude sphericalAmplitude s :=
  sqrt_energy_sub_le contDiff_sphericalAmplitude contDiff_sphericalAmplitude
    contDiff_sphericalPhase (isGeometricalOptics_spherical T) (ballSupportOn_sphericalAmplitude T)
    (ballSupportOn_sphericalAmplitude T)
    (contDiff_highFrequencyWave contDiff_sphericalAmplitude contDiff_sphericalAmplitude
      contDiff_sphericalPhase ε)
    (ballSupportOn_highFrequencyWave (ballSupportOn_sphericalAmplitude T)
      (ballSupportOn_sphericalAmplitude T) _ ε)
    (fun _ hp => waveOperator_spherical hε hp.1) hε (fun _ => rfl) (fun _ => rfl) ht

/-- **An instance of the relative error with a positive leading term**: the spherical shell and
its partner, with `u = w` and `u′ = w′`, satisfy the hypotheses of
`energy_sub_add_energy_sub_le` for every `ε ≠ 0`, since `M = 0` for equal amplitudes and `L > 0`. -/
theorem energy_sub_add_energy_sub_le_spherical {T : ℝ} (hT : 0 < T) {ε : ℝ} (hε : ε ≠ 0) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    Wave.energy (fun p =>
        Wave.highFrequencyWave sphericalAmplitude sphericalAmplitude sphericalPhase ε p -
          Wave.highFrequencyWave sphericalAmplitude sphericalAmplitude sphericalPhase ε p) t +
      Wave.energy (fun p =>
        Wave.highFrequencyWave sphericalAmplitude (fun q => -sphericalAmplitude q)
            sphericalPhase ε p -
          Wave.highFrequencyWave sphericalAmplitude (fun q => -sphericalAmplitude q)
            sphericalPhase ε p) t ≤
      ε ^ 2 * (4 * (∫ s in 0..t, amplitudeSource sphericalAmplitude sphericalAmplitude s) ^ 2 /
          leadingEnergy sphericalAmplitude sphericalAmplitude sphericalPhase t) *
        (Wave.energy (Wave.highFrequencyWave sphericalAmplitude sphericalAmplitude
            sphericalPhase ε) t +
          Wave.energy (Wave.highFrequencyWave sphericalAmplitude
            (fun q => -sphericalAmplitude q) sphericalPhase ε) t) := by
  have hnas : Wave.BallSupportOn T (T + 6) fun q => -sphericalAmplitude q := fun s hs y hy => by
    simp only [ballSupportOn_sphericalAmplitude T s hs y hy, neg_zero]
  refine energy_sub_add_energy_sub_le contDiff_sphericalAmplitude contDiff_sphericalAmplitude
    contDiff_sphericalPhase (isGeometricalOptics_spherical T) hT
    (ballSupportOn_sphericalAmplitude T) (ballSupportOn_sphericalAmplitude T)
    (contDiff_highFrequencyWave contDiff_sphericalAmplitude contDiff_sphericalAmplitude
      contDiff_sphericalPhase ε)
    (ballSupportOn_highFrequencyWave (ballSupportOn_sphericalAmplitude T)
      (ballSupportOn_sphericalAmplitude T) _ ε)
    (fun _ hp => waveOperator_spherical hε hp.1)
    (contDiff_highFrequencyWave contDiff_sphericalAmplitude contDiff_sphericalAmplitude.neg
      contDiff_sphericalPhase ε)
    (ballSupportOn_highFrequencyWave (ballSupportOn_sphericalAmplitude T) hnas _ ε)
    (fun _ hp => waveOperator_spherical_shift hε hp.1) hε (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) ht (leadingEnergy_spherical_pos ht.1) ?_
  rw [crossEnergy_self, abs_zero, mul_zero]
  exact div_nonneg (leadingEnergy_nonneg _ _ _ _) (by norm_num)

/-! ### The electromagnetic reading -/

/-- In the gauge of Lorenz, on an open set where the field satisfies the equations of Maxwell in
vacuum, each component `A_μ` of a `C²` potential, written in `(t, x)`, satisfies the scalar wave
equation `□A_μ = 0` (`maxwell_iff_box_of_lorenz` and `box = −□`). -/
theorem waveOperator_potentialComponent_eq_zero {U : Set Spacetime} (hU : IsOpen U)
    {A : Potential} (hA : ContDiff ℝ 2 A) (hL : ∀ y ∈ U, lorenzDivergence A y = 0)
    (hM : ∀ y ∈ U, (divergence3 (magneticField (fieldTensor A)) y = 0 ∧
        ∀ i, partialAt (magneticField (fieldTensor A) i) 0 y +
          curl (electricField (fieldTensor A)) y i = 0) ∧
      (divergence3 (electricField (fieldTensor A)) y = 0 ∧
        ∀ i, curl (magneticField (fieldTensor A)) y i -
          partialAt (electricField (fieldTensor A) i) 0 y = 0))
    (μ : Fin 4) {p : ℝ × E3} (hp : Wave.timeSpaceEquiv.symm p ∈ U) :
    Wave.waveOperator (fun q => potentialComponent A μ (Wave.timeSpaceEquiv.symm q)) p = 0 := by
  have hbox := (maxwell_iff_box_of_lorenz hU hA.contDiffOn hL 0).1 (by simpa using hM)
  have hc : ContDiff ℝ 2 fun q => potentialComponent A μ (Wave.timeSpaceEquiv.symm q) :=
    (contDiff_iff_contDiffAt.2 fun _ => contDiffAt_potentialComponent hA.contDiffAt μ).comp
      Wave.timeSpaceEquiv.symm.contDiff
  have hb : box (potentialComponent A μ) (Wave.timeSpaceEquiv.symm p) = 0 := by
    obtain ⟨h0, hi⟩ := hbox _ hp
    induction μ using Fin.cases with
    | zero => simpa using h0
    | succ i => simpa using hi i
  have hcomp := box_comp_timeSpaceEquiv hc (Wave.timeSpaceEquiv.symm p)
  simp only [ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.apply_symm_apply]
    at hcomp
  linarith

/-- **The error of geometrical optics for the electromagnetic potential**: in the gauge of
Lorenz, on a region containing `[0, T] × ℝ³` where the field is a vacuum solution of the
equations of Maxwell, each component `A_μ` of the potential with support in a ball is
approximated by a high-frequency wave `a cos(ψ/ε) + b sin(ψ/ε)` of geometrical optics with its
Cauchy data with an error of energy `√E(t) ≤ ∫₀ᵗ (∫ (□a)² + (□b)²)^{1/2} ds`, independent of
`ε`. -/
theorem sqrt_energy_potentialComponent_sub_le {U : Set Spacetime} (hU : IsOpen U)
    {A : Potential} (hA : ContDiff ℝ 2 A) (hL : ∀ y ∈ U, lorenzDivergence A y = 0)
    (hM : ∀ y ∈ U, (divergence3 (magneticField (fieldTensor A)) y = 0 ∧
        ∀ i, partialAt (magneticField (fieldTensor A) i) 0 y +
          curl (electricField (fieldTensor A)) y i = 0) ∧
      (divergence3 (electricField (fieldTensor A)) y = 0 ∧
        ∀ i, curl (magneticField (fieldTensor A)) y i -
          partialAt (electricField (fieldTensor A) i) 0 y = 0))
    {T R : ℝ} (hTU : ∀ p : ℝ × E3, p.1 ∈ Icc 0 T → Wave.timeSpaceEquiv.symm p ∈ U) (μ : Fin 4)
    (hAs : Wave.BallSupportOn T R fun q => potentialComponent A μ (Wave.timeSpaceEquiv.symm q))
    {a b ψ : ℝ × E3 → ℝ} (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b) (hψ : ContDiff ℝ 2 ψ)
    (h : IsGeometricalOptics T a b ψ) (has : Wave.BallSupportOn T R a)
    (hbs : Wave.BallSupportOn T R b) {ε : ℝ} (hε : ε ≠ 0)
    (h0 : ∀ x, potentialComponent A μ (Wave.timeSpaceEquiv.symm (0, x)) =
      Wave.highFrequencyWave a b ψ ε (0, x))
    (h1 : ∀ x, Wave.timeDeriv (fun q => potentialComponent A μ (Wave.timeSpaceEquiv.symm q))
      (0, x) = Wave.timeDeriv (Wave.highFrequencyWave a b ψ ε) (0, x))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    √(Wave.energy (fun q => potentialComponent A μ (Wave.timeSpaceEquiv.symm q) -
        Wave.highFrequencyWave a b ψ ε q) t) ≤ ∫ s in 0..t, amplitudeSource a b s :=
  sqrt_energy_sub_le ha hb hψ h has hbs
    ((contDiff_iff_contDiffAt.2 fun _ => contDiffAt_potentialComponent hA.contDiffAt μ).comp
      Wave.timeSpaceEquiv.symm.contDiff) hAs
    (fun p hp => waveOperator_potentialComponent_eq_zero hU hA hL hM μ (hTU p hp)) hε h0 h1 ht

end ProjectAinos.Electrodynamics.Optics.Limits
