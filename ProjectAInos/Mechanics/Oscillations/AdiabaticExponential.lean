/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Oscillations.AmplitudeReal
public import ProjectAInos.Mechanics.Oscillations.AdiabaticOscillator
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# The amplitude of an oscillator whose frequency depends on the slow phase

`IsStripProfile g σ m G U`: `g` is holomorphic on an open set `U` that contains
the strip `0 ≤ Im z ≤ σ`, real on the real axis, and bounded on the strip by
`m (Re z)`, where the integrals of `m` are at most `G` and `m` tends to zero
at both ends.

`IsSlowOscillator g q ε ω θ x v`: `x`, `v` solve `ẍ + ω² x = 0`, `θ` is the phase,
`θ̇ = ω`, and the frequency is `ω = exp q(ε θ)` with `q′ = 2g` on the real
axis: the logarithm of the frequency is a function of the slow phase `ε θ`.

* `amplitude`: `B = (ω x + i v) e^{iθ} e^{−q/2}`, with `|B|² = 2 I` for the action
  `I = (v² + ω² x²)/2ω` (`normSq_amplitude`).
* `hasDerivAt_amplitudePair`: `(B, B̄)` solves the amplitude system in the
  slow phase, and so it is given by its propagator
  (`amplitudePair_eq_propagator`).
* `abs_action_sub_le`: the change of the action between two times is bounded
  through the entry `β` of the propagator, `|I₁ − I₀| ≤ I₀ |β| (4|β| + 2)`.
-/

@[expose] public section
noncomputable section

open Set Filter
open scoped Topology ComplexConjugate

namespace ProjectAInos.Mechanics.AdiabaticAmplitude

open Complex (I)
open SmoothGeometry.LinearODE
open AdiabaticOscillator (action)

/-- The half of the logarithmic derivative of the frequency, as a function of
the slow phase: holomorphic near the strip `0 ≤ Im z ≤ σ`, real on the real
axis, and bounded on the strip by `m`, whose integrals are at most `G`. -/
structure IsStripProfile (g : ℂ → ℂ) (σ : ℝ) (m : ℝ → ℝ) (G : ℝ) (U : Set ℂ) : Prop where
  pos : 0 < σ
  isOpen : IsOpen U
  mem : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ σ → z ∈ U
  differentiableOn : DifferentiableOn ℂ g U
  real : ∀ s : ℝ, (g s).im = 0
  bound : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ σ → ‖g z‖ ≤ m z.re
  continuous : Continuous m
  integral_le : ∀ s₀ s₁ : ℝ, s₀ ≤ s₁ → ∫ r in s₀..s₁, m r ≤ G
  tendsto_atTop : Tendsto m atTop (𝓝 0)
  tendsto_atBot : Tendsto m atBot (𝓝 0)

namespace IsStripProfile

variable {g : ℂ → ℂ} {σ G : ℝ} {m : ℝ → ℝ} {U : Set ℂ}

theorem path_mem (h : IsStripProfile g σ m G U) (q : ℝ × ℝ) : path σ q ∈ U :=
  h.mem _ (path_im_nonneg h.pos.le q) (path_im_le h.pos.le q)

theorem norm_path_le (h : IsStripProfile g σ m G U) (q : ℝ × ℝ) : ‖g (path σ q)‖ ≤ m q.2 := by
  have h1 := h.bound (path σ q) (path_im_nonneg h.pos.le q) (path_im_le h.pos.le q)
  rwa [path_re] at h1

theorem ofReal_mem (h : IsStripProfile g σ m G U) (s : ℝ) : (s : ℂ) ∈ U :=
  h.mem _ (by simp) (by simpa using h.pos.le)

theorem norm_ofReal_le (h : IsStripProfile g σ m G U) (s : ℝ) : ‖g s‖ ≤ m s := by
  have h1 := h.bound (s : ℂ) (by simp) (by simpa using h.pos.le)
  simpa using h1

theorem nonneg (h : IsStripProfile g σ m G U) (s : ℝ) : 0 ≤ m s :=
  (norm_nonneg _).trans (h.norm_ofReal_le s)

theorem eq_ofReal_re (h : IsStripProfile g σ m G U) (s : ℝ) : g s = (((g s).re : ℝ) : ℂ) :=
  Complex.ext (by simp) (by simp [h.real s])

theorem conj_eq (h : IsStripProfile g σ m G U) (s : ℝ) : conj (g s) = g s :=
  Complex.conj_eq_iff_im.mpr (h.real s)

theorem continuous_coeffPlus (h : IsStripProfile g σ m G U) (ε : ℝ) :
    Continuous fun s : ℝ => coeffPlus g ε (s : ℂ) :=
  (differentiableOn_coeffPlus h.differentiableOn ε).continuousOn.comp_continuous
    Complex.continuous_ofReal h.ofReal_mem

theorem coeffMinus_ofReal (h : IsStripProfile g σ m G U) (ε s : ℝ) :
    coeffMinus g ε (s : ℂ) = conj (coeffPlus g ε (s : ℂ)) := by
  rw [coeffMinus, coeffPlus, map_mul, h.conj_eq, ← Complex.exp_conj, map_mul, map_mul,
    Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I, neg_mul, mul_neg]

theorem norm_coeffPlus_ofReal (g : ℂ → ℂ) (ε s : ℝ) : ‖coeffPlus g ε (s : ℂ)‖ = ‖g s‖ := by
  rw [norm_coeffPlus, Complex.ofReal_im, mul_zero, neg_zero, Real.exp_zero, mul_one]

/-- The coefficient of the amplitude system on the real line. -/
def realCurve (h : IsStripProfile g σ m G U) (ε : ℝ) : C(ℝ, ℂ × ℂ →L[ℝ] ℂ × ℂ) :=
  offDiagCurve (fun s : ℝ => coeffPlus g ε (s : ℂ))
    (fun s : ℝ => conj (coeffPlus g ε (s : ℂ))) (h.continuous_coeffPlus ε)
    (Complex.continuous_conj.comp (h.continuous_coeffPlus ε))

theorem realCurve_apply (h : IsStripProfile g σ m G U) (ε s : ℝ) (y : ℂ × ℂ) :
    h.realCurve ε s y =
      (coeffPlus g ε (s : ℂ) * y.2, conj (coeffPlus g ε (s : ℂ)) * y.1) := rfl

theorem coefficientCurve_zero (h : IsStripProfile g σ m G U) (ε : ℝ)
    (hc : Continuous (family g ε σ)) :
    coefficientCurve (family g ε σ) hc 0 = h.realCurve ε := by
  refine ContinuousMap.ext fun s => ?_
  change coeff g ε (path σ (0, s)) =
    offDiag (coeffPlus g ε (s : ℂ)) (conj (coeffPlus g ε (s : ℂ)))
  rw [path_zero, coeff, h.coeffMinus_ofReal]

/-- The entry of the propagator on the real line from the second unknown to
the first. -/
theorem exists_norm_fst_realCurve_le (h : IsStripProfile g σ m G U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ) (_ : 0 < ε) (s₀ s₁ : ℝ), s₀ ≤ s₁ →
      ‖(propagator (h.realCurve ε) s₁ s₀ (0, 1)).1‖ ≤
        Real.exp G * (Real.exp (2 / ε * σ))⁻¹ +
          C * (Real.exp (Real.exp (2 / ε * σ) * G) *
            (Real.exp (2 / ε * σ) * (m s₁ + m s₀))) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_fst_propagator_le h.isOpen h.differentiableOn h.pos.le
    h.path_mem
  refine ⟨C, hC0, fun ε hε s₀ s₁ hs => ?_⟩
  have h1 := hC ε hε m h.continuous h.norm_path_le G h.integral_le s₀ s₁ hs
  rwa [h.coefficientCurve_zero] at h1

end IsStripProfile

/-- An oscillator whose frequency is `exp q(ε θ)`, with the phase `θ` and
`q′ = 2g` on the real axis. -/
structure IsSlowOscillator (g : ℂ → ℂ) (q : ℝ → ℝ) (ε : ℝ) (ω θ x v : ℝ → ℝ) : Prop where
  pos : 0 < ε
  hasDerivAt_log : ∀ s : ℝ, HasDerivAt q (2 * (g s).re) s
  frequency : ∀ t : ℝ, ω t = Real.exp (q (ε * θ t))
  hasDerivAt_phase : ∀ t : ℝ, HasDerivAt θ (ω t) t
  hasDerivAt_position : ∀ t : ℝ, HasDerivAt x (v t) t
  hasDerivAt_velocity : ∀ t : ℝ, HasDerivAt v (-(ω t) ^ 2 * x t) t

/-- The complex amplitude `(ω x + i v) e^{iθ} e^{−q/2}`. -/
def amplitude (q : ℝ → ℝ) (ε : ℝ) (ω θ x v : ℝ → ℝ) (t : ℝ) : ℂ :=
  (((ω t * x t : ℝ) : ℂ) + ((v t : ℝ) : ℂ) * I) * Complex.exp (((θ t : ℝ) : ℂ) * I) *
    ((Real.exp (-(q (ε * θ t) / 2)) : ℝ) : ℂ)

/-- The amplitude and its conjugate. -/
def amplitudePair (q : ℝ → ℝ) (ε : ℝ) (ω θ x v : ℝ → ℝ) (t : ℝ) : ℂ × ℂ :=
  (amplitude q ε ω θ x v t, conj (amplitude q ε ω θ x v t))

section Oscillator

variable {g : ℂ → ℂ} {q : ℝ → ℝ} {ε : ℝ} {ω θ x v : ℝ → ℝ}

theorem IsSlowOscillator.frequency_pos (ho : IsSlowOscillator g q ε ω θ x v) (t : ℝ) :
    0 < ω t := by
  rw [ho.frequency t]
  exact Real.exp_pos _

/-- The square of the modulus of the amplitude is twice the action. -/
theorem IsSlowOscillator.normSq_amplitude (ho : IsSlowOscillator g q ε ω θ x v) (t : ℝ) :
    Complex.normSq (amplitude q ε ω θ x v t) = 2 * action (ω t) (x t) (v t) := by
  have he : Real.exp (-(q (ε * θ t) / 2)) * Real.exp (-(q (ε * θ t) / 2)) =
      (Real.exp (q (ε * θ t)))⁻¹ := by
    rw [← Real.exp_add, ← Real.exp_neg]
    congr 1
    ring
  rw [amplitude, map_mul, map_mul, Complex.normSq_add_mul_I,
    Complex.normSq_eq_norm_sq (Complex.exp _), Complex.norm_exp_ofReal_mul_I,
    Complex.normSq_ofReal, he, action, ho.frequency t]
  field_simp
  ring

theorem IsSlowOscillator.hasDerivAt_frequency (ho : IsSlowOscillator g q ε ω θ x v) (t : ℝ) :
    HasDerivAt ω (2 * (g (ε * θ t : ℝ)).re * (ε * ω t) * ω t) t := by
  have h1 : HasDerivAt (fun t => ε * θ t) (ε * ω t) t := (ho.hasDerivAt_phase t).const_mul ε
  have h2 : HasDerivAt (fun t => q (ε * θ t)) (2 * (g (ε * θ t : ℝ)).re * (ε * ω t)) t :=
    (ho.hasDerivAt_log (ε * θ t)).comp t h1
  have h3 := h2.exp
  have e : (fun t => Real.exp (q (ε * θ t))) = ω := funext fun t => (ho.frequency t).symm
  rw [e] at h3
  refine h3.congr_deriv ?_
  rw [← ho.frequency t]
  ring

/-- The equation of the amplitude in the time. -/
theorem IsSlowOscillator.hasDerivAt_amplitude (ho : IsSlowOscillator g q ε ω θ x v) (t : ℝ) :
    HasDerivAt (amplitude q ε ω θ x v)
      (((ε * ω t * (g (ε * θ t : ℝ)).re : ℝ) : ℂ) *
        ((((ω t * x t : ℝ) : ℂ) - ((v t : ℝ) : ℂ) * I) * Complex.exp (((θ t : ℝ) : ℂ) * I) *
          ((Real.exp (-(q (ε * θ t) / 2)) : ℝ) : ℂ))) t := by
  have hω := ho.hasDerivAt_frequency t
  have hP : HasDerivAt (fun t => ((ω t * x t : ℝ) : ℂ) + ((v t : ℝ) : ℂ) * I)
      (((2 * (g (ε * θ t : ℝ)).re * (ε * ω t) * ω t * x t + ω t * v t : ℝ) : ℂ) +
        ((-(ω t) ^ 2 * x t : ℝ) : ℂ) * I) t :=
    ((hω.mul (ho.hasDerivAt_position t)).ofReal_comp).add
      ((ho.hasDerivAt_velocity t).ofReal_comp.mul_const I)
  have hE : HasDerivAt (fun t => Complex.exp (((θ t : ℝ) : ℂ) * I))
      (Complex.exp (((θ t : ℝ) : ℂ) * I) * (((ω t : ℝ) : ℂ) * I)) t :=
    (((ho.hasDerivAt_phase t).ofReal_comp).mul_const I).cexp
  have hR : HasDerivAt (fun t => ((Real.exp (-(q (ε * θ t) / 2)) : ℝ) : ℂ))
      ((Real.exp (-(q (ε * θ t) / 2)) * -(2 * (g (ε * θ t : ℝ)).re * (ε * ω t) / 2) : ℝ) : ℂ)
      t := by
    have h1 : HasDerivAt (fun t => ε * θ t) (ε * ω t) t :=
      (ho.hasDerivAt_phase t).const_mul ε
    have h2 : HasDerivAt (fun t => q (ε * θ t)) (2 * (g (ε * θ t : ℝ)).re * (ε * ω t)) t :=
      (ho.hasDerivAt_log (ε * θ t)).comp t h1
    exact ((h2.div_const 2).neg.exp).ofReal_comp
  have h := (hP.mul hE).mul hR
  obtain ⟨E, hEdef⟩ : ∃ E : ℂ, E = Complex.exp (((θ t : ℝ) : ℂ) * I) := ⟨_, rfl⟩
  obtain ⟨R, hRdef⟩ : ∃ R : ℂ, R = ((Real.exp (-(q (ε * θ t) / 2)) : ℝ) : ℂ) := ⟨_, rfl⟩
  have hI := Complex.I_sq
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_neg,
    Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_ofNat]
  rw [← hEdef, ← hRdef]
  linear_combination (((v t : ℝ) : ℂ) * ((ω t : ℝ) : ℂ) * E * R) * hI

/-- The right-hand side of the equation of the amplitude, through the
coefficient of the amplitude system. -/
theorem coeffPlus_mul_conj_amplitude {σ G : ℝ} {m : ℝ → ℝ} {U : Set ℂ}
    (hp : IsStripProfile g σ m G U) (ho : IsSlowOscillator g q ε ω θ x v) (t : ℝ) :
    coeffPlus g ε ((ε * θ t : ℝ) : ℂ) * conj (amplitude q ε ω θ x v t) =
      (((g (ε * θ t : ℝ)).re : ℝ) : ℂ) *
        ((((ω t * x t : ℝ) : ℂ) - ((v t : ℝ) : ℂ) * I) * Complex.exp (((θ t : ℝ) : ℂ) * I) *
          ((Real.exp (-(q (ε * θ t) / 2)) : ℝ) : ℂ)) := by
  have hε : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ho.pos.ne'
  have h1 : Complex.exp (((2 / ε : ℝ) : ℂ) * (I * ((ε * θ t : ℝ) : ℂ))) =
      Complex.exp (((θ t : ℝ) : ℂ) * I) * Complex.exp (((θ t : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  have h2 : conj (Complex.exp (((θ t : ℝ) : ℂ) * I)) =
      (Complex.exp (((θ t : ℝ) : ℂ) * I))⁻¹ := by
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg,
      Complex.exp_neg]
  have hne : Complex.exp (((θ t : ℝ) : ℂ) * I) ≠ 0 := Complex.exp_ne_zero _
  rw [coeffPlus, amplitude]
  conv_lhs => rw [hp.eq_ofReal_re, h1]
  simp only [map_mul, map_add, Complex.conj_ofReal, Complex.conj_I, h2]
  field_simp
  ring

/-- The pair of the amplitude and its conjugate solves the amplitude system in
the slow phase. -/
theorem hasDerivAt_amplitudePair {σ G : ℝ} {m : ℝ → ℝ} {U : Set ℂ}
    (hp : IsStripProfile g σ m G U) (ho : IsSlowOscillator g q ε ω θ x v) (t : ℝ) :
    HasDerivAt (amplitudePair q ε ω θ x v)
      ((ε * ω t) • hp.realCurve ε (ε * θ t) (amplitudePair q ε ω θ x v t)) t := by
  have hB : HasDerivAt (amplitude q ε ω θ x v)
      (((ε * ω t : ℝ) : ℂ) *
        (coeffPlus g ε ((ε * θ t : ℝ) : ℂ) * conj (amplitude q ε ω θ x v t))) t := by
    refine (ho.hasDerivAt_amplitude t).congr_deriv ?_
    rw [coeffPlus_mul_conj_amplitude hp ho t]
    push_cast
    ring
  have hpair : HasDerivAt
      (fun t => (amplitude q ε ω θ x v t, star (amplitude q ε ω θ x v t)))
      (((ε * ω t : ℝ) : ℂ) *
          (coeffPlus g ε ((ε * θ t : ℝ) : ℂ) * conj (amplitude q ε ω θ x v t)),
        star (((ε * ω t : ℝ) : ℂ) *
          (coeffPlus g ε ((ε * θ t : ℝ) : ℂ) * conj (amplitude q ε ω θ x v t)))) t :=
    HasDerivAt.prodMk hB hB.star
  refine hpair.congr_deriv ?_
  rw [hp.realCurve_apply, Prod.smul_mk, Complex.real_smul, Complex.real_smul, Prod.mk.injEq]
  refine ⟨rfl, ?_⟩
  simp only [amplitudePair, Complex.star_def, map_mul, Complex.conj_ofReal, Complex.conj_conj]

theorem IsSlowOscillator.continuous_phase (ho : IsSlowOscillator g q ε ω θ x v) :
    Continuous θ :=
  continuous_iff_continuousAt.mpr fun t => (ho.hasDerivAt_phase t).continuousAt

theorem IsSlowOscillator.continuous_frequency (ho : IsSlowOscillator g q ε ω θ x v) :
    Continuous ω :=
  continuous_iff_continuousAt.mpr fun t => (ho.hasDerivAt_frequency t).continuousAt

/-- The amplitude at two times, through the propagator of the amplitude system
between the slow phases. -/
theorem amplitudePair_eq_propagator {σ G : ℝ} {m : ℝ → ℝ} {U : Set ℂ}
    (hp : IsStripProfile g σ m G U) (ho : IsSlowOscillator g q ε ω θ x v) (t₀ t : ℝ) :
    amplitudePair q ε ω θ x v t =
      propagator (hp.realCurve ε) (ε * θ t) (ε * θ t₀) (amplitudePair q ε ω θ x v t₀) := by
  obtain ⟨Ct, hCt⟩ : ∃ Ct : C(ℝ, ℂ × ℂ →L[ℝ] ℂ × ℂ),
      ∀ r : ℝ, Ct r = (ε * ω r) • hp.realCurve ε (ε * θ r) :=
    ⟨⟨fun r => (ε * ω r) • hp.realCurve ε (ε * θ r),
      (continuous_const.mul ho.continuous_frequency).smul
        ((hp.realCurve ε).continuous.comp (continuous_const.mul ho.continuous_phase))⟩,
      fun _ => rfl⟩
  have hY : ∀ r : ℝ, HasDerivAt (amplitudePair q ε ω θ x v)
      (Ct r (amplitudePair q ε ω θ x v r)) r := fun r => by
    rw [hCt]
    exact hasDerivAt_amplitudePair hp ho r
  have hZ : ∀ r : ℝ, HasDerivAt
      (fun r => propagator (hp.realCurve ε) (ε * θ r) (ε * θ t₀)
        (amplitudePair q ε ω θ x v t₀))
      (Ct r (propagator (hp.realCurve ε) (ε * θ r) (ε * θ t₀)
        (amplitudePair q ε ω θ x v t₀))) r := fun r => by
    rw [hCt]
    exact HasDerivAt.scomp r
      (g₁ := fun s => propagator (hp.realCurve ε) s (ε * θ t₀) (amplitudePair q ε ω θ x v t₀))
      (h := fun r => ε * θ r)
      (hasDerivAt_propagator_apply (hp.realCurve ε) (ε * θ r) (ε * θ t₀) _)
      ((ho.hasDerivAt_phase r).const_mul ε)
  have h1 := eq_propagator_apply_of_hasDerivAt Ct (f := amplitudePair q ε ω θ x v) (s := t₀)
    (t := t) (continuous_iff_continuousAt.mpr fun r => (hY r).continuousAt).continuousOn
    (fun r _ => hY r)
  have h2 := eq_propagator_apply_of_hasDerivAt Ct
    (f := fun r => propagator (hp.realCurve ε) (ε * θ r) (ε * θ t₀)
      (amplitudePair q ε ω θ x v t₀)) (s := t₀) (t := t)
    (continuous_iff_continuousAt.mpr fun r => (hZ r).continuousAt).continuousOn
    (fun r _ => hZ r)
  rw [propagator_self] at h2
  exact h1.trans h2.symm

/-- The change of the action between two times, through one entry of the
propagator of the amplitude system. -/
theorem abs_action_sub_le {σ G : ℝ} {m : ℝ → ℝ} {U : Set ℂ} (hp : IsStripProfile g σ m G U)
    (ho : IsSlowOscillator g q ε ω θ x v) (t₀ t₁ : ℝ) :
    |action (ω t₁) (x t₁) (v t₁) - action (ω t₀) (x t₀) (v t₀)| ≤
      action (ω t₀) (x t₀) (v t₀) *
        (‖(propagator (hp.realCurve ε) (ε * θ t₁) (ε * θ t₀) (0, 1)).1‖ *
          (4 * ‖(propagator (hp.realCurve ε) (ε * θ t₁) (ε * θ t₀) (0, 1)).1‖ + 2)) := by
  have h1 : |Complex.normSq (propagator (hp.realCurve ε) (ε * θ t₁) (ε * θ t₀)
        (amplitude q ε ω θ x v t₀, conj (amplitude q ε ω θ x v t₀))).1 -
      Complex.normSq (amplitude q ε ω θ x v t₀)| ≤
      Complex.normSq (amplitude q ε ω θ x v t₀) *
        (‖(propagator (hp.realCurve ε) (ε * θ t₁) (ε * θ t₀) (0, 1)).1‖ *
          (4 * ‖(propagator (hp.realCurve ε) (ε * θ t₁) (ε * θ t₀) (0, 1)).1‖ + 2)) :=
    abs_normSq_fst_propagator_sub_le (hp.continuous_coeffPlus ε)
      (Complex.continuous_conj.comp (hp.continuous_coeffPlus ε)) (ε * θ t₁) (ε * θ t₀)
      (amplitude q ε ω θ x v t₀)
  have h2 : (propagator (hp.realCurve ε) (ε * θ t₁) (ε * θ t₀)
      (amplitude q ε ω θ x v t₀, conj (amplitude q ε ω θ x v t₀))).1 =
      amplitude q ε ω θ x v t₁ :=
    (congrArg Prod.fst (amplitudePair_eq_propagator hp ho t₀ t₁)).symm
  rw [h2, ho.normSq_amplitude, ho.normSq_amplitude] at h1
  have h3 : |2 * action (ω t₁) (x t₁) (v t₁) - 2 * action (ω t₀) (x t₀) (v t₀)| =
      2 * |action (ω t₁) (x t₁) (v t₁) - action (ω t₀) (x t₀) (v t₀)| := by
    rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [h3] at h1
  linarith

end Oscillator

end ProjectAInos.Mechanics.AdiabaticAmplitude
