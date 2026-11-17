/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Mechanics.Oscillations.AdiabaticAccuracy
public import ProjectAinos.SmoothGeometry.ODE.FlowComplete
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Oscillators that satisfy the hypotheses of the estimate of §51

* `IsStripProfile.exists_isSlowOscillator`: for every profile `g`, every `q` with
  `q′ = 2g` on the real axis, every `ε > 0` and all initial values there is an
  oscillator with the frequency `exp q(ε θ)`. The phase is the solution of
  `θ̇ = exp q(ε θ)`, which exists for all times because the right-hand side is
  bounded, and `(x, v)` is given by the propagator of the linear system.
* `lorentzProfile a z = a z / (1 + z²)²`, with `q(s) = −a/(1 + s²)`
  (`lorentzLog`): holomorphic for `|Im z| < 1`, and a profile on every strip
  `0 ≤ Im z ≤ σ` with `σ < 1` (`isStripProfile_lorentz`). The poles `±i` limit
  the width of the strip, and with it the exponent `2σ/ε`.
* `exists_lorentz_oscillator`: the conclusion of the estimate for this
  profile.
-/

@[expose] public section
noncomputable section

open Set Filter
open scoped Topology Real

namespace ProjectAinos.Mechanics.AdiabaticAmplitude

open Complex (I)
open SmoothGeometry.LinearODE SmoothGeometry.NonlinearODE
open AdiabaticOscillator (action)

variable {g : ℂ → ℂ} {σ G : ℝ} {m : ℝ → ℝ} {U : Set ℂ} {q : ℝ → ℝ}

/-- The logarithm of the frequency is smooth. -/
theorem IsStripProfile.contDiff_log (hp : IsStripProfile g σ m G U)
    (hq : ∀ s : ℝ, HasDerivAt q (2 * (g s).re) s) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) q := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun s => (hq s).differentiableAt, ?_⟩
  have e : deriv q = fun s : ℝ => 2 * (g s).re := funext fun s => (hq s).deriv
  rw [e]
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun s : ℝ => g s :=
    ((hp.differentiableOn.contDiffOn hp.isOpen).restrict_scalars ℝ).comp_contDiff
      Complex.ofRealCLM.contDiff hp.ofReal_mem
  exact contDiff_const.mul (Complex.reCLM.contDiff.comp h1)

/-- The phase: the solution of `θ̇ = exp q(ε θ)` with `θ(0) = 0`. -/
theorem IsStripProfile.exists_phase (hp : IsStripProfile g σ m G U)
    (hq : ∀ s : ℝ, HasDerivAt q (2 * (g s).re) s) (ε : ℝ) :
    ∃ θ : ℝ → ℝ, θ 0 = 0 ∧ ∀ t, HasDerivAt θ (Real.exp (q (ε * θ t))) t := by
  have hX : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun y : ℝ => Real.exp (q (ε * y)) :=
    Real.contDiff_exp.comp ((hp.contDiff_log hq).comp (contDiff_const.mul contDiff_id))
  have hbound : ∀ y : ℝ, ‖Real.exp (q (ε * y))‖ ≤ Real.exp (q 0 + 2 * G) + 0 * ‖y‖ :=
    fun y => by
      rw [zero_mul, add_zero, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr (hp.log_le hq _)
  have hdom := flowDomain_eq_univ_of_norm_le hX hbound
  refine ⟨fun t => flow (fun y : ℝ => Real.exp (q (ε * y))) (t, 0), flow_zero _ _, fun t => ?_⟩
  exact hasDerivAt_flow hX (by
    rw [hdom]
    exact mem_univ _)

/-- For every profile there are oscillators with all initial values. -/
theorem IsStripProfile.exists_isSlowOscillator (hp : IsStripProfile g σ m G U)
    (hq : ∀ s : ℝ, HasDerivAt q (2 * (g s).re) s) {ε : ℝ} (hε : 0 < ε) (x₀ v₀ : ℝ) :
    ∃ ω θ x v : ℝ → ℝ, IsSlowOscillator g q ε ω θ x v ∧ x 0 = x₀ ∧ v 0 = v₀ := by
  obtain ⟨θ, -, hθ⟩ := hp.exists_phase hq ε
  obtain ⟨ω, hω⟩ : ∃ ω : ℝ → ℝ, ω = fun t => Real.exp (q (ε * θ t)) := ⟨_, rfl⟩
  have hθc : Continuous θ := continuous_iff_continuousAt.mpr fun t => (hθ t).continuousAt
  have hqc : Continuous q := continuous_iff_continuousAt.mpr fun s => (hq s).continuousAt
  have hωc : Continuous ω := by
    rw [hω]
    exact Real.continuous_exp.comp (hqc.comp (continuous_const.mul hθc))
  obtain ⟨A, hA⟩ : ∃ A : C(ℝ, ℝ × ℝ →L[ℝ] ℝ × ℝ),
      ∀ (t : ℝ) (y : ℝ × ℝ), A t y = (y.2, -(ω t) ^ 2 * y.1) := by
    refine ⟨⟨fun t => (ContinuousLinearMap.snd ℝ ℝ ℝ).prod
      ((-(ω t) ^ 2) • ContinuousLinearMap.fst ℝ ℝ ℝ), ?_⟩, fun t y => rfl⟩
    rw [continuous_clm_apply]
    intro y
    exact continuous_const.prodMk ((hωc.pow 2).neg.smul continuous_const)
  have hY : ∀ t : ℝ, HasDerivAt (fun t => propagator A t 0 (x₀, v₀))
      ((propagator A t 0 (x₀, v₀)).2, -(ω t) ^ 2 * (propagator A t 0 (x₀, v₀)).1) t :=
    fun t => by
      have h := hasDerivAt_propagator_apply A t 0 (x₀, v₀)
      rwa [hA] at h
  refine ⟨ω, θ, fun t => (propagator A t 0 (x₀, v₀)).1, fun t => (propagator A t 0 (x₀, v₀)).2,
    ⟨hε, hq, fun t => by rw [hω], fun t => ?_, fun t => ?_, fun t => ?_⟩, ?_, ?_⟩
  · rw [hω]
    exact hθ t
  · exact (hasFDerivAt_fst (𝕜 := ℝ) (p := propagator A t 0 (x₀, v₀))).comp_hasDerivAt t (hY t)
  · exact (hasFDerivAt_snd (𝕜 := ℝ) (p := propagator A t 0 (x₀, v₀))).comp_hasDerivAt t (hY t)
  · change (propagator A 0 0 (x₀, v₀)).1 = x₀
    rw [propagator_self]
    rfl
  · change (propagator A 0 0 (x₀, v₀)).2 = v₀
    rw [propagator_self]
    rfl

/-! ### A frequency with poles at the distance one from the real axis -/

/-- The profile `a z / (1 + z²)²`. -/
def lorentzProfile (a : ℝ) (z : ℂ) : ℂ := (a : ℂ) * z / (1 + z ^ 2) ^ 2

/-- The logarithm of the frequency, `−a / (1 + s²)`. -/
def lorentzLog (a s : ℝ) : ℝ := -a / (1 + s ^ 2)

theorem lorentzProfile_ofReal (a s : ℝ) :
    lorentzProfile a (s : ℂ) = ((a * s / (1 + s ^ 2) ^ 2 : ℝ) : ℂ) := by
  rw [lorentzProfile]
  push_cast
  rfl

theorem hasDerivAt_lorentzLog (a s : ℝ) :
    HasDerivAt (lorentzLog a) (2 * (lorentzProfile a (s : ℂ)).re) s := by
  have hne : 1 + s ^ 2 ≠ 0 := by positivity
  have h : HasDerivAt (fun s : ℝ => -a / (1 + s ^ 2))
      ((0 * (1 + s ^ 2) - -a * (2 * s)) / (1 + s ^ 2) ^ 2) s := by
    have hd : HasDerivAt (fun s : ℝ => 1 + s ^ 2) (2 * s) s := by
      have h1 := ((hasDerivAt_id s).pow 2).const_add 1
      simpa using h1
    exact (hasDerivAt_const s (-a)).div hd hne
  refine h.congr_deriv ?_
  rw [lorentzProfile_ofReal, Complex.ofReal_re]
  field_simp
  ring

theorem one_add_sq_re_pos {z : ℂ} (hz : |z.im| < 1) : 0 < (1 + z ^ 2).re := by
  have h1 : (1 + z ^ 2).re = 1 + z.re ^ 2 - z.im ^ 2 := by
    simp [pow_two, Complex.mul_re]
    ring
  have h2 : z.im ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one _).mpr hz
  rw [h1]
  nlinarith [sq_nonneg z.re]

/-- The profile of the Lorentzian frequency on a strip below the pole. -/
theorem isStripProfile_lorentz (a : ℝ) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    IsStripProfile (lorentzProfile a) σ
      (fun s => 2 * |a| / (1 - σ ^ 2) ^ 2 * (1 + s ^ 2)⁻¹) (2 * |a| / (1 - σ ^ 2) ^ 2 * π)
      {z : ℂ | |z.im| < 1} := by
  have h1σ : 0 < 1 - σ ^ 2 := by nlinarith
  have hc : 0 ≤ 2 * |a| / (1 - σ ^ 2) ^ 2 := by positivity
  refine
    { pos := hσ0
      isOpen := isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
      mem := fun z h0 h1 => show |z.im| < 1 from abs_lt.mpr ⟨by linarith, by linarith⟩
      differentiableOn := ?_
      real := fun s => by rw [lorentzProfile_ofReal, Complex.ofReal_im]
      bound := ?_
      continuous := ?_
      integral_le := ?_
      tendsto_atTop := ?_
      tendsto_atBot := ?_ }
  · refine DifferentiableOn.div ((differentiableOn_const (a : ℂ)).mul differentiableOn_id)
      (((differentiableOn_const (1 : ℂ)).add (differentiableOn_id.pow 2)).pow 2) fun z hz => ?_
    refine pow_ne_zero 2 fun h0 => ?_
    have h1 := one_add_sq_re_pos hz
    rw [h0] at h1
    simp at h1
  · intro z h0 hσ
    have hz : |z.im| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
    have hx : 0 < 1 + z.re ^ 2 := by positivity
    have hre : (1 + z ^ 2).re = 1 + z.re ^ 2 - z.im ^ 2 := by
      simp [pow_two, Complex.mul_re]
      ring
    have him2 : z.im ^ 2 ≤ σ ^ 2 := pow_le_pow_left₀ h0 hσ 2
    have hn : (1 - σ ^ 2) * (1 + z.re ^ 2) ≤ ‖1 + z ^ 2‖ := by
      refine le_trans ?_ (Complex.re_le_norm _)
      rw [hre]
      nlinarith [sq_nonneg z.re, mul_nonneg (sq_nonneg σ) (sq_nonneg z.re)]
    have hcpos : 0 < (1 - σ ^ 2) * (1 + z.re ^ 2) := mul_pos h1σ hx
    have hnpos : 0 < ‖1 + z ^ 2‖ := lt_of_lt_of_le hcpos hn
    have hn2 : ((1 - σ ^ 2) * (1 + z.re ^ 2)) ^ 2 ≤ ‖1 + z ^ 2‖ ^ 2 :=
      pow_le_pow_left₀ hcpos.le hn 2
    have hzn : ‖z‖ ≤ 2 * (1 + z.re ^ 2) := by
      refine (Complex.norm_le_abs_re_add_abs_im z).trans ?_
      have h1 : |z.re| ≤ 1 + z.re ^ 2 := by
        nlinarith [sq_nonneg (|z.re| - 1), sq_abs z.re, abs_nonneg z.re]
      have h2 : |z.im| ≤ 1 + z.re ^ 2 := by nlinarith [sq_nonneg z.re]
      linarith
    rw [lorentzProfile, norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      div_le_iff₀ (pow_pos hnpos 2)]
    calc |a| * ‖z‖ ≤ |a| * (2 * (1 + z.re ^ 2)) :=
          mul_le_mul_of_nonneg_left hzn (abs_nonneg a)
      _ = 2 * |a| / (1 - σ ^ 2) ^ 2 * (1 + z.re ^ 2)⁻¹ *
            ((1 - σ ^ 2) * (1 + z.re ^ 2)) ^ 2 := by
          field_simp
      _ ≤ 2 * |a| / (1 - σ ^ 2) ^ 2 * (1 + z.re ^ 2)⁻¹ * ‖1 + z ^ 2‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hn2 (by positivity)
  · exact continuous_const.mul ((continuous_const.add (continuous_id.pow 2)).inv₀
      fun s => (by positivity : (0 : ℝ) < 1 + s ^ 2).ne')
  · intro s₀ s₁ _
    rw [intervalIntegral.integral_const_mul, integral_inv_one_add_sq]
    refine mul_le_mul_of_nonneg_left ?_ hc
    linarith [Real.arctan_lt_pi_div_two s₁, Real.neg_pi_div_two_lt_arctan s₀]
  · have h : Tendsto (fun s : ℝ => 1 + s ^ 2) atTop atTop :=
      tendsto_atTop_add_const_left atTop 1 (tendsto_pow_atTop two_ne_zero)
    have h2 := (tendsto_inv_atTop_zero.comp h).const_mul (2 * |a| / (1 - σ ^ 2) ^ 2)
    rw [mul_zero] at h2
    exact h2
  · have h : Tendsto (fun s : ℝ => 1 + s ^ 2) atBot atTop := by
      have h1 := tendsto_atTop_add_const_left atBot (1 : ℝ)
        ((tendsto_pow_atTop (α := ℝ) two_ne_zero).comp tendsto_abs_atBot_atTop)
      simpa [sq_abs] using h1
    have h2 := (tendsto_inv_atTop_zero.comp h).const_mul (2 * |a| / (1 - σ ^ 2) ^ 2)
    rw [mul_zero] at h2
    exact h2

/-- An oscillator whose frequency is `exp (−a/(1 + s²))` in the slow phase
`s = ε θ`: the action has limits at both ends, and their difference is at most
of the order `e^{−2σ/ε}` for every `σ < 1`. An instance of all the hypotheses
of `exists_tendsto_action_and_abs_sub_le`. -/
theorem exists_lorentz_oscillator (a : ℝ) {σ ε : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hε : 0 < ε)
    (x₀ v₀ : ℝ) :
    ∃ ω θ x v : ℝ → ℝ, IsSlowOscillator (lorentzProfile a) (lorentzLog a) ε ω θ x v ∧
      x 0 = x₀ ∧ v 0 = v₀ ∧
      ∃ I₀ I₁ : ℝ, Tendsto (fun t => action (ω t) (x t) (v t)) atBot (𝓝 I₀) ∧
        Tendsto (fun t => action (ω t) (x t) (v t)) atTop (𝓝 I₁) ∧
        |I₁ - I₀| ≤ Real.exp (2 * |a| / (1 - σ ^ 2) ^ 2 * π) *
          (4 * Real.exp (2 * |a| / (1 - σ ^ 2) ^ 2 * π) + 2) * Real.exp (-(2 * σ / ε)) * I₀ := by
  have hp := isStripProfile_lorentz a hσ0 hσ1
  obtain ⟨ω, θ, x, v, ho, hx, hv⟩ :=
    hp.exists_isSlowOscillator (hasDerivAt_lorentzLog a) hε x₀ v₀
  exact ⟨ω, θ, x, v, ho, hx, hv, exists_tendsto_action_and_abs_sub_le hp ho⟩

end ProjectAinos.Mechanics.AdiabaticAmplitude
