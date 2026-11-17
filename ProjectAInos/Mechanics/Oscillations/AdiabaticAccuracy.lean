/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Oscillations.AdiabaticExponential

/-!
# The accuracy of the conservation of the adiabatic invariant

Landau–Lifshitz §51 for the oscillator `ẍ + ω² x = 0` whose frequency is
`ω = exp q(ε θ)`, `θ̇ = ω`, with `q′ = 2g` and `g` holomorphic near the strip
`0 ≤ Im z ≤ σ` of the slow phase (`IsStripProfile`, `IsSlowOscillator`).

* `IsSlowOscillator.tendsto_phase_atTop`, `tendsto_phase_atBot`: the phase
  tends to `±∞` with the time.
* `IsSlowOscillator.exists_tendsto_action`: the action
  `I = (v² + ω² x²)/2ω` has limits `I₀` as `t → −∞` and `I₁` as `t → +∞`.
* `abs_action_limit_sub_le`: the total change of the adiabatic invariant is
  exponentially small,
  `|I₁ − I₀| ≤ e^{G} (4 e^{G} + 2) e^{−2σ/ε} I₀`,
  for every `ε > 0` and every solution.
-/

@[expose] public section
noncomputable section

open Set Filter
open scoped Topology ComplexConjugate

namespace ProjectAInos.Mechanics.AdiabaticAmplitude

open Complex (I)
open SmoothGeometry.LinearODE
open AdiabaticOscillator (action)

variable {g : ℂ → ℂ} {σ G : ℝ} {m : ℝ → ℝ} {U : Set ℂ} {q : ℝ → ℝ} {ε : ℝ}
  {ω θ x v : ℝ → ℝ}

/-! ### The integral of the bound -/

/-- The integral of the bound from zero. -/
def boundIntegral (m : ℝ → ℝ) (s : ℝ) : ℝ := ∫ r in (0 : ℝ)..s, m r

theorem IsStripProfile.hasDerivAt_boundIntegral (hp : IsStripProfile g σ m G U) (s : ℝ) :
    HasDerivAt (boundIntegral m) (m s) s :=
  (hp.continuous.integral_hasStrictDerivAt 0 s).hasDerivAt

theorem IsStripProfile.abs_boundIntegral_le (hp : IsStripProfile g σ m G U) (s : ℝ) :
    |boundIntegral m s| ≤ G := by
  rcases le_total 0 s with hs | hs
  · have h0 : 0 ≤ boundIntegral m s :=
      intervalIntegral.integral_nonneg hs fun r _ => hp.nonneg r
    rw [abs_of_nonneg h0]
    exact hp.integral_le 0 s hs
  · have h0 : 0 ≤ ∫ r in s..(0 : ℝ), m r :=
      intervalIntegral.integral_nonneg hs fun r _ => hp.nonneg r
    have e : boundIntegral m s = -∫ r in s..(0 : ℝ), m r := intervalIntegral.integral_symm _ _
    rw [e, abs_neg, abs_of_nonneg h0]
    exact hp.integral_le s 0 hs

theorem IsStripProfile.abs_re_le (hp : IsStripProfile g σ m G U) (s : ℝ) :
    |(g s).re| ≤ m s :=
  (Complex.abs_re_le_norm _).trans (hp.norm_ofReal_le s)

/-- The logarithm of the frequency is bounded. -/
theorem IsStripProfile.abs_log_sub_le (hp : IsStripProfile g σ m G U)
    (hq : ∀ s : ℝ, HasDerivAt q (2 * (g s).re) s) (s : ℝ) : |q s - q 0| ≤ 2 * G := by
  have hd1 : ∀ s : ℝ, HasDerivAt (fun s => q s + 2 * boundIntegral m s)
      (2 * (g s).re + 2 * m s) s := fun s =>
    (hq s).add ((hp.hasDerivAt_boundIntegral s).const_mul 2)
  have hd2 : ∀ s : ℝ, HasDerivAt (fun s => q s - 2 * boundIntegral m s)
      (2 * (g s).re - 2 * m s) s := fun s =>
    (hq s).sub ((hp.hasDerivAt_boundIntegral s).const_mul 2)
  have hup : Monotone fun s => q s + 2 * boundIntegral m s := by
    refine monotone_of_deriv_nonneg (fun s => (hd1 s).differentiableAt) fun s => ?_
    rw [(hd1 s).deriv]
    have h := (abs_le.mp (hp.abs_re_le s)).1
    linarith
  have hdown : Antitone fun s => q s - 2 * boundIntegral m s := by
    refine antitone_of_deriv_nonpos (fun s => (hd2 s).differentiableAt) fun s => ?_
    rw [(hd2 s).deriv]
    have h := (abs_le.mp (hp.abs_re_le s)).2
    linarith
  have h0 : boundIntegral m 0 = 0 := intervalIntegral.integral_same
  have hb := abs_le.mp (hp.abs_boundIntegral_le s)
  rcases le_total 0 s with hs | hs
  · have h1 := hup hs
    have h2 := hdown hs
    simp only [h0, mul_zero, add_zero, sub_zero] at h1 h2
    exact abs_le.mpr ⟨by linarith [hb.2], by linarith [hb.2]⟩
  · have h1 := hup hs
    have h2 := hdown hs
    simp only [h0, mul_zero, add_zero, sub_zero] at h1 h2
    exact abs_le.mpr ⟨by linarith [hb.1], by linarith [hb.1]⟩

theorem IsStripProfile.log_ge (hp : IsStripProfile g σ m G U)
    (hq : ∀ s : ℝ, HasDerivAt q (2 * (g s).re) s) (s : ℝ) : q 0 - 2 * G ≤ q s := by
  have h := (abs_le.mp (hp.abs_log_sub_le hq s)).1
  linarith

theorem IsStripProfile.log_le (hp : IsStripProfile g σ m G U)
    (hq : ∀ s : ℝ, HasDerivAt q (2 * (g s).re) s) (s : ℝ) : q s ≤ q 0 + 2 * G := by
  have h := (abs_le.mp (hp.abs_log_sub_le hq s)).2
  linarith

/-! ### The phase -/

theorem IsSlowOscillator.frequency_ge (ho : IsSlowOscillator g q ε ω θ x v)
    (hp : IsStripProfile g σ m G U) (t : ℝ) : Real.exp (q 0 - 2 * G) ≤ ω t := by
  rw [ho.frequency t]
  exact Real.exp_le_exp.mpr (hp.log_ge ho.hasDerivAt_log _)

theorem IsSlowOscillator.monotone_phase (ho : IsSlowOscillator g q ε ω θ x v) : Monotone θ :=
  monotone_of_deriv_nonneg (fun t => (ho.hasDerivAt_phase t).differentiableAt) fun t => by
    rw [(ho.hasDerivAt_phase t).deriv]
    exact (ho.frequency_pos t).le

theorem IsSlowOscillator.monotone_phase_sub (ho : IsSlowOscillator g q ε ω θ x v)
    (hp : IsStripProfile g σ m G U) :
    Monotone fun t => θ t - Real.exp (q 0 - 2 * G) * t := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t => θ t - Real.exp (q 0 - 2 * G) * t)
      (ω t - Real.exp (q 0 - 2 * G) * 1) t := fun t =>
    (ho.hasDerivAt_phase t).sub ((hasDerivAt_id t).const_mul _)
  refine monotone_of_deriv_nonneg (fun t => (hd t).differentiableAt) fun t => ?_
  rw [(hd t).deriv, mul_one]
  exact sub_nonneg.mpr (ho.frequency_ge hp t)

/-- The phase tends to `+∞` with the time. -/
theorem IsSlowOscillator.tendsto_phase_atTop (ho : IsSlowOscillator g q ε ω θ x v)
    (hp : IsStripProfile g σ m G U) : Tendsto θ atTop atTop := by
  have hlin : Tendsto (fun t : ℝ => θ 0 + Real.exp (q 0 - 2 * G) * t) atTop atTop :=
    tendsto_atTop_add_const_left atTop (θ 0) (tendsto_id.const_mul_atTop (Real.exp_pos _))
  refine tendsto_atTop_mono' atTop ?_ hlin
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  have h := ho.monotone_phase_sub hp ht
  simp only [mul_zero, sub_zero] at h
  linarith

/-- The phase tends to `−∞` with the time. -/
theorem IsSlowOscillator.tendsto_phase_atBot (ho : IsSlowOscillator g q ε ω θ x v)
    (hp : IsStripProfile g σ m G U) : Tendsto θ atBot atBot := by
  have hlin : Tendsto (fun t : ℝ => θ 0 + Real.exp (q 0 - 2 * G) * t) atBot atBot :=
    tendsto_atBot_add_const_left atBot (θ 0) (tendsto_id.const_mul_atBot (Real.exp_pos _))
  refine tendsto_atBot_mono' atBot ?_ hlin
  filter_upwards [eventually_le_atBot (0 : ℝ)] with t ht
  have h := ho.monotone_phase_sub hp ht
  simp only [mul_zero, sub_zero] at h
  linarith

/-! ### The limits of the action -/

/-- A nonnegative function `N` with `|N′| ≤ 2 W′ N`, where `W` is bounded and
`W′ ≥ 0`, has limits at both ends: `N e^{2W}` is monotone and bounded. -/
theorem exists_tendsto_of_abs_deriv_le {N W N' W' : ℝ → ℝ} {G : ℝ}
    (hN : ∀ t, HasDerivAt N (N' t) t) (hW : ∀ t, HasDerivAt W (W' t) t) (hN0 : ∀ t, 0 ≤ N t)
    (hW0 : ∀ t, 0 ≤ W' t) (hbound : ∀ t, |N' t| ≤ 2 * W' t * N t) (hG : ∀ t, |W t| ≤ G) :
    ∃ L₀ L₁ : ℝ, Tendsto N atBot (𝓝 L₀) ∧ Tendsto N atTop (𝓝 L₁) := by
  have hP : ∀ t, HasDerivAt (fun t => N t * Real.exp (2 * W t))
      (N' t * Real.exp (2 * W t) + N t * (Real.exp (2 * W t) * (2 * W' t))) t := fun t =>
    (hN t).mul (((hW t).const_mul 2).exp)
  have hQ : ∀ t, HasDerivAt (fun t => N t * Real.exp (-(2 * W t)))
      (N' t * Real.exp (-(2 * W t)) + N t * (Real.exp (-(2 * W t)) * -(2 * W' t))) t :=
    fun t => (hN t).mul ((((hW t).const_mul 2).neg).exp)
  have hPmono : Monotone fun t => N t * Real.exp (2 * W t) := by
    refine monotone_of_deriv_nonneg (fun t => (hP t).differentiableAt) fun t => ?_
    rw [(hP t).deriv]
    have h1 := (abs_le.mp (hbound t)).1
    have h2 := Real.exp_pos (2 * W t)
    have e : N' t * Real.exp (2 * W t) + N t * (Real.exp (2 * W t) * (2 * W' t)) =
        (N' t + 2 * W' t * N t) * Real.exp (2 * W t) := by ring
    rw [e]
    exact mul_nonneg (by linarith) h2.le
  have hQanti : Antitone fun t => N t * Real.exp (-(2 * W t)) := by
    refine antitone_of_deriv_nonpos (fun t => (hQ t).differentiableAt) fun t => ?_
    rw [(hQ t).deriv]
    have h1 := (abs_le.mp (hbound t)).2
    have h2 := Real.exp_pos (-(2 * W t))
    have e : N' t * Real.exp (-(2 * W t)) + N t * (Real.exp (-(2 * W t)) * -(2 * W' t)) =
        -((2 * W' t * N t - N' t) * Real.exp (-(2 * W t))) := by ring
    rw [e]
    exact neg_nonpos.mpr (mul_nonneg (by linarith) h2.le)
  have hWmono : Monotone W :=
    monotone_of_deriv_nonneg (fun t => (hW t).differentiableAt) fun t => by
      rw [(hW t).deriv]
      exact hW0 t
  have hGW : ∀ t, -G ≤ W t ∧ W t ≤ G := fun t => abs_le.mp (hG t)
  have hNle : ∀ t, N t ≤ N 0 * Real.exp (4 * G) := by
    intro t
    rcases le_total 0 t with ht | ht
    · have h : N t * Real.exp (-(2 * W t)) ≤ N 0 * Real.exp (-(2 * W 0)) := hQanti ht
      have e1 : N t = N t * Real.exp (-(2 * W t)) * Real.exp (2 * W t) := by
        rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
      rw [e1]
      calc N t * Real.exp (-(2 * W t)) * Real.exp (2 * W t)
          ≤ N 0 * Real.exp (-(2 * W 0)) * Real.exp (2 * W t) :=
            mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
        _ = N 0 * Real.exp (2 * W t - 2 * W 0) := by
            rw [mul_assoc, ← Real.exp_add]
            congr 2
            ring
        _ ≤ N 0 * Real.exp (4 * G) :=
            mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.mpr (by linarith [(hGW t).2, (hGW 0).1])) (hN0 0)
    · have h : N t * Real.exp (2 * W t) ≤ N 0 * Real.exp (2 * W 0) := hPmono ht
      have e1 : N t = N t * Real.exp (2 * W t) * Real.exp (-(2 * W t)) := by
        rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
      rw [e1]
      calc N t * Real.exp (2 * W t) * Real.exp (-(2 * W t))
          ≤ N 0 * Real.exp (2 * W 0) * Real.exp (-(2 * W t)) :=
            mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
        _ = N 0 * Real.exp (2 * W 0 - 2 * W t) := by
            rw [mul_assoc, ← Real.exp_add, ← sub_eq_add_neg]
        _ ≤ N 0 * Real.exp (4 * G) :=
            mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.mpr (by linarith [(hGW t).1, (hGW 0).2])) (hN0 0)
  have hPabove : BddAbove (range fun t => N t * Real.exp (2 * W t)) :=
    ⟨N 0 * Real.exp (4 * G) * Real.exp (2 * G), by
      rintro _ ⟨t, rfl⟩
      exact mul_le_mul (hNle t) (Real.exp_le_exp.mpr (by linarith [(hGW t).2]))
        (Real.exp_pos _).le (mul_nonneg (hN0 0) (Real.exp_pos _).le)⟩
  have hPbelow : BddBelow (range fun t => N t * Real.exp (2 * W t)) :=
    ⟨0, by
      rintro _ ⟨t, rfl⟩
      exact mul_nonneg (hN0 t) (Real.exp_pos _).le⟩
  have hWabove : BddAbove (range W) := ⟨G, by
    rintro _ ⟨t, rfl⟩
    exact (hGW t).2⟩
  have hWbelow : BddBelow (range W) := ⟨-G, by
    rintro _ ⟨t, rfl⟩
    exact (hGW t).1⟩
  have hNeq : ∀ t, N t * Real.exp (2 * W t) * Real.exp (-2 * W t) = N t := fun t => by
    rw [mul_assoc, ← Real.exp_add, show 2 * W t + -2 * W t = 0 by ring, Real.exp_zero, mul_one]
  refine ⟨(⨅ t, N t * Real.exp (2 * W t)) * Real.exp (-2 * ⨅ t, W t),
    (⨆ t, N t * Real.exp (2 * W t)) * Real.exp (-2 * ⨆ t, W t), ?_, ?_⟩
  · exact ((tendsto_atBot_ciInf hPmono hPbelow).mul ((Real.continuous_exp.tendsto _).comp
      ((tendsto_atBot_ciInf hWmono hWbelow).const_mul (-2)))).congr hNeq
  · exact ((tendsto_atTop_ciSup hPmono hPabove).mul ((Real.continuous_exp.tendsto _).comp
      ((tendsto_atTop_ciSup hWmono hWabove).const_mul (-2)))).congr hNeq

/-- The derivative of the square of the modulus of a complex function. -/
theorem hasDerivAt_normSq {B : ℝ → ℂ} {B' : ℂ} {t : ℝ} (h : HasDerivAt B B' t) :
    HasDerivAt (fun t => Complex.normSq (B t)) (2 * (conj (B t) * B').re) t := by
  have h1 : HasDerivAt (fun t => B t * star (B t)) (B' * star (B t) + B t * star B') t :=
    h.mul h.star
  have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h1
  have e : (fun t => Complex.normSq (B t)) = Complex.reCLM ∘ fun t => B t * star (B t) := by
    funext t
    change Complex.normSq (B t) = (B t * conj (B t)).re
    rw [Complex.mul_conj, Complex.ofReal_re]
  rw [e]
  refine h2.congr_deriv ?_
  change (B' * conj (B t) + B t * conj B').re = _
  simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The action has limits as the time tends to `−∞` and to `+∞`. -/
theorem IsSlowOscillator.exists_tendsto_action (ho : IsSlowOscillator g q ε ω θ x v)
    (hp : IsStripProfile g σ m G U) :
    ∃ I₀ I₁ : ℝ, Tendsto (fun t => action (ω t) (x t) (v t)) atBot (𝓝 I₀) ∧
      Tendsto (fun t => action (ω t) (x t) (v t)) atTop (𝓝 I₁) := by
  -- the equation of the amplitude
  have hB : ∀ t : ℝ, HasDerivAt (amplitude q ε ω θ x v)
      ((ε * ω t) • (coeffPlus g ε ((ε * θ t : ℝ) : ℂ) * conj (amplitude q ε ω θ x v t))) t :=
    fun t => by
      have h1 : HasDerivAt (fun t => (amplitudePair q ε ω θ x v t).1)
          (((ε * ω t) • hp.realCurve ε (ε * θ t) (amplitudePair q ε ω θ x v t)).1) t :=
        (hasFDerivAt_fst (𝕜 := ℝ) (p := amplitudePair q ε ω θ x v t)).comp_hasDerivAt t
          (hasDerivAt_amplitudePair hp ho t)
      rw [Prod.smul_fst, hp.realCurve_apply] at h1
      exact h1
  have hN : ∀ t : ℝ, HasDerivAt (fun t => Complex.normSq (amplitude q ε ω θ x v t))
      (2 * (conj (amplitude q ε ω θ x v t) * ((ε * ω t) •
        (coeffPlus g ε ((ε * θ t : ℝ) : ℂ) * conj (amplitude q ε ω θ x v t)))).re) t :=
    fun t => hasDerivAt_normSq (hB t)
  have hW : ∀ t : ℝ, HasDerivAt (fun t => boundIntegral m (ε * θ t))
      (m (ε * θ t) * (ε * ω t)) t := fun t =>
    HasDerivAt.comp t (h₂ := boundIntegral m) (h := fun t => ε * θ t)
      (hp.hasDerivAt_boundIntegral (ε * θ t)) ((ho.hasDerivAt_phase t).const_mul ε)
  have hκ : ∀ t : ℝ, 0 ≤ ε * ω t := fun t => mul_nonneg ho.pos.le (ho.frequency_pos t).le
  obtain ⟨L₀, L₁, hL₀, hL₁⟩ := exists_tendsto_of_abs_deriv_le hN hW
    (fun t => Complex.normSq_nonneg _) (fun t => mul_nonneg (hp.nonneg _) (hκ t))
    (fun t => by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul, norm_smul, Real.norm_of_nonneg (hκ t), norm_mul, RCLike.norm_conj,
        IsStripProfile.norm_coeffPlus_ofReal, Complex.normSq_eq_norm_sq]
      have h1 := hp.norm_ofReal_le (ε * θ t)
      have h2 := norm_nonneg (amplitude q ε ω θ x v t)
      have h3 : ‖amplitude q ε ω θ x v t‖ * (ε * ω t * (‖g ((ε * θ t : ℝ) : ℂ)‖ *
          ‖amplitude q ε ω θ x v t‖)) =
          ‖g ((ε * θ t : ℝ) : ℂ)‖ * (ε * ω t) * ‖amplitude q ε ω θ x v t‖ ^ 2 := by ring
      rw [h3]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (hκ t)) (sq_nonneg _))
    (fun t => hp.abs_boundIntegral_le _)
  have e : (fun t => action (ω t) (x t) (v t)) =
      fun t => Complex.normSq (amplitude q ε ω θ x v t) / 2 := funext fun t => by
    rw [ho.normSq_amplitude]
    ring
  rw [e]
  exact ⟨L₀ / 2, L₁ / 2, hL₀.div_const 2, hL₁.div_const 2⟩

/-! ### The total change of the adiabatic invariant -/

/-- Landau–Lifshitz §51: the total change of the adiabatic invariant of an
oscillator, whose frequency is a function of the slow phase that is
holomorphic on a strip of the width `σ`, is at most of the order
`e^{−2σ/ε}`. -/
theorem abs_action_limit_sub_le (hp : IsStripProfile g σ m G U)
    (ho : IsSlowOscillator g q ε ω θ x v) {I₀ I₁ : ℝ}
    (h₀ : Tendsto (fun t => action (ω t) (x t) (v t)) atBot (𝓝 I₀))
    (h₁ : Tendsto (fun t => action (ω t) (x t) (v t)) atTop (𝓝 I₁)) :
    |I₁ - I₀| ≤ Real.exp G * (4 * Real.exp G + 2) * Real.exp (-(2 * σ / ε)) * I₀ := by
  obtain ⟨C, -, hC⟩ := hp.exists_norm_fst_realCurve_le
  have hε := ho.pos
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = Real.exp (2 / ε * σ) := ⟨_, rfl⟩
  have hE1 : 1 ≤ E := by
    rw [hEdef]
    exact Real.one_le_exp (mul_nonneg (div_nonneg zero_le_two hε.le) hp.pos.le)
  have hE : 0 < E := lt_of_lt_of_le one_pos hE1
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = Real.exp G * E⁻¹ := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = C * (Real.exp (E * G) * E) := ⟨_, rfl⟩
  -- the estimate between two times
  have hfin : ∀ t₀ t₁ : ℝ, t₀ ≤ t₁ →
      |action (ω t₁) (x t₁) (v t₁) - action (ω t₀) (x t₀) (v t₀)| ≤
        action (ω t₀) (x t₀) (v t₀) * ((κ + D * (m (ε * θ t₁) + m (ε * θ t₀))) *
          (4 * (κ + D * (m (ε * θ t₁) + m (ε * θ t₀))) + 2)) := by
    intro t₀ t₁ ht
    have hs : ε * θ t₀ ≤ ε * θ t₁ := mul_le_mul_of_nonneg_left (ho.monotone_phase ht) hε.le
    have hβ := hC ε hε (ε * θ t₀) (ε * θ t₁) hs
    rw [← hEdef] at hβ
    have hβ' : ‖(propagator (hp.realCurve ε) (ε * θ t₁) (ε * θ t₀) (0, 1)).1‖ ≤
        κ + D * (m (ε * θ t₁) + m (ε * θ t₀)) := by
      rw [hκdef, hDdef]
      refine hβ.trans (le_of_eq ?_)
      ring
    have hI0 : 0 ≤ action (ω t₀) (x t₀) (v t₀) :=
      AdiabaticOscillator.action_nonneg (ho.frequency_pos t₀) _ _
    have hβ0 := norm_nonneg (propagator (hp.realCurve ε) (ε * θ t₁) (ε * θ t₀) (0, 1)).1
    exact (abs_action_sub_le hp ho t₀ t₁).trans (mul_le_mul_of_nonneg_left
      (mul_le_mul hβ' (by linarith) (by linarith) (hβ0.trans hβ')) hI0)
  have hmtop : Tendsto (fun t => m (ε * θ t)) atTop (𝓝 0) :=
    hp.tendsto_atTop.comp ((ho.tendsto_phase_atTop hp).const_mul_atTop hε)
  have hmbot : Tendsto (fun t => m (ε * θ t)) atBot (𝓝 0) :=
    hp.tendsto_atBot.comp ((ho.tendsto_phase_atBot hp).const_mul_atBot hε)
  -- the later time tends to infinity
  have hstep : ∀ t₀ : ℝ, |I₁ - action (ω t₀) (x t₀) (v t₀)| ≤
      action (ω t₀) (x t₀) (v t₀) * ((κ + D * (0 + m (ε * θ t₀))) *
        (4 * (κ + D * (0 + m (ε * θ t₀))) + 2)) := by
    intro t₀
    have hb : Tendsto (fun t₁ => κ + D * (m (ε * θ t₁) + m (ε * θ t₀))) atTop
        (𝓝 (κ + D * (0 + m (ε * θ t₀)))) :=
      tendsto_const_nhds.add ((hmtop.add tendsto_const_nhds).const_mul D)
    have hR : Tendsto (fun t₁ => action (ω t₀) (x t₀) (v t₀) *
        ((κ + D * (m (ε * θ t₁) + m (ε * θ t₀))) *
          (4 * (κ + D * (m (ε * θ t₁) + m (ε * θ t₀))) + 2))) atTop
        (𝓝 (action (ω t₀) (x t₀) (v t₀) * ((κ + D * (0 + m (ε * θ t₀))) *
          (4 * (κ + D * (0 + m (ε * θ t₀))) + 2)))) :=
      (hb.mul ((hb.const_mul 4).add_const 2)).const_mul _
    have hL : Tendsto (fun t₁ => |action (ω t₁) (x t₁) (v t₁) - action (ω t₀) (x t₀) (v t₀)|)
        atTop (𝓝 |I₁ - action (ω t₀) (x t₀) (v t₀)|) := (h₁.sub_const _).abs
    exact le_of_tendsto_of_tendsto hL hR
      ((eventually_ge_atTop t₀).mono fun t₁ ht => hfin t₀ t₁ ht)
  -- the earlier time tends to minus infinity
  have hb : Tendsto (fun t₀ => κ + D * (0 + m (ε * θ t₀))) atBot (𝓝 (κ + D * (0 + 0))) :=
    tendsto_const_nhds.add ((tendsto_const_nhds.add hmbot).const_mul D)
  have hR : Tendsto (fun t₀ => action (ω t₀) (x t₀) (v t₀) *
      ((κ + D * (0 + m (ε * θ t₀))) * (4 * (κ + D * (0 + m (ε * θ t₀))) + 2))) atBot
      (𝓝 (I₀ * ((κ + D * (0 + 0)) * (4 * (κ + D * (0 + 0)) + 2)))) :=
    h₀.mul (hb.mul ((hb.const_mul 4).add_const 2))
  have hL : Tendsto (fun t₀ => |I₁ - action (ω t₀) (x t₀) (v t₀)|) atBot (𝓝 |I₁ - I₀|) :=
    (h₀.const_sub I₁).abs
  have hfinal := le_of_tendsto_of_tendsto' hL hR hstep
  have hI0 : 0 ≤ I₀ := ge_of_tendsto' h₀ fun t =>
    AdiabaticOscillator.action_nonneg (ho.frequency_pos t) _ _
  have hinv : E⁻¹ = Real.exp (-(2 * σ / ε)) := by
    rw [hEdef, ← Real.exp_neg]
    congr 1
    ring
  have hinv1 : E⁻¹ ≤ 1 := (inv_le_one₀ hE).mpr hE1
  have hinv0 : 0 < E⁻¹ := inv_pos.mpr hE
  have hG0 := Real.exp_pos G
  have hκ : (κ + D * (0 + 0)) * (4 * (κ + D * (0 + 0)) + 2) ≤
      Real.exp G * (4 * Real.exp G + 2) * E⁻¹ := by
    rw [hκdef]
    simp only [add_zero, mul_zero]
    nlinarith [mul_nonneg (mul_pos (mul_pos hG0 hG0) hinv0).le (sub_nonneg.mpr hinv1)]
  rw [← hinv]
  calc |I₁ - I₀| ≤ I₀ * ((κ + D * (0 + 0)) * (4 * (κ + D * (0 + 0)) + 2)) := hfinal
    _ ≤ I₀ * (Real.exp G * (4 * Real.exp G + 2) * E⁻¹) := mul_le_mul_of_nonneg_left hκ hI0
    _ = Real.exp G * (4 * Real.exp G + 2) * E⁻¹ * I₀ := by ring

/-- The limits of the action exist and their difference is exponentially
small. -/
theorem exists_tendsto_action_and_abs_sub_le (hp : IsStripProfile g σ m G U)
    (ho : IsSlowOscillator g q ε ω θ x v) :
    ∃ I₀ I₁ : ℝ, Tendsto (fun t => action (ω t) (x t) (v t)) atBot (𝓝 I₀) ∧
      Tendsto (fun t => action (ω t) (x t) (v t)) atTop (𝓝 I₁) ∧
      |I₁ - I₀| ≤ Real.exp G * (4 * Real.exp G + 2) * Real.exp (-(2 * σ / ε)) * I₀ := by
  obtain ⟨I₀, I₁, h₀, h₁⟩ := ho.exists_tendsto_action hp
  exact ⟨I₀, I₁, h₀, h₁, abs_action_limit_sub_le hp ho h₀ h₁⟩

end ProjectAInos.Mechanics.AdiabaticAmplitude
