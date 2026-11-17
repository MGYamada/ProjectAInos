/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.ODE.Averaging
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The adiabatic theorem for the oscillator

Landau–Lifshitz §49 for `ẍ + ω(t)² x = 0` with a slowly varying frequency
`ω(t) = Ω(εt)`. The action variable is `I = (ẋ² + ω² x²)/2ω`
(`action`). With `a = Ω′/2Ω²` the corrected action
`I + ε a(εt) x ẋ` has the derivative `ε² a′(εt) x ẋ`
(`hasDerivAt_correctedAction`), and `|x ẋ| ≤ I`. Hence there is a constant `C`,
which depends on `Ω` and `T` only, with

`|I(t) − I(0)| ≤ C ε I(0)` for `0 ≤ t ≤ T/ε`

for every `ε > 0` and every motion (`exists_forall_abs_action_sub_le`).
-/

@[expose] public section
noncomputable section

open Set

namespace ProjectAinos.Mechanics.AdiabaticOscillator

/-- The action variable `I = (v² + ω² x²)/2ω` of the oscillator. -/
def action (ω x v : ℝ) : ℝ := (v ^ 2 + ω ^ 2 * x ^ 2) / (2 * ω)

theorem action_nonneg {ω : ℝ} (hω : 0 < ω) (x v : ℝ) : 0 ≤ action ω x v := by
  unfold action
  positivity

/-- `|x v| ≤ I`. -/
theorem abs_mul_le_action {ω : ℝ} (hω : 0 < ω) (x v : ℝ) : |x * v| ≤ action ω x v := by
  rw [action, le_div_iff₀ (by positivity), abs_mul]
  nlinarith [sq_nonneg (|v| - ω * |x|), sq_abs v, sq_abs x, abs_nonneg x, abs_nonneg v]

/-- `|ω² x² − v²| ≤ 2ω I`. -/
theorem abs_sub_le_action {ω : ℝ} (hω : 0 < ω) (x v : ℝ) :
    |ω ^ 2 * x ^ 2 - v ^ 2| ≤ 2 * ω * action ω x v := by
  have h : 2 * ω * action ω x v = v ^ 2 + ω ^ 2 * x ^ 2 := by
    rw [action]
    field_simp
  rw [h, abs_le]
  constructor <;> nlinarith [sq_nonneg v, sq_nonneg (ω * x)]

theorem contDiff_deriv {Ω : ℝ → ℝ} (hΩ : ContDiff ℝ 2 Ω) : ContDiff ℝ 1 (deriv Ω) := by
  have h2 : ContDiff ℝ (1 + 1) Ω := by
    rw [one_add_one_eq_two]
    exact hΩ
  exact h2.deriv'

/-- The coefficient `a = Ω′/2Ω²` of the correction of the action. -/
def coefficient (Ω : ℝ → ℝ) (τ : ℝ) : ℝ := deriv Ω τ / (2 * Ω τ ^ 2)

/-- The derivative of the coefficient. -/
def coefficientDeriv (Ω : ℝ → ℝ) (τ : ℝ) : ℝ :=
  (deriv (deriv Ω) τ * (2 * Ω τ ^ 2) - deriv Ω τ * (4 * Ω τ * deriv Ω τ)) / (2 * Ω τ ^ 2) ^ 2

theorem hasDerivAt_coefficient {Ω : ℝ → ℝ} (hΩ : ContDiff ℝ 2 Ω) {τ : ℝ} (hτ : Ω τ ≠ 0) :
    HasDerivAt (coefficient Ω) (coefficientDeriv Ω τ) τ := by
  have h1 : HasDerivAt Ω (deriv Ω τ) τ := (hΩ.differentiable (by norm_num) τ).hasDerivAt
  have h2 : HasDerivAt (deriv Ω) (deriv (deriv Ω) τ) τ :=
    ((contDiff_deriv hΩ).differentiable one_ne_zero τ).hasDerivAt
  have h3 : HasDerivAt (fun τ => 2 * Ω τ ^ 2) (4 * Ω τ * deriv Ω τ) τ := by
    refine ((h1.pow 2).const_mul 2).congr_deriv ?_
    ring
  exact h2.div h3 (by positivity)

section Motion

variable {Ω x v : ℝ → ℝ} {ε L : ℝ}

/-- The derivative of the action along a motion:
`İ = (ω̇/2ω²)(ω² x² − ẋ²)` with `ω = Ω(εt)`. -/
theorem hasDerivAt_action (hΩ : ContDiff ℝ 2 Ω) {t : ℝ} (hpos : Ω (ε * t) ≠ 0)
    (hx : HasDerivAt x (v t) t) (hv : HasDerivAt v (-(Ω (ε * t)) ^ 2 * x t) t) :
    HasDerivAt (fun s => action (Ω (ε * s)) (x s) (v s))
      (ε * coefficient Ω (ε * t) * (Ω (ε * t) ^ 2 * x t ^ 2 - v t ^ 2)) t := by
  have hΩd : HasDerivAt Ω (deriv Ω (ε * t)) (ε * t) :=
    (hΩ.differentiable (by norm_num) _).hasDerivAt
  have hω : HasDerivAt (fun s => Ω (ε * s)) (deriv Ω (ε * t) * ε) t := by
    have hin : HasDerivAt (fun s : ℝ => ε * s) ε t := by
      simpa using (hasDerivAt_id t).const_mul ε
    exact hΩd.comp t hin
  have hnum : HasDerivAt (fun s => v s ^ 2 + Ω (ε * s) ^ 2 * x s ^ 2)
      (2 * v t * (-(Ω (ε * t)) ^ 2 * x t) +
        (2 * Ω (ε * t) * (deriv Ω (ε * t) * ε) * x t ^ 2 +
          Ω (ε * t) ^ 2 * (2 * x t * v t))) t := by
    have h1 := (hv.pow 2).add ((hω.pow 2).mul (hx.pow 2))
    refine h1.congr_deriv ?_
    simp only [Pi.pow_apply]
    norm_num
  have hden : HasDerivAt (fun s => 2 * Ω (ε * s)) (2 * (deriv Ω (ε * t) * ε)) t :=
    hω.const_mul 2
  have h : HasDerivAt (fun s => action (Ω (ε * s)) (x s) (v s))
      (((2 * v t * (-(Ω (ε * t)) ^ 2 * x t) +
          (2 * Ω (ε * t) * (deriv Ω (ε * t) * ε) * x t ^ 2 +
            Ω (ε * t) ^ 2 * (2 * x t * v t))) * (2 * Ω (ε * t)) -
        (v t ^ 2 + Ω (ε * t) ^ 2 * x t ^ 2) * (2 * (deriv Ω (ε * t) * ε))) /
          (2 * Ω (ε * t)) ^ 2) t :=
    hnum.div hden (by positivity)
  refine h.congr_deriv ?_
  rw [coefficient]
  field_simp
  ring

/-- The corrected action `I + ε a(εt) x v` has a derivative of the second
order in `ε`. -/
theorem hasDerivAt_correctedAction (hΩ : ContDiff ℝ 2 Ω) {t : ℝ} (hpos : Ω (ε * t) ≠ 0)
    (hx : HasDerivAt x (v t) t) (hv : HasDerivAt v (-(Ω (ε * t)) ^ 2 * x t) t) :
    HasDerivAt
      (fun s => action (Ω (ε * s)) (x s) (v s) + ε * coefficient Ω (ε * s) * (x s * v s))
      (ε ^ 2 * coefficientDeriv Ω (ε * t) * (x t * v t)) t := by
  have h1 := hasDerivAt_action hΩ hpos hx hv
  have hin : HasDerivAt (fun s : ℝ => ε * s) ε t := by
    simpa using (hasDerivAt_id t).const_mul ε
  have ha : HasDerivAt (fun s => coefficient Ω (ε * s)) (coefficientDeriv Ω (ε * t) * ε) t :=
    (hasDerivAt_coefficient hΩ hpos).comp t hin
  have h2 : HasDerivAt (fun s => ε * coefficient Ω (ε * s) * (x s * v s))
      (ε * (coefficientDeriv Ω (ε * t) * ε) * (x t * v t) +
        ε * coefficient Ω (ε * t) * (v t * v t + x t * (-(Ω (ε * t)) ^ 2 * x t))) t :=
    (ha.const_mul ε).mul (hx.mul hv)
  refine (h1.add h2).congr_deriv ?_
  ring

end Motion

/-- **The adiabatic theorem for the oscillator** (Landau–Lifshitz §49). For a
frequency `Ω(εt)` with `Ω` positive on `[0, T]` there is a constant `C` such
that for every `ε > 0` the action variable of every motion changes by at most
`C ε I(0)` up to the time `T/ε`. -/
theorem exists_forall_abs_action_sub_le {Ω : ℝ → ℝ} (hΩ : ContDiff ℝ 2 Ω) {T : ℝ}
    (hT : 0 ≤ T) (hpos : ∀ τ ∈ Icc 0 T, 0 < Ω τ) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ∀ x v : ℝ → ℝ,
      (∀ t ∈ Icc 0 (T / ε), HasDerivAt x (v t) t) →
      (∀ t ∈ Icc 0 (T / ε), HasDerivAt v (-(Ω (ε * t)) ^ 2 * x t) t) →
      ∀ t ∈ Icc 0 (T / ε),
        |action (Ω (ε * t)) (x t) (v t) - action (Ω 0) (x 0) (v 0)| ≤
          C * ε * action (Ω 0) (x 0) (v 0) := by
  have hΩc : Continuous Ω := hΩ.continuous
  have hΩ'c : Continuous (deriv Ω) := hΩ.continuous_deriv (by norm_num)
  have hΩ''c : Continuous (deriv (deriv Ω)) :=
    (contDiff_deriv hΩ).continuous_deriv le_rfl
  have hne : ∀ τ ∈ Icc 0 T, Ω τ ≠ 0 := fun τ hτ => (hpos τ hτ).ne'
  obtain ⟨b, hb⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc 0 T)
    (f := fun τ => deriv Ω τ / Ω τ) (hΩ'c.continuousOn.div hΩc.continuousOn hne)
  obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc 0 T)
    (f := coefficient Ω) (hΩ'c.continuousOn.div (by fun_prop)
      fun τ hτ => by have := hne τ hτ; positivity)
  obtain ⟨A', hA'⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc 0 T)
    (f := coefficientDeriv Ω) (ContinuousOn.div (by fun_prop) (by fun_prop)
      fun τ hτ => by have := hne τ hτ; positivity)
  have h0T : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0 h0T)
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 h0T)
  have hA'0 : 0 ≤ A' := (norm_nonneg _).trans (hA' 0 h0T)
  refine ⟨(A' * T + 2 * A) * Real.exp (b * T), fun ε hε x v hx hv => ?_⟩
  have hL : 0 ≤ T / ε := div_nonneg hT hε.le
  have hmem : ∀ t ∈ Icc 0 (T / ε), ε * t ∈ Icc 0 T := fun t ht =>
    ⟨mul_nonneg hε.le ht.1, by
      have := mul_le_mul_of_nonneg_left ht.2 hε.le
      rwa [mul_div_cancel₀ T hε.ne'] at this⟩
  obtain ⟨I, hI⟩ : ∃ I : ℝ → ℝ, I = fun s => action (Ω (ε * s)) (x s) (v s) := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ → ℝ, K = fun s => x s * v s := ⟨_, rfl⟩
  have hId : ∀ t ∈ Icc 0 (T / ε), HasDerivAt I
      (ε * coefficient Ω (ε * t) * (Ω (ε * t) ^ 2 * x t ^ 2 - v t ^ 2)) t := fun t ht => by
    rw [hI]
    exact hasDerivAt_action hΩ (hne _ (hmem t ht)) (hx t ht) (hv t ht)
  have hInn : ∀ t ∈ Icc 0 (T / ε), 0 ≤ I t := fun t ht => by
    rw [hI]
    exact action_nonneg (hpos _ (hmem t ht)) _ _
  have hKI : ∀ t ∈ Icc 0 (T / ε), |K t| ≤ I t := fun t ht => by
    rw [hI, hK]
    exact abs_mul_le_action (hpos _ (hmem t ht)) _ _
  have hI0 : I 0 = action (Ω 0) (x 0) (v 0) := by
    rw [hI]
    simp
  -- The action grows at most by the factor `e^{bT}`.
  have hgrow : ∀ t ∈ Icc 0 (T / ε), I t ≤ I 0 * Real.exp (b * T) := by
    intro t ht
    have hbound : ∀ s ∈ Ico 0 (T / ε),
        ‖ε * coefficient Ω (ε * s) * (Ω (ε * s) ^ 2 * x s ^ 2 - v s ^ 2)‖ ≤
          ε * b * ‖I s‖ + 0 := by
      intro s hs
      have hs' : s ∈ Icc 0 (T / ε) := ⟨hs.1, hs.2.le⟩
      have hΩs := hpos _ (hmem s hs')
      have h1 := abs_sub_le_action hΩs (x s) (v s)
      have h2 := hb _ (hmem s hs')
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hΩs] at h2
      rw [div_le_iff₀ hΩs] at h2
      rw [add_zero, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hInn s hs'), abs_mul,
        abs_mul, abs_of_pos hε, coefficient, abs_div,
        abs_of_pos (by positivity : (0 : ℝ) < 2 * Ω (ε * s) ^ 2)]
      have hIs : I s = action (Ω (ε * s)) (x s) (v s) := by rw [hI]
      rw [hIs]
      have h3 : |deriv Ω (ε * s)| / (2 * Ω (ε * s) ^ 2) *
          |Ω (ε * s) ^ 2 * x s ^ 2 - v s ^ 2| ≤ b * action (Ω (ε * s)) (x s) (v s) := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        calc |deriv Ω (ε * s)| * |Ω (ε * s) ^ 2 * x s ^ 2 - v s ^ 2|
            ≤ (b * Ω (ε * s)) * (2 * Ω (ε * s) * action (Ω (ε * s)) (x s) (v s)) :=
              mul_le_mul h2 h1 (abs_nonneg _) (by positivity)
          _ = b * action (Ω (ε * s)) (x s) (v s) * (2 * Ω (ε * s) ^ 2) := by ring
      calc ε * (|deriv Ω (ε * s)| / (2 * Ω (ε * s) ^ 2)) *
            |Ω (ε * s) ^ 2 * x s ^ 2 - v s ^ 2|
          = ε * (|deriv Ω (ε * s)| / (2 * Ω (ε * s) ^ 2) *
            |Ω (ε * s) ^ 2 * x s ^ 2 - v s ^ 2|) := by ring
        _ ≤ ε * (b * action (Ω (ε * s)) (x s) (v s)) := mul_le_mul_of_nonneg_left h3 hε.le
        _ = ε * b * action (Ω (ε * s)) (x s) (v s) := by ring
    have hg := norm_le_gronwallBound_of_norm_deriv_right_le (f := I) (δ := I 0) (K := ε * b)
      (ε := 0) (a := 0) (b := T / ε)
      (fun s hs => (hId s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hId s ⟨hs.1, hs.2.le⟩).hasDerivWithinAt)
      (by rw [Real.norm_eq_abs, abs_of_nonneg (hInn 0 ⟨le_rfl, hL⟩)]) hbound t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (hInn t ht), sub_zero] at hg
    have hle := SmoothGeometry.Averaging.gronwallBound_le_mul_exp (δ := I 0) (K := ε * b)
      (ε := 0) (hInn 0 ⟨le_rfl, hL⟩) (mul_nonneg hε.le hb0) le_rfl ht.1 ht.2
    have he : ε * b * (T / ε) = b * T := by
      field_simp
    rw [zero_mul, add_zero, he] at hle
    exact hg.trans hle
  -- The corrected action.
  obtain ⟨J, hJ⟩ : ∃ J : ℝ → ℝ, J = fun s => I s + ε * coefficient Ω (ε * s) * K s := ⟨_, rfl⟩
  have hJd : ∀ t ∈ Icc 0 (T / ε), HasDerivAt J
      (ε ^ 2 * coefficientDeriv Ω (ε * t) * K t) t := fun t ht => by
    rw [hJ, hI, hK]
    exact hasDerivAt_correctedAction hΩ (hne _ (hmem t ht)) (hx t ht) (hv t ht)
  have hJbound : ∀ t ∈ Icc 0 (T / ε),
      ‖ε ^ 2 * coefficientDeriv Ω (ε * t) * K t‖ ≤ ε ^ 2 * A' * (I 0 * Real.exp (b * T)) := by
    intro t ht
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg ε)]
    have h1 := hA' _ (hmem t ht)
    rw [Real.norm_eq_abs] at h1
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (sq_nonneg ε))
      ((hKI t ht).trans (hgrow t ht)) (abs_nonneg _) (by positivity)
  intro t ht
  have hmv := (convex_Icc 0 (T / ε)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := J) (fun s hs => (hJd s hs).hasDerivWithinAt) hJbound ⟨le_rfl, hL⟩ ht
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, abs_of_nonneg ht.1] at hmv
  have hI0nn := hInn 0 ⟨le_rfl, hL⟩
  have hexp : 1 ≤ Real.exp (b * T) := Real.one_le_exp (mul_nonneg hb0 hT)
  have hcorr : ∀ s ∈ Icc 0 (T / ε),
      |ε * coefficient Ω (ε * s) * K s| ≤ ε * A * (I 0 * Real.exp (b * T)) := by
    intro s hs
    rw [abs_mul, abs_mul, abs_of_pos hε]
    have h1 := hA _ (hmem s hs)
    rw [Real.norm_eq_abs] at h1
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hε.le)
      ((hKI s hs).trans (hgrow s hs)) (abs_nonneg _) (by positivity)
  have hsplit : I t - I 0 = (J t - J 0) - ε * coefficient Ω (ε * t) * K t +
      ε * coefficient Ω (ε * 0) * K 0 := by
    rw [hJ]
    ring
  have htime : ε ^ 2 * A' * (I 0 * Real.exp (b * T)) * t ≤
      ε * (A' * T) * (I 0 * Real.exp (b * T)) := by
    have h1 : ε * t ≤ T := (hmem t ht).2
    have h2 : 0 ≤ ε * A' * (I 0 * Real.exp (b * T)) := by positivity
    calc ε ^ 2 * A' * (I 0 * Real.exp (b * T)) * t
        = ε * A' * (I 0 * Real.exp (b * T)) * (ε * t) := by ring
      _ ≤ ε * A' * (I 0 * Real.exp (b * T)) * T := mul_le_mul_of_nonneg_left h1 h2
      _ = ε * (A' * T) * (I 0 * Real.exp (b * T)) := by ring
  have hfinal : |I t - I 0| ≤ (A' * T + 2 * A) * Real.exp (b * T) * ε * I 0 := by
    rw [hsplit]
    calc |J t - J 0 - ε * coefficient Ω (ε * t) * K t + ε * coefficient Ω (ε * 0) * K 0|
        ≤ |J t - J 0| + |ε * coefficient Ω (ε * t) * K t| +
          |ε * coefficient Ω (ε * 0) * K 0| :=
          (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ ε * (A' * T) * (I 0 * Real.exp (b * T)) + ε * A * (I 0 * Real.exp (b * T)) +
          ε * A * (I 0 * Real.exp (b * T)) :=
          add_le_add (add_le_add (hmv.trans htime) (hcorr t ht)) (hcorr 0 ⟨le_rfl, hL⟩)
      _ = (A' * T + 2 * A) * Real.exp (b * T) * ε * I 0 := by ring
  have hIt : I t = action (Ω (ε * t)) (x t) (v t) := by rw [hI]
  rw [← hIt, ← hI0]
  exact hfinal

/-- The theorem for the frequency `e^{εt}`, which is positive at all times. -/
theorem exists_forall_abs_action_sub_le_exp {T : ℝ} (hT : 0 ≤ T) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ∀ x v : ℝ → ℝ,
      (∀ t ∈ Icc 0 (T / ε), HasDerivAt x (v t) t) →
      (∀ t ∈ Icc 0 (T / ε), HasDerivAt v (-(Real.exp (ε * t)) ^ 2 * x t) t) →
      ∀ t ∈ Icc 0 (T / ε),
        |action (Real.exp (ε * t)) (x t) (v t) - action (Real.exp 0) (x 0) (v 0)| ≤
          C * ε * action (Real.exp 0) (x 0) (v 0) :=
  exists_forall_abs_action_sub_le Real.contDiff_exp hT fun τ _ => Real.exp_pos τ

/-- With a constant frequency the action variable is constant. -/
theorem action_eq_of_const {ω₀ L : ℝ} {x v : ℝ → ℝ}
    (hx : ∀ t ∈ Icc 0 L, HasDerivAt x (v t) t)
    (hv : ∀ t ∈ Icc 0 L, HasDerivAt v (-ω₀ ^ 2 * x t) t) {t : ℝ} (ht : t ∈ Icc 0 L) :
    action ω₀ (x t) (v t) = action ω₀ (x 0) (v 0) := by
  have hd : ∀ s ∈ Icc 0 L, HasDerivAt (fun s => action ω₀ (x s) (v s)) 0 s := by
    intro s hs
    have h1 := ((hv s hs).pow 2).add (((hx s hs).pow 2).const_mul (ω₀ ^ 2))
    have h2 : HasDerivAt (fun s => action ω₀ (x s) (v s))
        ((2 * v s ^ (2 - 1) * (-ω₀ ^ 2 * x s) + ω₀ ^ 2 * (2 * x s ^ (2 - 1) * v s)) /
          (2 * ω₀)) s := h1.div_const (2 * ω₀)
    refine h2.congr_deriv ?_
    have e : 2 * v s ^ (2 - 1) * (-ω₀ ^ 2 * x s) + ω₀ ^ 2 * (2 * x s ^ (2 - 1) * v s) = 0 := by
      simp only [Nat.reduceSub, pow_one]
      ring
    rw [e, zero_div]
  have hL : (0 : ℝ) ≤ L := ht.1.trans ht.2
  have h := (convex_Icc 0 L).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s => action ω₀ (x s) (v s)) (C := 0)
    (fun s hs => (hd s hs).hasDerivWithinAt) (fun s _ => by simp) ⟨le_rfl, hL⟩ ht
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at h
  exact h

end ProjectAinos.Mechanics.AdiabaticOscillator
