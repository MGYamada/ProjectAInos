/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# A slowly varying parameter and a corrector of the first order

Let `ż = X(z, λ)` with a parameter `λ = Λ(εt)`. Suppose that a function
`I(z, λ)` is invariant under the field with a fixed parameter, and that its
derivative in the parameter is the derivative of a function `G(z, λ)` along the
field with a fixed parameter. Then `I − ε Λ′(εt) G` has a derivative of the
order `ε²` along the motion, and

`|I(t) − I(0)| ≤ ε (T (L₂ M₀ + L₁² M₁) + 2 L₁ M₀)` for `0 ≤ t ≤ T/ε`

(`abs_sub_le_of_corrector`), with bounds `L₁`, `L₂` of `Λ′`, `Λ″` and `M₀`,
`M₁` of `G`, `∂G/∂λ`. This is the estimate behind adiabatic invariance.
-/

@[expose] public section
noncomputable section

open Set

namespace ProjectAInos.SmoothGeometry.SlowParameter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The adiabatic estimate from a corrector of the first order. -/
theorem abs_sub_le_of_corrector {X : E × ℝ → E} {I G : E × ℝ → ℝ}
    {I' G' : E × ℝ → (E × ℝ →L[ℝ] ℝ)} {S : Set (E × ℝ)} {Λ Λ' Λ'' : ℝ → ℝ}
    {T ε L₁ L₂ M₀ M₁ : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (hI : ∀ w ∈ S, HasFDerivAt I (I' w) w) (hG : ∀ w ∈ S, HasFDerivAt G (G' w) w)
    (hinv : ∀ w ∈ S, I' w (X w, 0) = 0)
    (hhom : ∀ w ∈ S, I' w (0, 1) = G' w (X w, 0))
    (hΛ : ∀ τ ∈ Icc 0 T, HasDerivAt Λ (Λ' τ) τ)
    (hΛ' : ∀ τ ∈ Icc 0 T, HasDerivAt Λ' (Λ'' τ) τ)
    (hL₁ : ∀ τ ∈ Icc 0 T, |Λ' τ| ≤ L₁) (hL₂ : ∀ τ ∈ Icc 0 T, |Λ'' τ| ≤ L₂)
    (hM₀ : ∀ w ∈ S, |G w| ≤ M₀) (hM₁ : ∀ w ∈ S, |G' w (0, 1)| ≤ M₁)
    {z : ℝ → E} (hz : ∀ t ∈ Icc 0 (T / ε), HasDerivAt z (X (z t, Λ (ε * t))) t)
    (hS : ∀ t ∈ Icc 0 (T / ε), (z t, Λ (ε * t)) ∈ S) :
    ∀ t ∈ Icc 0 (T / ε),
      |I (z t, Λ (ε * t)) - I (z 0, Λ 0)| ≤
        ε * (T * (L₂ * M₀ + L₁ ^ 2 * M₁) + 2 * L₁ * M₀) := by
  have hL : 0 ≤ T / ε := div_nonneg hT hε.le
  have h0 : (0 : ℝ) ∈ Icc 0 (T / ε) := ⟨le_rfl, hL⟩
  have hmem : ∀ t ∈ Icc 0 (T / ε), ε * t ∈ Icc 0 T := fun t ht =>
    ⟨mul_nonneg hε.le ht.1, by
      have := mul_le_mul_of_nonneg_left ht.2 hε.le
      rwa [mul_div_cancel₀ T hε.ne'] at this⟩
  have hin : ∀ t : ℝ, HasDerivAt (fun s : ℝ => ε * s) ε t := fun t => by
    simpa using (hasDerivAt_id t).const_mul ε
  have hL₁0 : 0 ≤ L₁ := (abs_nonneg _).trans (hL₁ 0 ⟨le_rfl, hT⟩)
  have hL₂0 : 0 ≤ L₂ := (abs_nonneg _).trans (hL₂ 0 ⟨le_rfl, hT⟩)
  have hM₀0 : 0 ≤ M₀ := (abs_nonneg _).trans (hM₀ _ (hS 0 h0))
  have hM₁0 : 0 ≤ M₁ := (abs_nonneg _).trans (hM₁ _ (hS 0 h0))
  -- the curve in the product
  have hΛc : ∀ t ∈ Icc 0 (T / ε), HasDerivAt (fun s => Λ (ε * s)) (Λ' (ε * t) * ε) t :=
    fun t ht => HasDerivAt.comp t (hΛ _ (hmem t ht)) (hin t)
  have hΛ'c : ∀ t ∈ Icc 0 (T / ε), HasDerivAt (fun s => Λ' (ε * s)) (Λ'' (ε * t) * ε) t :=
    fun t ht => HasDerivAt.comp t (hΛ' _ (hmem t ht)) (hin t)
  have hw : ∀ t ∈ Icc 0 (T / ε), HasDerivAt (fun s => (z s, Λ (ε * s)))
      (X (z t, Λ (ε * t)), Λ' (ε * t) * ε) t := fun t ht =>
    (hz t ht).prodMk (hΛc t ht)
  have hsplit : ∀ (A : E × ℝ →L[ℝ] ℝ) (x : E) (c : ℝ), A (x, c) = A (x, 0) + c * A (0, 1) := by
    intro A x c
    have e : ((x, c) : E × ℝ) = (x, 0) + c • ((0 : E), (1 : ℝ)) := by
      simp
    rw [e, map_add, map_smul, smul_eq_mul]
  have hId : ∀ t ∈ Icc 0 (T / ε), HasDerivAt (fun s => I (z s, Λ (ε * s)))
      (Λ' (ε * t) * ε * G' (z t, Λ (ε * t)) (X (z t, Λ (ε * t)), 0)) t := by
    intro t ht
    have h1 := HasFDerivAt.comp_hasDerivAt t (hI _ (hS t ht)) (hw t ht)
    refine h1.congr_deriv ?_
    rw [hsplit, hinv _ (hS t ht), hhom _ (hS t ht), zero_add]
  have hGd : ∀ t ∈ Icc 0 (T / ε), HasDerivAt (fun s => G (z s, Λ (ε * s)))
      (G' (z t, Λ (ε * t)) (X (z t, Λ (ε * t)), 0) +
        Λ' (ε * t) * ε * G' (z t, Λ (ε * t)) (0, 1)) t := by
    intro t ht
    have h1 := HasFDerivAt.comp_hasDerivAt t (hG _ (hS t ht)) (hw t ht)
    refine h1.congr_deriv ?_
    rw [hsplit]
  obtain ⟨J, hJ⟩ : ∃ J : ℝ → ℝ,
      J = fun s => I (z s, Λ (ε * s)) - ε * Λ' (ε * s) * G (z s, Λ (ε * s)) := ⟨_, rfl⟩
  have hJd : ∀ t ∈ Icc 0 (T / ε), HasDerivAt J
      (-(ε ^ 2 * (Λ'' (ε * t) * G (z t, Λ (ε * t)) +
        Λ' (ε * t) ^ 2 * G' (z t, Λ (ε * t)) (0, 1)))) t := by
    intro t ht
    have h1 : HasDerivAt (fun s => ε * Λ' (ε * s)) (ε * (Λ'' (ε * t) * ε)) t :=
      (hΛ'c t ht).const_mul ε
    have h2 := (hId t ht).sub (h1.mul (hGd t ht))
    rw [hJ]
    refine h2.congr_deriv ?_
    ring
  have hJbound : ∀ t ∈ Icc 0 (T / ε),
      ‖-(ε ^ 2 * (Λ'' (ε * t) * G (z t, Λ (ε * t)) +
        Λ' (ε * t) ^ 2 * G' (z t, Λ (ε * t)) (0, 1)))‖ ≤
        ε ^ 2 * (L₂ * M₀ + L₁ ^ 2 * M₁) := by
    intro t ht
    rw [norm_neg, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ε)]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg ε)
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      exact mul_le_mul (hL₂ _ (hmem t ht)) (hM₀ _ (hS t ht)) (abs_nonneg _) hL₂0
    · rw [abs_mul, abs_pow]
      exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hL₁ _ (hmem t ht)) 2)
        (hM₁ _ (hS t ht)) (abs_nonneg _) (by positivity)
  intro t ht
  have hmv := (convex_Icc 0 (T / ε)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := J) (fun s hs => (hJd s hs).hasDerivWithinAt) hJbound h0 ht
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, abs_of_nonneg ht.1] at hmv
  have hcorr : ∀ s ∈ Icc 0 (T / ε), |ε * Λ' (ε * s) * G (z s, Λ (ε * s))| ≤ ε * (L₁ * M₀) := by
    intro s hs
    rw [abs_mul, abs_mul, abs_of_pos hε, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul (hL₁ _ (hmem s hs)) (hM₀ _ (hS s hs)) (abs_nonneg _) hL₁0) hε.le
  have htime : ε ^ 2 * (L₂ * M₀ + L₁ ^ 2 * M₁) * t ≤ ε * (T * (L₂ * M₀ + L₁ ^ 2 * M₁)) := by
    have h1 : ε * t ≤ T := (hmem t ht).2
    have h2 : 0 ≤ ε * (L₂ * M₀ + L₁ ^ 2 * M₁) := by positivity
    calc ε ^ 2 * (L₂ * M₀ + L₁ ^ 2 * M₁) * t = ε * (L₂ * M₀ + L₁ ^ 2 * M₁) * (ε * t) := by ring
      _ ≤ ε * (L₂ * M₀ + L₁ ^ 2 * M₁) * T := mul_le_mul_of_nonneg_left h1 h2
      _ = ε * (T * (L₂ * M₀ + L₁ ^ 2 * M₁)) := by ring
  have hsplit2 : I (z t, Λ (ε * t)) - I (z 0, Λ 0) =
      (J t - J 0) + ε * Λ' (ε * t) * G (z t, Λ (ε * t)) -
        ε * Λ' (ε * 0) * G (z 0, Λ (ε * 0)) := by
    rw [hJ]
    simp only [mul_zero]
    ring
  rw [hsplit2]
  calc |J t - J 0 + ε * Λ' (ε * t) * G (z t, Λ (ε * t)) -
        ε * Λ' (ε * 0) * G (z 0, Λ (ε * 0))|
      ≤ |J t - J 0| + |ε * Λ' (ε * t) * G (z t, Λ (ε * t))| +
        |ε * Λ' (ε * 0) * G (z 0, Λ (ε * 0))| :=
        (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ ε * (T * (L₂ * M₀ + L₁ ^ 2 * M₁)) + ε * (L₁ * M₀) + ε * (L₁ * M₀) :=
        add_le_add (add_le_add (hmv.trans htime) (hcorr t ht)) (hcorr 0 h0)
    _ = ε * (T * (L₂ * M₀ + L₁ ^ 2 * M₁) + 2 * L₁ * M₀) := by ring

end ProjectAInos.SmoothGeometry.SlowParameter
