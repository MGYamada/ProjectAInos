/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Averaging: a perturbation with a small integral

A solution of `ż = F(z) + r(t)` stays close to the solution of `Ż = F(Z)` with
the same initial value when the integral of `r` is small, even if `r` is not.

* `abs_integral_mul_sin_le`, `abs_integral_mul_cos_le`: for a function `φ` with
  `|φ| ≤ M₀` and `|φ′| ≤ M₁` on `[0, t]`,
  `|∫₀ᵗ φ(s) sin ωs ds| ≤ (2 M₀ + t M₁)/ω`, by an integration by parts.
* `norm_integral_prodMk_le`: the integral of a curve in the plane, from its
  two components.
* `norm_sub_le_of_norm_integral_le`: if `F` is Lipschitz with the constant `K`
  on a set that contains the two solutions on `[0, L]`, and
  `‖∫₀ᵗ r‖ ≤ δ` there, then `‖z(t) − Z(t)‖ ≤ δ e^{K t}`.

Together they are the method of averaging to the first order for a
perturbation that oscillates with a high frequency: the oscillating terms of
the equation are `r`, and `δ` is of the order of the inverse frequency.

* `exists_forall_norm_sub_le`: the general statement for a perturbation
  `Σ_j (cos (n_j γ t) P_j(z) + sin (n_j γ t) Q_j(z))` (`harmonics`) with
  continuously differentiable amplitudes: on a compact convex set the solution
  and the solution of the averaged equation differ by at most `C/γ` on
  `[0, L]`, with a constant that does not depend on `γ`.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped NNReal

namespace ProjectAinos.SmoothGeometry.Averaging

/-! ### The integral of a slowly varying amplitude against a fast oscillation -/

/-- `|∫₀ᵗ φ(s) sin ωs ds| ≤ (2 M₀ + t M₁)/ω`. -/
theorem abs_integral_mul_sin_le {φ φ' : ℝ → ℝ} {t ω M₀ M₁ : ℝ} (ht : 0 ≤ t) (hω : 0 < ω)
    (hφ : ∀ s ∈ Icc 0 t, HasDerivAt φ (φ' s) s) (hc : ContinuousOn φ' (Icc 0 t))
    (h0 : ∀ s ∈ Icc 0 t, |φ s| ≤ M₀) (h1 : ∀ s ∈ Icc 0 t, |φ' s| ≤ M₁) :
    |∫ s in 0..t, φ s * Real.sin (ω * s)| ≤ (2 * M₀ + t * M₁) / ω := by
  have hI : uIcc 0 t = Icc 0 t := uIcc_of_le ht
  have hv : ∀ s : ℝ, HasDerivAt (fun s => -Real.cos (ω * s) / ω) (Real.sin (ω * s)) s := by
    intro s
    have h := (((hasDerivAt_id s).const_mul ω).cos.neg).div_const ω
    refine h.congr_deriv ?_
    simp only [id_eq, mul_one]
    field_simp
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := t)
    (u := φ) (u' := φ') (v := fun s => -Real.cos (ω * s) / ω)
    (v' := fun s => Real.sin (ω * s)) (fun s hs => hφ s (hI ▸ hs)) (fun s _ => hv s)
    (ContinuousOn.intervalIntegrable (μ := volume) (hI ▸ hc : ContinuousOn φ' (uIcc 0 t)))
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 t)
  rw [hparts]
  have hM₀ : 0 ≤ M₀ := (abs_nonneg _).trans (h0 0 ⟨le_rfl, ht⟩)
  have hcos : ∀ s : ℝ, |-Real.cos (ω * s) / ω| ≤ 1 / ω := by
    intro s
    rw [abs_div, abs_neg, abs_of_pos hω]
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) hω.le
  have hb1 : |φ t * (-Real.cos (ω * t) / ω)| ≤ M₀ / ω := by
    rw [abs_mul]
    calc |φ t| * |-Real.cos (ω * t) / ω| ≤ M₀ * (1 / ω) :=
          mul_le_mul (h0 t ⟨ht, le_rfl⟩) (hcos t) (abs_nonneg _) hM₀
      _ = M₀ / ω := by ring
  have hb0 : |φ 0 * (-Real.cos (ω * 0) / ω)| ≤ M₀ / ω := by
    rw [abs_mul]
    calc |φ 0| * |-Real.cos (ω * 0) / ω| ≤ M₀ * (1 / ω) :=
          mul_le_mul (h0 0 ⟨le_rfl, ht⟩) (hcos 0) (abs_nonneg _) hM₀
      _ = M₀ / ω := by ring
  have hint : |∫ s in 0..t, φ' s * (-Real.cos (ω * s) / ω)| ≤ M₁ / ω * |t - 0| := by
    rw [← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => ?_
    have hs' : s ∈ Icc 0 t := by
      rw [uIoc_of_le ht] at hs
      exact ⟨hs.1.le, hs.2⟩
    have hM₁ : 0 ≤ M₁ := (abs_nonneg _).trans (h1 s hs')
    rw [Real.norm_eq_abs, abs_mul]
    calc |φ' s| * |-Real.cos (ω * s) / ω| ≤ M₁ * (1 / ω) :=
          mul_le_mul (h1 s hs') (hcos s) (abs_nonneg _) hM₁
      _ = M₁ / ω := by ring
  rw [sub_zero, abs_of_nonneg ht] at hint
  calc |φ t * (-Real.cos (ω * t) / ω) - φ 0 * (-Real.cos (ω * 0) / ω) -
        ∫ s in 0..t, φ' s * (-Real.cos (ω * s) / ω)|
      ≤ |φ t * (-Real.cos (ω * t) / ω)| + |φ 0 * (-Real.cos (ω * 0) / ω)| +
          |∫ s in 0..t, φ' s * (-Real.cos (ω * s) / ω)| := by
        refine (abs_sub _ _).trans ?_
        gcongr
        exact abs_sub _ _
    _ ≤ M₀ / ω + M₀ / ω + M₁ / ω * t := by gcongr
    _ = (2 * M₀ + t * M₁) / ω := by ring

/-- `|∫₀ᵗ φ(s) cos ωs ds| ≤ (2 M₀ + t M₁)/ω`. -/
theorem abs_integral_mul_cos_le {φ φ' : ℝ → ℝ} {t ω M₀ M₁ : ℝ} (ht : 0 ≤ t) (hω : 0 < ω)
    (hφ : ∀ s ∈ Icc 0 t, HasDerivAt φ (φ' s) s) (hc : ContinuousOn φ' (Icc 0 t))
    (h0 : ∀ s ∈ Icc 0 t, |φ s| ≤ M₀) (h1 : ∀ s ∈ Icc 0 t, |φ' s| ≤ M₁) :
    |∫ s in 0..t, φ s * Real.cos (ω * s)| ≤ (2 * M₀ + t * M₁) / ω := by
  have hI : uIcc 0 t = Icc 0 t := uIcc_of_le ht
  have hv : ∀ s : ℝ, HasDerivAt (fun s => Real.sin (ω * s) / ω) (Real.cos (ω * s)) s := by
    intro s
    have h := (((hasDerivAt_id s).const_mul ω).sin).div_const ω
    refine h.congr_deriv ?_
    simp only [id_eq, mul_one]
    field_simp
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := t)
    (u := φ) (u' := φ') (v := fun s => Real.sin (ω * s) / ω)
    (v' := fun s => Real.cos (ω * s)) (fun s hs => hφ s (hI ▸ hs)) (fun s _ => hv s)
    (ContinuousOn.intervalIntegrable (μ := volume) (hI ▸ hc : ContinuousOn φ' (uIcc 0 t)))
    ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 t)
  rw [hparts]
  have hM₀ : 0 ≤ M₀ := (abs_nonneg _).trans (h0 0 ⟨le_rfl, ht⟩)
  have hsin : ∀ s : ℝ, |Real.sin (ω * s) / ω| ≤ 1 / ω := by
    intro s
    rw [abs_div, abs_of_pos hω]
    exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) hω.le
  have hb1 : |φ t * (Real.sin (ω * t) / ω)| ≤ M₀ / ω := by
    rw [abs_mul]
    calc |φ t| * |Real.sin (ω * t) / ω| ≤ M₀ * (1 / ω) :=
          mul_le_mul (h0 t ⟨ht, le_rfl⟩) (hsin t) (abs_nonneg _) hM₀
      _ = M₀ / ω := by ring
  have hb0 : |φ 0 * (Real.sin (ω * 0) / ω)| ≤ M₀ / ω := by
    rw [abs_mul]
    calc |φ 0| * |Real.sin (ω * 0) / ω| ≤ M₀ * (1 / ω) :=
          mul_le_mul (h0 0 ⟨le_rfl, ht⟩) (hsin 0) (abs_nonneg _) hM₀
      _ = M₀ / ω := by ring
  have hint : |∫ s in 0..t, φ' s * (Real.sin (ω * s) / ω)| ≤ M₁ / ω * |t - 0| := by
    rw [← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => ?_
    have hs' : s ∈ Icc 0 t := by
      rw [uIoc_of_le ht] at hs
      exact ⟨hs.1.le, hs.2⟩
    have hM₁ : 0 ≤ M₁ := (abs_nonneg _).trans (h1 s hs')
    rw [Real.norm_eq_abs, abs_mul]
    calc |φ' s| * |Real.sin (ω * s) / ω| ≤ M₁ * (1 / ω) :=
          mul_le_mul (h1 s hs') (hsin s) (abs_nonneg _) hM₁
      _ = M₁ / ω := by ring
  rw [sub_zero, abs_of_nonneg ht] at hint
  calc |φ t * (Real.sin (ω * t) / ω) - φ 0 * (Real.sin (ω * 0) / ω) -
        ∫ s in 0..t, φ' s * (Real.sin (ω * s) / ω)|
      ≤ |φ t * (Real.sin (ω * t) / ω)| + |φ 0 * (Real.sin (ω * 0) / ω)| +
          |∫ s in 0..t, φ' s * (Real.sin (ω * s) / ω)| := by
        refine (abs_sub _ _).trans ?_
        gcongr
        exact abs_sub _ _
    _ ≤ M₀ / ω + M₀ / ω + M₁ / ω * t := by gcongr
    _ = (2 * M₀ + t * M₁) / ω := by ring

/-- The integral of a curve in the plane is small if the integrals of its two
components are. -/
theorem norm_integral_prodMk_le {r₁ r₂ : ℝ → ℝ} (h₁ : Continuous r₁) (h₂ : Continuous r₂)
    {t δ : ℝ} (hb₁ : |∫ u in 0..t, r₁ u| ≤ δ) (hb₂ : |∫ u in 0..t, r₂ u| ≤ δ) :
    ‖∫ u in 0..t, (r₁ u, r₂ u)‖ ≤ δ := by
  have hint : IntervalIntegrable (fun u => (r₁ u, r₂ u)) volume 0 t :=
    (h₁.prodMk h₂).intervalIntegrable 0 t
  have e₁ : (∫ u in 0..t, r₁ u) = (∫ u in 0..t, (r₁ u, r₂ u)).1 :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).intervalIntegral_comp_comm hint
  have e₂ : (∫ u in 0..t, r₂ u) = (∫ u in 0..t, (r₁ u, r₂ u)).2 :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).intervalIntegral_comp_comm hint
  rw [Prod.norm_def, max_le_iff, Real.norm_eq_abs, Real.norm_eq_abs, ← e₁, ← e₂]
  exact ⟨hb₁, hb₂⟩

/-- A bound of Gronwall's bound on an interval of time: for `0 ≤ t ≤ L`,
`gronwallBound δ K ε t ≤ (δ + ε L) e^{K L}`. -/
theorem gronwallBound_le_mul_exp {δ K ε t L : ℝ} (hδ : 0 ≤ δ) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (ht : 0 ≤ t) (htL : t ≤ L) : gronwallBound δ K ε t ≤ (δ + ε * L) * Real.exp (K * L) := by
  have hL : 0 ≤ L := ht.trans htL
  have hmono : (δ + ε * t) * Real.exp (K * t) ≤ (δ + ε * L) * Real.exp (K * L) :=
    mul_le_mul (add_le_add le_rfl (mul_le_mul_of_nonneg_left htL hε))
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htL hK)) (Real.exp_pos _).le
      (add_nonneg hδ (mul_nonneg hε hL))
  refine le_trans ?_ hmono
  by_cases hK0 : K = 0
  · rw [hK0, gronwallBound_K0]
    simp
  · have hKpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hK0)
    rw [gronwallBound_of_K_ne_0 hK0]
    beta_reduce
    have h1 : Real.exp (K * t) - 1 ≤ K * t * Real.exp (K * t) := by
      have h2 := Real.add_one_le_exp (-(K * t))
      have h3 : (-(K * t) + 1) * Real.exp (K * t) ≤ Real.exp (-(K * t)) * Real.exp (K * t) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h3
      linarith
    have h4 : ε / K * (Real.exp (K * t) - 1) ≤ ε * t * Real.exp (K * t) := by
      calc ε / K * (Real.exp (K * t) - 1) ≤ ε / K * (K * t * Real.exp (K * t)) :=
            mul_le_mul_of_nonneg_left h1 (div_nonneg hε hK)
        _ = ε * t * Real.exp (K * t) := by
            field_simp
    linarith

/-! ### Comparison with the unperturbed equation -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A perturbation with a small integral. Let `ż = F(z) + r(t)` and
`Ż = F(Z)` on `[0, L]` with `z(0) = Z(0)`, let `F` be Lipschitz with the
constant `K` on a set that contains both curves, and let `‖∫₀ᵗ r‖ ≤ δ` on
`[0, L]`. Then `‖z(t) − Z(t)‖ ≤ δ e^{K t}`. -/
theorem norm_sub_le_of_norm_integral_le {F : E → E} {K : ℝ≥0} {s : Set E}
    (hF : LipschitzOnWith K F s) {z Z r : ℝ → E} {L δ : ℝ} (hr : Continuous r)
    (hz : ∀ t ∈ Icc 0 L, HasDerivAt z (F (z t) + r t) t)
    (hZ : ∀ t ∈ Icc 0 L, HasDerivAt Z (F (Z t)) t) (hzs : ∀ t ∈ Icc 0 L, z t ∈ s)
    (hZs : ∀ t ∈ Icc 0 L, Z t ∈ s) (hδ : ∀ t ∈ Icc 0 L, ‖∫ u in 0..t, r u‖ ≤ δ)
    (h0 : z 0 = Z 0) : ∀ t ∈ Icc 0 L, ‖z t - Z t‖ ≤ δ * Real.exp (K * t) := by
  intro t ht
  have hR : ∀ x : ℝ, HasDerivAt (fun x => ∫ u in 0..x, r u) (r x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (hr.intervalIntegrable 0 x)
      (hr.stronglyMeasurableAtFilter _ _) hr.continuousAt
  have hu : ∀ x ∈ Icc 0 L,
      HasDerivAt (fun x => z x - Z x - ∫ u in 0..x, r u) (F (z x) - F (Z x)) x := by
    intro x hx
    refine (((hz x hx).sub (hZ x hx)).sub (hR x)).congr_deriv ?_
    abel
  have hbound : ∀ x ∈ Ico 0 L, ‖F (z x) - F (Z x)‖ ≤
      K * ‖z x - Z x - ∫ u in 0..x, r u‖ + K * δ := by
    intro x hx
    have hx' : x ∈ Icc 0 L := ⟨hx.1, hx.2.le⟩
    have h1 := hF.norm_sub_le (hzs x hx') (hZs x hx')
    have h2 : ‖z x - Z x‖ ≤ ‖z x - Z x - ∫ u in 0..x, r u‖ + δ := by
      have h3 : z x - Z x = (z x - Z x - ∫ u in 0..x, r u) + ∫ u in 0..x, r u := by abel
      calc ‖z x - Z x‖ = ‖(z x - Z x - ∫ u in 0..x, r u) + ∫ u in 0..x, r u‖ := by rw [← h3]
        _ ≤ ‖z x - Z x - ∫ u in 0..x, r u‖ + ‖∫ u in 0..x, r u‖ := norm_add_le _ _
        _ ≤ ‖z x - Z x - ∫ u in 0..x, r u‖ + δ := by gcongr; exact hδ x hx'
    calc ‖F (z x) - F (Z x)‖ ≤ K * ‖z x - Z x‖ := h1
      _ ≤ K * (‖z x - Z x - ∫ u in 0..x, r u‖ + δ) := by gcongr
      _ = K * ‖z x - Z x - ∫ u in 0..x, r u‖ + K * δ := by ring
  have hcont : ContinuousOn (fun x => z x - Z x - ∫ u in 0..x, r u) (Icc 0 L) :=
    fun x hx => (hu x hx).continuousAt.continuousWithinAt
  have hinit : ‖z 0 - Z 0 - ∫ u in (0 : ℝ)..0, r u‖ ≤ 0 := by
    rw [h0, sub_self, intervalIntegral.integral_same, sub_zero, norm_zero]
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le hcont
    (fun x hx => (hu x ⟨hx.1, hx.2.le⟩).hasDerivWithinAt) hinit hbound t ht
  rw [sub_zero] at hg
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hδ t ht)
  have hgb : gronwallBound 0 K (K * δ) t ≤ δ * (Real.exp (K * t) - 1) := by
    by_cases hK : (K : ℝ) = 0
    · rw [hK, gronwallBound_K0]
      simp
    · rw [gronwallBound_of_K_ne_0 hK]
      beta_reduce
      rw [zero_mul, zero_add, mul_div_cancel_left₀ _ hK]
  have h3 : z t - Z t = (z t - Z t - ∫ u in 0..t, r u) + ∫ u in 0..t, r u := by abel
  calc ‖z t - Z t‖ = ‖(z t - Z t - ∫ u in 0..t, r u) + ∫ u in 0..t, r u‖ := by rw [← h3]
    _ ≤ ‖z t - Z t - ∫ u in 0..t, r u‖ + ‖∫ u in 0..t, r u‖ := norm_add_le _ _
    _ ≤ δ * (Real.exp (K * t) - 1) + δ := add_le_add (hg.trans hgb) (hδ t ht)
    _ = δ * Real.exp (K * t) := by ring

/-- The same comparison when the perturbation is continuous on the interval
of time only. -/
theorem norm_sub_le_of_norm_integral_le' {F : E → E} {K : ℝ≥0} {s : Set E}
    (hF : LipschitzOnWith K F s) {z Z r : ℝ → E} {L δ : ℝ} (hr : ContinuousOn r (Icc 0 L))
    (hz : ∀ t ∈ Icc 0 L, HasDerivAt z (F (z t) + r t) t)
    (hZ : ∀ t ∈ Icc 0 L, HasDerivAt Z (F (Z t)) t) (hzs : ∀ t ∈ Icc 0 L, z t ∈ s)
    (hZs : ∀ t ∈ Icc 0 L, Z t ∈ s) (hδ : ∀ t ∈ Icc 0 L, ‖∫ u in 0..t, r u‖ ≤ δ)
    (h0 : z 0 = Z 0) : ∀ t ∈ Icc 0 L, ‖z t - Z t‖ ≤ δ * Real.exp (K * t) := by
  intro t ht
  have hL : (0 : ℝ) ≤ L := ht.1.trans ht.2
  have hext : ∀ x ∈ Icc 0 L, IccExtend hL (fun x : Icc (0 : ℝ) L => r x) x = r x :=
    fun x hx => IccExtend_of_mem hL _ hx
  have hcont : Continuous (IccExtend hL fun x : Icc (0 : ℝ) L => r x) :=
    (continuousOn_iff_continuous_domRestrict.mp hr).Icc_extend'
  refine norm_sub_le_of_norm_integral_le hF hcont
    (fun x hx => by rw [hext x hx]; exact hz x hx) hZ hzs hZs (fun x hx => ?_) h0 t ht
  have hcongr : (∫ u in 0..x, IccExtend hL (fun x : Icc (0 : ℝ) L => r x) u) =
      ∫ u in 0..x, r u :=
    intervalIntegral.integral_congr fun u hu => by
      rw [uIcc_of_le hx.1] at hu
      exact hext u ⟨hu.1, hu.2.trans hx.2⟩
  rw [hcongr]
  exact hδ x hx

/-! ### Vector amplitudes -/

/-- `‖∫₀ᵗ sin ωs • φ(s) ds‖ ≤ (2 M₀ + t M₁)/ω` for an amplitude with values in
a Banach space. -/
theorem norm_integral_sin_smul_le {φ φ' : ℝ → E} {t ω M₀ M₁ : ℝ} (ht : 0 ≤ t) (hω : 0 < ω)
    (hφ : ∀ s ∈ Icc 0 t, HasDerivAt φ (φ' s) s) (hc : ContinuousOn φ' (Icc 0 t))
    (h0 : ∀ s ∈ Icc 0 t, ‖φ s‖ ≤ M₀) (h1 : ∀ s ∈ Icc 0 t, ‖φ' s‖ ≤ M₁) :
    ‖∫ s in 0..t, Real.sin (ω * s) • φ s‖ ≤ (2 * M₀ + t * M₁) / ω := by
  have hI : uIcc 0 t = Icc 0 t := uIcc_of_le ht
  have hu : ∀ s : ℝ, HasDerivAt (fun s => -Real.cos (ω * s) / ω) (Real.sin (ω * s)) s := by
    intro s
    have h := (((hasDerivAt_id s).const_mul ω).cos.neg).div_const ω
    refine h.congr_deriv ?_
    simp only [id_eq, mul_one]
    field_simp
  have hparts := intervalIntegral.integral_smul_deriv_eq_deriv_smul (a := 0) (b := t)
    (u := fun s => -Real.cos (ω * s) / ω) (u' := fun s => Real.sin (ω * s)) (v := φ)
    (v' := φ') (fun s _ => hu s) (fun s hs => hφ s (hI ▸ hs))
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 t)
    (ContinuousOn.intervalIntegrable (μ := volume) (hI ▸ hc : ContinuousOn φ' (uIcc 0 t)))
  have hrew : (∫ s in 0..t, Real.sin (ω * s) • φ s) =
      (-Real.cos (ω * t) / ω) • φ t - (-Real.cos (ω * 0) / ω) • φ 0 -
        ∫ s in 0..t, (-Real.cos (ω * s) / ω) • φ' s := by
    rw [hparts]
    abel
  rw [hrew]
  have hM₀ : 0 ≤ M₀ := (norm_nonneg _).trans (h0 0 ⟨le_rfl, ht⟩)
  have hcos : ∀ s : ℝ, ‖-Real.cos (ω * s) / ω‖ ≤ 1 / ω := by
    intro s
    rw [Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos hω]
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) hω.le
  have hb : ∀ s ∈ Icc 0 t, ‖(-Real.cos (ω * s) / ω) • φ s‖ ≤ M₀ / ω := by
    intro s hs
    rw [norm_smul]
    calc ‖-Real.cos (ω * s) / ω‖ * ‖φ s‖ ≤ 1 / ω * M₀ :=
          mul_le_mul (hcos s) (h0 s hs) (norm_nonneg _) (by positivity)
      _ = M₀ / ω := by ring
  have hint : ‖∫ s in 0..t, (-Real.cos (ω * s) / ω) • φ' s‖ ≤ M₁ / ω * |t - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => ?_
    have hs' : s ∈ Icc 0 t := by
      rw [uIoc_of_le ht] at hs
      exact ⟨hs.1.le, hs.2⟩
    have hM₁ : 0 ≤ M₁ := (norm_nonneg _).trans (h1 s hs')
    rw [norm_smul]
    calc ‖-Real.cos (ω * s) / ω‖ * ‖φ' s‖ ≤ 1 / ω * M₁ :=
          mul_le_mul (hcos s) (h1 s hs') (norm_nonneg _) (by positivity)
      _ = M₁ / ω := by ring
  rw [sub_zero, abs_of_nonneg ht] at hint
  calc ‖(-Real.cos (ω * t) / ω) • φ t - (-Real.cos (ω * 0) / ω) • φ 0 -
        ∫ s in 0..t, (-Real.cos (ω * s) / ω) • φ' s‖
      ≤ ‖(-Real.cos (ω * t) / ω) • φ t‖ + ‖(-Real.cos (ω * 0) / ω) • φ 0‖ +
          ‖∫ s in 0..t, (-Real.cos (ω * s) / ω) • φ' s‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ M₀ / ω + M₀ / ω + M₁ / ω * t :=
        add_le_add (add_le_add (hb t ⟨ht, le_rfl⟩) (hb 0 ⟨le_rfl, ht⟩)) hint
    _ = (2 * M₀ + t * M₁) / ω := by ring

/-- `‖∫₀ᵗ cos ωs • φ(s) ds‖ ≤ (2 M₀ + t M₁)/ω` for an amplitude with values in
a Banach space. -/
theorem norm_integral_cos_smul_le {φ φ' : ℝ → E} {t ω M₀ M₁ : ℝ} (ht : 0 ≤ t) (hω : 0 < ω)
    (hφ : ∀ s ∈ Icc 0 t, HasDerivAt φ (φ' s) s) (hc : ContinuousOn φ' (Icc 0 t))
    (h0 : ∀ s ∈ Icc 0 t, ‖φ s‖ ≤ M₀) (h1 : ∀ s ∈ Icc 0 t, ‖φ' s‖ ≤ M₁) :
    ‖∫ s in 0..t, Real.cos (ω * s) • φ s‖ ≤ (2 * M₀ + t * M₁) / ω := by
  have hI : uIcc 0 t = Icc 0 t := uIcc_of_le ht
  have hu : ∀ s : ℝ, HasDerivAt (fun s => Real.sin (ω * s) / ω) (Real.cos (ω * s)) s := by
    intro s
    have h := (((hasDerivAt_id s).const_mul ω).sin).div_const ω
    refine h.congr_deriv ?_
    simp only [id_eq, mul_one]
    field_simp
  have hparts := intervalIntegral.integral_smul_deriv_eq_deriv_smul (a := 0) (b := t)
    (u := fun s => Real.sin (ω * s) / ω) (u' := fun s => Real.cos (ω * s)) (v := φ)
    (v' := φ') (fun s _ => hu s) (fun s hs => hφ s (hI ▸ hs))
    ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 t)
    (ContinuousOn.intervalIntegrable (μ := volume) (hI ▸ hc : ContinuousOn φ' (uIcc 0 t)))
  have hrew : (∫ s in 0..t, Real.cos (ω * s) • φ s) =
      (Real.sin (ω * t) / ω) • φ t - (Real.sin (ω * 0) / ω) • φ 0 -
        ∫ s in 0..t, (Real.sin (ω * s) / ω) • φ' s := by
    rw [hparts]
    abel
  rw [hrew]
  have hM₀ : 0 ≤ M₀ := (norm_nonneg _).trans (h0 0 ⟨le_rfl, ht⟩)
  have hsin : ∀ s : ℝ, ‖Real.sin (ω * s) / ω‖ ≤ 1 / ω := by
    intro s
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hω]
    exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) hω.le
  have hb : ∀ s ∈ Icc 0 t, ‖(Real.sin (ω * s) / ω) • φ s‖ ≤ M₀ / ω := by
    intro s hs
    rw [norm_smul]
    calc ‖Real.sin (ω * s) / ω‖ * ‖φ s‖ ≤ 1 / ω * M₀ :=
          mul_le_mul (hsin s) (h0 s hs) (norm_nonneg _) (by positivity)
      _ = M₀ / ω := by ring
  have hint : ‖∫ s in 0..t, (Real.sin (ω * s) / ω) • φ' s‖ ≤ M₁ / ω * |t - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => ?_
    have hs' : s ∈ Icc 0 t := by
      rw [uIoc_of_le ht] at hs
      exact ⟨hs.1.le, hs.2⟩
    have hM₁ : 0 ≤ M₁ := (norm_nonneg _).trans (h1 s hs')
    rw [norm_smul]
    calc ‖Real.sin (ω * s) / ω‖ * ‖φ' s‖ ≤ 1 / ω * M₁ :=
          mul_le_mul (hsin s) (h1 s hs') (norm_nonneg _) (by positivity)
      _ = M₁ / ω := by ring
  rw [sub_zero, abs_of_nonneg ht] at hint
  calc ‖(Real.sin (ω * t) / ω) • φ t - (Real.sin (ω * 0) / ω) • φ 0 -
        ∫ s in 0..t, (Real.sin (ω * s) / ω) • φ' s‖
      ≤ ‖(Real.sin (ω * t) / ω) • φ t‖ + ‖(Real.sin (ω * 0) / ω) • φ 0‖ +
          ‖∫ s in 0..t, (Real.sin (ω * s) / ω) • φ' s‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ M₀ / ω + M₀ / ω + M₁ / ω * t :=
        add_le_add (add_le_add (hb t ⟨ht, le_rfl⟩) (hb 0 ⟨le_rfl, ht⟩)) hint
    _ = (2 * M₀ + t * M₁) / ω := by ring

/-! ### Averaging for a finite sum of harmonics -/

/-- A perturbation that is a finite sum of harmonics of the fast time:
`Σ_j (cos (n_j γ t) P_j(y) + sin (n_j γ t) Q_j(y))`. -/
def harmonics {J : Type*} [Fintype J] (n : J → ℝ) (P Q : J → E → E) (γ t : ℝ) (y : E) : E :=
  ∑ j, (Real.cos (n j * γ * t) • P j y + Real.sin (n j * γ * t) • Q j y)

/-- The method of averaging to the first order. Let the field `F` and the
amplitudes `P_j`, `Q_j` be continuously differentiable, `n_j > 0`, and let `K`
be a compact convex set. There is a constant `C` such that for every `γ > 0`,
a solution of `ż = F(z) + Σ_j (cos (n_j γ t) P_j(z) + sin (n_j γ t) Q_j(z))` and
the solution of `Ż = F(Z)` with the same initial value differ by at most `C/γ`
on `[0, L]`, as long as both stay in `K`. -/
theorem exists_forall_norm_sub_le {J : Type*} [Fintype J] {F : E → E} {P Q : J → E → E}
    {n : J → ℝ} (hF : ContDiff ℝ 1 F) (hP : ∀ j, ContDiff ℝ 1 (P j))
    (hQ : ∀ j, ContDiff ℝ 1 (Q j)) (hn : ∀ j, 0 < n j) {K : Set E} (hK : IsCompact K)
    (hconv : Convex ℝ K) (L : ℝ) :
    ∃ C : ℝ, ∀ γ : ℝ, 0 < γ → ∀ z Z : ℝ → E,
      (∀ t ∈ Icc 0 L, HasDerivAt z (F (z t) + harmonics n P Q γ t (z t)) t) →
      (∀ t ∈ Icc 0 L, HasDerivAt Z (F (Z t)) t) → (∀ t ∈ Icc 0 L, z t ∈ K) →
      (∀ t ∈ Icc 0 L, Z t ∈ K) → z 0 = Z 0 → ∀ t ∈ Icc 0 L, ‖z t - Z t‖ ≤ C / γ := by
  obtain ⟨D₀, hD₀⟩ := hK.exists_bound_of_continuousOn hF.continuous.continuousOn
  obtain ⟨KF, hKF⟩ :=
    hK.exists_bound_of_continuousOn (hF.continuous_fderiv one_ne_zero).continuousOn
  choose MP hMP using fun j => hK.exists_bound_of_continuousOn (hP j).continuous.continuousOn
  choose MQ hMQ using fun j => hK.exists_bound_of_continuousOn (hQ j).continuous.continuousOn
  choose GP hGP using fun j =>
    hK.exists_bound_of_continuousOn ((hP j).continuous_fderiv one_ne_zero).continuousOn
  choose GQ hGQ using fun j =>
    hK.exists_bound_of_continuousOn ((hQ j).continuous_fderiv one_ne_zero).continuousOn
  let M₀ : ℝ := ∑ j, (|MP j| + |MQ j|)
  let G : ℝ := ∑ j, (|GP j| + |GQ j|)
  have hM₀ : 0 ≤ M₀ := Finset.sum_nonneg fun j _ => add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hG0 : 0 ≤ G := Finset.sum_nonneg fun j _ => add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hjM : ∀ j, |MP j| + |MQ j| ≤ M₀ := fun j =>
    Finset.single_le_sum (f := fun j => |MP j| + |MQ j|)
      (fun i _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ j)
  have hjG : ∀ j, |GP j| + |GQ j| ≤ G := fun j =>
    Finset.single_le_sum (f := fun j => |GP j| + |GQ j|)
      (fun i _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ j)
  have hPb : ∀ j, ∀ y ∈ K, ‖P j y‖ ≤ M₀ := fun j y hy =>
    (hMP j y hy).trans ((le_abs_self _).trans (by linarith [hjM j, abs_nonneg (MQ j)]))
  have hQb : ∀ j, ∀ y ∈ K, ‖Q j y‖ ≤ M₀ := fun j y hy =>
    (hMQ j y hy).trans ((le_abs_self _).trans (by linarith [hjM j, abs_nonneg (MP j)]))
  have hPg : ∀ j, ∀ y ∈ K, ‖fderiv ℝ (P j) y‖ ≤ G := fun j y hy =>
    (hGP j y hy).trans ((le_abs_self _).trans (by linarith [hjG j, abs_nonneg (GQ j)]))
  have hQg : ∀ j, ∀ y ∈ K, ‖fderiv ℝ (Q j) y‖ ≤ G := fun j y hy =>
    (hGQ j y hy).trans ((le_abs_self _).trans (by linarith [hjG j, abs_nonneg (GP j)]))
  let D : ℝ := |D₀| + Fintype.card J * (2 * M₀)
  have hD0 : 0 ≤ D := add_nonneg (abs_nonneg _) (by positivity)
  have hLip : LipschitzOnWith (Real.toNNReal KF) F K :=
    LipschitzOnWith.of_dist_le' fun y₁ hy₁ y₂ hy₂ => by
      rw [dist_eq_norm, dist_eq_norm]
      exact hconv.norm_image_sub_le_of_norm_fderiv_le
        (fun y _ => hF.differentiable one_ne_zero y) hKF hy₂ hy₁
  refine ⟨(∑ j, 2 * ((2 * M₀ + L * (G * D)) / n j)) * Real.exp (Real.toNNReal KF * L), ?_⟩
  intro γ hγ z Z hz hZ hzK hZK h0 t ht
  have hL : 0 ≤ L := ht.1.trans ht.2
  have hzc : ContinuousOn z (Icc 0 L) := fun s hs => (hz s hs).continuousAt.continuousWithinAt
  have hrc : ContinuousOn (fun s => harmonics n P Q γ s (z s)) (Icc 0 L) := by
    unfold harmonics
    refine continuousOn_finsetSum _ fun j _ => ?_
    have hc : Continuous fun s : ℝ => Real.cos (n j * γ * s) := by fun_prop
    have hs : Continuous fun s : ℝ => Real.sin (n j * γ * s) := by fun_prop
    exact (hc.continuousOn.smul ((hP j).continuous.comp_continuousOn hzc)).add
      (hs.continuousOn.smul ((hQ j).continuous.comp_continuousOn hzc))
  have hspeed : ∀ s ∈ Icc 0 L, ‖F (z s) + harmonics n P Q γ s (z s)‖ ≤ D := by
    intro s hs
    have h1 : ‖harmonics n P Q γ s (z s)‖ ≤ Fintype.card J * (2 * M₀) := by
      unfold harmonics
      refine (norm_sum_le _ _).trans ?_
      have h2 : ∀ j ∈ (Finset.univ : Finset J),
          ‖Real.cos (n j * γ * s) • P j (z s) + Real.sin (n j * γ * s) • Q j (z s)‖ ≤
            2 * M₀ := by
        intro j _
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        have h3 : |Real.cos (n j * γ * s)| * ‖P j (z s)‖ ≤ 1 * M₀ :=
          mul_le_mul (Real.abs_cos_le_one _) (hPb j _ (hzK s hs)) (norm_nonneg _) zero_le_one
        have h4 : |Real.sin (n j * γ * s)| * ‖Q j (z s)‖ ≤ 1 * M₀ :=
          mul_le_mul (Real.abs_sin_le_one _) (hQb j _ (hzK s hs)) (norm_nonneg _) zero_le_one
        linarith
      refine (Finset.sum_le_sum h2).trans ?_
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    refine (norm_add_le _ _).trans (add_le_add ?_ h1)
    exact (hD₀ _ (hzK s hs)).trans (le_abs_self _)
  have hδ : ∀ x ∈ Icc 0 L, ‖∫ u in 0..x, harmonics n P Q γ u (z u)‖ ≤
      (∑ j, 2 * ((2 * M₀ + L * (G * D)) / n j)) / γ := by
    intro x hx
    have hsub : Icc 0 x ⊆ Icc 0 L := Icc_subset_Icc_right hx.2
    have hI : uIcc 0 x = Icc 0 x := uIcc_of_le hx.1
    have hzc' : ContinuousOn z (Icc 0 x) := hzc.mono hsub
    have hvel : ContinuousOn (fun s => F (z s) + harmonics n P Q γ s (z s)) (Icc 0 x) :=
      (hF.continuous.comp_continuousOn hzc').add (hrc.mono hsub)
    have hterm : ∀ j, ‖(∫ u in 0..x, Real.cos (n j * γ * u) • P j (z u)) +
        ∫ u in 0..x, Real.sin (n j * γ * u) • Q j (z u)‖ ≤
          2 * ((2 * M₀ + L * (G * D)) / n j) / γ := by
      intro j
      have hω : 0 < n j * γ := mul_pos (hn j) hγ
      have hbound : (2 * M₀ + x * (G * D)) / (n j * γ) ≤
          (2 * M₀ + L * (G * D)) / n j / γ := by
        rw [div_div]
        exact div_le_div_of_nonneg_right (add_le_add le_rfl
          (mul_le_mul_of_nonneg_right hx.2 (mul_nonneg hG0 hD0))) hω.le
      have hc := norm_integral_cos_smul_le (φ := fun u => P j (z u))
        (φ' := fun u => fderiv ℝ (P j) (z u) (F (z u) + harmonics n P Q γ u (z u)))
        (M₀ := M₀) (M₁ := G * D) hx.1 hω
        (fun u hu => ((hP j).differentiable one_ne_zero (z u)).hasFDerivAt.comp_hasDerivAt u
          (hz u (hsub hu)))
        ((((hP j).continuous_fderiv one_ne_zero).comp_continuousOn hzc').clm_apply hvel)
        (fun u hu => hPb j _ (hzK u (hsub hu)))
        (fun u hu => (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul (hPg j _ (hzK u (hsub hu))) (hspeed u (hsub hu)) (norm_nonneg _) hG0))
      have hs := norm_integral_sin_smul_le (φ := fun u => Q j (z u))
        (φ' := fun u => fderiv ℝ (Q j) (z u) (F (z u) + harmonics n P Q γ u (z u)))
        (M₀ := M₀) (M₁ := G * D) hx.1 hω
        (fun u hu => ((hQ j).differentiable one_ne_zero (z u)).hasFDerivAt.comp_hasDerivAt u
          (hz u (hsub hu)))
        ((((hQ j).continuous_fderiv one_ne_zero).comp_continuousOn hzc').clm_apply hvel)
        (fun u hu => hQb j _ (hzK u (hsub hu)))
        (fun u hu => (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul (hQg j _ (hzK u (hsub hu))) (hspeed u (hsub hu)) (norm_nonneg _) hG0))
      have e : 2 * ((2 * M₀ + L * (G * D)) / n j) / γ =
          (2 * M₀ + L * (G * D)) / n j / γ + (2 * M₀ + L * (G * D)) / n j / γ := by ring
      rw [e]
      exact (norm_add_le _ _).trans (add_le_add (hc.trans hbound) (hs.trans hbound))
    have hcj : ∀ j, ContinuousOn (fun u : ℝ => Real.cos (n j * γ * u) • P j (z u)) (uIcc 0 x) :=
      fun j => by
        have hc : Continuous fun s : ℝ => Real.cos (n j * γ * s) := by fun_prop
        rw [hI]
        exact hc.continuousOn.smul ((hP j).continuous.comp_continuousOn hzc')
    have hsj : ∀ j, ContinuousOn (fun u : ℝ => Real.sin (n j * γ * u) • Q j (z u)) (uIcc 0 x) :=
      fun j => by
        have hs : Continuous fun s : ℝ => Real.sin (n j * γ * s) := by fun_prop
        rw [hI]
        exact hs.continuousOn.smul ((hQ j).continuous.comp_continuousOn hzc')
    have hint : (∫ u in 0..x, harmonics n P Q γ u (z u)) =
        ∑ j, ((∫ u in 0..x, Real.cos (n j * γ * u) • P j (z u)) +
          ∫ u in 0..x, Real.sin (n j * γ * u) • Q j (z u)) := by
      unfold harmonics
      rw [intervalIntegral.integral_finsetSum fun j _ =>
        ((hcj j).intervalIntegrable).add ((hsj j).intervalIntegrable)]
      exact Finset.sum_congr rfl fun j _ =>
        intervalIntegral.integral_add (hcj j).intervalIntegrable (hsj j).intervalIntegrable
    rw [hint, Finset.sum_div]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hterm j)
  have hcomp := norm_sub_le_of_norm_integral_le' hLip hrc hz hZ hzK hZK hδ h0 t ht
  have hsum0 : 0 ≤ ∑ j, 2 * ((2 * M₀ + L * (G * D)) / n j) :=
    Finset.sum_nonneg fun j _ => mul_nonneg zero_le_two
      (div_nonneg (add_nonneg (by positivity) (mul_nonneg hL (mul_nonneg hG0 hD0))) (hn j).le)
  refine hcomp.trans ?_
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hγ]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left ht.2 (Real.toNNReal KF).coe_nonneg)) hsum0

end ProjectAinos.SmoothGeometry.Averaging
