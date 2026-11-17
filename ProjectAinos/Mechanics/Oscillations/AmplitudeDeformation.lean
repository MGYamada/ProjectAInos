/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Mechanics.Oscillations.AmplitudeSystem

/-!
# The amplitude system on a line parallel to the real axis

The coefficient of the amplitude system on the line `Im z = σ` contains the
factors `e^{∓2σ/ε}`. The change of the first unknown by the factor
`κ = e^{−2σ/ε}` (`scaleFst`, `propagator_scaleFst`) removes them: the new
coefficient is bounded by `|g|`, and the entry of the propagator that takes
the second unknown to the first is `κ` times a bounded number. By
`SmoothGeometry.LinearODE.norm_propagator_apply_sub_le_of_deformation` the
propagators on the lines of the heights `0` and `σ` differ by a term that is
bounded by the coefficient at the two ends. Hence
(`exists_norm_fst_propagator_le`), for the system on the real line between
`s₀` and `s₁`,

`|β| ≤ e^{G − 2σ/ε} + C e^{e^{2σ/ε} G} e^{2σ/ε} (m(s₁) + m(s₀))`,

where `β` is the first component of the solution with the initial value
`(0, 1)`, `|g(s + iη)| ≤ m(s)` on the strip and `∫ m ≤ G`.
-/

@[expose] public section
noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace ProjectAinos.Mechanics.AdiabaticAmplitude

open Complex (I)
open SmoothGeometry.LinearODE

/-! ### Coefficients with two continuous entries -/

theorem continuous_offDiag {a b : ℝ → ℂ} (ha : Continuous a) (hb : Continuous b) :
    Continuous fun s => offDiag (a s) (b s) := by
  rw [continuous_clm_apply]
  intro y
  exact (ha.mul continuous_const).prodMk (hb.mul continuous_const)

/-- The coefficient `s ↦ offDiag (a s) (b s)` of a linear equation. -/
def offDiagCurve (a b : ℝ → ℂ) (ha : Continuous a) (hb : Continuous b) :
    C(ℝ, ℂ × ℂ →L[ℝ] ℂ × ℂ) :=
  ⟨fun s => offDiag (a s) (b s), continuous_offDiag ha hb⟩

theorem offDiagCurve_apply (a b : ℝ → ℂ) (ha : Continuous a) (hb : Continuous b) (s : ℝ) :
    offDiagCurve a b ha hb s = offDiag (a s) (b s) := rfl

/-- The map `(u, w) ↦ (κ u, w)`. -/
def scaleFst (κ : ℂ) : ℂ × ℂ →L[ℝ] ℂ × ℂ :=
  ((ContinuousLinearMap.mul ℝ ℂ κ).comp (ContinuousLinearMap.fst ℝ ℂ ℂ)).prod
    (ContinuousLinearMap.snd ℝ ℂ ℂ)

theorem scaleFst_apply (κ : ℂ) (y : ℂ × ℂ) : scaleFst κ y = (κ * y.1, y.2) := rfl

theorem offDiag_scaleFst {κ : ℂ} (hκ : κ ≠ 0) (a b : ℂ) (y : ℂ × ℂ) :
    offDiag a b (scaleFst κ y) = scaleFst κ (offDiag (κ⁻¹ * a) (κ * b) y) := by
  rw [offDiag_apply, scaleFst_apply, scaleFst_apply, offDiag_apply, Prod.mk.injEq]
  constructor
  · change a * y.2 = κ * (κ⁻¹ * a * y.2)
    rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hκ, one_mul]
  · change b * (κ * y.1) = κ * b * y.1
    ring

/-- The change of the first unknown by a constant factor. -/
theorem propagator_scaleFst {κ : ℂ} (hκ : κ ≠ 0) {a b : ℝ → ℂ} (ha : Continuous a)
    (hb : Continuous b) (ha' : Continuous fun s => κ⁻¹ * a s)
    (hb' : Continuous fun s => κ * b s) (s₁ s₀ : ℝ) (y₀ : ℂ × ℂ) :
    propagator (offDiagCurve a b ha hb) s₁ s₀ (scaleFst κ y₀) =
      scaleFst κ (propagator
        (offDiagCurve (fun s => κ⁻¹ * a s) (fun s => κ * b s) ha' hb') s₁ s₀ y₀) := by
  have hf : ∀ s : ℝ, HasDerivAt
      (fun s => scaleFst κ (propagator
        (offDiagCurve (fun s => κ⁻¹ * a s) (fun s => κ * b s) ha' hb') s s₀ y₀))
      (offDiagCurve a b ha hb s (scaleFst κ (propagator
        (offDiagCurve (fun s => κ⁻¹ * a s) (fun s => κ * b s) ha' hb') s s₀ y₀))) s := by
    intro s
    have h1 := (scaleFst κ).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_propagator_apply
      (offDiagCurve (fun s => κ⁻¹ * a s) (fun s => κ * b s) ha' hb') s s₀ y₀)
    exact h1.congr_deriv (offDiag_scaleFst hκ (a s) (b s) _).symm
  have h := eq_propagator_apply_of_hasDerivAt (offDiagCurve a b ha hb)
    (f := fun s => scaleFst κ (propagator
      (offDiagCurve (fun s => κ⁻¹ * a s) (fun s => κ * b s) ha' hb') s s₀ y₀))
    (s := s₀) (t := s₁)
    (continuous_iff_continuousAt.mpr fun s => (hf s).continuousAt).continuousOn
    (fun s _ => hf s)
  rw [propagator_self] at h
  exact h.symm

/-- A bound for a solution of a system whose coefficient is bounded by `m`. -/
theorem norm_propagator_offDiagCurve_le {a b : ℝ → ℂ} (ha : Continuous a) (hb : Continuous b)
    {m : ℝ → ℝ} (hm : Continuous m) (ham : ∀ s, ‖a s‖ ≤ m s) (hbm : ∀ s, ‖b s‖ ≤ m s)
    {G : ℝ} (hG : ∀ s₀ s₁ : ℝ, s₀ ≤ s₁ → ∫ r in s₀..s₁, m r ≤ G) {s₀ s₁ : ℝ} (hs : s₀ ≤ s₁)
    (y : ℂ × ℂ) : ‖propagator (offDiagCurve a b ha hb) s₁ s₀ y‖ ≤ Real.exp G * ‖y‖ := by
  have h1 := norm_propagator_apply_le_exp_integral (offDiagCurve a b ha hb) hs y
  have h2 : ∫ r in s₀..s₁, ‖offDiagCurve a b ha hb r‖ ≤ G :=
    (intervalIntegral.integral_mono_on hs
      ((offDiagCurve a b ha hb).continuous.norm.intervalIntegrable _ _)
      (hm.intervalIntegrable _ _)
      fun r _ => norm_offDiag_le _ _ (ham r) (hbm r)).trans (hG s₀ s₁ hs)
  rw [mul_comm]
  exact h1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h2) (norm_nonneg y))

/-! ### The estimate on the real line -/

section Estimate

variable {g : ℂ → ℂ} {U : Set ℂ} {σ ε : ℝ}

/-- The coefficient on a line, as a coefficient with two continuous entries. -/
theorem coefficientCurve_family (hc : Continuous (family g ε σ)) (p : ℝ)
    (hp : Continuous fun s : ℝ => coeffPlus g ε (path σ (p, s)))
    (hm : Continuous fun s : ℝ => coeffMinus g ε (path σ (p, s))) :
    coefficientCurve (family g ε σ) hc p =
      offDiagCurve (fun s => coeffPlus g ε (path σ (p, s)))
        (fun s => coeffMinus g ε (path σ (p, s))) hp hm :=
  ContinuousMap.ext fun _ => rfl

/-- On the line of the height `σ` the entry of the propagator from the second
unknown to the first is at most `e^{G} e^{−2σ/ε}`. -/
theorem norm_fst_propagator_top_le (hc : Continuous (family g ε σ))
    (hcp : Continuous fun q => coeffPlus g ε (path σ q))
    (hcm : Continuous fun q => coeffMinus g ε (path σ q)) {m : ℝ → ℝ} (hm : Continuous m)
    (hbound : ∀ q : ℝ × ℝ, ‖g (path σ q)‖ ≤ m q.2) {G : ℝ}
    (hG : ∀ s₀ s₁ : ℝ, s₀ ≤ s₁ → ∫ r in s₀..s₁, m r ≤ G) {s₀ s₁ : ℝ} (hs : s₀ ≤ s₁) :
    ‖(propagator (coefficientCurve (family g ε σ) hc 1) s₁ s₀ (0, 1)).1‖ ≤
      Real.exp G * (Real.exp (2 / ε * σ))⁻¹ := by
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = Real.exp (2 / ε * σ) := ⟨_, rfl⟩
  have hE : 0 < E := by
    rw [hEdef]
    exact Real.exp_pos _
  rw [← hEdef]
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℂ, κ = ((E⁻¹ : ℝ) : ℂ) := ⟨_, rfl⟩
  have hκn : ‖κ‖ = E⁻¹ := by
    rw [hκdef, Complex.norm_real, Real.norm_of_nonneg (inv_pos.mpr hE).le]
  have hκ : κ ≠ 0 := by
    rw [← norm_pos_iff, hκn]
    exact inv_pos.mpr hE
  have hline : Continuous fun s : ℝ => (((1 : ℝ), s) : ℝ × ℝ) :=
    continuous_const.prodMk continuous_id
  have ha : Continuous fun s : ℝ => coeffPlus g ε (path σ (1, s)) := hcp.comp hline
  have hb : Continuous fun s : ℝ => coeffMinus g ε (path σ (1, s)) := hcm.comp hline
  have ha' : Continuous fun s : ℝ => κ⁻¹ * coeffPlus g ε (path σ (1, s)) :=
    continuous_const.mul ha
  have hb' : Continuous fun s : ℝ => κ * coeffMinus g ε (path σ (1, s)) :=
    continuous_const.mul hb
  have him : ∀ s : ℝ, (path σ (1, s)).im = σ := fun s => by
    rw [path_im, Real.smoothTransition.one_of_one_le le_rfl, mul_one]
  have ham : ∀ s : ℝ, ‖κ⁻¹ * coeffPlus g ε (path σ (1, s))‖ ≤ m s := fun s => by
    rw [norm_mul, norm_inv, hκn, inv_inv, norm_coeffPlus, him, Real.exp_neg, ← hEdef]
    have e : E * (‖g (path σ (1, s))‖ * E⁻¹) = ‖g (path σ (1, s))‖ := by field_simp
    rw [e]
    exact hbound (1, s)
  have hbm : ∀ s : ℝ, ‖κ * coeffMinus g ε (path σ (1, s))‖ ≤ m s := fun s => by
    rw [norm_mul, hκn, norm_coeffMinus, him, ← hEdef]
    have e : E⁻¹ * (‖g (path σ (1, s))‖ * E) = ‖g (path σ (1, s))‖ := by field_simp
    rw [e]
    exact hbound (1, s)
  have hy : ((0 : ℂ), (1 : ℂ)) = scaleFst κ (0, 1) := by
    rw [scaleFst_apply, mul_zero]
  have hnorm : ‖((0 : ℂ), (1 : ℂ))‖ = 1 := by simp [Prod.norm_def]
  have hprop := norm_propagator_offDiagCurve_le ha' hb' hm ham hbm hG hs ((0 : ℂ), (1 : ℂ))
  rw [hnorm, mul_one] at hprop
  rw [coefficientCurve_family hc 1 ha hb, hy, propagator_scaleFst hκ ha hb ha' hb',
    scaleFst_apply]
  change ‖κ * _‖ ≤ _
  rw [norm_mul, hκn, mul_comm]
  exact mul_le_mul_of_nonneg_right ((norm_fst_le _).trans hprop) (inv_pos.mpr hE).le

/-- The entry of the propagator on the real line from the second unknown to
the first: exponentially small, up to a term that is bounded by the
coefficient at the two ends. -/
theorem exists_norm_fst_propagator_le (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
    (hσ : 0 ≤ σ) (hmem : ∀ q, path σ q ∈ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ) (_ : 0 < ε) (m : ℝ → ℝ), Continuous m →
      (∀ q : ℝ × ℝ, ‖g (path σ q)‖ ≤ m q.2) → ∀ G : ℝ,
      (∀ s₀ s₁ : ℝ, s₀ ≤ s₁ → ∫ r in s₀..s₁, m r ≤ G) → ∀ s₀ s₁ : ℝ, s₀ ≤ s₁ →
      ‖(propagator (coefficientCurve (family g ε σ)
          (contDiff_family hU hg hmem ε).continuous 0) s₁ s₀ (0, 1)).1‖ ≤
        Real.exp G * (Real.exp (2 / ε * σ))⁻¹ +
          C * (Real.exp (Real.exp (2 / ε * σ) * G) *
            (Real.exp (2 / ε * σ) * (m s₁ + m s₀))) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_pathSpeed_le σ
  refine ⟨C, hC0, fun ε hε m hm hbound G hG s₀ s₁ hs => ?_⟩
  have hA := contDiff_family hU hg hmem ε
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = Real.exp (2 / ε * σ) := ⟨_, rfl⟩
  have hE : 0 < E := by
    rw [hEdef]
    exact Real.exp_pos _
  rw [← hEdef]
  have hfam : ∀ q : ℝ × ℝ, ‖family g ε σ q‖ ≤ m q.2 * E := fun q => by
    rw [hEdef]
    exact (norm_coeff_le g hε (path_im_nonneg hσ q) (path_im_le hσ q)).trans
      (mul_le_mul_of_nonneg_right (hbound q) (Real.exp_pos _).le)
  have hK : ∀ p ∈ Icc (0 : ℝ) 1, ∀ y : ℂ × ℂ,
      ‖propagator (coefficientCurve (family g ε σ) hA.continuous p) s₁ s₀ y‖ ≤
        Real.exp (E * G) * ‖y‖ := by
    intro p _ y
    have h1 := norm_propagator_apply_le_exp_integral
      (coefficientCurve (family g ε σ) hA.continuous p) hs y
    have h2 : ∫ r in s₀..s₁, ‖coefficientCurve (family g ε σ) hA.continuous p r‖ ≤ E * G := by
      have hmE : Continuous fun r => m r * E := hm.mul continuous_const
      have h3 := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
        (g := fun r => m r * E) hs
        ((coefficientCurve (family g ε σ) hA.continuous p).continuous.norm.intervalIntegrable
          _ _)
        (hmE.intervalIntegrable _ _) (fun r _ => hfam (p, r))
      rw [intervalIntegral.integral_mul_const] at h3
      exact h3.trans ((mul_comm _ _).le.trans (mul_le_mul_of_nonneg_left (hG s₀ s₁ hs) hE.le))
    rw [mul_comm]
    exact h1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h2) (norm_nonneg y))
  have hdef := norm_propagator_apply_sub_le_of_deformation hA mulI (pathSpeed σ)
    (family_mulI g ε σ) (fun q v => fderiv_family_one_zero hU hg hmem ε q v)
    (p₀ := 0) (p₁ := 1) (s₀ := s₀) (s₁ := s₁) (C := C) (K := Real.exp (E * G))
    (M₀ := m s₀ * E) (M₁ := m s₁ * E) zero_le_one (Real.exp_pos _).le norm_mulI_le hC hK
    (fun p _ => hfam (p, s₀)) (fun p _ => hfam (p, s₁)) ((0 : ℂ), (1 : ℂ))
  have hnorm : ‖((0 : ℂ), (1 : ℂ))‖ = 1 := by simp [Prod.norm_def]
  rw [hnorm] at hdef
  have htop := norm_fst_propagator_top_le hA.continuous
    (contDiff_comp_path hU (differentiableOn_coeffPlus hg ε) hmem).continuous
    (contDiff_comp_path hU (differentiableOn_coeffMinus hg ε) hmem).continuous hm hbound hG hs
  rw [← hEdef] at htop
  have hsplit : (propagator (coefficientCurve (family g ε σ) hA.continuous 0) s₁ s₀ (0, 1)).1 =
      (propagator (coefficientCurve (family g ε σ) hA.continuous 1) s₁ s₀ (0, 1)).1 -
        (propagator (coefficientCurve (family g ε σ) hA.continuous 1) s₁ s₀ (0, 1) -
          propagator (coefficientCurve (family g ε σ) hA.continuous 0) s₁ s₀ (0, 1)).1 := by
    rw [Prod.fst_sub, sub_sub_cancel]
  rw [hsplit]
  refine (norm_sub_le _ _).trans (add_le_add htop ((norm_fst_le _).trans (hdef.trans ?_)))
  refine le_of_eq ?_
  ring

end Estimate

end ProjectAinos.Mechanics.AdiabaticAmplitude
