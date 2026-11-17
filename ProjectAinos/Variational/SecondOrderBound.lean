/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.Compactness.Compact

/-!
# The remainder of the first-order expansion

* `abs_sub_sub_le_of_abs_le`: if `|f″| ≤ M` on `[−δ, δ]`, then
  `|f(ε) − f(0) − ε f′(0)| ≤ M ε²` for `|ε| ≤ δ`.
* `exists_pos_forall_abs_le_mem`: an open set that contains `{0} × K` for a
  compact `K` contains `[−δ, δ] × K`.
* `exists_second_order_bound`: for a function of `ε` and a parameter that is
  twice continuously differentiable at the points `(0, l)` with `l` in a compact
  set, the same bound holds with one `δ` and one `M` for all these `l`.
-/

@[expose] public section
noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace ProjectAinos.Variational

/-- The remainder of the first-order expansion at zero is at most `M ε²` if the
second derivative is at most `M`. -/
theorem abs_sub_sub_le_of_abs_le {f f' f'' : ℝ → ℝ} {δ M : ℝ}
    (hf : ∀ x ∈ Icc (-δ) δ, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Icc (-δ) δ, HasDerivAt f' (f'' x) x)
    (hM : ∀ x ∈ Icc (-δ) δ, |f'' x| ≤ M) {ε : ℝ} (hε : |ε| ≤ δ) :
    |f ε - f 0 - ε * f' 0| ≤ M * ε ^ 2 := by
  have hδ : 0 ≤ δ := (abs_nonneg ε).trans hε
  have h0 : (0 : ℝ) ∈ Icc (-δ) δ := ⟨by linarith, hδ⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 h0)
  have hderiv_bound : ∀ x ∈ Icc (-δ) δ, |f' x - f' 0| ≤ M * |x| := by
    intro x hx
    have h := (convex_Icc (-δ) δ).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := f') (fun y hy => (hf' y hy).hasDerivWithinAt)
      (fun y hy => by rw [Real.norm_eq_abs]; exact hM y hy) h0 hx
    simpa [Real.norm_eq_abs] using h
  obtain ⟨R, hR⟩ : ∃ R : ℝ → ℝ, R = fun x => f x - f 0 - x * f' 0 := ⟨_, rfl⟩
  have hRd : ∀ x ∈ Icc (-|ε|) |ε|, HasDerivWithinAt R (f' x - f' 0) (Icc (-|ε|) |ε|) x := by
    intro x hx
    have hx' : x ∈ Icc (-δ) δ := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have h1 : HasDerivAt (fun y => f y - f 0 - y * f' 0) (f' x - f' 0) x := by
      have h2 := ((hf x hx').sub_const (f 0)).sub ((hasDerivAt_id x).mul_const (f' 0))
      refine h2.congr_deriv ?_
      simp
    rw [hR]
    exact h1.hasDerivWithinAt
  have hRb : ∀ x ∈ Icc (-|ε|) |ε|, ‖f' x - f' 0‖ ≤ M * |ε| := by
    intro x hx
    have hx' : x ∈ Icc (-δ) δ := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    rw [Real.norm_eq_abs]
    exact (hderiv_bound x hx').trans (mul_le_mul_of_nonneg_left (abs_le.mpr hx) hM0)
  have h0ε : (0 : ℝ) ∈ Icc (-|ε|) |ε| := ⟨by linarith [abs_nonneg ε], abs_nonneg ε⟩
  have hεε : ε ∈ Icc (-|ε|) |ε| := ⟨neg_abs_le ε, le_abs_self ε⟩
  have h := (convex_Icc (-|ε|) |ε|).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := R) hRd hRb h0ε hεε
  have hR0 : R 0 = 0 := by rw [hR]; simp
  rw [hR0, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, sub_zero] at h
  have hRε : R ε = f ε - f 0 - ε * f' 0 := by rw [hR]
  rw [← hRε]
  calc |R ε| ≤ M * |ε| * |ε| := h
    _ = M * ε ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

/-- An open set that contains `{0} × K` for a compact set `K` contains
`[−δ, δ] × K` for some `δ > 0`. -/
theorem exists_pos_forall_abs_le_mem {Q : Type*} [TopologicalSpace Q] {K : Set Q}
    (hK : IsCompact K) {U : Set (ℝ × Q)} (hU : IsOpen U) (h : ∀ l ∈ K, ((0 : ℝ), l) ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ l ∈ K, ∀ ε : ℝ, |ε| ≤ δ → (ε, l) ∈ U := by
  obtain ⟨S, W, hS, _, h0S, hKW, hSW⟩ := generalized_tube_lemma
    (isCompact_singleton (x := (0 : ℝ))) hK hU (by
      rintro ⟨e, l⟩ ⟨he, hl⟩
      rw [mem_singleton_iff] at he
      subst he
      exact h l hl)
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.isOpen_iff.mp hS 0 (h0S rfl)
  refine ⟨δ₀ / 2, by positivity, fun l hl ε hε => hSW ⟨hball ?_, hKW hl⟩⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero]
  linarith

variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]

/-- The remainder of the first-order expansion in `ε`, uniformly for the
parameter in a compact set. -/
theorem exists_second_order_bound {f : ℝ × Q → ℝ} {K : Set Q} (hK : IsCompact K)
    (hf : ∀ l ∈ K, ContDiffAt ℝ 2 f (0, l)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, ∀ l ∈ K, ∀ ε : ℝ, |ε| ≤ δ →
      |f (ε, l) - f (0, l) - ε * deriv (fun e => f (e, l)) 0| ≤ M * ε ^ 2 := by
  have hU : IsOpen {p : ℝ × Q | ContDiffAt ℝ 2 f p} :=
    isOpen_iff_mem_nhds.mpr fun p hp =>
      (show ContDiffAt ℝ 2 f p from hp).eventually (by norm_num)
  obtain ⟨δ, hδ, hδU⟩ := exists_pos_forall_abs_le_mem hK hU hf
  have hIcc : ∀ e ∈ Icc (-δ) δ, ∀ l ∈ K, ContDiffAt ℝ 2 f (e, l) := fun e he l hl =>
    hδU l hl e (abs_le.mpr he)
  obtain ⟨D₁, hD₁⟩ : ∃ D₁ : ℝ × Q → ℝ, D₁ = fun p => fderiv ℝ f p (1, 0) := ⟨_, rfl⟩
  obtain ⟨D₂, hD₂⟩ : ∃ D₂ : ℝ × Q → ℝ, D₂ = fun p => fderiv ℝ D₁ p (1, 0) := ⟨_, rfl⟩
  have hline : ∀ (e : ℝ) (l : Q),
      HasDerivAt (fun x : ℝ => ((x, l) : ℝ × Q)) ((1 : ℝ), (0 : Q)) e := fun e l =>
    (hasDerivAt_id e).prodMk (hasDerivAt_const e l)
  have hD₁c : ∀ p : ℝ × Q, ContDiffAt ℝ 2 f p → ContDiffAt ℝ 1 D₁ p := fun p hp => by
    have h2 : ContDiffAt ℝ (1 + 1) f p := by
      rw [one_add_one_eq_two]
      exact hp
    rw [hD₁]
    exact (h2.fderiv_right (m := 1) le_rfl).clm_apply contDiffAt_const
  have hd₁ : ∀ e ∈ Icc (-δ) δ, ∀ l ∈ K,
      HasDerivAt (fun x => f (x, l)) (D₁ (e, l)) e := fun e he l hl => by
    have h1 : HasFDerivAt f (fderiv ℝ f (e, l)) (e, l) :=
      ((hIcc e he l hl).differentiableAt (by norm_num)).hasFDerivAt
    have h2 := HasFDerivAt.comp_hasDerivAt e h1 (hline e l)
    rw [hD₁]
    exact h2
  have hd₂ : ∀ e ∈ Icc (-δ) δ, ∀ l ∈ K,
      HasDerivAt (fun x => D₁ (x, l)) (D₂ (e, l)) e := fun e he l hl => by
    have h1 : HasFDerivAt D₁ (fderiv ℝ D₁ (e, l)) (e, l) :=
      ((hD₁c _ (hIcc e he l hl)).differentiableAt one_ne_zero).hasFDerivAt
    have h2 := HasFDerivAt.comp_hasDerivAt e h1 (hline e l)
    rw [hD₂]
    exact h2
  have hcont : ContinuousOn D₂ (Icc (-δ) δ ×ˢ K) := by
    rintro ⟨e, l⟩ ⟨he, hl⟩
    rw [hD₂]
    exact (((hD₁c _ (hIcc e he l hl)).continuousAt_fderiv one_ne_zero).clm_apply
      continuousAt_const).continuousWithinAt
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hcont
  refine ⟨δ, hδ, M, fun l hl ε hε => ?_⟩
  have h0 : (0 : ℝ) ∈ Icc (-δ) δ := ⟨by linarith, hδ.le⟩
  have h := abs_sub_sub_le_of_abs_le (f := fun x => f (x, l)) (f' := fun x => D₁ (x, l))
    (f'' := fun x => D₂ (x, l)) (fun e he => hd₁ e he l hl) (fun e he => hd₂ e he l hl)
    (fun e he => by
      have := hM (e, l) ⟨he, hl⟩
      rwa [Real.norm_eq_abs] at this) hε
  rw [(hd₁ 0 h0 l hl).deriv]
  exact h

end ProjectAinos.Variational
