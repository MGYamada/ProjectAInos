/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.ODE.Superposition
public import ProjectAInos.SmoothGeometry.ODE.VolterraInverse
public import ProjectAInos.SmoothAlgebra.ImplicitFunction
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# The integral equation of a flow on the unit interval

The solution of `ẋ = X(x)` through `x`, traversed up to the time `τ`, is a
curve `γ` on the unit interval with

`γ(σ) = x + τ ∫₀^σ X(γ(s)) ds`.

The time is a factor in the equation, not the length of an interval, so one
Banach space of curves serves for all times of both signs.

* `IsFlowCurve X τ x γ` is this equation. A flow curve is unique for a
  continuously differentiable field, the curve `σ ↦ γ(cσ)` is the flow curve
  of the time `cτ`, and a solution of the differential equation between the
  times `0` and `t` gives a flow curve of the time `t`.
* `equation X` is the map `((τ, x), γ) ↦ γ − x − τ ∫ X(γ)` into the curves. It
  is smooth for a smooth field, and its derivative in `γ` is the equation
  operator of the linear equation with the coefficient `τ DX(γ)`, which is
  invertible for every coefficient. So every flow curve belongs to a smooth
  family of flow curves on an open set of times and points
  (`exists_local_family`).
-/

@[expose] public section
noncomputable section

open Set Filter ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff

namespace ProjectAInos.SmoothGeometry.NonlinearODE

open LinearODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {X : E → E} {τ : ℝ} {x : E} {γ : Curve E}

/-! ### Flow curves -/

/-- A curve on the unit interval that solves `γ(σ) = x + τ ∫₀^σ X(γ(s)) ds`. -/
def IsFlowCurve (X : E → E) (τ : ℝ) (x : E) (γ : Curve E) : Prop :=
  ∀ σ : unitInterval, γ σ = x + τ • ∫ s in (0 : ℝ)..σ, X (extend γ s)

omit [CompleteSpace E] in
theorem mul_mem_Icc {c s : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    c * s ∈ Icc (0 : ℝ) 1 :=
  ⟨mul_nonneg hc.1 hs.1, (mul_le_mul hc.2 hs.2 hs.1 zero_le_one).trans_eq (one_mul 1)⟩

theorem mul_mem_uIcc (t : ℝ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : t * s ∈ uIcc 0 t := by
  rcases le_total 0 t with ht | ht
  · rw [uIcc_of_le ht]
    exact ⟨mul_nonneg ht hs.1, mul_le_of_le_one_right ht hs.2⟩
  · rw [uIcc_of_ge ht]
    exact ⟨le_mul_of_le_one_right ht hs.2, mul_nonpos_of_nonpos_of_nonneg ht hs.1⟩

namespace IsFlowCurve

omit [CompleteSpace E] in
/-- The equation at a real point of the unit interval. -/
theorem extend_eq (h : IsFlowCurve X τ x γ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    extend γ s = x + τ • ∫ r in (0 : ℝ)..s, X (extend γ r) :=
  (extend_coe γ ⟨s, hs⟩).trans (h ⟨s, hs⟩)

omit [CompleteSpace E] in
theorem apply_zero (h : IsFlowCurve X τ x γ) : γ 0 = x := by
  have h0 := h 0
  simpa using h0

omit [CompleteSpace E] in
theorem extend_zero (h : IsFlowCurve X τ x γ) : extend γ 0 = x := by
  have h0 := h.extend_eq ⟨le_rfl, zero_le_one⟩
  simpa using h0

/-- A flow curve solves `γ′ = τ X(γ)` on the unit interval, with one-sided
derivatives at the two ends. -/
theorem hasDerivWithinAt (h : IsFlowCurve X τ x γ) (hX : Continuous X) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (extend γ) (τ • X (extend γ s)) (Icc 0 1) s := by
  have hc : Continuous fun r => X (extend γ r) := hX.comp (extend_continuous γ)
  have hR : HasDerivAt (fun u => x + τ • ∫ r in (0 : ℝ)..u, X (extend γ r))
      (τ • X (extend γ s)) s :=
    ((hc.integral_hasStrictDerivAt 0 s).hasDerivAt.const_smul τ).const_add x
  exact hR.hasDerivWithinAt.congr (fun r hr => h.extend_eq hr) (h.extend_eq hs)

/-- A flow curve is unique. -/
theorem eq (hX : ContDiff ℝ 1 X) {γ₁ γ₂ : Curve E} (h₁ : IsFlowCurve X τ x γ₁)
    (h₂ : IsFlowCurve X τ x γ₂) : γ₁ = γ₂ := by
  have hY : ContDiff ℝ 1 fun y => τ • X y := contDiff_const.smul hX
  have hK : IsCompact (range γ₁ ∪ range γ₂) :=
    (isCompact_range γ₁.continuous).union (isCompact_range γ₂.continuous)
  obtain ⟨C, hC⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK
    hY.locallyLipschitz.locallyLipschitzOn
  have hmem : ∀ r ∈ Ico (0 : ℝ) 1, Icc (0 : ℝ) 1 ∈ 𝓝[≥] r := fun r hr =>
    Icc_mem_nhdsGE_of_mem hr
  have he : EqOn (extend γ₁) (extend γ₂) (Icc 0 1) :=
    ODE_solution_unique_of_mem_Icc_right (v := fun _ y => τ • X y)
      (s := fun _ => range γ₁ ∪ range γ₂) (K := C) (fun _ _ => hC)
      (extend_continuous γ₁).continuousOn
      (fun r hr => (h₁.hasDerivWithinAt hX.continuous ⟨hr.1, hr.2.le⟩).mono_of_mem_nhdsWithin
        (hmem r hr))
      (fun r _ => Or.inl (mem_range_self _))
      (extend_continuous γ₂).continuousOn
      (fun r hr => (h₂.hasDerivWithinAt hX.continuous ⟨hr.1, hr.2.le⟩).mono_of_mem_nhdsWithin
        (hmem r hr))
      (fun r _ => Or.inr (mem_range_self _))
      (h₁.extend_zero.trans h₂.extend_zero.symm)
  ext σ
  rw [← extend_coe γ₁ σ, ← extend_coe γ₂ σ]
  exact he σ.2

end IsFlowCurve

omit [CompleteSpace E] in
/-- The constant curve is the flow curve of the time zero. -/
theorem isFlowCurve_const (X : E → E) (x : E) :
    IsFlowCurve X 0 x (ContinuousMap.const unitInterval x) := by
  intro σ
  simp

/-- The curve `σ ↦ γ(cσ)`. -/
def rescale (γ : Curve E) (c : ℝ) : Curve E :=
  ⟨fun σ => extend γ (c * σ), (extend_continuous γ).comp (by fun_prop)⟩

omit [NormedSpace ℝ E] [CompleteSpace E] in
@[simp] theorem rescale_apply (γ : Curve E) (c : ℝ) (σ : unitInterval) :
    rescale γ c σ = extend γ (c * σ) := rfl

omit [CompleteSpace E] in
/-- The part of a flow curve up to the fraction `c` of the time is the flow
curve of the time `cτ`. -/
theorem IsFlowCurve.rescale (h : IsFlowCurve X τ x γ) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    IsFlowCurve X (c * τ) x (rescale γ c) := by
  intro σ
  have hsub : ∫ r in (0 : ℝ)..c * σ, X (extend γ r) =
      c • ∫ s in (0 : ℝ)..σ, X (extend γ (c * s)) := by
    have hsm := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := (σ : ℝ))
      (fun r => X (extend γ r)) c
    rw [mul_zero] at hsm
    exact hsm.symm
  rw [rescale_apply, h.extend_eq (mul_mem_Icc hc σ.2), hsub]
  have hcongr : ∫ s in (0 : ℝ)..σ, X (extend γ (c * s)) =
      ∫ s in (0 : ℝ)..σ, X (extend (NonlinearODE.rescale γ c) s) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le σ.2.1] at hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans σ.2.2⟩
    have he : extend (NonlinearODE.rescale γ c) s = extend γ (c * s) :=
      extend_coe (NonlinearODE.rescale γ c) ⟨s, hs'⟩
    change X (extend γ (c * s)) = X (extend (NonlinearODE.rescale γ c) s)
    rw [he]
  rw [hcongr, smul_smul, mul_comm τ c]

/-- A solution of the differential equation between the times `0` and `t` gives a
flow curve of the time `t`. -/
theorem exists_isFlowCurve_of_hasDerivWithinAt (hX : Continuous X) {y : ℝ → E} {t : ℝ}
    (h0 : y 0 = x) (hy : ∀ r ∈ uIcc 0 t, HasDerivWithinAt y (X (y r)) (uIcc 0 t) r) :
    ∃ γ : Curve E, IsFlowCurve X t x γ ∧ ∀ σ : unitInterval, γ σ = y (t * σ) := by
  have hyc : ContinuousOn y (uIcc 0 t) := fun r hr => (hy r hr).continuousWithinAt
  let γ : Curve E := ⟨fun σ => y (t * σ),
    hyc.comp_continuous (by fun_prop) fun σ => mul_mem_uIcc t σ.2⟩
  refine ⟨γ, fun σ => ?_, fun σ => rfl⟩
  have hext : ∀ s ∈ Icc (0 : ℝ) 1, extend γ s = y (t * s) := fun s hs =>
    extend_coe γ ⟨s, hs⟩
  have hg : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun s => y (t * s)) (t • X (y (t * s))) (Icc 0 1) s := by
    intro s hs
    have hin : HasDerivWithinAt (fun s : ℝ => t * s) t (Icc 0 1) s := by
      simpa using ((hasDerivAt_id s).const_mul t).hasDerivWithinAt
    exact (hy (t * s) (mul_mem_uIcc t hs)).scomp s hin fun r hr => mul_mem_uIcc t hr
  have hcont : ContinuousOn (fun s => y (t * s)) (Icc 0 (σ : ℝ)) := fun s hs =>
    ((hg s ⟨hs.1, hs.2.trans σ.2.2⟩).continuousWithinAt).mono
      (Icc_subset_Icc_right σ.2.2)
  have hderiv : ∀ s ∈ Ioo (0 : ℝ) σ,
      HasDerivAt (fun s => y (t * s)) (t • X (extend γ s)) s := by
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2.le.trans σ.2.2⟩
    rw [hext s hs']
    exact (hg s hs').hasDerivAt (Icc_mem_nhds hs.1 (hs.2.trans_le σ.2.2))
  have hc : Continuous fun s => t • X (extend γ s) :=
    (hX.comp (extend_continuous γ)).const_smul t
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le σ.2.1 hcont hderiv
    (hc.intervalIntegrable _ _)
  rw [intervalIntegral.integral_smul] at hftc
  change y (t * σ) = x + t • ∫ s in (0 : ℝ)..σ, X (extend γ s)
  rw [hftc, mul_zero, h0]
  abel

/-! ### The equation as a map into the curves -/

/-- The map `((τ, x), γ) ↦ γ − x − τ ∫ X(γ)`. -/
def equation (X : E → E) (hX : Continuous X) (q : (ℝ × E) × Curve E) : Curve E :=
  q.2 - ContinuousLinearMap.const ℝ unitInterval q.1.2 -
    q.1.1 • primitiveCLM (Superposition.comp X hX q.2)

theorem equation_apply (hX : Continuous X) (q : (ℝ × E) × Curve E) (σ : unitInterval) :
    equation X hX q σ = q.2 σ - q.1.2 - q.1.1 • ∫ s in (0 : ℝ)..σ, X (extend q.2 s) := rfl

/-- The zeros of the equation are the flow curves. -/
theorem equation_eq_zero_iff (hX : Continuous X) :
    equation X hX ((τ, x), γ) = 0 ↔ IsFlowCurve X τ x γ := by
  constructor
  · intro h σ
    have hσ := congrArg (fun f : Curve E => f σ) h
    change equation X hX ((τ, x), γ) σ = 0 at hσ
    rw [equation_apply, sub_sub, sub_eq_zero] at hσ
    exact hσ
  · intro h
    ext σ
    rw [equation_apply]
    change γ σ - x - τ • ∫ s in (0 : ℝ)..σ, X (extend γ s) = 0
    rw [sub_sub, sub_eq_zero]
    exact h σ

/-- The equation of a smooth field is a smooth map. -/
theorem equation_contDiff (hX : ContDiff ℝ ∞ X) :
    ContDiff ℝ ∞ (equation X hX.continuous) := by
  have h1 : ContDiff ℝ ∞ fun q : (ℝ × E) × Curve E => q.2 := contDiff_snd
  have h2 : ContDiff ℝ ∞ fun q : (ℝ × E) × Curve E =>
      ContinuousLinearMap.const ℝ unitInterval q.1.2 :=
    (ContinuousLinearMap.const ℝ unitInterval (M := E)).contDiff.comp
      (contDiff_snd.comp contDiff_fst)
  have h3 : ContDiff ℝ ∞ fun q : (ℝ × E) × Curve E =>
      q.1.1 • primitiveCLM (Superposition.comp X hX.continuous q.2) :=
    (contDiff_fst.comp contDiff_fst).smul
      ((primitiveCLM (E := E)).contDiff.comp
        ((Superposition.comp_contDiff hX).comp contDiff_snd))
  exact (h1.sub h2).sub h3

/-- The derivative of the equation in the curve is the equation operator of the
linear equation with the coefficient `τ DX(γ)`. -/
theorem equation_fderiv_inr (hX : ContDiff ℝ ∞ X) (q : (ℝ × E) × Curve E) :
    fderiv ℝ (equation X hX.continuous) q ∘L .inr ℝ (ℝ × E) (Curve E) =
      equationOperator (q.1.1 • Superposition.comp (fderiv ℝ X)
        ((hX.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)).continuous_fderiv one_ne_zero) q.2) := by
  have hX1 : ContDiff ℝ 1 X := hX.of_le (by simp)
  have hG : HasFDerivAt (equation X hX.continuous) (fderiv ℝ (equation X hX.continuous) q)
      (q.1, q.2) := ((equation_contDiff hX).differentiable (by simp) q).hasFDerivAt
  have hpart := hG.comp q.2 (hasFDerivAt_prodMk_right q.1 q.2)
  have hdirect : HasFDerivAt (fun γ : Curve E => equation X hX.continuous (q.1, γ))
      (ContinuousLinearMap.id ℝ (Curve E) - q.1.1 • (primitiveCLM (E := E)).comp
        (Superposition.pointwise (Superposition.comp (fderiv ℝ X)
          (hX1.continuous_fderiv one_ne_zero) q.2))) q.2 := by
    have hc := (primitiveCLM (E := E)).hasFDerivAt.comp q.2
      (Superposition.hasFDerivAt_comp hX1 q.2)
    exact ((hasFDerivAt_id q.2).sub_const
      (ContinuousLinearMap.const ℝ unitInterval q.1.2)).sub (hc.const_smul q.1.1)
  rw [← hdirect.unique hpart]
  unfold equationOperator
  rw [map_smul]
  rfl

/-- Every flow curve belongs to a smooth family of flow curves, defined on an
open set of times and points. -/
theorem exists_local_family (hX : ContDiff ℝ ∞ X) (h : IsFlowCurve X τ x γ) :
    ∃ (V : Set (ℝ × E)) (ψ : ℝ × E → Curve E), IsOpen V ∧ (τ, x) ∈ V ∧ ψ (τ, x) = γ ∧
      ContDiffOn ℝ ∞ ψ V ∧ ∀ p ∈ V, IsFlowCurve X p.1 p.2 (ψ p) := by
  obtain ⟨V, ψ, hV, hqV, hψq, hψ, hzero⟩ := SmoothAlgebra.exists_contDiffOn_implicitFunction
    (f := equation X hX.continuous) (W := univ) (u := ((τ, x), γ)) isOpen_univ
    (equation_contDiff hX).contDiffOn
    (fun v _ => by
      rw [equation_fderiv_inr hX v]
      exact isInvertible_equationOperator _)
    (mem_univ _)
  refine ⟨V, ψ, hV, hqV, hψq, hψ, fun p hp => ?_⟩
  have hp0 := (hzero p hp).2.trans ((equation_eq_zero_iff hX.continuous).mpr h)
  exact (equation_eq_zero_iff (τ := p.1) (x := p.2) hX.continuous).mp hp0

end ProjectAInos.SmoothGeometry.NonlinearODE
