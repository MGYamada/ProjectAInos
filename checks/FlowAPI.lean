/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAinos.SmoothGeometry.ODE.FlowComplete

/-! Typed contracts for the solutions of an autonomous equation: a given family
of solutions (the variational equation, uniqueness, the determinant of the
derivative in the initial point and the preservation of volume), and the flow
of a smooth vector field (the integral equation on the unit interval, the open
domain, smoothness, the group law and completeness). These examples use default
elaborator options. -/

open ProjectAinos.SmoothGeometry ProjectAinos.SmoothGeometry.LinearODE
open ProjectAinos.SmoothGeometry.NonlinearODE
open Set Filter MeasureTheory
open scoped Topology ContDiff

noncomputable section

section Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

example {Φ : ℝ × E → E} {p : ℝ × E} (hp : DifferentiableAt ℝ Φ p) :
    HasFDerivAt (fun y => Φ (p.1, y)) (fderiv ℝ Φ p ∘L ContinuousLinearMap.inr ℝ ℝ E) p.2 :=
  hasFDerivAt_slice hp

example {Φ : ℝ × E → E} {p : ℝ × E} (hp : DifferentiableAt ℝ Φ p) :
    HasDerivAt (fun s => Φ (s, p.2)) (fderiv ℝ Φ p (1, 0)) p.1 :=
  hasDerivAt_slice_time hp

/-- The variational equation of a given family of solutions. -/
example {Φ : ℝ × E → E} {X : E → E} {t : ℝ} {x : E}
    (hΦ : ContDiffAt ℝ 2 Φ (t, x)) (hX : DifferentiableAt ℝ X (Φ (t, x)))
    (hsol : ∀ᶠ p in 𝓝 (t, x), HasDerivAt (fun s => Φ (s, p.2)) (X (Φ p)) p.1) :
    HasDerivAt (fun s => fderiv ℝ (fun y => Φ (s, y)) x)
      (fderiv ℝ X (Φ (t, x)) ∘L fderiv ℝ (fun y => Φ (t, y)) x) t :=
  hasDerivAt_fderiv_of_isLocalFlow hΦ hX hsol

end Variation

section Uniqueness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

example {X : E → E} (hX : ContDiff ℝ 1 X) {f g : ℝ → E} {a b : ℝ}
    (hf : ∀ r ∈ Icc a b, HasDerivAt f (X (f r)) r)
    (hg : ∀ r ∈ Icc a b, HasDerivAt g (X (g r)) r) (h : f a = g a) : EqOn f g (Icc a b) :=
  eqOn_of_hasDerivAt_of_eq_left hX hf hg h

example {X : E → E} (hX : ContDiff ℝ 1 X) {f g : ℝ → E} {a b : ℝ}
    (hf : ∀ r ∈ Icc a b, HasDerivAt f (X (f r)) r)
    (hg : ∀ r ∈ Icc a b, HasDerivAt g (X (g r)) r) (h : f b = g b) : EqOn f g (Icc a b) :=
  eqOn_of_hasDerivAt_of_eq_right hX hf hg h

/-- Two solutions that agree at one time agree at every time between. -/
example {X : E → E} (hX : ContDiff ℝ 1 X) {f g : ℝ → E} {s t : ℝ}
    (hf : ∀ r ∈ uIcc s t, HasDerivAt f (X (f r)) r)
    (hg : ∀ r ∈ uIcc s t, HasDerivAt g (X (g r)) r) (h : f s = g s) : f t = g t :=
  eq_of_hasDerivAt_of_eq hX hf hg h

end Uniqueness

section LocalFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {X : E → E} {Φ : ℝ × E → E}
  {Ω : Set (ℝ × E)}

example (h : IsLocalFlowOn X Φ Ω) : IsOpen Ω := h.isOpen

example (h : IsLocalFlowOn X Φ Ω) (p : ℝ × E) (hp : p ∈ Ω) : ContDiffAt ℝ 2 Φ p :=
  h.contDiffAt p hp

example (h : IsLocalFlowOn X Φ Ω) (p : ℝ × E) (hp : p ∈ Ω) :
    HasDerivAt (fun s => Φ (s, p.2)) (X (Φ p)) p.1 := h.hasDerivAt p hp

example (h : IsLocalFlowOn X Φ Ω) (p : ℝ × E) (hp : p ∈ Ω) (s : ℝ) (hs : s ∈ uIcc 0 p.1) :
    (s, p.2) ∈ Ω := h.segment p hp s hs

example (h : IsLocalFlowOn X Φ Ω) (p : ℝ × E) (hp : p ∈ Ω) : Φ (0, p.2) = p.2 :=
  h.initial p hp

/-- Translation along a constant field is a flow. -/
example (v : E) : IsLocalFlowOn (fun _ => v) (fun p : ℝ × E => p.2 + p.1 • v) univ :=
  isLocalFlowOn_translation v

example (h : IsLocalFlowOn X Φ Ω) {p : ℝ × E} (hp : p ∈ Ω) : (0, p.2) ∈ Ω := h.zero_mem hp

example (h : IsLocalFlowOn X Φ Ω) {p : ℝ × E} (hp : p ∈ Ω) : DifferentiableAt ℝ Φ p :=
  h.differentiableAt hp

example (h : IsLocalFlowOn X Φ Ω) {p : ℝ × E} (hp : p ∈ Ω) :
    ∀ᶠ q in 𝓝 p, HasDerivAt (fun s => Φ (s, q.2)) (X (Φ q)) q.1 :=
  h.eventually_hasDerivAt hp

example (h : IsLocalFlowOn X Φ Ω) {t : ℝ} {x : E} (hp : (t, x) ∈ Ω) :
    HasFDerivAt (fun y => Φ (t, y)) (fderiv ℝ (fun y => Φ (t, y)) x) x :=
  h.hasFDerivAt hp

/-- The variational equation along a solution of the family. -/
example (h : IsLocalFlowOn X Φ Ω) (hX : ContDiff ℝ 1 X) {t : ℝ} {x : E}
    (hp : (t, x) ∈ Ω) :
    HasDerivAt (fun s => fderiv ℝ (fun y => Φ (s, y)) x)
      (fderiv ℝ X (Φ (t, x)) ∘L fderiv ℝ (fun y => Φ (t, y)) x) t :=
  h.hasDerivAt_fderiv hX hp

example (h : IsLocalFlowOn X Φ Ω) {x : E} (hx : (0, x) ∈ Ω) :
    fderiv ℝ (fun y => Φ (0, y)) x = ContinuousLinearMap.id ℝ E := h.fderiv_zero hx

/-- A solution through a point is the solution of the family. -/
example (h : IsLocalFlowOn X Φ Ω) (hX : ContDiff ℝ 1 X) {t : ℝ} {x : E}
    (hp : (t, x) ∈ Ω) {y : ℝ → E} (hy : ∀ r ∈ uIcc 0 t, HasDerivAt y (X (y r)) r)
    (h0 : y 0 = x) : y t = Φ (t, x) :=
  h.eq_of_hasDerivAt hX hp hy h0

example (h : IsLocalFlowOn X Φ Ω) (hX : ContDiff ℝ 1 X) {t : ℝ} {A : Set E}
    (hA : ∀ x ∈ A, (t, x) ∈ Ω) : InjOn (fun x => Φ (t, x)) A := h.injOn hX hA

example (h : IsLocalFlowOn X Φ Ω) (hX : ContDiff ℝ 1 X) (hΩ : Ω = univ) (s t : ℝ) (x : E) :
    Φ (s + t, x) = Φ (s, Φ (t, x)) := h.apply_add hX hΩ s t x

end LocalFlow

section Volume

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {X : E → E} {Φ : ℝ × E → E} {Ω : Set (ℝ × E)}

/-- The determinant of the derivative in the initial point. -/
example (h : IsLocalFlowOn X Φ Ω) (hX : ContDiff ℝ 1 X) {t : ℝ} {x : E}
    (hp : (t, x) ∈ Ω) :
    LinearMap.det (fderiv ℝ (fun y => Φ (t, y)) x : E →ₗ[ℝ] E) =
      Real.exp (∫ s in 0..t, traceCLM (fderiv ℝ X (Φ (s, x)))) :=
  h.det_fderiv hX hp

example (h : IsLocalFlowOn X Φ Ω) (hX : ContDiff ℝ 1 X)
    (hdiv : ∀ x, traceCLM (fderiv ℝ X x) = 0) {t : ℝ} {x : E} (hp : (t, x) ∈ Ω) :
    LinearMap.det (fderiv ℝ (fun y => Φ (t, y)) x : E →ₗ[ℝ] E) = 1 :=
  h.det_fderiv_eq_one hX hdiv hp

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- Liouville's theorem for a measurable set in the domain of a given flow. -/
example (h : IsLocalFlowOn X Φ Ω) (hX : ContDiff ℝ 1 X)
    (hdiv : ∀ x, traceCLM (fderiv ℝ X x) = 0) {t : ℝ} {A : Set E} (hA : MeasurableSet A)
    (hAΩ : ∀ x ∈ A, (t, x) ∈ Ω) : μ ((fun x => Φ (t, x)) '' A) = μ A :=
  h.measure_image μ hX hdiv hA hAΩ

/-- Liouville's theorem for a given flow defined for all times and points. -/
example (h : IsLocalFlowOn X Φ Ω) (hX : ContDiff ℝ 1 X)
    (hdiv : ∀ x, traceCLM (fderiv ℝ X x) = 0) (hΩ : Ω = univ) (t : ℝ) :
    MeasurePreserving (fun x => Φ (t, x)) μ μ :=
  h.measurePreserving μ hX hdiv hΩ t

end Volume

section Linear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (A₀ : E →L[ℝ] E)

example : ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × E =>
    propagator (ContinuousMap.const ℝ A₀) p.1 0 := contDiff_propagator_const A₀

example : ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × E =>
    propagator (ContinuousMap.const ℝ A₀) p.1 0 p.2 := contDiff_propagator_const_apply A₀

example (t : ℝ) (x : E) :
    HasDerivAt (fun s => propagator (ContinuousMap.const ℝ A₀) s 0 x)
      (A₀ (propagator (ContinuousMap.const ℝ A₀) t 0 x)) t :=
  hasDerivAt_propagator_const_apply A₀ t x

/-- The propagator of a constant coefficient is the flow of the linear field. -/
example : IsLocalFlowOn (fun x => A₀ x)
    (fun p : ℝ × E => propagator (ContinuousMap.const ℝ A₀) p.1 0 p.2) univ :=
  isLocalFlowOn_linear A₀

/-- The flow of a linear field of trace zero preserves the volume. -/
example [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (hA : traceCLM A₀ = 0) (t : ℝ) :
    MeasurePreserving (fun x => propagator (ContinuousMap.const ℝ A₀) t 0 x) μ μ :=
  measurePreserving_propagator_const μ A₀ hA t

end Linear

section ConstantDivergence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {X : E → E} {Φ : ℝ × E → E} {Ω : Set (ℝ × E)}
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- A flow of a field of constant divergence multiplies the volume by `exp (d t)`. -/
example (h : IsLocalFlowOn X Φ Ω) (hX : ContDiff ℝ 1 X) {d : ℝ}
    (hdiv : ∀ x, traceCLM (fderiv ℝ X x) = d) {t : ℝ} {A : Set E} (hA : MeasurableSet A)
    (hAΩ : ∀ x ∈ A, (t, x) ∈ Ω) :
    μ ((fun x => Φ (t, x)) '' A) = ENNReal.ofReal (Real.exp (d * t)) * μ A :=
  h.measure_image_of_trace_eq μ hX hdiv hA hAΩ

end ConstantDivergence

section ImplicitFunction

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [CompleteSpace E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [CompleteSpace E₂]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The implicit function theorem with a smooth function on a neighbourhood. -/
example {f : E₁ × E₂ → F} {W : Set (E₁ × E₂)}
    (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f W)
    (hinv : ∀ v ∈ W, (fderiv ℝ f v ∘L .inr ℝ E₁ E₂).IsInvertible) {u : E₁ × E₂}
    (hu : u ∈ W) :
    ∃ (V : Set E₁) (ψ : E₁ → E₂), IsOpen V ∧ u.1 ∈ V ∧ ψ u.1 = u.2 ∧ ContDiffOn ℝ ∞ ψ V ∧
      ∀ x ∈ V, (x, ψ x) ∈ W ∧ f (x, ψ x) = f u :=
  ProjectAinos.SmoothAlgebra.exists_contDiffOn_implicitFunction hW hf hinv hu


end ImplicitFunction

section Superposition

universe u

open Superposition

variable {K : Type*} {E F : Type u} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

example (X : E → F) (hX : Continuous X) (γ : C(K, E)) (t : K) : comp X hX γ t = X (γ t) := rfl

example (X : E → F) (hX : Continuous X) (γ : C(K, E)) (t : K) :
    comp X hX γ t = X (γ t) :=
  comp_apply X hX γ t

example (X : E → F) (hX : Continuous X) :
    Continuous (comp (K := K) X hX) :=
  comp_continuous X hX

example (A : C(K, E →L[ℝ] F)) (γ : C(K, E)) (t : K) : pointwiseApply A γ t = A t (γ t) := rfl

example (A : C(K, E →L[ℝ] F)) (γ : C(K, E)) :
    ‖pointwiseApply A γ‖ ≤ ‖A‖ * ‖γ‖ :=
  pointwiseApply_norm_le A γ

example (A : C(K, E →L[ℝ] F)) (γ : C(K, E)) : pointwiseCLM A γ = pointwiseApply A γ := rfl

example (A : C(K, E →L[ℝ] F)) (γ : C(K, E)) (t : K) :
    pointwiseCLM A γ t = A t (γ t) :=
  pointwiseCLM_apply A γ t

example (A : C(K, E →L[ℝ] F)) :
    ‖pointwiseCLM A‖ ≤ ‖A‖ :=
  pointwiseCLM_norm_le A

example (A : C(K, E →L[ℝ] F)) : pointwise A = pointwiseCLM A := rfl

example (A : C(K, E →L[ℝ] F)) (γ : C(K, E)) (t : K) :
    pointwise A γ t = A t (γ t) :=
  pointwise_apply A γ t

example {X : E → F} (hX : ContDiff ℝ 1 X) (γ : C(K, E)) :
    HasFDerivAt (comp (K := K) X hX.continuous)
      (pointwise (comp (fderiv ℝ X) (hX.continuous_fderiv one_ne_zero) γ)) γ :=
  hasFDerivAt_comp hX γ

example (n : ℕ) {X : E → F} (hX : ContDiff ℝ n X) :
    ContDiff ℝ n (comp (K := K) X hX.continuous) :=
  comp_contDiff_nat n hX

example {X : E → F} (hX : ContDiff ℝ ∞ X) :
    ContDiff ℝ ∞ (comp (K := K) X hX.continuous) :=
  comp_contDiff hX


end Superposition

section FlowEquation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {X : E → E} {τ : ℝ} {x : E} {γ : Curve E}

example (X : E → E) (τ : ℝ) (x : E) (γ : Curve E) :
    IsFlowCurve X τ x γ ↔
      ∀ σ : unitInterval, γ σ = x + τ • ∫ s in (0 : ℝ)..σ, X (extend γ s) := Iff.rfl

example {c s : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    c * s ∈ Icc (0 : ℝ) 1 :=
  mul_mem_Icc hc hs

example (t : ℝ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    t * s ∈ uIcc 0 t :=
  mul_mem_uIcc t hs

example (h : IsFlowCurve X τ x γ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    extend γ s = x + τ • ∫ r in (0 : ℝ)..s, X (extend γ r) :=
  IsFlowCurve.extend_eq h hs

example (h : IsFlowCurve X τ x γ) :
    γ 0 = x :=
  IsFlowCurve.apply_zero h

example (h : IsFlowCurve X τ x γ) :
    extend γ 0 = x :=
  IsFlowCurve.extend_zero h

example (h : IsFlowCurve X τ x γ) (hX : Continuous X) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (extend γ) (τ • X (extend γ s)) (Icc 0 1) s :=
  IsFlowCurve.hasDerivWithinAt h hX hs

example (hX : ContDiff ℝ 1 X) {γ₁ γ₂ : Curve E} (h₁ : IsFlowCurve X τ x γ₁)
    (h₂ : IsFlowCurve X τ x γ₂) :
    γ₁ = γ₂ :=
  IsFlowCurve.eq hX h₁ h₂

example (X : E → E) (x : E) :
    IsFlowCurve X 0 x (ContinuousMap.const unitInterval x) :=
  isFlowCurve_const X x

example (γ : Curve E) (c : ℝ) (σ : unitInterval) : rescale γ c σ = extend γ (c * σ) := rfl

example (γ : Curve E) (c : ℝ) (σ : unitInterval) :
    rescale γ c σ = extend γ (c * σ) :=
  rescale_apply γ c σ

example (h : IsFlowCurve X τ x γ) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    IsFlowCurve X (c * τ) x (rescale γ c) :=
  IsFlowCurve.rescale h hc

example (hX : Continuous X) {y : ℝ → E} {t : ℝ}
    (h0 : y 0 = x) (hy : ∀ r ∈ uIcc 0 t, HasDerivWithinAt y (X (y r)) (uIcc 0 t) r) :
    ∃ γ : Curve E, IsFlowCurve X t x γ ∧ ∀ σ : unitInterval, γ σ = y (t * σ) :=
  exists_isFlowCurve_of_hasDerivWithinAt hX h0 hy

example (X : E → E) (hX : Continuous X) (q : (ℝ × E) × Curve E) :
    equation X hX q = q.2 - ContinuousLinearMap.const ℝ unitInterval q.1.2 -
      q.1.1 • primitiveCLM (Superposition.comp X hX q.2) := rfl

example (hX : Continuous X) (q : (ℝ × E) × Curve E) (σ : unitInterval) :
    equation X hX q σ = q.2 σ - q.1.2 - q.1.1 • ∫ s in (0 : ℝ)..σ, X (extend q.2 s) :=
  equation_apply hX q σ

example (hX : Continuous X) :
    equation X hX ((τ, x), γ) = 0 ↔ IsFlowCurve X τ x γ :=
  equation_eq_zero_iff hX

example (hX : ContDiff ℝ ∞ X) :
    ContDiff ℝ ∞ (equation X hX.continuous) :=
  equation_contDiff hX

example (hX : ContDiff ℝ ∞ X) (q : (ℝ × E) × Curve E) :
    fderiv ℝ (equation X hX.continuous) q ∘L .inr ℝ (ℝ × E) (Curve E) =
      equationOperator (q.1.1 • Superposition.comp (fderiv ℝ X)
        ((hX.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)).continuous_fderiv one_ne_zero) q.2) :=
  equation_fderiv_inr hX q

example (hX : ContDiff ℝ ∞ X) (h : IsFlowCurve X τ x γ) :
    ∃ (V : Set (ℝ × E)) (ψ : ℝ × E → Curve E), IsOpen V ∧ (τ, x) ∈ V ∧ ψ (τ, x) = γ ∧
      ContDiffOn ℝ ∞ ψ V ∧ ∀ p ∈ V, IsFlowCurve X p.1 p.2 (ψ p) :=
  exists_local_family hX h


end FlowEquation

section Flow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {X : E → E} {t τ : ℝ} {x : E}

example (X : E → E) :
    flowDomain X = {p | ∃ γ : Curve E, IsFlowCurve X p.1 p.2 γ} := rfl

example (X : E → E) (p : ℝ × E) (h : p ∈ flowDomain X) :
    IsFlowCurve X p.1 p.2 (flowCurve X p) := isFlowCurve_flowCurve h

example (X : E → E) (p : ℝ × E) : flow X p = flowCurve X p 1 := rfl

example {p : ℝ × E} (h : p ∈ flowDomain X) :
    IsFlowCurve X p.1 p.2 (flowCurve X p) :=
  isFlowCurve_flowCurve h

example (hX : ContDiff ℝ 1 X) {γ : Curve E} (h : IsFlowCurve X τ x γ) :
    flowCurve X (τ, x) = γ :=
  flowCurve_eq hX h

example (hX : ContDiff ℝ 1 X) {γ : Curve E} (h : IsFlowCurve X τ x γ) :
    flow X (τ, x) = γ 1 :=
  flow_eq hX h

example (X : E → E) (x : E) :
    (0, x) ∈ flowDomain X :=
  zero_mem_flowDomain X x

example (X : E → E) (x : E) :
    flow X (0, x) = x :=
  flow_zero X x

example (h : (τ, x) ∈ flowDomain X) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    (c * τ, x) ∈ flowDomain X :=
  mul_mem_flowDomain h hc

example (h : (t, x) ∈ flowDomain X) {s : ℝ}
    (hs : s ∈ uIcc 0 t) :
    (s, x) ∈ flowDomain X :=
  mem_flowDomain_of_mem_uIcc h hs

example (hX : ContDiff ℝ 1 X) (h : (τ, x) ∈ flowDomain X)
    (σ : unitInterval) :
    flowCurve X (τ, x) σ = flow X (σ * τ, x) :=
  flowCurve_apply hX h σ

example (hX : ContDiff ℝ 1 X) (h : (t, x) ∈ flowDomain X) :
    flow X (t, x) = x + ∫ r in (0 : ℝ)..t, X (flow X (r, x)) :=
  flow_integral_eq hX h

example (hX : ContDiff ℝ ∞ X) :
    IsOpen (flowDomain X) :=
  isOpen_flowDomain hX

example (hX : ContDiff ℝ ∞ X) {p : ℝ × E} (hp : p ∈ flowDomain X) :
    ContDiffAt ℝ ∞ (flow X) p :=
  contDiffAt_flow hX hp

example (hX : ContDiff ℝ ∞ X) :
    ContDiffOn ℝ ∞ (flow X) (flowDomain X) :=
  contDiffOn_flow hX

example (hX : ContDiff ℝ ∞ X) :
    ContinuousOn (flow X) (flowDomain X) :=
  continuousOn_flow hX

example (hX : ContDiff ℝ ∞ X) (h : (t, x) ∈ flowDomain X) :
    HasDerivAt (fun s => flow X (s, x)) (X (flow X (t, x))) t :=
  hasDerivAt_flow hX h

/-- The flow of a smooth field is a local flow on its domain. -/
example (hX : ContDiff ℝ ∞ X) : IsLocalFlowOn X (flow X) (flowDomain X) :=
  isLocalFlowOn_flow hX

example (hX : Continuous X) {y : ℝ → E} (h0 : y 0 = x)
    (hy : ∀ r ∈ uIcc 0 t, HasDerivWithinAt y (X (y r)) (uIcc 0 t) r) :
    (t, x) ∈ flowDomain X :=
  mem_flowDomain_of_hasDerivWithinAt hX h0 hy

example (hX : ContDiff ℝ 1 X) {y : ℝ → E} (h0 : y 0 = x)
    (hy : ∀ r ∈ uIcc 0 t, HasDerivWithinAt y (X (y r)) (uIcc 0 t) r) :
    flow X (t, x) = y t :=
  flow_eq_of_hasDerivWithinAt hX h0 hy

example (hX : ContDiff ℝ ∞ X) :
    (t, x) ∈ flowDomain X ↔ ∃ y : ℝ → E, y 0 = x ∧
      ∀ r ∈ uIcc 0 t, HasDerivWithinAt y (X (y r)) (uIcc 0 t) r :=
  mem_flowDomain_iff hX


end Flow

section FlowComplete

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {X : E → E} {t : ℝ} {x : E}

example (hX : ContDiff ℝ ∞ X) (h : (t, x) ∈ flowDomain X) :
    (-t, flow X (t, x)) ∈ flowDomain X ∧ flow X (-t, flow X (t, x)) = x :=
  neg_mem_flowDomain hX h

example (hX : ContDiff ℝ ∞ X) {s : ℝ} (hs : (s, x) ∈ flowDomain X)
    (ht : (t, flow X (s, x)) ∈ flowDomain X) :
    (s + t, x) ∈ flowDomain X ∧ flow X (s + t, x) = flow X (t, flow X (s, x)) :=
  flow_add hX hs ht

example (hX : ContDiff ℝ ∞ X) {K : Set E} (hK : IsCompact K)
    {T : ℝ} (h : ∀ t ∈ uIcc 0 T, (t, x) ∈ flowDomain X → flow X (t, x) ∈ K) :
    (T, x) ∈ flowDomain X :=
  mem_flowDomain_of_isCompact hX hK h

example (hX : ContDiff ℝ ∞ X) {a b : ℝ}
    (hab : ∀ y, ‖X y‖ ≤ a + b * ‖y‖) (h : (t, x) ∈ flowDomain X) :
    ‖flow X (t, x)‖ ≤ gronwallBound ‖x‖ b a |t| :=
  norm_flow_le_gronwallBound hX hab h

example [FiniteDimensional ℝ E] (hX : ContDiff ℝ ∞ X)
    {a b : ℝ} (hab : ∀ y, ‖X y‖ ≤ a + b * ‖y‖) :
    flowDomain X = univ :=
  flowDomain_eq_univ_of_norm_le hX hab

example (A₀ : E →L[ℝ] E) :
    flowDomain (fun y => A₀ y) = univ :=
  flowDomain_linear A₀

example (A₀ : E →L[ℝ] E) (t : ℝ) (x : E) :
    flow (fun y => A₀ y) (t, x) = propagator (ContinuousMap.const ℝ A₀) t 0 x :=
  flow_linear A₀ t x


end FlowComplete
