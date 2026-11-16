/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAInos.SmoothGeometry.ODE.LocalFlow

/-! Typed contracts for a given family of solutions of an autonomous equation:
the variational equation, uniqueness, the determinant of the derivative in the
initial point and the preservation of volume. These examples use default
elaborator options. -/

open ProjectAInos.SmoothGeometry ProjectAInos.SmoothGeometry.LinearODE
open ProjectAInos.SmoothGeometry.NonlinearODE
open Set Filter MeasureTheory
open scoped Topology

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
