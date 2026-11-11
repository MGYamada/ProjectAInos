/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The Koszul uniqueness argument is adapted from mathlib's
Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivita.lean
by Patrick Massot, Michael Rothgang and Heather Macbeth.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.Dual
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion

/-! # Connections compatible with a Lorentz metric

Compatibility is expressed using the given nondegenerate bilinear metric,
without introducing a positive-definite inner product on tangent fibres.
Connections are mathlib `CovariantDerivative` objects. Uniqueness is equality
of their action on vector fields differentiable at the evaluation point.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle FiberBundle VectorField ContinuousLinearMap
open scoped Manifold ContDiff

attribute [local fun_prop] MDifferentiable MDifferentiableAt
  MDifferentiable.add MDifferentiableAt.add
  mdifferentiableAt_fun_add_section MDifferentiableAt.fun_smul_section

namespace ProjectAInos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]
  (g : LorentzMetric σ d M)

local notation "I" => 𝓘(ℝ, MinkowskiModel d)
local notation "TM" => TangentSpace I (M := M)

variable {X Y Z : ∀ x : M, TangentSpace 𝓘(ℝ, MinkowskiModel d) x} {x : M}

/-- The metric pairs vector fields differentiable at a point to a
differentiable scalar function near that point. -/
@[fun_prop] theorem mdifferentiableAt_pairing
    (hX : MDifferentiableAt I ((I).prod I) (T% X) x)
    (hY : MDifferentiableAt I ((I).prod I) (T% Y) x) :
    MDifferentiableAt I 𝓘(ℝ) (fun y => g.form y (X y) (Y y)) x := by
  have h : MDifferentiableAt I ((I).prod 𝓘(ℝ))
      (fun y => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) y (g.form y (X y) (Y y))) x :=
    (g.smooth.mdifferentiableAt (by simp)).clm_bundle_apply₂ hX hY
  rw [mdifferentiableAt_totalSpace] at h
  exact h.2

/-- Nondegeneracy can be tested against vector fields differentiable at the point.
The test fields are local extensions of arbitrary tangent vectors. -/
theorem injective_form_mdifferentiableAt (x : M) :
    Function.Injective (fun v : TM x =>
      fun (Z : ∀ y : M, TM y) (_ : MDifferentiableAt I ((I).prod I) (T% Z) x) => g.form x v (Z x)) := by
  intro v w h
  apply (g.flat x).injective
  ext z
  simpa using congr($h _ (mdifferentiableAt_extend _ _ z))

/-- Metric compatibility with explicit differentiability assumptions. The
direction is an arbitrary tangent vector, not an assumed global frame. -/
def MetricCompatible (cov : CovariantDerivative I (MinkowskiModel d) TM) : Prop :=
  ∀ {x : M} (v : TM x) {Y Z : ∀ y : M, TM y},
    MDifferentiableAt I ((I).prod I) (T% Y) x →
    MDifferentiableAt I ((I).prod I) (T% Z) x →
    mvfderiv I (fun y => g.form y (Y y) (Z y)) x v =
      g.form x (cov Y x v) (Z x) + g.form x (Y x) (cov Z x v)

/-- A connection for the given Lorentz metric is Levi-Civita when it is
metric compatible and its intrinsic torsion tensor vanishes. -/
structure IsLeviCivita (cov : CovariantDerivative I (MinkowskiModel d) TM) : Prop where
  metricCompatible : g.MetricCompatible cov
  torsion : cov.torsion = 0

/-- Negating the whole metric preserves compatibility with a fixed connection. -/
theorem MetricCompatible.opposite {cov : CovariantDerivative I (MinkowskiModel d) TM}
    (h : g.MetricCompatible cov) : g.opposite.MetricCompatible cov := by
  intro x v Y Z hY hZ
  simpa [mvfderiv_fun_neg, add_comm] using congrArg Neg.neg (h v hY hZ)

/-- The Levi-Civita conditions do not depend on the overall metric sign. -/
theorem IsLeviCivita.opposite {cov : CovariantDerivative I (MinkowskiModel d) TM}
    (h : g.IsLeviCivita cov) : g.opposite.IsLeviCivita cov :=
  ⟨MetricCompatible.opposite g h.metricCompatible, h.torsion⟩

/-- The Koszul expression, with no connection as input. -/
def koszul (X Y Z : ∀ y : M, TM y) (x : M) : ℝ :=
  (mvfderiv I (fun y => g.form y (Y y) (Z y)) x (X x) +
    mvfderiv I (fun y => g.form y (Z y) (X y)) x (Y x) -
    mvfderiv I (fun y => g.form y (X y) (Y y)) x (Z x) -
    g.form x (Y x) (mlieBracket I X Z x) -
    g.form x (Z x) (mlieBracket I Y X x) +
    g.form x (X x) (mlieBracket I Z Y x)) / 2

/-- Compatibility and vanishing torsion force the Koszul formula. -/
theorem IsLeviCivita.koszul_eq {cov : CovariantDerivative I (MinkowskiModel d) TM}
    (h : g.IsLeviCivita cov)
    (hX : MDifferentiableAt I ((I).prod I) (T% X) x)
    (hY : MDifferentiableAt I ((I).prod I) (T% Y) x)
    (hZ : MDifferentiableAt I ((I).prod I) (T% Z) x) :
    g.form x (cov Y x (X x)) (Z x) = g.koszul X Y Z x := by
  have e₁ := h.metricCompatible (X x) hY hZ
  have e₂ := h.metricCompatible (Y x) hZ hX
  have e₃ := h.metricCompatible (Z x) hX hY
  have t₁ := congr(g.form x (Y x) ($(h.torsion) x (X x) (Z x)))
  have t₂ := congr(g.form x (Z x) ($(h.torsion) x (Y x) (X x)))
  have t₃ := congr(g.form x (X x) ($(h.torsion) x (Z x) (Y x)))
  simp only [CovariantDerivative.torsion_apply cov hX hZ, map_sub, Pi.zero_apply,
    zero_apply, map_zero] at t₁
  simp only [CovariantDerivative.torsion_apply cov hY hX, map_sub, Pi.zero_apply,
    zero_apply, map_zero] at t₂
  simp only [CovariantDerivative.torsion_apply cov hZ hY, map_sub, Pi.zero_apply,
    zero_apply, map_zero] at t₃
  simp only [koszul]
  simp only [g.symmetric] at e₁ e₂ e₃ t₁ t₂ t₃ ⊢
  linear_combination - (e₁ + t₁ + e₂ + t₂ - e₃ - t₃) / 2

/-- Levi-Civita uniqueness is action equality on differentiable sections;
it makes no claim about the arbitrary values of a connection on other fields. -/
theorem IsLeviCivita.uniqueness {cov cov' : CovariantDerivative I (MinkowskiModel d) TM}
    (h : g.IsLeviCivita cov) (h' : g.IsLeviCivita cov')
    (hY : MDifferentiableAt I ((I).prod I) (T% Y) x)
    (v : TM x) : cov Y x v = cov' Y x v := by
  apply g.injective_form_mdifferentiableAt
  funext Z hZ
  have hX := mdifferentiableAt_extend I (MinkowskiModel d) v
  have h₁ := h.koszul_eq g hX hY hZ
  have h₂ := h'.koszul_eq g hX hY hZ
  simpa using h₁.trans h₂.symm

end ProjectAInos.SmoothGeometry.LorentzMetric
