/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Tensor.Bundle
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality

/-! # Covariant differentiation of native bilinear tensors

The construction uses the connection on the actual tangent bundle. The
Leibniz correction is tensorial in both vector arguments, so its value is
independent of their local extensions. Native tangent fibres need no norm.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Bundle FiberBundle ContinuousLinearMap
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.Tensor

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "TM" => TangentSpace I (M := M)

/-- Smooth covariant bilinear tensors, in the existing iterated hom bundle. -/
abbrev SmoothBilinear :=
  Cₛ^∞⟮I; E →L[ℝ] E →L[ℝ] ℝ, (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)⟯

variable (connection : _root_.CovariantDerivative I E (TangentSpace I (M := M)))
  (B : SmoothBilinear (I := I) (M := M))

theorem SmoothBilinear.mdifferentiableAt_apply {X Y : ∀ x, TM x} {x : M}
    (hX : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% X) x)
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% Y) x) :
    MDifferentiableAt I 𝓘(ℝ) (fun y => B y (X y) (Y y)) x := by
  have h := ((B.contMDiff x).mdifferentiableAt (by simp)).clm_bundle_apply₂ hX hY
  rw [mdifferentiableAt_totalSpace] at h
  exact h.2

/-- The scalar Leibniz rule, before descending from sections to fibre values. -/
def bilinearDerivativeAux (X Y : ∀ x, TM x) (x : M) : TM x →L[ℝ] ℝ :=
  mvfderiv I (fun y => B y (X y) (Y y)) x -
    ((B x).flip (Y x)).comp (connection.toFun X x) -
      (B x (X x)).comp (connection.toFun Y x)

@[simp] theorem bilinearDerivativeAux_apply (X Y : ∀ x, TM x) (x : M) (u : TM x) :
    bilinearDerivativeAux connection B X Y x u =
      mvfderiv I (fun y => B y (X y) (Y y)) x u -
        B x (connection X x u) (Y x) - B x (X x) (connection Y x u) := rfl

theorem bilinearDerivative_tensorial_left {Y : ∀ x, TM x} {x : M}
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% Y) x) :
    TensorialAt I E (fun X => bilinearDerivativeAux connection B X Y x) x where
  smul hf hX := by
    ext u
    simp only [bilinearDerivativeAux_apply, Pi.smul_apply', map_smul, smul_apply,
      smul_eq_mul]
    rw [mvfderiv_fun_mul hf (B.mdifferentiableAt_apply hX hY),
      connection.isCovariantDerivativeOnUniv.leibniz hX hf]
    simp only [add_apply, smul_apply, smulRight_apply, map_add, map_smul, smul_eq_mul]
    ring
  add hX hZ := by
    ext u
    simp only [bilinearDerivativeAux_apply, Pi.add_apply, map_add, add_apply]
    rw [mvfderiv_fun_add (B.mdifferentiableAt_apply hX hY) (B.mdifferentiableAt_apply hZ hY),
      connection.isCovariantDerivativeOnUniv.add hX hZ]
    simp only [add_apply, map_add]
    abel

theorem bilinearDerivative_tensorial_right {X : ∀ x, TM x} {x : M}
    (hX : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% X) x) :
    TensorialAt I E (fun Y => bilinearDerivativeAux connection B X Y x) x where
  smul hf hY := by
    ext u
    simp only [bilinearDerivativeAux_apply, Pi.smul_apply', map_smul, smul_apply,
      smul_eq_mul]
    rw [mvfderiv_fun_mul hf (B.mdifferentiableAt_apply hX hY),
      connection.isCovariantDerivativeOnUniv.leibniz hY hf]
    simp only [add_apply, smul_apply, smulRight_apply, map_add, map_smul, smul_eq_mul]
    ring
  add hY hZ := by
    ext u
    simp only [bilinearDerivativeAux_apply, Pi.add_apply, map_add, add_apply]
    rw [mvfderiv_fun_add (B.mdifferentiableAt_apply hX hY) (B.mdifferentiableAt_apply hX hZ),
      connection.isCovariantDerivativeOnUniv.add hY hZ]
    simp only [add_apply, map_add]
    abel

variable [FiniteDimensional ℝ E]

/-- The actual covariant derivative, linear in both tensor slots and the direction. -/
def bilinearCovariantDerivative (x : M) : TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] ℝ :=
  TensorialAt.mkHom₂ (fun X Y => bilinearDerivativeAux connection B X Y x) x
    (fun _ h => bilinearDerivative_tensorial_left connection B h)
    (fun _ h => bilinearDerivative_tensorial_right connection B h)

/-- Local differentiable extensions evaluate to the intrinsic tensor. -/
theorem bilinearCovariantDerivative_apply {X Y : ∀ x, TM x} {x : M}
    (hX : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% X) x)
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% Y) x) (u : TM x) :
    bilinearCovariantDerivative connection B x (X x) (Y x) u =
      mvfderiv I (fun y => B y (X y) (Y y)) x u -
        B x (connection X x u) (Y x) - B x (X x) (connection Y x u) := by
  unfold bilinearCovariantDerivative
  rw [TensorialAt.mkHom₂_apply _ _ hX hY, bilinearDerivativeAux_apply]

/-- Antisymmetry of the two covariant slots is preserved by the connection. -/
theorem bilinearCovariantDerivative_skew
    (hB : ∀ x (v w : TM x), B x v w = -B x w v) (x : M) (v w u : TM x) :
    bilinearCovariantDerivative connection B x v w u =
      -bilinearCovariantDerivative connection B x w v u := by
  simp only [bilinearCovariantDerivative, TensorialAt.mkHom₂_apply_eq_extend,
    bilinearDerivativeAux_apply]
  have hfun : (fun y => B y (extend E v y) (extend E w y)) =
      fun y => -B y (extend E w y) (extend E v y) := funext fun y => hB y _ _
  rw [hfun, mvfderiv_fun_neg]
  simp only [neg_apply]
  rw [hB x (connection (extend E v) x u) _, hB x (extend E v x) _]
  ring

end ProjectAInos.SmoothGeometry.Tensor
