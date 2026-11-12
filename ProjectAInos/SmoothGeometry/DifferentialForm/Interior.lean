/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.DifferentialForm.OneForm
public import Mathlib.LinearAlgebra.Alternating.Curry

/-! # Interior product on native tangent fibres

Insert a vector in the first slot. Continuity uses the given topology and
the continuity of the original form, with no choice of a fibre norm.
-/

@[expose] public section
noncomputable section

namespace ProjectAInos.SmoothGeometry.DifferentialForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] {k : ℕ}

def interior (v : V) (α : V [⋀^Fin (k + 1)]→L[ℝ] ℝ) : V [⋀^Fin k]→L[ℝ] ℝ where
  toAlternatingMap := α.toAlternatingMap.curryLeft v
  cont := α.cont.comp (by fun_prop : Continuous (fun w : Fin k → V => Matrix.vecCons v w))

@[simp] theorem interior_apply (v : V) (α : V [⋀^Fin (k + 1)]→L[ℝ] ℝ) (w : Fin k → V) :
    interior v α w = α (Matrix.vecCons v w) := rfl

@[simp] theorem interior_smul (v : V) (a : ℝ) (α : V [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    interior v (a • α) = a • interior v α := by ext w; rfl

@[simp] theorem interior_smul_vector (a : ℝ) (v : V) (α : V [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    interior (a • v) α = a • interior v α := by
  ext w
  change (α.toAlternatingMap.curryLeft (a • v)) w = _
  rw [map_smul]
  rfl

variable {W : Type*} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]

theorem interior_comp (L : V →L[ℝ] W) (v : V) (α : W [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    interior v (α.compContinuousLinearMap L) = (interior (L v) α).compContinuousLinearMap L := by
  ext w
  change α (fun i => L (Matrix.vecCons v w i)) = α (Matrix.vecCons (L v) (fun i => L (w i)))
  congr 1
  ext i
  exact Fin.cases rfl (fun _ => rfl) i

end ProjectAInos.SmoothGeometry.DifferentialForm
