/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-! # Open-submanifold inclusions and their tangent maps -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open TopologicalSpace
open scoped Manifold ContDiff

namespace ProjectAInos.SmoothGeometry.Manifold

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M]

/-- The inclusion of an open submanifold is a smooth local diffeomorphism.
Its local inverse is the ordinary subtype lift on that open set. -/
theorem isLocalDiffeomorph_subtype_val (U : Opens M) :
    IsLocalDiffeomorph I I ∞ (Subtype.val : U → M) := by
  intro x
  let e := U.openPartialHomeomorphSubtypeCoe ⟨x⟩
  have he : ContMDiffOn I I ∞ e.symm e.target := by
    intro y hy
    apply (ContMDiffWithinAt.subtypeVal_comp_iff U e.symm e.target y).mp
    exact contMDiffWithinAt_id.congr_of_mem (fun z hz => e.right_inv hz) hy
  let φ : PartialDiffeomorph I I U M ∞ :=
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
      contMDiffOn_invFun := he }
  exact PartialDiffeomorph.isLocalDiffeomorphAt I I ∞ φ (Set.mem_univ x)

/-- The differential of an open inclusion is invertible on the actual fibres. -/
theorem isInvertible_mfderiv_subtype_val (U : Opens M) (x : U) :
    (mfderiv I I (Subtype.val : U → M) x).IsInvertible :=
  (isLocalDiffeomorph_subtype_val I U).isInvertible_mfderiv (by simp) x

end ProjectAInos.SmoothGeometry.Manifold
