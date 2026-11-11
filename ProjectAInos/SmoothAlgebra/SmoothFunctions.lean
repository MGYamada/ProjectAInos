/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothAlgebra.Models
public import Mathlib.Geometry.Manifold.ContMDiff.Constructions

/-! # C∞ operations on smooth functions on a manifold -/

@[expose] public section

noncomputable section

namespace ProjectAInos.SmoothAlgebra

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]

/-- Smooth functions carry their pointwise C∞ operations on any smooth charted space. -/
instance (priority := 90) instSmoothRingContMDiffMap : SmoothRing C^∞⟮I, M; ℝ⟯ where
  op f a := ⟨fun x => f (fun i => a i x),
    f.contMDiff.comp (contMDiff_pi_module_iff.mpr (fun i => (a i).contMDiff))⟩
  op_proj _ _ := rfl
  op_comp _ _ _ := rfl
  op_nullary _ _ := rfl
  op_addition _ := rfl
  op_multiplication _ := rfl

/-- Evaluation at a point preserves the complete smooth structure. -/
def smoothEvaluation (x : M) : SmoothRingHom C^∞⟮I, M; ℝ⟯ ℝ where
  toFun f := f x
  map_op' _ _ := rfl

variable {I M}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

/-- Pullback along a smooth map, as a C∞-ring morphism. -/
def smoothPullback (f : M → N) (hf : ContMDiff I I' ∞ f) :
    SmoothRingHom C^∞⟮I', N; ℝ⟯ C^∞⟮I, M; ℝ⟯ where
  toFun g := ⟨fun x => g (f x), g.contMDiff.comp hf⟩
  map_op' _ _ := rfl

@[simp] theorem smoothEvaluation_pullback (f : M → N) (hf : ContMDiff I I' ∞ f)
    (x : M) (g : C^∞⟮I', N; ℝ⟯) :
    smoothEvaluation I M x (smoothPullback f hf g) = smoothEvaluation I' N (f x) g := rfl

end ProjectAInos.SmoothAlgebra
