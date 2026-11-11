/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothAlgebra.SmoothFunctions
public import ProjectAInos.SmoothGeometry.LocallyRingedSpace
public import Mathlib.Geometry.Manifold.Sheaf.LocallyRingedSpace

/-! # Manifolds as local C∞-ringed spaces -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open scoped Manifold ContDiff

namespace ProjectAInos.SmoothGeometry.Manifold

open SmoothAlgebra CategoryTheory TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]

/-- Retain the smooth operations on mathlib's manifold function sheaf. -/
instance smoothStructure : SmoothStructure (ChartedSpace.locallyRingedSpace I M).toPresheafedSpace := by
  change SmoothStructure
    { carrier := TopCat.of M
      presheaf := smoothPresheafCommRing I 𝓘(ℝ) M ℝ }
  exact {
    algebra U := inferInstanceAs (Algebra ℝ C^∞⟮I, U.unop; ℝ⟯)
    smoothRing U := inferInstanceAs (SmoothRing C^∞⟮I, U.unop; ℝ⟯)
    map_op := by intros; rfl }

/-- The manifold's actual smooth-function sheaf with local real stalks. -/
@[implicit_reducible] def locallyRingedSpace : LocallyRingedSpace where
  toLocallyRingedSpace := ChartedSpace.locallyRingedSpace I M
  realResidue x := by
    refine ⟨smoothSheafCommRing.eval I 𝓘(ℝ) M ℝ x, ⟨fun a ha => ?_⟩, fun U hx r => ?_⟩
    · apply (smoothSheafCommRing.isUnit_stalk_iff I a).mpr
      exact ha.ne_zero
    · exact smoothSheafCommRing.eval_germ (IM := I) (I := 𝓘(ℝ))
        (R := ℝ) (M := M) U x hx (ContMDiffMap.const r)

variable {I M}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {N : Type} [TopologicalSpace N] [ChartedSpace H' N]

/-- Smooth maps induce smooth morphisms of the associated local ringed spaces. -/
def map (f : M → N) (hf : ContMDiff I I' ∞ f) :
    locallyRingedSpace I M ⟶ locallyRingedSpace I' N where
  toLRSHom := ChartedSpace.locallyRingedSpaceMap f hf
  map_op := by intros; rfl

@[simp] theorem map_id : map (I := I) (M := M) id contMDiff_id = 𝟙 _ := rfl

variable {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
  {P : Type} [TopologicalSpace P] [ChartedSpace H'' P]

theorem map_comp (f : M → N) (hf : ContMDiff I I' ∞ f)
    (g : N → P) (hg : ContMDiff I' I'' ∞ g) :
    map (g ∘ f) (hg.comp hf) = map f hf ≫ map g hg := rfl

end ProjectAInos.SmoothGeometry.Manifold
