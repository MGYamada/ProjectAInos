/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAInos.SmoothGeometry.Gluing

/-! External API regressions: use the public definitions with default elaborator
options, without unfolding morphism wrappers or adding local instances. -/

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open ProjectAInos.SmoothGeometry

noncomputable section

universe u

section OpenImmersions

variable {X Y Z : Scheme.{u}}

example : Scheme.IsOpenImmersion (𝟙 X) := inferInstance

example (f : X ⟶ Y) [IsIso f] : Scheme.IsOpenImmersion f := inferInstance

example (f : X ⟶ Y) (g : Y ⟶ Z) [Scheme.IsOpenImmersion f] [Scheme.IsOpenImmersion g] :
    Scheme.IsOpenImmersion (f ≫ g) := inferInstance

example (U : Opens X.carrier) : Scheme.IsOpenImmersion (X.ofRestrict U.isOpenEmbedding) :=
  inferInstance

example (U : Opens X.carrier) (f : Y ⟶ X) :
    HasPullback (X.ofRestrict U.isOpenEmbedding) f := inferInstance

example (U : Opens X.carrier) (e : X ≅ Y) (f : Z ⟶ Y) :
    HasPullback (X.ofRestrict U.isOpenEmbedding ≫ e.hom) f := inferInstance

end OpenImmersions

section LocallyRingedGluing

variable (D : LocallyRingedSpace.GlueData.{u})

example : HasMulticoequalizer D.toGlueData.diagram := inferInstance

example : D.glued = D.toGlueData.glued := rfl

example (i : D.J) : D.ι i = Multicoequalizer.π D.toGlueData.diagram i := rfl

example (i : D.J) : LocallyRingedSpace.IsOpenImmersion (D.toGlueData.ι i) := inferInstance

example (i j : D.J) : PullbackCone (D.ι i) (D.ι j) := D.toGlueData.vPullbackCone i j

example (X : LocallyRingedSpace.{u}) (f : ∀ i, D.U i ⟶ X)
    (h : ∀ p, D.toGlueData.diagram.fst p ≫ f p.1 = D.toGlueData.diagram.snd p ≫ f p.2)
    (i : D.J) : D.ι i ≫ Multicoequalizer.desc D.toGlueData.diagram X f h = f i :=
  Multicoequalizer.π_desc D.toGlueData.diagram X f h i

end LocallyRingedGluing

section SchemeGluing

variable (D : Scheme.GlueData.{u})

example : HasMulticoequalizer D.toGlueData.diagram := inferInstance

example : D.glued = D.toGlueData.glued := rfl

example (i : D.J) : D.ι i = Multicoequalizer.π D.toGlueData.diagram i := rfl

example (i : D.J) : Scheme.IsOpenImmersion (D.toGlueData.ι i) := inferInstance

example (i j : D.J) : PullbackCone (D.ι i) (D.ι j) := D.toGlueData.vPullbackCone i j

example (X : Scheme.{u}) (f : ∀ i, D.U i ⟶ X)
    (h : ∀ p, D.toGlueData.diagram.fst p ≫ f p.1 = D.toGlueData.diagram.snd p ≫ f p.2)
    (i : D.J) : D.ι i ≫ Multicoequalizer.desc D.toGlueData.diagram X f h = f i :=
  Multicoequalizer.π_desc D.toGlueData.diagram X f h i

end SchemeGluing
