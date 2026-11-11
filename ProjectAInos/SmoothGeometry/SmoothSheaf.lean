/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothAlgebra.Limits
public import ProjectAInos.SmoothGeometry.OpenPullback
public import Mathlib.Topology.Sheaves.Forget

/-! # The sheaf of C∞-rings and change of values -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace ProjectAInos.SmoothGeometry

open SmoothAlgebra CategoryTheory CategoryTheory.Limits

/-- A smooth-ring-valued presheaf carries its smooth structure after forgetting
to ordinary rings. -/
instance smoothStructure_mapPresheaf
    (X : AlgebraicGeometry.PresheafedSpace SmoothRingCat) :
    SmoothStructure (SmoothRingCat.forgetToCommRingCat.mapPresheaf.obj X) where
  algebra U := inferInstanceAs (Algebra ℝ (X.presheaf.obj U))
  smoothRing U := inferInstanceAs (SmoothRing (X.presheaf.obj U))
  map_op i := (X.presheaf.map i).map_op

/-- Change a smooth sheaf to its underlying ordinary ring sheaf. -/
def underlyingRingedSpace (X : AlgebraicGeometry.SheafedSpace SmoothRingCat) :
    AlgebraicGeometry.SheafedSpace CommRingCat where
  toPresheafedSpace := SmoothRingCat.forgetToCommRingCat.mapPresheaf.obj X.toPresheafedSpace
  IsSheaf := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp SmoothRingCat.forgetToCommRingCat
    X.presheaf).mp X.IsSheaf

instance underlying_isOpenImmersion
    {X Y : AlgebraicGeometry.PresheafedSpace SmoothRingCat} (f : X ⟶ Y)
    [H : AlgebraicGeometry.PresheafedSpace.IsOpenImmersion f] :
    AlgebraicGeometry.PresheafedSpace.IsOpenImmersion
      (SmoothRingCat.forgetToCommRingCat.mapPresheaf.map f) where
  base_open := H.base_open
  c_iso U :=
    let : IsIso (f.c.app (.op (H.base_open.functor.obj U))) := H.c_iso U
    SmoothRingCat.forgetToCommRingCat.map_isIso _

namespace LocallyRingedSpace

/-- Bundle the complete C∞ structure sheaf of a smooth locally ringed space. -/
def forgetToSmoothSheafedSpace : LocallyRingedSpace ⥤
    AlgebraicGeometry.SheafedSpace SmoothRingCat where
  obj X :=
    { toPresheafedSpace := forgetToSmoothPresheafedSpace.obj X
      IsSheaf := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp SmoothRingCat.forgetToCommRingCat
        (SmoothStructure.presheaf X.toPresheafedSpace)).mpr X.IsSheaf }
  map f := InducedCategory.homMk (forgetToSmoothPresheafedSpace.map f)
  map_id X := InducedCategory.hom_ext (forgetToSmoothPresheafedSpace.map_id X)
  map_comp f g := InducedCategory.hom_ext (forgetToSmoothPresheafedSpace.map_comp f g)

instance : forgetToSmoothSheafedSpace.Faithful where
  map_injective h := by
    apply Hom.ext
    apply AlgebraicGeometry.LocallyRingedSpace.Hom.ext'
    exact congrArg (fun k => SmoothRingCat.forgetToCommRingCat.mapPresheaf.map k.hom) h

instance smoothSheafMap_isOpenImmersion {X Y : LocallyRingedSpace} (f : X ⟶ Y)
    [IsOpenImmersion f] :
    AlgebraicGeometry.SheafedSpace.IsOpenImmersion (forgetToSmoothSheafedSpace.map f) :=
  smoothPresheafMap_isOpenImmersion f

instance smoothSheaf_preservesPullback {X Y Z : LocallyRingedSpace}
    (f : X ⟶ Z) [IsOpenImmersion f] (g : Y ⟶ Z) :
    PreservesLimit (cospan f g) forgetToSmoothSheafedSpace := by
  let : PreservesLimit (cospan f g)
      (forgetToSmoothSheafedSpace ⋙ AlgebraicGeometry.SheafedSpace.forgetToPresheafedSpace) :=
    inferInstanceAs (PreservesLimit (cospan f g) forgetToSmoothPresheafedSpace)
  exact preservesLimit_of_reflects_of_preserves forgetToSmoothSheafedSpace
    AlgebraicGeometry.SheafedSpace.forgetToPresheafedSpace

end LocallyRingedSpace
end ProjectAInos.SmoothGeometry
