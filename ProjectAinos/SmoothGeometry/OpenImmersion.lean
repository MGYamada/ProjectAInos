/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.LocallyRingedSpace
public import Mathlib.Geometry.RingedSpace.OpenImmersion

/-! # Smooth isomorphisms and open immersions -/

@[expose] public section

noncomputable section

namespace ProjectAinos.SmoothGeometry.LocallyRingedSpace

open SmoothAlgebra CategoryTheory TopologicalSpace Opposite Topology

variable {X Y : LocallyRingedSpace}

/-- A smooth isomorphism of underlying local ringed spaces has a smooth inverse. -/
def inverse (f : X ⟶ Y) [IsIso (forgetToLocallyRingedSpace.map f)] : Y ⟶ X where
  toLRSHom := inv (forgetToLocallyRingedSpace.map f)
  map_op := by
    intro U n g a
    let e : X.toPresheafedSpace ≅ Y.toPresheafedSpace :=
      (AlgebraicGeometry.LocallyRingedSpace.forgetToSheafedSpace ⋙
        AlgebraicGeometry.SheafedSpace.forgetToPresheafedSpace).mapIso
          (X := forgetToLocallyRingedSpace.obj X) (Y := forgetToLocallyRingedSpace.obj Y)
          (asIso (forgetToLocallyRingedSpace.map f))
    have h := congrArg
      (fun k : X.toLocallyRingedSpace ⟶ X.toLocallyRingedSpace => k.toHom)
      (asIso (forgetToLocallyRingedSpace.map f)).hom_inv_id
    have hc (s : X.presheaf.obj U) := ConcreteCategory.congr_hom
      (AlgebraicGeometry.PresheafedSpace.congr_app h U) s
    apply (ConcreteCategory.bijective_of_isIso
      ((AlgebraicGeometry.PresheafedSpace.sheafIsoOfIso e).app
        (op ((Opens.map (inv (forgetToLocallyRingedSpace.map f)).base).obj U.unop))).hom).injective
    exact ((hc _).trans ((SmoothStructure.map_op (X := X.toPresheafedSpace) _ g a).trans
      (congrArg (SmoothRing.op g) (funext fun i => (hc (a i)).symm)))).trans
        (f.map_op _ g _).symm

/-- Lift an underlying isomorphism while retaining all C∞ operations. -/
def isoOfUnderlying (f : X ⟶ Y) [IsIso (forgetToLocallyRingedSpace.map f)] : X ≅ Y where
  hom := f
  inv := inverse f
  hom_inv_id := Hom.ext (asIso (forgetToLocallyRingedSpace.map f)).hom_inv_id
  inv_hom_id := Hom.ext (asIso (forgetToLocallyRingedSpace.map f)).inv_hom_id

instance : forgetToLocallyRingedSpace.ReflectsIsomorphisms where
  reflects f _ := (isoOfUnderlying f).isIso_hom

/-- Open immersions use mathlib's underlying open-immersion condition. -/
abbrev IsOpenImmersion (f : X ⟶ Y) : Prop :=
  AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion f.toLRSHom

instance ofRestrict_isOpenImmersion (X : LocallyRingedSpace) {U : TopCat}
    {f : U ⟶ X.carrier} (h : IsOpenEmbedding f) : IsOpenImmersion (X.ofRestrict h) :=
  inferInstanceAs (AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
    (X.toLocallyRingedSpace.ofRestrict h))

instance IsOpenImmersion.of_isIso (f : X ⟶ Y) [IsIso f] : IsOpenImmersion f :=
  inferInstanceAs (AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
    (forgetToLocallyRingedSpace.map f))

instance IsOpenImmersion.comp {Z : LocallyRingedSpace} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] : IsOpenImmersion (f ≫ g) :=
  AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.comp f.toLRSHom g.toLRSHom

instance IsOpenImmersion.mono (f : X ⟶ Y) [H : IsOpenImmersion f] : Mono f := by
  let : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
      (forgetToLocallyRingedSpace.map f) := H
  exact forgetToLocallyRingedSpace.mono_of_mono_map
    (show Mono (forgetToLocallyRingedSpace.map f) from inferInstance)

namespace IsOpenImmersion

variable (f : X ⟶ Y) [H : IsOpenImmersion f]

/-- An open immersion factored through restriction to its carrier. -/
def toRestrict : X ⟶ Y.restrict H.base_open where
  toLRSHom := (AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.isoRestrict f.toLRSHom).hom
  map_op := by
    intro U n g a
    change X.presheaf.map _ (f.c.app _ (SmoothRing.op g a)) = _
    exact (congrArg (X.presheaf.map _) (f.map_op _ g a)).trans (SmoothStructure.map_op _ g _)

/-- An open immersion identifies its source with the corresponding restriction. -/
def isoRestrict : X ≅ Y.restrict H.base_open :=
  let : IsIso (forgetToLocallyRingedSpace.map (toRestrict f)) :=
    (AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.isoRestrict f.toLRSHom).isIso_hom
  isoOfUnderlying (toRestrict f)

end IsOpenImmersion
end ProjectAinos.SmoothGeometry.LocallyRingedSpace
