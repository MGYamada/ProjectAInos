/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.OpenImmersion

/-! # Bundling the presheaf of C∞-rings

This bridge makes mathlib's category-independent restriction, open-immersion,
and gluing constructions available without discarding the smooth operations.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace ProjectAInos.SmoothGeometry.LocallyRingedSpace

open SmoothAlgebra CategoryTheory TopologicalSpace Opposite

/-- Retain smooth-ring values while forgetting the sheaf and local-ring conditions. -/
def forgetToSmoothPresheafedSpace : LocallyRingedSpace ⥤
    AlgebraicGeometry.PresheafedSpace SmoothRingCat where
  obj X := { carrier := X.carrier, presheaf := SmoothStructure.presheaf X.toPresheafedSpace }
  map f :=
    { base := f.base
      c :=
        { app U := { toFun := f.c.app U, map_op' := f.map_op U }
          naturality := by
            intro U V i
            apply SmoothRingHom.ext
            intro a
            exact congrArg (fun h => h a) (f.c.naturality i) } }
  map_id X := by
    apply AlgebraicGeometry.PresheafedSpace.hext _ _ rfl
    rfl
  map_comp f g := by
    apply AlgebraicGeometry.PresheafedSpace.hext _ _ rfl
    rfl

@[simp] theorem forget_smoothPresheaf_map {X Y : LocallyRingedSpace} (f : X ⟶ Y) :
    SmoothRingCat.forgetToCommRingCat.mapPresheaf.map (forgetToSmoothPresheafedSpace.map f) =
      f.toHom := rfl

instance smoothPresheafMap_isOpenImmersion {X Y : LocallyRingedSpace}
    (f : X ⟶ Y) [H : IsOpenImmersion f] :
    AlgebraicGeometry.PresheafedSpace.IsOpenImmersion (forgetToSmoothPresheafedSpace.map f) where
  base_open := H.base_open
  c_iso U := by
    have : IsIso (SmoothRingCat.forgetToCommRingCat.map
        ((forgetToSmoothPresheafedSpace.map f).c.app (op (H.base_open.functor.obj U)))) :=
      H.c_iso U
    exact isIso_of_reflects_iso _ SmoothRingCat.forgetToCommRingCat

namespace IsOpenImmersion

variable {X Y Z : LocallyRingedSpace} (f : X ⟶ Z) [H : IsOpenImmersion f] (g : Y ⟶ Z)

/-- The open-immersion lifting property, retaining all smooth operations. -/
def lift (h : Set.range g.base ⊆ Set.range f.base) : Y ⟶ X := by
  let k := AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift
    (forgetToSmoothPresheafedSpace.map f) (forgetToSmoothPresheafedSpace.map g) h
  let l := AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift f.toLRSHom g.toLRSHom h
  have he : SmoothRingCat.forgetToCommRingCat.mapPresheaf.map k = l.toHom := by
    apply (cancel_mono f.toHom).mp
    exact (SmoothRingCat.forgetToCommRingCat.mapPresheaf.map_comp k
      (forgetToSmoothPresheafedSpace.map f)).symm.trans
      ((congrArg SmoothRingCat.forgetToCommRingCat.mapPresheaf.map
        (AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift_fac
          (forgetToSmoothPresheafedSpace.map f) (forgetToSmoothPresheafedSpace.map g) h)).trans
        (congrArg AlgebraicGeometry.LocallyRingedSpace.Hom.toHom
          (AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift_fac
            f.toLRSHom g.toLRSHom h)).symm)
  exact
    { toLRSHom :=
        { toHom := SmoothRingCat.forgetToCommRingCat.mapPresheaf.map k
          prop := by rw [he]; exact l.prop }
      map_op U := (k.c.app U).map_op }

@[simp] theorem lift_fac (h : Set.range g.base ⊆ Set.range f.base) :
    lift f g h ≫ f = g := by
  apply Hom.ext
  apply AlgebraicGeometry.LocallyRingedSpace.Hom.ext'
  exact congrArg (SmoothRingCat.forgetToCommRingCat.mapPresheaf.map)
    (AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift_fac
      (forgetToSmoothPresheafedSpace.map f) (forgetToSmoothPresheafedSpace.map g) h)

theorem lift_underlying (h : Set.range g.base ⊆ Set.range f.base) :
    (lift f g h).toLRSHom =
      AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift f.toLRSHom g.toLRSHom h := by
  let : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
      (forgetToLocallyRingedSpace.map f) := H
  apply (cancel_mono (forgetToLocallyRingedSpace.map f)).mp
  exact (congrArg (forgetToLocallyRingedSpace.map) (lift_fac f g h)).trans
    (AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift_fac
      f.toLRSHom g.toLRSHom h).symm

instance lift_isOpenImmersion [IsOpenImmersion g]
    (h : Set.range g.base ⊆ Set.range f.base) : IsOpenImmersion (lift f g h) := by
  unfold IsOpenImmersion
  rw [lift_underlying]
  let := AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset
    f.toLRSHom g.toLRSHom h
  unfold AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift
  infer_instance

/-- Open immersions with the same image identify the same smooth open subspace. -/
def isoOfRangeEq [IsOpenImmersion g] (h : Set.range f.base = Set.range g.base) : X ≅ Y where
  hom := lift g f h.le
  inv := lift f g h.ge
  hom_inv_id := by
    apply (cancel_mono f).mp
    simp only [Category.assoc, lift_fac, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono g).mp
    simp only [Category.assoc, lift_fac, Category.id_comp]

end IsOpenImmersion
end ProjectAInos.SmoothGeometry.LocallyRingedSpace
