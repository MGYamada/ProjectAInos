/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.RingedSpace
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace

/-!
# Local C∞-ringed spaces

Joyce's local rings have residue field ℝ. The real residue condition is
explicit and compatible with constants on every open set. Morphisms retain
the C∞ operations, in addition to the underlying local ringed-space map.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

namespace ProjectAInos.SmoothGeometry

open SmoothAlgebra CategoryTheory TopologicalSpace Opposite Topology

/-- Real residue maps are compatible with constants on all neighbourhoods. -/
def HasRealResidues (X : AlgebraicGeometry.LocallyRingedSpace.{u})
    [SmoothStructure X.toPresheafedSpace] : Prop :=
  ∀ x, ∃ e : X.presheaf.stalk x →+* ℝ,
    IsLocalHom e ∧ ∀ (U : Opens X.carrier) (hx : x ∈ U) (r : ℝ),
      e (X.presheaf.germ U x hx (algebraMap ℝ (X.presheaf.obj (op U)) r)) = r

/-- A locally ringed C∞ space with real residue fields (Joyce, Definition 4.8). -/
structure LocallyRingedSpace extends AlgebraicGeometry.LocallyRingedSpace.{u} where
  [smoothStructure : SmoothStructure toPresheafedSpace]
  realResidue : @HasRealResidues toLocallyRingedSpace smoothStructure

attribute [instance] LocallyRingedSpace.smoothStructure

namespace LocallyRingedSpace

instance : CoeSort LocallyRingedSpace (Type u) := ⟨fun X => X.carrier⟩
instance (X : LocallyRingedSpace) : TopologicalSpace X := X.carrier.str

/-- Forget locality but retain the C∞ structure. -/
def toSmoothRingedSpace (X : LocallyRingedSpace) : RingedSpace where
  toSheafedSpace := X.toSheafedSpace

/-- Morphisms preserve all smooth operations on sections. -/
structure Hom (X Y : LocallyRingedSpace.{u}) extends
    toLRSHom : X.toLocallyRingedSpace.Hom Y.toLocallyRingedSpace where
  map_op : ∀ (U : (Opens Y.carrier)ᵒᵖ) {n} (f : SmoothOperation n)
    (a : Fin n → Y.presheaf.obj U),
    c.app U (SmoothRing.op f a) =
      SmoothRing.op (A := X.presheaf.obj (op ((Opens.map base).obj U.unop)))
        f (fun i => c.app U (a i))

@[ext] theorem Hom.ext {X Y : LocallyRingedSpace} {f g : Hom X Y}
    (h : f.toLRSHom = g.toLRSHom) : f = g := by cases f; cases g; cases h; rfl

/-- The identity smooth morphism. -/
def id (X : LocallyRingedSpace.{u}) : Hom X X where
  toLRSHom := 𝟙 X.toLocallyRingedSpace
  map_op := by intros; rfl

/-- Composition of smooth local-ringed-space morphisms. -/
def comp {X Y Z : LocallyRingedSpace.{u}} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  toLRSHom := AlgebraicGeometry.LocallyRingedSpace.comp f.toLRSHom g.toLRSHom
  map_op := by
    intro U n h a
    change f.c.app _ (g.c.app U (SmoothRing.op h a)) = _
    rw [g.map_op, f.map_op]
    rfl

instance : Category LocallyRingedSpace where
  Hom := Hom
  id := id
  comp f g := comp f g
  id_comp f := by
    apply Hom.ext
    exact @Category.id_comp AlgebraicGeometry.LocallyRingedSpace _ _ _ f.toLRSHom
  comp_id f := by
    apply Hom.ext
    exact @Category.comp_id AlgebraicGeometry.LocallyRingedSpace _ _ _ f.toLRSHom
  assoc f g h := by
    apply Hom.ext
    exact @Category.assoc AlgebraicGeometry.LocallyRingedSpace _ _ _ _ _
      f.toLRSHom g.toLRSHom h.toLRSHom

/-- Forget smooth operations, retaining mathlib's locally ringed space. -/
def forgetToLocallyRingedSpace : LocallyRingedSpace.{u} ⥤ AlgebraicGeometry.LocallyRingedSpace.{u} where
  obj X := X.toLocallyRingedSpace
  map f := f.toLRSHom

instance : forgetToLocallyRingedSpace.Faithful where
  map_injective := Hom.ext

/-- Restriction to an open subspace. -/
def restrict (X : LocallyRingedSpace.{u}) {U : TopCat.{u}}
    {f : U ⟶ X.carrier} (h : IsOpenEmbedding f) : LocallyRingedSpace where
  toLocallyRingedSpace := X.toLocallyRingedSpace.restrict h
  smoothStructure := SmoothStructure.restrict X.toPresheafedSpace h
  realResidue x := by
    obtain ⟨e, he, hc⟩ := X.realResidue (f x)
    let : IsLocalHom e := he
    refine ⟨e.comp (X.toLocallyRingedSpace.restrictStalkIso h x).hom.hom,
      inferInstance, fun V hx r => ?_⟩
    change e ((X.toLocallyRingedSpace.restrictStalkIso h x).hom
      ((X.toLocallyRingedSpace.restrict h).presheaf.germ V x hx _)) = r
    rw [AlgebraicGeometry.LocallyRingedSpace.restrictStalkIso_hom_eq_germ_apply]
    exact hc _ _ r

/-- The inclusion of an open subspace is a smooth local-ringed-space morphism. -/
def ofRestrict (X : LocallyRingedSpace.{u}) {U : TopCat.{u}}
    {f : U ⟶ X.carrier} (h : IsOpenEmbedding f) : X.restrict h ⟶ X where
  toLRSHom := X.toLocallyRingedSpace.ofRestrict h
  map_op V := SmoothStructure.map_op (X := X.toPresheafedSpace)
    (h.isOpenMap.adjunction.counit.app V.unop).op

/-- Restricting to the whole space changes only the presentation of its carrier. -/
def restrictTopIso (X : LocallyRingedSpace.{u}) :
    X.restrict (Opens.isOpenEmbedding ⊤) ≅ X where
  hom := X.ofRestrict (Opens.isOpenEmbedding ⊤)
  inv :=
    { toLRSHom := X.toLocallyRingedSpace.restrictTopIso.inv
      map_op := by
        intro U n f a
        have hU := congrArg (fun F : Opens (TopCat.of (⊤ : Opens X.carrier)) ⥤ Opens X.carrier =>
          F.obj U.unop) (Opens.inclusion'_top_functor X.carrier)
        have h := SmoothStructure.map_op (X := X.toPresheafedSpace)
          (eqToHom (congrArg op hU)) f a
        have hmap : X.toLocallyRingedSpace.restrictTopIso.inv.c.app U =
            X.presheaf.map (eqToHom (congrArg op hU)) := by
          change (eqToHom (AlgebraicGeometry.PresheafedSpace.restrict_top_presheaf
            X.toPresheafedSpace)).app U = _
          rw [CategoryTheory.eqToHom_app, CategoryTheory.eqToHom_map]
        rw [hmap]
        exact h }
  hom_inv_id := Hom.ext X.toLocallyRingedSpace.restrictTopIso.hom_inv_id
  inv_hom_id := Hom.ext X.toLocallyRingedSpace.restrictTopIso.inv_hom_id

end LocallyRingedSpace
end ProjectAInos.SmoothGeometry
