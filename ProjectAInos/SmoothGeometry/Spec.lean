/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.StructureSheaf
public import ProjectAInos.SmoothGeometry.LocallyRingedSpace

/-!
# The C∞ spectrum functor

This parallels mathlib's `AlgebraicGeometry.Spec`: first the underlying
space, then its structure sheaf, then the locally ringed space. Every affine
model is constructed from a C∞-ring; no existence of Spec is assumed.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

namespace ProjectAInos.SmoothGeometry

open SmoothAlgebra CategoryTheory TopologicalSpace Opposite TopCat

namespace Spec

/-- The topological real spectrum. -/
@[implicit_reducible] def topObj (A : SmoothRingCat.{u}) : TopCat.{u} := TopCat.of (RealSpectrum A)

/-- The map on real points, given by precomposition. -/
def topMap {A B : SmoothRingCat.{u}} (f : A ⟶ B) : topObj B ⟶ topObj A :=
  TopCat.ofHom ⟨RealSpectrum.comap f, RealSpectrum.continuous_comap f⟩

/-- The contravariant topological spectrum. -/
def toTop : SmoothRingCat.{u}ᵒᵖ ⥤ TopCat.{u} where
  obj A := topObj A.unop
  map f := topMap f.unop

/-- The spectrum as a C∞-ringed space. -/
@[implicit_reducible] def ringedSpaceObj (A : SmoothRingCat.{u}) : RingedSpace.{u} where
  carrier := topObj A
  presheaf := StructureSheaf.presheaf A
  IsSheaf := (StructureSheaf.sheaf A).property
  smoothStructure :=
    { algebra U := inferInstanceAs (Algebra ℝ (StructureSheaf.Sections A U.unop))
      smoothRing U := inferInstanceAs (SmoothRing (StructureSheaf.Sections A U.unop))
      map_op i := (StructureSheaf.restriction A i.unop).map_op }

/-- The spectrum as a local C∞-ringed space with real residue fields. -/
def locallyRingedSpaceObj (A : SmoothRingCat.{u}) : LocallyRingedSpace.{u} where
  toLocallyRingedSpace :=
    { toSheafedSpace := (ringedSpaceObj A).toSheafedSpace
      isLocalRing x := (StructureSheaf.stalkIso A x).symm.commRingCatIsoToRingEquiv.isLocalRing }
  smoothStructure := (ringedSpaceObj A).smoothStructure
  realResidue x := by
    refine ⟨(PointLocalization.residue x.hom).toAlgHom.toRingHom.comp
      (StructureSheaf.stalkIso A x).hom.hom, ⟨fun a ha => ?_⟩, fun U hx r => ?_⟩
    · have hu := (PointLocalization.isUnit_iff x.hom _).mpr ha.ne_zero
      let := isLocalHom_of_iso (StructureSheaf.stalkIso A x)
      exact IsLocalHom.map_nonunit (f := (StructureSheaf.stalkIso A x).hom.hom) a hu
    · change PointLocalization.residue x.hom
        (StructureSheaf.stalkEvaluation A x ((StructureSheaf.presheaf A).germ U x hx _)) = r
      rw [StructureSheaf.stalkEvaluation_germ]
      exact (PointLocalization.residue x.hom).map_algebraMap r

/-- Pullback of sections along a smooth-ring morphism. -/
def comap {A B : SmoothRingCat.{u}} (f : A ⟶ B) (U : Opens (topObj A)) :
    SmoothRingHom (StructureSheaf.Sections A U)
      (StructureSheaf.Sections B ((Opens.map (topMap f)).obj U)) where
  toFun s :=
    ⟨fun y => PointLocalization.map f y.val.hom (s.val ⟨RealSpectrum.comap f y.val, y.property⟩), by
      intro y
      obtain ⟨V, hyV, iV, a, ha⟩ := s.property ⟨RealSpectrum.comap f y.val, y.property⟩
      refine ⟨(Opens.map (topMap f)).obj V, hyV, (Opens.map (topMap f)).map iV,
        f a, fun z => ?_⟩
      change PointLocalization.map f z.val.hom
        (s.val ⟨RealSpectrum.comap f z.val, _⟩) = _
      exact congrArg (PointLocalization.map f z.val.hom)
        (ha ⟨RealSpectrum.comap f z.val, z.property⟩)⟩
  map_op' g a := Subtype.ext (funext fun y => (PointLocalization.map f y.val.hom).map_op g _)

/-- The underlying map of sheafed spaces. -/
def sheafedSpaceMap {A B : SmoothRingCat.{u}} (f : A ⟶ B) :
    (ringedSpaceObj B).toSheafedSpace ⟶ (ringedSpaceObj A).toSheafedSpace where
  hom.base := topMap f
  hom.c :=
    { app U := CommRingCat.ofHom (comap f U.unop).toAlgHom.toRingHom
      naturality := by intros; ext s; rfl }

/-- The induced stalk map agrees with the map of point localizations. -/
theorem stalkMap_evaluation {A B : SmoothRingCat.{u}} (f : A ⟶ B) (y : RealSpectrum B)
    (a : (StructureSheaf.presheaf A).stalk (RealSpectrum.comap f y)) :
    StructureSheaf.stalkEvaluation B y ((sheafedSpaceMap f).hom.stalkMap y a) =
      PointLocalization.map f y.hom
        (StructureSheaf.stalkEvaluation A (RealSpectrum.comap f y) a) := by
  obtain ⟨U, hy, s, rfl⟩ := (StructureSheaf.presheaf A).exists_germ_eq a
  have h := congrArg (fun k => k s)
    (AlgebraicGeometry.PresheafedSpace.stalkMap_germ (sheafedSpaceMap f).hom U y hy)
  change (sheafedSpaceMap f).hom.stalkMap y
      ((StructureSheaf.presheaf A).germ U (RealSpectrum.comap f y) hy s) =
    (StructureSheaf.presheaf B).germ ((Opens.map (topMap f)).obj U) y hy (comap f U s) at h
  rw [h, StructureSheaf.stalkEvaluation_germ, StructureSheaf.stalkEvaluation_germ]
  rfl

/-- The induced morphism of local C∞-ringed spaces. -/
def locallyRingedSpaceMap {A B : SmoothRingCat.{u}} (f : A ⟶ B) :
    locallyRingedSpaceObj B ⟶ locallyRingedSpaceObj A where
  toLRSHom :=
    { toHom := (sheafedSpaceMap f).hom
      prop y := ⟨fun a ha => by
        have hb := ha.map (StructureSheaf.stalkEvaluation B y).hom
        change IsUnit (StructureSheaf.stalkEvaluation B y
          ((sheafedSpaceMap f).hom.stalkMap y a)) at hb
        rw [stalkMap_evaluation f y a] at hb
        have hc : IsUnit (StructureSheaf.stalkEvaluation A (RealSpectrum.comap f y) a) := by
          apply (PointLocalization.isUnit_iff (RealSpectrum.comap f y).hom _).mpr
          have hd := (PointLocalization.isUnit_iff y.hom _).mp hb
          simpa only [RealSpectrum.comap, RealSpectrum.hom, PointLocalization.residue_map] using hd
        let := isLocalHom_of_iso (StructureSheaf.stalkIso A (RealSpectrum.comap f y))
        exact IsLocalHom.map_nonunit
          (f := (StructureSheaf.stalkIso A (RealSpectrum.comap f y)).hom.hom) a hc⟩ }
  map_op := by
    intro U n g a
    exact (comap f U.unop).map_op g a

@[simp] theorem locallyRingedSpaceMap_id (A : SmoothRingCat.{u}) :
    locallyRingedSpaceMap (𝟙 A) = 𝟙 (locallyRingedSpaceObj A) := by
  apply LocallyRingedSpace.Hom.ext
  apply AlgebraicGeometry.LocallyRingedSpace.Hom.ext'
  apply AlgebraicGeometry.PresheafedSpace.ext
    (locallyRingedSpaceMap (𝟙 A)).toHom
    ((𝟙 (locallyRingedSpaceObj A)) : locallyRingedSpaceObj A ⟶ locallyRingedSpaceObj A).toHom rfl
  ext U s
  apply Subtype.ext
  funext x
  exact PointLocalization.map_id x.val.hom (s.val x)

theorem locallyRingedSpaceMap_comp {A B C : SmoothRingCat.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    locallyRingedSpaceMap (f ≫ g) = locallyRingedSpaceMap g ≫ locallyRingedSpaceMap f := by
  apply LocallyRingedSpace.Hom.ext
  apply AlgebraicGeometry.LocallyRingedSpace.Hom.ext'
  apply AlgebraicGeometry.PresheafedSpace.ext
    (locallyRingedSpaceMap (f ≫ g)).toHom
    (locallyRingedSpaceMap g ≫ locallyRingedSpaceMap f).toHom rfl
  ext U s
  apply Subtype.ext
  funext x
  exact (PointLocalization.map_comp f g x.val.hom _).symm

/-- Joyce's spectrum, as a contravariant functor to local C∞-ringed spaces. -/
def toLocallyRingedSpace : SmoothRingCat.{u}ᵒᵖ ⥤ LocallyRingedSpace.{u} where
  obj A := locallyRingedSpaceObj A.unop
  map f := locallyRingedSpaceMap f.unop
  map_id A := locallyRingedSpaceMap_id A.unop
  map_comp f g := locallyRingedSpaceMap_comp g.unop f.unop

end Spec
end ProjectAInos.SmoothGeometry
