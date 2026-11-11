/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.SchemeOpenPullback
public import Mathlib.Geometry.RingedSpace.PresheafedSpace.Gluing

/-! # Gluing C∞ schemes

The gluing data have the same categorical form as mathlib's scheme gluing.
The construction glues sheaves of C∞-rings, then proves locality and local
affineness using the open immersions of the pieces.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

namespace ProjectAInos.SmoothGeometry

open SmoothAlgebra CategoryTheory CategoryTheory.Limits

namespace LocallyRingedSpace

/-- Open gluing data for smooth locally ringed spaces. -/
structure GlueData extends CategoryTheory.GlueData LocallyRingedSpace.{u} where
  f_open : ∀ i j, IsOpenImmersion (f i j)

attribute [instance] GlueData.f_open

namespace GlueData

variable (D : GlueData.{u})

/-- Glue the full C∞-ring-valued sheaves using mathlib's construction. -/
def toSmoothSheafGlueData : AlgebraicGeometry.SheafedSpace.GlueData SmoothRingCat.{u} where
  toGlueData := D.toGlueData.mapGlueData forgetToSmoothSheafedSpace
  f_open i j := smoothSheafMap_isOpenImmersion (D.f i j)

/-- The underlying glued smooth sheaf. -/
abbrev smoothGlued := D.toSmoothSheafGlueData.toGlueData.glued

/-- The underlying ringed-space inclusion of a piece. -/
def underlyingι (i : D.J) : (D.U i).toPresheafedSpace ⟶
    (underlyingRingedSpace D.smoothGlued).toPresheafedSpace :=
  SmoothRingCat.forgetToCommRingCat.mapPresheaf.map
    (D.toSmoothSheafGlueData.toGlueData.ι i).hom

instance underlyingι_open (i : D.J) :
    AlgebraicGeometry.PresheafedSpace.IsOpenImmersion (D.underlyingι i) :=
  underlying_isOpenImmersion (D.toSmoothSheafGlueData.toGlueData.ι i).hom

theorem underlyingι_jointly_surjective (x : D.smoothGlued.carrier) :
    ∃ (i : D.J) (y : D.U i), (D.underlyingι i).base y = x :=
  D.toSmoothSheafGlueData.ι_jointly_surjective x

/-- The ordinary stalks of the glued space are local, since they are stalks of pieces. -/
def underlyingGlued : AlgebraicGeometry.LocallyRingedSpace where
  toSheafedSpace := underlyingRingedSpace D.smoothGlued
  isLocalRing x := by
    obtain ⟨i, y, rfl⟩ := D.underlyingι_jointly_surjective x
    exact (asIso ((D.underlyingι i).stalkMap y)).symm.commRingCatIsoToRingEquiv.isLocalRing

/-- (Implementation) The concrete smooth locally ringed space, including real residues.
Use `glued` for the categorical gluing. -/
def constructedGlued : LocallyRingedSpace where
  toLocallyRingedSpace := D.underlyingGlued
  smoothStructure := smoothStructure_mapPresheaf D.smoothGlued.toPresheafedSpace
  realResidue x := by
    obtain ⟨i, y, rfl⟩ := D.underlyingι_jointly_surjective x
    obtain ⟨e, he, hc⟩ := (D.U i).realResidue y
    let : IsLocalHom e := he
    refine ⟨e.comp ((D.underlyingι i).stalkMap y).hom, inferInstance, ?_⟩
    intro U hy r
    change e ((D.underlyingι i).stalkMap y
      ((underlyingRingedSpace D.smoothGlued).presheaf.germ U _ hy _)) = r
    rw [AlgebraicGeometry.PresheafedSpace.stalkMap_germ_apply]
    change e ((D.U i).presheaf.germ _ y hy
      ((D.toSmoothSheafGlueData.toGlueData.ι i).hom.c.app (.op U)
        (algebraMap ℝ (D.smoothGlued.presheaf.obj (.op U)) r))) = r
    rw [SmoothRingHom.map_algebraMap]
    exact hc _ hy r

/-- The canonical smooth open immersion of a piece into the glued space. -/
def constructedι (i : D.J) : D.U i ⟶ D.constructedGlued where
  toLRSHom := { toHom := D.underlyingι i, prop _ := inferInstance }
  map_op U := ((D.toSmoothSheafGlueData.toGlueData.ι i).hom.c.app U).map_op

instance constructedι_isOpenImmersion (i : D.J) : IsOpenImmersion (D.constructedι i) :=
  D.underlyingι_open i

theorem constructedι_jointly_surjective (x : D.constructedGlued) :
    ∃ (i : D.J) (y : D.U i), (D.constructedι i).base y = x :=
  D.underlyingι_jointly_surjective x

theorem constructed_glue_condition (i j : D.J) :
    D.t i j ≫ D.f j i ≫ D.constructedι j = D.f i j ≫ D.constructedι i := by
  apply Hom.ext
  apply AlgebraicGeometry.LocallyRingedSpace.Hom.ext'
  exact congrArg (fun h => SmoothRingCat.forgetToCommRingCat.mapPresheaf.map h.hom)
    (D.toSmoothSheafGlueData.toGlueData.glue_condition i j)

variable {X : LocallyRingedSpace.{u}} (f : ∀ i, D.U i ⟶ X)
  (hf : ∀ i j, D.t i j ≫ D.f j i ≫ f j = D.f i j ≫ f i)

/-- Descent at the level of the full smooth sheaves. -/
def smoothDesc : D.smoothGlued ⟶ forgetToSmoothSheafedSpace.obj X :=
  Multicoequalizer.desc D.toSmoothSheafGlueData.toGlueData.diagram _
    (fun i => forgetToSmoothSheafedSpace.map (f i)) (by
      rintro ⟨i, j⟩
      change forgetToSmoothSheafedSpace.map (D.f i j) ≫ forgetToSmoothSheafedSpace.map (f i) =
        (forgetToSmoothSheafedSpace.map (D.t i j) ≫ forgetToSmoothSheafedSpace.map (D.f j i)) ≫
          forgetToSmoothSheafedSpace.map (f j)
      simpa only [Functor.map_comp, Category.assoc] using
        (forgetToSmoothSheafedSpace.congr_map (hf i j)).symm)

theorem smoothDesc_fac (i : D.J) :
    D.toSmoothSheafGlueData.toGlueData.ι i ≫ D.smoothDesc f hf =
      forgetToSmoothSheafedSpace.map (f i) :=
  Multicoequalizer.π_desc D.toSmoothSheafGlueData.toGlueData.diagram _ _ _ i

/-- Compatible smooth local morphisms descend to the glued locally ringed space. -/
def constructedDesc : D.constructedGlued ⟶ X where
  toLRSHom :=
    { toHom := SmoothRingCat.forgetToCommRingCat.mapPresheaf.map (D.smoothDesc f hf).hom
      prop x := by
        obtain ⟨i, y, rfl⟩ := D.underlyingι_jointly_surjective x
        let d := SmoothRingCat.forgetToCommRingCat.mapPresheaf.map (D.smoothDesc f hf).hom
        have he : D.underlyingι i ≫ d = (f i).toHom :=
          congrArg (fun k : forgetToSmoothSheafedSpace.obj (D.U i) ⟶
            forgetToSmoothSheafedSpace.obj X =>
              SmoothRingCat.forgetToCommRingCat.mapPresheaf.map k.hom)
            (D.smoothDesc_fac f hf i)
        have hl : IsLocalHom (((D.underlyingι i ≫ d).stalkMap y).hom) := by
          rw [he]
          exact (f i).toLRSHom.prop y
        rw [AlgebraicGeometry.PresheafedSpace.stalkMap.comp] at hl
        exact isLocalHom_of_comp (d.stalkMap ((D.underlyingι i).base y)).hom
          ((D.underlyingι i).stalkMap y).hom }
  map_op U := ((D.smoothDesc f hf).hom.c.app U).map_op

@[simp] theorem constructedι_desc (i : D.J) :
    D.constructedι i ≫ D.constructedDesc f hf = f i := by
  apply Hom.ext
  apply AlgebraicGeometry.LocallyRingedSpace.Hom.ext'
  exact congrArg (fun k => SmoothRingCat.forgetToCommRingCat.mapPresheaf.map k.hom)
    (D.smoothDesc_fac f hf i)

/-- Morphisms from a gluing are determined by their restrictions to its pieces. -/
theorem constructed_hom_ext {f g : D.constructedGlued ⟶ X}
    (h : ∀ i, D.constructedι i ≫ f = D.constructedι i ≫ g) : f = g := by
  apply forgetToSmoothSheafedSpace.map_injective
  apply Multicoequalizer.hom_ext D.toSmoothSheafGlueData.toGlueData.diagram
  intro i
  exact forgetToSmoothSheafedSpace.congr_map (h i)

/-- The glued locally ringed space is the multicoequalizer of the gluing diagram. -/
def constructedGluedIsColimit : IsColimit
    (Multicofork.ofπ D.toGlueData.diagram D.constructedGlued D.constructedι
    (fun ⟨i, j⟩ => by
      change D.f i j ≫ D.constructedι i = (D.t i j ≫ D.f j i) ≫ D.constructedι j
      rw [Category.assoc]
      exact (D.constructed_glue_condition i j).symm)) :=
  Multicofork.IsColimit.mk _
    (fun s => D.constructedDesc s.π (fun i j => by
      simpa only [CategoryTheory.GlueData.diagram, MultispanShape.prod, Category.assoc] using
        (s.condition (i, j)).symm))
    (fun s i => D.constructedι_desc _ _ i)
    (fun s m hm => D.constructed_hom_ext fun i => (hm i).trans (D.constructedι_desc _ _ i).symm)

/-- Register the constructed colimit for mathlib's generic gluing API. -/
instance hasMulticoequalizer : HasMulticoequalizer D.toGlueData.diagram :=
  ⟨⟨_, D.constructedGluedIsColimit⟩⟩

/-- The glued object is mathlib's chosen multicoequalizer of the gluing diagram. -/
abbrev glued : LocallyRingedSpace.{u} := D.toGlueData.glued

/-- The canonical inclusion is the corresponding multicoequalizer leg. -/
abbrev ι (i : D.J) : D.U i ⟶ D.glued := D.toGlueData.ι i

/-- Compare the categorical gluing with the concrete construction used to prove existence. -/
def isoConstructed : D.glued ≅ D.constructedGlued :=
  colimit.isoColimitCocone ⟨_, D.constructedGluedIsColimit⟩

@[reassoc (attr := simp)]
theorem ι_isoConstructed_hom (i : D.J) : D.ι i ≫ D.isoConstructed.hom = D.constructedι i :=
  colimit.isoColimitCocone_ι_hom ⟨_, D.constructedGluedIsColimit⟩ (.right i)

@[reassoc (attr := simp)]
theorem constructedι_isoConstructed_inv (i : D.J) :
    D.constructedι i ≫ D.isoConstructed.inv = D.ι i :=
  colimit.isoColimitCocone_ι_inv ⟨_, D.constructedGluedIsColimit⟩ (.right i)

instance ι_isOpenImmersion (i : D.J) : IsOpenImmersion (D.ι i) := by
  rw [← D.constructedι_isoConstructed_inv i]
  infer_instance

theorem ι_jointly_surjective (x : D.glued) :
    ∃ (i : D.J) (y : D.U i), (D.ι i).base y = x := by
  obtain ⟨i, y, hy⟩ := D.constructedι_jointly_surjective (D.isoConstructed.hom.base x)
  refine ⟨i, y, ?_⟩
  calc
    (D.ι i).base y = D.isoConstructed.inv.base ((D.constructedι i).base y) :=
      (congrArg (fun k : D.U i ⟶ D.glued => k.base y)
        (D.constructedι_isoConstructed_inv i)).symm
    _ = D.isoConstructed.inv.base (D.isoConstructed.hom.base x) :=
      congrArg D.isoConstructed.inv.base hy
    _ = x := congrArg (fun k : D.glued ⟶ D.glued => k.base x) D.isoConstructed.hom_inv_id

@[reassoc (attr := simp)]
theorem glue_condition (i j : D.J) : D.t i j ≫ D.f j i ≫ D.ι j = D.f i j ≫ D.ι i :=
  D.toGlueData.glue_condition i j

/-- Descend compatible morphisms using the categorical multicoequalizer. -/
abbrev desc : D.glued ⟶ X :=
  Multicoequalizer.desc D.toGlueData.diagram X f (fun ⟨i, j⟩ => by
    simpa only [CategoryTheory.GlueData.diagram, MultispanShape.prod, Category.assoc] using
      (hf i j).symm)

@[reassoc (attr := simp)]
theorem ι_desc (i : D.J) : D.ι i ≫ D.desc f hf = f i :=
  Multicoequalizer.π_desc D.toGlueData.diagram X f _ i

theorem hom_ext {f g : D.glued ⟶ X} (h : ∀ i, D.ι i ≫ f = D.ι i ≫ g) : f = g :=
  Multicoequalizer.hom_ext D.toGlueData.diagram f g h

/-- The public gluing and its canonical inclusions satisfy the universal property. -/
def gluedIsColimit : IsColimit (Multicofork.ofπ D.toGlueData.diagram D.glued D.ι
    (fun ⟨i, j⟩ => by
      change D.f i j ≫ D.ι i = (D.t i j ≫ D.f j i) ≫ D.ι j
      rw [Category.assoc]
      exact (D.glue_condition i j).symm)) :=
  Multicofork.IsColimit.mk _
    (fun s => D.desc s.π (fun i j => by
      simpa only [CategoryTheory.GlueData.diagram, MultispanShape.prod, Category.assoc] using
        (s.condition (i, j)).symm))
    (fun s i => D.ι_desc _ _ i)
    (fun s m hm => D.hom_ext fun i => (hm i).trans (D.ι_desc _ _ i).symm)

end GlueData
end LocallyRingedSpace

namespace Scheme

/-- Open gluing data in the category of C∞ schemes, parallel to mathlib's `Scheme.GlueData`. -/
structure GlueData extends CategoryTheory.GlueData Scheme.{u} where
  f_open : ∀ i j, IsOpenImmersion (f i j)

attribute [instance] GlueData.f_open

namespace GlueData

variable (D : GlueData.{u})

/-- Forget only local affineness in the gluing diagram. -/
def toLocallyRingedSpaceGlueData : LocallyRingedSpace.GlueData.{u} where
  toGlueData := D.toGlueData.mapGlueData forgetToLocallyRingedSpace
  f_open := D.f_open

/-- (Implementation) The concrete glued scheme, with local affineness proved by its pieces.
Use `glued` for the categorical gluing. -/
def constructedGlued : Scheme.{u} :=
  Scheme.ofOpenCover D.toLocallyRingedSpaceGlueData.glued fun x => by
    obtain ⟨i, y, rfl⟩ := D.toLocallyRingedSpaceGlueData.ι_jointly_surjective x
    exact ⟨D.U i, D.toLocallyRingedSpaceGlueData.ι i, ⟨y, rfl⟩, inferInstance⟩

/-- The canonical inclusion of each scheme into its gluing. -/
def constructedι (i : D.J) : D.U i ⟶ D.constructedGlued :=
  ⟨D.toLocallyRingedSpaceGlueData.ι i⟩

instance constructedι_isOpenImmersion (i : D.J) : IsOpenImmersion (D.constructedι i) :=
  D.toLocallyRingedSpaceGlueData.ι_isOpenImmersion i

theorem constructedι_jointly_surjective (x : D.constructedGlued) :
    ∃ (i : D.J) (y : D.U i), (D.constructedι i).toSmoothLRSHom.base y = x :=
  D.toLocallyRingedSpaceGlueData.ι_jointly_surjective x

theorem constructed_glue_condition (i j : D.J) :
    D.t i j ≫ D.f j i ≫ D.constructedι j = D.f i j ≫ D.constructedι i :=
  Hom.ext (D.toLocallyRingedSpaceGlueData.glue_condition i j)

variable {X : Scheme.{u}} (f : ∀ i, D.U i ⟶ X)
  (hf : ∀ i j, D.t i j ≫ D.f j i ≫ f j = D.f i j ≫ f i)

/-- Descent of compatible C∞ scheme morphisms. -/
def constructedDesc : D.constructedGlued ⟶ X :=
  ⟨D.toLocallyRingedSpaceGlueData.desc (fun i => (f i).toSmoothLRSHom)
    (fun i j => congrArg Hom.toSmoothLRSHom (hf i j))⟩

@[simp] theorem constructedι_desc (i : D.J) :
    D.constructedι i ≫ D.constructedDesc f hf = f i :=
  Hom.ext (D.toLocallyRingedSpaceGlueData.ι_desc (fun j => (f j).toSmoothLRSHom)
    (fun j k => congrArg Hom.toSmoothLRSHom (hf j k)) i)

theorem constructed_hom_ext {f g : D.constructedGlued ⟶ X}
    (h : ∀ i, D.constructedι i ≫ f = D.constructedι i ≫ g) : f = g :=
  Hom.ext (D.toLocallyRingedSpaceGlueData.hom_ext fun i => congrArg Hom.toSmoothLRSHom (h i))

/-- The glued C∞ scheme has the universal gluing property. -/
def constructedGluedIsColimit : IsColimit
    (Multicofork.ofπ D.toGlueData.diagram D.constructedGlued D.constructedι
    (fun ⟨i, j⟩ => by
      change D.f i j ≫ D.constructedι i = (D.t i j ≫ D.f j i) ≫ D.constructedι j
      rw [Category.assoc]
      exact (D.constructed_glue_condition i j).symm)) :=
  Multicofork.IsColimit.mk _
    (fun s => D.constructedDesc s.π (fun i j => by
      simpa only [CategoryTheory.GlueData.diagram, MultispanShape.prod, Category.assoc] using
        (s.condition (i, j)).symm))
    (fun s i => D.constructedι_desc _ _ i)
    (fun s m hm => D.constructed_hom_ext fun i => (hm i).trans (D.constructedι_desc _ _ i).symm)

/-- Register the constructed colimit for mathlib's generic gluing API. -/
instance hasMulticoequalizer : HasMulticoequalizer D.toGlueData.diagram :=
  ⟨⟨_, D.constructedGluedIsColimit⟩⟩

/-- The glued object is mathlib's chosen multicoequalizer of the gluing diagram. -/
abbrev glued : Scheme.{u} := D.toGlueData.glued

/-- The canonical inclusion is the corresponding multicoequalizer leg. -/
abbrev ι (i : D.J) : D.U i ⟶ D.glued := D.toGlueData.ι i

/-- Compare the categorical gluing with the concrete construction used to prove existence. -/
def isoConstructed : D.glued ≅ D.constructedGlued :=
  colimit.isoColimitCocone ⟨_, D.constructedGluedIsColimit⟩

@[reassoc (attr := simp)]
theorem ι_isoConstructed_hom (i : D.J) : D.ι i ≫ D.isoConstructed.hom = D.constructedι i :=
  colimit.isoColimitCocone_ι_hom ⟨_, D.constructedGluedIsColimit⟩ (.right i)

@[reassoc (attr := simp)]
theorem constructedι_isoConstructed_inv (i : D.J) :
    D.constructedι i ≫ D.isoConstructed.inv = D.ι i :=
  colimit.isoColimitCocone_ι_inv ⟨_, D.constructedGluedIsColimit⟩ (.right i)

instance ι_isOpenImmersion (i : D.J) : IsOpenImmersion (D.ι i) := by
  rw [← D.constructedι_isoConstructed_inv i]
  infer_instance

theorem ι_jointly_surjective (x : D.glued) :
    ∃ (i : D.J) (y : D.U i), (D.ι i).toSmoothLRSHom.base y = x := by
  obtain ⟨i, y, hy⟩ :=
    D.constructedι_jointly_surjective (D.isoConstructed.hom.toSmoothLRSHom.base x)
  refine ⟨i, y, ?_⟩
  calc
    (D.ι i).toSmoothLRSHom.base y =
        D.isoConstructed.inv.toSmoothLRSHom.base ((D.constructedι i).toSmoothLRSHom.base y) :=
      (congrArg (fun k : D.U i ⟶ D.glued => k.toSmoothLRSHom.base y)
        (D.constructedι_isoConstructed_inv i)).symm
    _ = D.isoConstructed.inv.toSmoothLRSHom.base (D.isoConstructed.hom.toSmoothLRSHom.base x) :=
      congrArg D.isoConstructed.inv.toSmoothLRSHom.base hy
    _ = x := congrArg (fun k : D.glued ⟶ D.glued => k.toSmoothLRSHom.base x)
      D.isoConstructed.hom_inv_id

@[reassoc (attr := simp)]
theorem glue_condition (i j : D.J) : D.t i j ≫ D.f j i ≫ D.ι j = D.f i j ≫ D.ι i :=
  D.toGlueData.glue_condition i j

/-- Descend compatible morphisms using the categorical multicoequalizer. -/
abbrev desc : D.glued ⟶ X :=
  Multicoequalizer.desc D.toGlueData.diagram X f (fun ⟨i, j⟩ => by
    simpa only [CategoryTheory.GlueData.diagram, MultispanShape.prod, Category.assoc] using
      (hf i j).symm)

@[reassoc (attr := simp)]
theorem ι_desc (i : D.J) : D.ι i ≫ D.desc f hf = f i :=
  Multicoequalizer.π_desc D.toGlueData.diagram X f _ i

theorem hom_ext {f g : D.glued ⟶ X} (h : ∀ i, D.ι i ≫ f = D.ι i ≫ g) : f = g :=
  Multicoequalizer.hom_ext D.toGlueData.diagram f g h

/-- The public gluing and its canonical inclusions satisfy the universal property. -/
def gluedIsColimit : IsColimit (Multicofork.ofπ D.toGlueData.diagram D.glued D.ι
    (fun ⟨i, j⟩ => by
      change D.f i j ≫ D.ι i = (D.t i j ≫ D.f j i) ≫ D.ι j
      rw [Category.assoc]
      exact (D.glue_condition i j).symm)) :=
  Multicofork.IsColimit.mk _
    (fun s => D.desc s.π (fun i j => by
      simpa only [CategoryTheory.GlueData.diagram, MultispanShape.prod, Category.assoc] using
        (s.condition (i, j)).symm))
    (fun s i => D.ι_desc _ _ i)
    (fun s m hm => D.hom_ext fun i => (hm i).trans (D.ι_desc _ _ i).symm)

end GlueData
end Scheme
end ProjectAInos.SmoothGeometry
