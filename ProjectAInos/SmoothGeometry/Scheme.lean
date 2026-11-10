/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Spec

/-!
# C∞ schemes

The definition follows `Mathlib.AlgebraicGeometry.Scheme`: a locally ringed
space equipped with a proof that every point has an affine open neighbourhood.
Here the sheaf and its morphisms retain all C∞ operations, the residue fields
are real, and the affine model is Joyce's constructed real spectrum.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace ProjectAInos.SmoothGeometry

open SmoothAlgebra CategoryTheory TopologicalSpace Opposite

/-- A C∞ scheme is locally isomorphic to the spectrum of a C∞-ring.
No finite generation, Hausdorffness, or reducedness is imposed. -/
structure Scheme extends toSmoothLocallyRingedSpace : LocallyRingedSpace.{u} where
  local_affine : ∀ x : carrier, ∃ (U : OpenNhds x) (A : SmoothRingCat.{u}),
    Nonempty (toSmoothLocallyRingedSpace.restrict U.isOpenEmbedding ≅
      Spec.toLocallyRingedSpace.obj (op A))

namespace Scheme

instance : CoeSort Scheme (Type u) := ⟨fun X => X.carrier⟩
instance (X : Scheme) : TopologicalSpace X := X.carrier.str

/-- Scheme morphisms are the underlying C∞ local-ringed-space morphisms. -/
structure Hom (X Y : Scheme.{u}) where
  toSmoothLRSHom : X.toSmoothLocallyRingedSpace ⟶ Y.toSmoothLocallyRingedSpace

@[ext] theorem Hom.ext {X Y : Scheme.{u}} {f g : Hom X Y}
    (h : f.toSmoothLRSHom = g.toSmoothLRSHom) : f = g := by cases f; cases g; cases h; rfl

instance : Category Scheme where
  Hom := Hom
  id X := ⟨𝟙 X.toSmoothLocallyRingedSpace⟩
  comp f g := ⟨f.toSmoothLRSHom ≫ g.toSmoothLRSHom⟩
  id_comp f := Hom.ext (@Category.id_comp LocallyRingedSpace _ _ _ f.toSmoothLRSHom)
  comp_id f := Hom.ext (@Category.comp_id LocallyRingedSpace _ _ _ f.toSmoothLRSHom)
  assoc f g h := Hom.ext (@Category.assoc LocallyRingedSpace _ _ _ _ _
    f.toSmoothLRSHom g.toSmoothLRSHom h.toSmoothLRSHom)

/-- Schemes form a full subcategory of local C∞-ringed spaces. -/
def forgetToLocallyRingedSpace : Scheme.{u} ⥤ LocallyRingedSpace.{u} where
  obj X := X.toSmoothLocallyRingedSpace
  map f := f.toSmoothLRSHom

instance : forgetToLocallyRingedSpace.Faithful where
  map_injective := Hom.ext

instance : forgetToLocallyRingedSpace.Full where
  map_surjective f := ⟨⟨f⟩, rfl⟩

/-- The affine scheme associated to a C∞-ring. -/
def specObj (A : SmoothRingCat.{u}) : Scheme.{u} where
  toSmoothLocallyRingedSpace := Spec.locallyRingedSpaceObj A
  local_affine _ := ⟨⟨⊤, trivial⟩, A,
    ⟨(Spec.locallyRingedSpaceObj A).restrictTopIso⟩⟩

/-- The actual spectrum functor with values in C∞ schemes. -/
def Spec : SmoothRingCat.{u}ᵒᵖ ⥤ Scheme.{u} where
  obj A := specObj A.unop
  map f := ⟨SmoothGeometry.Spec.locallyRingedSpaceMap f.unop⟩
  map_id A := Hom.ext (SmoothGeometry.Spec.locallyRingedSpaceMap_id A.unop)
  map_comp f g := Hom.ext (SmoothGeometry.Spec.locallyRingedSpaceMap_comp g.unop f.unop)

/-- Sections of the C∞ structure sheaf on an open set. -/
abbrev sections (X : Scheme.{u}) (U : Opens X.carrier) := X.presheaf.obj (op U)

/-- The morphism on sections over an open set. -/
def Hom.app {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Opens Y.carrier) :
    SmoothRingHom (Y.sections U)
      (X.sections ((Opens.map f.toSmoothLRSHom.base).obj U)) where
  toFun := f.toSmoothLRSHom.c.app (op U)
  map_op' := f.toSmoothLRSHom.map_op (op U)

/-- Global sections as a contravariant C∞-ring-valued functor. -/
def Γ : Scheme.{u}ᵒᵖ ⥤ SmoothRingCat.{u} where
  obj X := SmoothRingCat.of (X.unop.sections ⊤)
  map f := f.unop.app ⊤
  map_id X := by apply SmoothRingHom.ext; intro a; rfl
  map_comp f g := by apply SmoothRingHom.ext; intro a; rfl

end Scheme
end ProjectAInos.SmoothGeometry
