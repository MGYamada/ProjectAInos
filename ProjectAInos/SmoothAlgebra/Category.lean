/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothAlgebra.Models
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-! # The category of C∞-rings -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

namespace ProjectAInos.SmoothAlgebra

open CategoryTheory

/-- Bundled C∞-rings, parallel to mathlib's `CommAlgCat`. -/
structure SmoothRingCat where
  carrier : Type u
  [commRing : CommRing carrier]
  [algebra : Algebra ℝ carrier]
  [smoothRing : SmoothRing carrier]

attribute [instance] SmoothRingCat.commRing SmoothRingCat.algebra SmoothRingCat.smoothRing

namespace SmoothRingCat

instance : CoeSort SmoothRingCat (Type u) := ⟨carrier⟩

/-- Bundle an existing smooth ring. -/
abbrev of (A : Type u) [CommRing A] [Algebra ℝ A] [SmoothRing A] : SmoothRingCat := ⟨A⟩

instance : Category SmoothRingCat where
  Hom A B := SmoothRingHom A B
  id A := SmoothRingHom.id A
  comp f g := g.comp f

instance : ConcreteCategory SmoothRingCat (fun A B => SmoothRingHom A B) where
  hom f := f
  ofHom f := f

/-- Forget the smooth operations, retaining the real algebra. -/
def forgetToCommAlgCat : SmoothRingCat.{u} ⥤ CommAlgCat.{u} ℝ where
  obj A := .of ℝ A
  map f := CommAlgCat.ofHom f.toAlgHom

instance : forgetToCommAlgCat.Faithful where
  map_injective h := by
    apply SmoothRingHom.ext
    intro a
    exact congrArg (fun f => f.hom a) h

/-- Forget to ordinary commutative rings. -/
def forgetToCommRingCat : SmoothRingCat.{u} ⥤ CommRingCat.{u} :=
  forgetToCommAlgCat ⋙ forget₂ _ _

/-- A bijective smooth-ring morphism has a smooth inverse. -/
noncomputable def isoOfBijective {A B : SmoothRingCat.{u}} (f : A ⟶ B)
    (hf : Function.Bijective f) : A ≅ B where
  hom := f
  inv :=
    { toFun := Function.invFun f
      map_op' g a := by
        apply hf.injective
        rw [Function.rightInverse_invFun hf.surjective]
        refine Eq.trans ?_ (f.map_op g (fun i => Function.invFun f (a i))).symm
        congr 1
        funext i
        exact (Function.rightInverse_invFun hf.surjective (a i)).symm }
  hom_inv_id := SmoothRingHom.ext (Function.leftInverse_invFun hf.injective)
  inv_hom_id := SmoothRingHom.ext (Function.rightInverse_invFun hf.surjective)

instance : forgetToCommRingCat.ReflectsIsomorphisms where
  reflects f _ := (isoOfBijective f (ConcreteCategory.bijective_of_isIso
    (forgetToCommRingCat.map f))).isIso_hom

end SmoothRingCat
end ProjectAInos.SmoothAlgebra
