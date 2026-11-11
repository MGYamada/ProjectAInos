/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothAlgebra.Category
public import Mathlib.Algebra.Category.Ring.Limits

/-! # Limits of C∞-rings

Limits are compatible families in products, with pointwise smooth operations.
The forgetful functor to commutative rings preserves these limits.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

namespace ProjectAInos.SmoothAlgebra.SmoothRingCat

open CategoryTheory CategoryTheory.Limits

variable {J : Type u} [Category.{u} J] (F : J ⥤ SmoothRingCat.{u})

/-- Compatible families of elements in a diagram of smooth rings. -/
def sectionsSubalgebra : Subalgebra ℝ (∀ j, F.obj j) where
  carrier := {a | ∀ {j k} (f : j ⟶ k), F.map f (a j) = a k}
  add_mem' {a b} ha hb := by
    intro j k f
    exact ((F.map f).map_add (a j) (b j)).trans (congrArg₂ (· + ·) (ha f) (hb f))
  mul_mem' {a b} ha hb := by
    intro j k f
    exact ((F.map f).map_mul (a j) (b j)).trans (congrArg₂ (· * ·) (ha f) (hb f))
  algebraMap_mem' r := by intro j k f; exact (F.map f).map_algebraMap r

instance sectionsSmoothRing : SmoothRing (sectionsSubalgebra F) where
  op g a := ⟨fun j => SmoothRing.op g (fun i => (a i).val j), by
    intro j k f
    refine ((F.map f).map_op g (fun i => (a i).val j)).trans ?_
    congr 1
    funext i
    exact (a i).property f⟩
  op_proj i a := Subtype.ext (funext fun j => SmoothRing.op_proj i (fun k => (a k).val j))
  op_comp f g a := Subtype.ext (funext fun j => SmoothRing.op_comp f g (fun k => (a k).val j))
  op_nullary r a := Subtype.ext (funext fun j => SmoothRing.op_nullary r (fun k => (a k).val j))
  op_addition a := Subtype.ext (funext fun j => SmoothRing.op_addition (fun k => (a k).val j))
  op_multiplication a :=
    Subtype.ext (funext fun j => SmoothRing.op_multiplication (fun k => (a k).val j))

/-- The compatible-family limit cone. -/
def limitCone : Cone F where
  pt := of (sectionsSubalgebra F)
  π :=
    { app j := { toFun := fun a => a.val j, map_op' := by intros; rfl }
      naturality := by intro j k f; apply SmoothRingHom.ext; intro a; exact (a.property f).symm }

/-- The universal property of compatible families. -/
def limitConeIsLimit : IsLimit (limitCone F) where
  lift s :=
    { toFun a := ⟨fun j => s.π.app j a, by
        intro j k f
        exact (congrArg (fun h => h a) (s.π.naturality f)).symm⟩
      map_op' g a := Subtype.ext (funext fun j => (s.π.app j).map_op g a) }
  fac _ _ := rfl
  uniq s m hm := by
    apply SmoothRingHom.ext
    intro a
    apply Subtype.ext
    funext j
    exact congrArg (fun h => h a) (hm j)

instance : HasLimit F := ⟨⟨limitCone F, limitConeIsLimit F⟩⟩

instance : HasLimits SmoothRingCat.{u} where
  has_limits_of_shape _ _ := { has_limit := fun _F => inferInstance }

/-- The underlying ordinary-ring cone is limiting as well. -/
def forgetLimitConeIsLimit : IsLimit (forgetToCommRingCat.mapCone (limitCone F)) where
  lift s := CommRingCat.ofHom
    { toFun a := ⟨fun j => s.π.app j a, by
        intro j k f
        exact (congrArg (fun h => h a) (s.π.naturality f)).symm⟩
      map_one' := Subtype.ext (funext fun j => map_one (s.π.app j).hom)
      map_mul' a b := Subtype.ext (funext fun j => map_mul (s.π.app j).hom a b)
      map_zero' := Subtype.ext (funext fun j => map_zero (s.π.app j).hom)
      map_add' a b := Subtype.ext (funext fun j => map_add (s.π.app j).hom a b) }
  fac _ _ := rfl
  uniq s m hm := by
    ext a
    apply Subtype.ext
    funext j
    exact congrArg (fun h => h a) (hm j)

instance forgetToCommRingCat_preservesLimits : PreservesLimits forgetToCommRingCat.{u} where
  preservesLimitsOfShape :=
    { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit F) (forgetLimitConeIsLimit F) }

end ProjectAInos.SmoothAlgebra.SmoothRingCat
