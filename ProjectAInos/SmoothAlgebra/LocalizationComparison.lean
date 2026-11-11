/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothAlgebra.GeneralLocalization
public import ProjectAInos.SmoothAlgebra.Localization

/-! # Localization followed by localization at a real point -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ProjectAInos.SmoothAlgebra.SmoothLocalization

variable {A : Type*} [CommRing A] [Algebra ℝ A] [SmoothRing A]
  (S : Set A) (y : SmoothRingHom (SmoothLocalization S) ℝ)

/-- The original localization maps to the local ring at the corresponding point. -/
def toPoint : SmoothRingHom (SmoothLocalization S) (PointLocalization (y.comp (of S))) :=
  lift S (PointLocalization.of (y.comp (of S))) (fun s =>
    PointLocalization.isUnit_of (y.comp (of S)) s.val
      (((isUnit_of S s).map y.toAlgHom.toRingHom).ne_zero))

@[simp] theorem toPoint_of (a : A) :
    toPoint S y (of S a) = PointLocalization.of (y.comp (of S)) a := lift_of ..

theorem residue_toPoint (a : SmoothLocalization S) :
    PointLocalization.residue (y.comp (of S)) (toPoint S y a) = y a := by
  have h : (PointLocalization.residue (y.comp (of S))).comp (toPoint S y) = y := by
    apply hom_ext
    intro a
    simp
  exact congrArg (fun f : SmoothRingHom (SmoothLocalization S) ℝ => f a) h

/-- The inverse to the induced map of point localizations. -/
def pointInverse : SmoothRingHom (PointLocalization y) (PointLocalization (y.comp (of S))) :=
  PointLocalization.lift y (toPoint S y) (fun a ha =>
    (PointLocalization.isUnit_iff _ _).mpr (by rwa [residue_toPoint]))

@[simp] theorem pointInverse_of (a : SmoothLocalization S) :
    pointInverse S y (PointLocalization.of y a) = toPoint S y a := rfl

theorem pointInverse_map (a : PointLocalization (y.comp (of S))) :
    pointInverse S y (PointLocalization.map (of S) y a) = a := by
  obtain ⟨a, rfl⟩ := PointLocalization.of_surjective (y.comp (of S)) a
  simp

theorem map_pointInverse (a : PointLocalization y) :
    PointLocalization.map (of S) y (pointInverse S y a) = a := by
  obtain ⟨a, rfl⟩ := PointLocalization.of_surjective y a
  have h : (PointLocalization.map (of S) y).comp (toPoint S y) = PointLocalization.of y := by
    apply hom_ext
    intro a
    simp
  exact congrArg (fun f : SmoothRingHom (SmoothLocalization S) (PointLocalization y) => f a) h

/-- Localizing first at any set does not change the local ring at a surviving point. -/
def pointRingEquiv : PointLocalization (y.comp (of S)) ≃+* PointLocalization y where
  toFun := PointLocalization.map (of S) y
  invFun := pointInverse S y
  left_inv := pointInverse_map S y
  right_inv := map_pointInverse S y
  map_mul' := (PointLocalization.map (of S) y).map_mul
  map_add' := (PointLocalization.map (of S) y).map_add

end ProjectAInos.SmoothAlgebra.SmoothLocalization
