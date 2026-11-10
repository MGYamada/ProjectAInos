/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Scheme
public import Mathlib.CategoryTheory.EssentialImage

/-!
# Affine C∞ schemes

As in mathlib, affine schemes are the essential image of Spec. Unlike ordinary
commutative rings, arbitrary C∞-rings are not asserted to be equivalent to this
category. The complete-ring comparison is a subsequent theorem.
-/

@[expose] public section

noncomputable section

universe u

namespace ProjectAInos.SmoothGeometry

open CategoryTheory

/-- The category of affine C∞ schemes. -/
def AffineScheme := Scheme.Spec.{u}.EssImageSubcategory
  deriving Category

/-- A scheme is affine when it is isomorphic to a constructed spectrum. -/
def IsAffine (X : Scheme.{u}) : Prop := Scheme.Spec.essImage X

theorem isAffine_spec (A : SmoothAlgebra.SmoothRingCat.{u}) : IsAffine (Scheme.specObj A) :=
  ⟨Opposite.op A, ⟨Iso.refl _⟩⟩

end ProjectAInos.SmoothGeometry
