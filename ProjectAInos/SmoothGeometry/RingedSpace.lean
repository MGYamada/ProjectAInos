/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothAlgebra.Category
public import Mathlib.Geometry.RingedSpace.SheafedSpace

/-!
# C∞ structures on ringed spaces

The underlying sheaf and all topological infrastructure are mathlib's. The
additional structure makes the sections and restrictions C∞-rings and C∞
morphisms. This is the unbundled presentation of a sheaf of `SmoothRingCat`.
-/

@[expose] public section

universe u

namespace ProjectAInos.SmoothGeometry

open SmoothAlgebra CategoryTheory TopologicalSpace Opposite

/-- Smooth operations on the sections of an ordinary presheafed space. -/
class SmoothStructure (X : AlgebraicGeometry.PresheafedSpace CommRingCat.{u}) where
  [algebra : ∀ U, Algebra ℝ (X.presheaf.obj U)]
  [smoothRing : ∀ U, SmoothRing (X.presheaf.obj U)]
  map_op : ∀ {U V} (i : U ⟶ V) {n} (f : SmoothOperation n) (a : Fin n → X.presheaf.obj U),
    X.presheaf.map i (SmoothRing.op f a) =
      SmoothRing.op f (fun j => X.presheaf.map i (a j))

attribute [instance_reducible] SmoothStructure.algebra SmoothStructure.smoothRing
attribute [instance] SmoothStructure.algebra SmoothStructure.smoothRing

/-- A C∞-ringed space is a sheafed space with smooth structure on its sheaf. -/
structure RingedSpace extends AlgebraicGeometry.SheafedSpace CommRingCat.{u} where
  [smoothStructure : SmoothStructure toPresheafedSpace]

attribute [instance] RingedSpace.smoothStructure

namespace SmoothStructure

variable (X : AlgebraicGeometry.PresheafedSpace CommRingCat.{u}) [SmoothStructure X]

/-- A restriction map bundled as a C∞ morphism. -/
def restriction {U V} (i : U ⟶ V) :
    SmoothRingHom (X.presheaf.obj U) (X.presheaf.obj V) where
  toFun := X.presheaf.map i
  map_op' := map_op i

/-- The same presheaf with values bundled in the category of C∞-rings. -/
def presheaf : X.carrier.Presheaf SmoothRingCat where
  obj U := SmoothRingCat.of (X.presheaf.obj U)
  map i := restriction X i
  map_id U := by
    apply SmoothRingHom.ext
    intro a
    exact congrArg (fun h => h a) (X.presheaf.map_id U)
  map_comp i j := by
    apply SmoothRingHom.ext
    intro a
    exact congrArg (fun h => h a) (X.presheaf.map_comp i j)

/-- Smooth structure restricts along open embeddings. -/
@[instance_reducible] def restrict {U : TopCat.{u}} {f : U ⟶ X.carrier}
    (h : Topology.IsOpenEmbedding f) :
    SmoothStructure (X.restrict h) where
  algebra V := inferInstanceAs (Algebra ℝ (X.presheaf.obj (op (h.functor.obj V.unop))))
  smoothRing V := inferInstanceAs (SmoothRing (X.presheaf.obj (op (h.functor.obj V.unop))))
  map_op i := SmoothStructure.map_op ((h.functor.map i.unop).op)

end SmoothStructure
end ProjectAInos.SmoothGeometry
