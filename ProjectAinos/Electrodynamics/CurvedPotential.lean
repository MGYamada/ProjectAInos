/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.Curved
public import ProjectAinos.SmoothGeometry.DifferentialForm.NativeNaturality

/-!
# Potentials as one-forms on a manifold

On a manifold modelled on space-time a potential is a smooth one-form `A`, and its field is
the two-form `fieldOf A = dA` (Landau–Lifshitz, *The Classical Theory of Fields*, §§16, 18).

* `fieldOf_closed`: the field of a potential satisfies the homogeneous equation `dF = 0`.
* `fieldOf_gaugeShift`: the gauge change `A ↦ A + dχ` by a smooth function `χ` does not change
  the field; `source_gaugeShift` and `maxwell_gaugeShift_iff` are the consequences for the
  current and for the equations of Maxwell.
* `fieldOf_pullback`: the field of the pullback of a potential by a smooth map is the pullback
  of the field, so the field does not depend on the co-ordinates.
* `fieldOf_ofFlat`: for a smooth potential on flat space-time it is the field tensor.

A potential here is defined on the whole manifold. Potentials that are defined on the sets of a
cover and differ by gauge changes, the connections of a line bundle, are not treated.
-/

@[expose] public section
noncomputable section
open Bundle
open scoped Manifold ContDiff

namespace ProjectAinos.Electrodynamics.Curved
open SmoothGeometry SmoothGeometry.DifferentialForm

variable {M : Type} [TopologicalSpace M] [ChartedSpace (MinkowskiModel 3) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel 3) ∞ M]

/-- A gauge function: a smooth function on the manifold, as a form of degree zero. -/
abbrev GaugeFunction := SmoothForm 𝓘(ℝ, MinkowskiModel 3) M 0

/-- The field `dA` of a potential. -/
def fieldOf (A : Potential (M := M)) : Field (M := M) := smoothExteriorDerivative A

/-- The field of a potential satisfies the homogeneous equation. -/
theorem fieldOf_closed (A : Potential (M := M)) : smoothExteriorDerivative (fieldOf A) = 0 :=
  smoothExteriorDerivative_squared A

/-- The gauge change `A ↦ A + dχ`. -/
def gaugeShift (A : Potential (M := M)) (χ : GaugeFunction (M := M)) : Potential (M := M) :=
  A + smoothExteriorDerivative χ

/-- The gauge change does not change the field. -/
theorem fieldOf_gaugeShift (A : Potential (M := M)) (χ : GaugeFunction (M := M)) :
    fieldOf (gaugeShift A χ) = fieldOf A := by
  rw [fieldOf, gaugeShift, smoothExteriorDerivative_add, smoothExteriorDerivative_squared,
    add_zero]
  rfl

/-- The current of the field of a potential does not depend on the gauge. -/
theorem source_gaugeShift (g : LorentzMetric .timeNegative 3 M) (o : OrientedAtlas 4 M)
    (A : Potential (M := M)) (χ : GaugeFunction (M := M)) :
    source g o (fieldOf (gaugeShift A χ)) = source g o (fieldOf A) := by
  rw [fieldOf_gaugeShift]

/-- The equations of Maxwell for the field of a potential do not depend on the gauge. -/
theorem maxwell_gaugeShift_iff (g : LorentzMetric .timeNegative 3 M) (o : OrientedAtlas 4 M)
    (A : Potential (M := M)) (χ : GaugeFunction (M := M)) (j : CurrentVector (M := M)) :
    Maxwell g o (fieldOf (gaugeShift A χ)) j ↔ Maxwell g o (fieldOf A) j := by
  rw [fieldOf_gaugeShift]

/-- The field of a potential and its current satisfy the equations of Maxwell. -/
theorem maxwell_fieldOf (g : LorentzMetric .timeNegative 3 M) (o : OrientedAtlas 4 M)
    (A : Potential (M := M)) : Maxwell g o (fieldOf A) (source g o (fieldOf A)) :=
  potential_maxwell g o A

section Pullback

variable {N : Type} [TopologicalSpace N] [ChartedSpace (MinkowskiModel 3) N]
  [IsManifold 𝓘(ℝ, MinkowskiModel 3) ∞ N]

/-- The field of the pullback of a potential is the pullback of the field. -/
theorem fieldOf_pullback (f : C^∞⟮𝓘(ℝ, MinkowskiModel 3), M; 𝓘(ℝ, MinkowskiModel 3), N⟯)
    (A : Potential (M := N)) :
    fieldOf (smoothPullback 𝓘(ℝ, MinkowskiModel 3) 𝓘(ℝ, MinkowskiModel 3) f A) =
      smoothPullback 𝓘(ℝ, MinkowskiModel 3) 𝓘(ℝ, MinkowskiModel 3) f (fieldOf A) :=
  smoothExteriorDerivative_pullback f A

end Pullback

/-- For a smooth potential on flat space-time the field is the field tensor. -/
theorem fieldOf_ofFlat (A : Electrodynamics.Potential) (hA : ContDiff ℝ ∞ A)
    (x : SpecialRelativity.Spacetime) :
    fieldOf (ofFlat A hA) x = Electrodynamics.fieldTensor A x :=
  congrFun (smoothExteriorDerivative_flat A hA) x

end ProjectAinos.Electrodynamics.Curved
