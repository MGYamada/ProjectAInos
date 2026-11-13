/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Electrodynamics.Field
public import ProjectAInos.SmoothGeometry.DifferentialForm.OneForm
public import ProjectAInos.SmoothGeometry.DifferentialForm.NativeExteriorDerivative
public import ProjectAInos.SmoothGeometry.Lorentzian.HodgeSquare

/-! # Maxwell forms on a fixed Lorentz spacetime

Time comes first, signature is `(-+++)`, and the constitutive normalization
is one. The public convention is `H = -⋆F`, `J = ⋆(j♭)`, so the source vector
satisfies `∇_μ F^{μν} = j^ν`. Under the flat conventions `F_{0i} = -E_i` and
particle coupling `+e∫A`, the compatible matter current is `-j`. That bridge is
a recorded proof obligation: see the source sign contract in
`docs/cinfty-electrodynamics.md`. All objects are smooth sections on the actual
tangent bundle. Maxwell equations are explicit physical premises; no field
action or gravitational dynamics is assumed.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Bundle
open scoped Manifold ContDiff

namespace ProjectAInos.Electrodynamics.Curved
open SmoothGeometry SmoothGeometry.DifferentialForm

variable {M : Type} [TopologicalSpace M] [ChartedSpace (MinkowskiModel 3) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel 3) ∞ M]

abbrev CurrentVector :=
  Cₛ^∞⟮𝓘(ℝ, MinkowskiModel 3); MinkowskiModel 3,
    (fun x : M => TangentSpace 𝓘(ℝ, MinkowskiModel 3) x)⟯

abbrev Field := SmoothForm 𝓘(ℝ, MinkowskiModel 3) M 2
abbrev CurrentForm := SmoothForm 𝓘(ℝ, MinkowskiModel 3) M 3
abbrev Potential := SmoothForm 𝓘(ℝ, MinkowskiModel 3) M 1

/-- Lower the actual current vector and identify its covector with an alternating one-form. -/
def currentOneForm (g : LorentzMetric .timeNegative 3 M) (j : CurrentVector (M := M)) :
    SmoothForm 𝓘(ℝ, MinkowskiModel 3) M 1 :=
  smoothOneFormEquiv 𝓘(ℝ, MinkowskiModel 3) (g.lower j)

@[simp] theorem currentOneForm_apply (g : LorentzMetric .timeNegative 3 M)
    (j : CurrentVector (M := M)) (x : M) (v : Fin 1 → TangentSpace 𝓘(ℝ, MinkowskiModel 3) x) :
    currentOneForm g j x v = g.form x (j x) (v 0) := rfl

/-- The physical current three-form is `⋆(j♭)`. -/
def currentForm (g : LorentzMetric .timeNegative 3 M) (o : OrientedAtlas 4 M)
    (j : CurrentVector (M := M)) : CurrentForm (M := M) :=
  g.smoothHodge o (by decide : 1 + 3 = 3 + 1) (currentOneForm g j)

/-- The inverse current identification uses `⋆² = +1` in degrees one and three. -/
def currentVector (g : LorentzMetric .timeNegative 3 M) (o : OrientedAtlas 4 M)
    (J : CurrentForm (M := M)) : CurrentVector (M := M) :=
  g.raise ((smoothOneFormEquiv 𝓘(ℝ, MinkowskiModel 3)).symm
    (g.smoothHodge o (by decide : 3 + 1 = 3 + 1) J))

theorem currentForm_currentVector (g : LorentzMetric .timeNegative 3 M) (o : OrientedAtlas 4 M)
    (J : CurrentForm (M := M)) : currentForm g o (currentVector g o J) = J := by
  unfold currentForm currentOneForm currentVector
  rw [g.lower_raise, LinearEquiv.apply_symm_apply, g.smoothHodge_square]
  norm_num [LorentzConvention.negativeIndex]

theorem currentVector_currentForm (g : LorentzMetric .timeNegative 3 M) (o : OrientedAtlas 4 M)
    (j : CurrentVector (M := M)) : currentVector g o (currentForm g o j) = j := by
  unfold currentVector currentForm currentOneForm
  rw [g.smoothHodge_square]
  norm_num [LorentzConvention.negativeIndex, g.raise_lower]

/-- No current degrees of freedom are lost by the three-form representation. -/
def currentEquiv (g : LorentzMetric .timeNegative 3 M) (o : OrientedAtlas 4 M) :
    CurrentVector (M := M) ≃ CurrentForm (M := M) where
  toFun := currentForm g o
  invFun := currentVector g o
  left_inv := currentVector_currentForm g o
  right_inv := currentForm_currentVector g o

/-- Constitutive excitation on the fixed background, with normalization one. -/
def excitation (g : LorentzMetric .timeNegative 3 M) (o : OrientedAtlas 4 M)
    (F : Field (M := M)) : Field (M := M) :=
  -g.smoothHodge o (by decide : 2 + 2 = 3 + 1) F

/-- Premetric Maxwell equations with the fixed Lorentz constitutive law and actual current. -/
def Maxwell (g : LorentzMetric .timeNegative 3 M) (o : OrientedAtlas 4 M)
    (F : Field (M := M)) (j : CurrentVector (M := M)) : Prop :=
  smoothExteriorDerivative F = 0 ∧
    smoothExteriorDerivative (excitation g o F) = currentForm g o j

/-- The sourced Maxwell equation implies closedness of the actual current three-form. -/
theorem current_closed_of_source (g : LorentzMetric .timeNegative 3 M) (o : OrientedAtlas 4 M)
    (F : Field (M := M)) (j : CurrentVector (M := M))
    (h : smoothExteriorDerivative (excitation g o F) = currentForm g o j) :
    smoothExteriorDerivative (currentForm g o j) = 0 := by
  rw [← h]
  exact smoothExteriorDerivative_squared (excitation g o F)

theorem Maxwell.current_closed {g : LorentzMetric .timeNegative 3 M} {o : OrientedAtlas 4 M}
    {F : Field (M := M)} {j : CurrentVector (M := M)} (h : Maxwell g o F j) :
    smoothExteriorDerivative (currentForm g o j) = 0 := current_closed_of_source g o F j h.2

/-- The current determined by the actual excitation derivative. -/
def source (g : LorentzMetric .timeNegative 3 M) (o : OrientedAtlas 4 M)
    (F : Field (M := M)) : CurrentVector (M := M) :=
  currentVector g o (smoothExteriorDerivative (excitation g o F))

theorem source_spec (g : LorentzMetric .timeNegative 3 M) (o : OrientedAtlas 4 M)
    (F : Field (M := M)) : currentForm g o (source g o F) =
      smoothExteriorDerivative (excitation g o F) := currentForm_currentVector g o _

/-- The source is unique; the homogeneous equation is the remaining condition on the field. -/
theorem maxwell_iff (g : LorentzMetric .timeNegative 3 M) (o : OrientedAtlas 4 M)
    (F : Field (M := M)) (j : CurrentVector (M := M)) :
    Maxwell g o F j ↔ smoothExteriorDerivative F = 0 ∧ j = source g o F := by
  constructor
  · rintro ⟨hF, hJ⟩
    refine ⟨hF, (currentEquiv g o).injective ?_⟩
    exact hJ.symm.trans (source_spec g o F).symm
  · rintro ⟨hF, rfl⟩
    exact ⟨hF, (source_spec g o F).symm⟩

/-- A global potential produces a closed field with its uniquely determined smooth current. -/
theorem potential_maxwell (g : LorentzMetric .timeNegative 3 M) (o : OrientedAtlas 4 M)
    (A : Potential (M := M)) : Maxwell g o (smoothExteriorDerivative A)
      (source g o (smoothExteriorDerivative A)) :=
  (maxwell_iff g o _ _).mpr ⟨smoothExteriorDerivative_squared A, rfl⟩

/-- Reversing orientation negates the current form. -/
theorem currentForm_reverse (g : LorentzMetric .timeNegative 3 M) (o : OrientedAtlas 4 M)
    (j : CurrentVector (M := M)) : currentForm g o.reverse j = -currentForm g o j :=
  g.smoothHodge_reverse o _ _

theorem excitation_reverse (g : LorentzMetric .timeNegative 3 M) (o : OrientedAtlas 4 M)
    (F : Field (M := M)) : excitation g o.reverse F = -excitation g o F := by
  unfold excitation
  rw [g.smoothHodge_reverse]

/-- The physical equations are independent of the choice of the two opposite orientations. -/
theorem maxwell_reverse_iff (g : LorentzMetric .timeNegative 3 M) (o : OrientedAtlas 4 M)
    (F : Field (M := M)) (j : CurrentVector (M := M)) :
    Maxwell g o.reverse F j ↔ Maxwell g o F j := by
  unfold Maxwell
  rw [excitation_reverse, currentForm_reverse]
  change _ ∧ smoothExteriorDerivativeLinear (-excitation g o F) = -currentForm g o j ↔ _
  rw [map_neg, neg_inj]
  rfl

/-- The excitation on Minkowski space specializes to the existing physical flat star, with minus sign. -/
theorem excitation_flat (F : Electrodynamics.Field) (hF : ContDiff ℝ ∞ F) (x : SpecialRelativity.Spacetime) :
    excitation (minkowskiMetric .timeNegative 3) (OrientedAtlas.standard 4) (ofFlat F hF) x =
      -Electrodynamics.star (F x) := by
  change -(LorentzMetric.smoothHodge _ _ _ _ x) = _
  rw [LorentzMetric.smoothHodge_minkowski]
  rfl

end ProjectAInos.Electrodynamics.Curved
