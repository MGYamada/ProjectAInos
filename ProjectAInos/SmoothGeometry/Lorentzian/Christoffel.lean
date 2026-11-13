/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.Regularity
public import ProjectAInos.SmoothGeometry.Lorentzian.Tensor

/-! # Coordinate coefficients of the Lorentz Levi-Civita connection

On a coordinate model, the constant coordinate fields use the canonical
identification with the actual tangent bundle. Connection coefficients are
evaluations of the constructed native connection, not independent arrays.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle FiberBundle VectorField ContinuousLinearMap
open scoped Manifold ContDiff

namespace ProjectAInos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ}

local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)

/-- The constant vector field on a coordinate model, in its actual tangent bundle. -/
def modelField (v : MinkowskiModel d) (x : MinkowskiModel d) : TangentSpace I x :=
  (NormedSpace.fromTangentSpace x).symm v

theorem modelField_contMDiff (v : MinkowskiModel d) :
    ContMDiff I ((I).prod I) ∞ (T% (modelField v)) := by
  intro x
  rw [contMDiffAt_section]
  simpa [modelField, NormedSpace.fromTangentSpace, tangentSpaceCastModel,
    TangentBundle.trivializationAt_apply] using!
    (contMDiffAt_const (c := v) : ContMDiffAt I I ∞ (fun _ : E => v) x)

/-- Constant coordinate fields commute. -/
@[simp] theorem modelField_bracket (v w : MinkowskiModel d) (x : MinkowskiModel d) :
    mlieBracket I (modelField v) (modelField w) x = 0 := by
  rw [← mlieBracketWithin_univ, mlieBracketWithin_eq_lieBracketWithin]
  change lieBracketWithin ℝ (fun _ : E => v) (fun _ : E => w) Set.univ x = 0
  simp [lieBracketWithin]

variable (g : LorentzMetric σ d (MinkowskiModel d))

/-- Metric coefficients in the standard coordinates of the model. -/
def modelComponent (x : MinkowskiModel d) (i j : Fin (d + 1)) : ℝ :=
  g.form x (modelField (Pi.single i 1) x) (modelField (Pi.single j 1) x)

/-- `Γ^k_ij` is extracted from `∇_{∂ᵢ} ∂ⱼ` using the model coordinates. -/
def christoffel (x : MinkowskiModel d) (k i j : Fin (d + 1)) : ℝ :=
  NormedSpace.fromTangentSpace x
    (g.leviCivita (modelField (Pi.single j 1)) x (modelField (Pi.single i 1) x)) k

/-- The Koszul formula in constant coordinate directions has no Lie-bracket terms. -/
theorem modelField_leviCivita_pairing (x v w z : MinkowskiModel d) :
    g.form x (g.leviCivita (modelField w) x (modelField v x)) (modelField z x) =
      (fderiv ℝ (fun y => g.form y (modelField w y) (modelField z y)) x v +
       fderiv ℝ (fun y => g.form y (modelField z y) (modelField v y)) x w -
       fderiv ℝ (fun y => g.form y (modelField v y) (modelField w y)) x z) / 2 := by
  rw [g.leviCivita_pairing
    ((modelField_contMDiff v).mdifferentiableAt (by simp))
    ((modelField_contMDiff w).mdifferentiableAt (by simp))
    ((modelField_contMDiff z).mdifferentiableAt (by simp))]
  simp [koszul, mvfderiv_eq_fderiv, modelField]

/-- The standard Christoffel formula, with inverse coefficients derived from `sharp`. -/
theorem christoffel_eq (x : MinkowskiModel d) (k i j : Fin (d + 1)) :
    g.christoffel x k i j = ∑ l,
      g.inverseComponent x (NormedSpace.fromTangentSpace x) k l *
        (fderiv ℝ (fun y => g.modelComponent y j l) x (Pi.single i 1) +
         fderiv ℝ (fun y => g.modelComponent y l i) x (Pi.single j 1) -
         fderiv ℝ (fun y => g.modelComponent y i j) x (Pi.single l 1)) / 2 := by
  let a := g.leviCivita (modelField (Pi.single j 1)) x (modelField (Pi.single i 1) x)
  have ha := g.sharp_flat x a
  change NormedSpace.fromTangentSpace x a k = _
  rw [← ha, Tensor.covector_eq_sum x (NormedSpace.fromTangentSpace x) (g.flat x a)]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    flat_apply, inverseComponent]
  apply Finset.sum_congr rfl
  intro l _
  change g.form x a (modelField (Pi.single l 1) x) *
      NormedSpace.fromTangentSpace x
        (g.sharp x (Tensor.coordinateCovector x (NormedSpace.fromTangentSpace x) l)) k = _
  rw [show g.form x a (modelField (Pi.single l 1) x) = _ from
    g.modelField_leviCivita_pairing x (Pi.single i 1) (Pi.single j 1) (Pi.single l 1)]
  simp only [modelComponent]
  ring

/-- Linearity in the tangent direction reconstructs the coefficient sum. -/
theorem christoffel_direction (x v : MinkowskiModel d) (k j : Fin (d + 1)) :
    NormedSpace.fromTangentSpace x
      (g.leviCivita (modelField (Pi.single j 1)) x (modelField v x)) k =
        ∑ i, v i * g.christoffel x k i j := by
  have hv : modelField v x = ∑ i, v i • modelField (Pi.single i 1) x := by
    apply (NormedSpace.fromTangentSpace x).injective
    simpa [modelField] using pi_eq_sum_univ' v
  rw [hv]
  simp [christoffel]

/-- The connection on an arbitrary differentiable coordinate vector field has
the usual derivative term plus the Christoffel correction. -/
theorem leviCivita_model_coordinates {Y : MinkowskiModel d → MinkowskiModel d}
    {x : MinkowskiModel d} (hY : DifferentiableAt ℝ Y x)
    (v : MinkowskiModel d) (k : Fin (d + 1)) :
    NormedSpace.fromTangentSpace x
      (g.leviCivita (fun y => modelField (Y y) y) x (modelField v x)) k =
        fderiv ℝ Y x v k + ∑ i, ∑ j, g.christoffel x k i j * v i * Y x j := by
  have hf (j : Fin (d + 1)) : MDifferentiableAt I 𝓘(ℝ) (fun y => Y y j) x := by
    exact ((proj j : E →L[ℝ] ℝ).differentiableAt.comp x hY).mdifferentiableAt
  have hb (j : Fin (d + 1)) :=
    (modelField_contMDiff (Pi.single j 1)).mdifferentiableAt (x := x) (by simp)
  have hV (j : Fin (d + 1)) (_ : j ∈ Finset.univ) := (hf j).smul_section (hb j)
  have he : (fun y => modelField (Y y) y) =
      ∑ j : Fin (d + 1), (fun y => Y y j) • modelField (Pi.single j 1) := by
    funext y
    apply (NormedSpace.fromTangentSpace y).injective
    simpa [modelField] using pi_eq_sum_univ' (Y y)
  have hd (j : Fin (d + 1)) : fderiv ℝ (fun y => Y y j) x =
      (proj j : E →L[ℝ] ℝ).comp (fderiv ℝ Y x) :=
    ((proj j : E →L[ℝ] ℝ).hasFDerivAt.comp x hY.hasFDerivAt).fderiv
  rw [he, g.leviCivita_sum _ _ hV]
  simp only [sum_apply, map_sum, Finset.sum_apply]
  simp_rw [g.leviCivita.isCovariantDerivativeOnUniv.leibniz (hb _) (hf _)]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply,
    smul_apply, map_add, map_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, christoffel_direction]
  simp [modelField, mvfderiv_eq_fderiv, hd, Finset.sum_add_distrib, Finset.mul_sum,
    Pi.single_apply]
  rw [add_comm, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The coordinate coefficients are smooth functions, as consequences of the
native connection regularity, without extra coefficient assumptions. -/
theorem christoffel_contDiff (k i j : Fin (d + 1)) :
    ContDiff ℝ ∞ (fun x => g.christoffel x k i j) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have h := (g.contMDiffAt_leviCivita (n := ⊤)
    (by simpa using modelField_contMDiff (Pi.single j 1) x)).clm_bundle_apply
      (modelField_contMDiff (Pi.single i 1) x)
  rw [contMDiffAt_section] at h
  have hk := ((proj k : E →L[ℝ] ℝ).contDiff.contDiffAt).comp x h.contDiffAt
  simpa [christoffel, NormedSpace.fromTangentSpace, tangentSpaceCastModel,
    TangentBundle.trivializationAt_apply] using! hk

/-- Torsion-freeness gives symmetry in the two lower coordinate indices. -/
theorem christoffel_symmetric (x : MinkowskiModel d) (k i j : Fin (d + 1)) :
    g.christoffel x k i j = g.christoffel x k j i := by
  have h := (CovariantDerivative.torsion_eq_zero_iff g.leviCivita).mp
    g.leviCivita_torsion
    ((modelField_contMDiff (Pi.single i 1)).mdifferentiableAt (by simp) (x := x))
    ((modelField_contMDiff (Pi.single j 1)).mdifferentiableAt (by simp) (x := x))
  rw [modelField_bracket, sub_eq_zero] at h
  exact congrArg (fun v => NormedSpace.fromTangentSpace x v k) h

@[simp] theorem christoffel_opposite (x : MinkowskiModel d) (k i j : Fin (d + 1)) :
    g.opposite.christoffel x k i j = g.christoffel x k i j := by
  simp only [christoffel, leviCivita_opposite]

/-- The native Minkowski connection has zero Christoffel coefficients in its
standard coordinates, for both Lorentz signatures and every dimension. -/
@[simp] theorem minkowski_christoffel (σ : LorentzConvention) (d : ℕ)
    (x : MinkowskiModel d) (k i j : Fin (d + 1)) :
    (minkowskiMetric σ d).christoffel x k i j = 0 := by
  rw [christoffel_eq]
  have hc (y : MinkowskiModel d) (a b : Fin (d + 1)) :
      (minkowskiMetric σ d).modelComponent y a b =
        minkowskiForm σ d (Pi.single a 1) (Pi.single b 1) := rfl
  simp [hc]

end ProjectAInos.SmoothGeometry.LorentzMetric
