/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Electrodynamics.Curved
public import ProjectAInos.SmoothGeometry.Minkowski.HodgeFour

/-! # A time-dependent Maxwell field with nonzero current

On Minkowski spacetime, `F = t dt ∧ dx` has `H = t dy ∧ dz` and
`dH = dt ∧ dy ∧ dz`. These are direct component computations, including
the physical constitutive sign, rather than an assumed source equation.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff

namespace ProjectAInos.Electrodynamics.Curved.Examples
open SmoothGeometry SmoothGeometry.DifferentialForm

local notation "E" => SpecialRelativity.Spacetime
local notation "g" => minkowskiMetric LorentzConvention.timeNegative 3
local notation "o" => OrientedAtlas.standard 4

def electric : Field (M := E) := ofFlat (fun x => x 0 • coordinateForm ![0, 1])
  ((ContinuousLinearMap.proj 0 : E →L[ℝ] ℝ).smulRight (coordinateForm ![0, 1])).contDiff

def magneticExcitation : Field (M := E) := ofFlat (fun x => x 0 • coordinateForm ![2, 3])
  ((ContinuousLinearMap.proj 0 : E →L[ℝ] ℝ).smulRight (coordinateForm ![2, 3])).contDiff

def spatialCurrent : CurrentForm (M := E) :=
  ofFlat (fun _ => coordinateForm ![0, 2, 3]) contDiff_const

theorem electric_excitation : excitation g o electric = magneticExcitation := by
  ext x : 1
  unfold electric
  rw [excitation_flat]
  change -Minkowski.hodgeFiber _ _ _ (x 0 • coordinateForm ![0, 1]) = _
  rw [map_smul, Minkowski.hodge_dt_dx]
  simp [magneticExcitation, ofFlat]

theorem electric_closed : smoothExteriorDerivative electric = 0 := by
  ext x v
  change nativeExteriorDerivative (fun y : E => y 0 • coordinateForm ![0, 1]) x v = 0
  rw [nativeExteriorDerivative_flat]
  have hd : fderiv ℝ (fun y : E => y 0 • coordinateForm (n := 4) ![0, 1]) x =
      (ContinuousLinearMap.proj 0 : E →L[ℝ] ℝ).smulRight (coordinateForm (n := 4) ![0, 1]) :=
    ((ContinuousLinearMap.proj 0 : E →L[ℝ] ℝ).smulRight (coordinateForm (n := 4) ![0, 1])).fderiv
  simp only [extDeriv, hd]
  change (ContinuousAlternatingMap.alternatizeUncurryFin (n := 2)
    ((ContinuousLinearMap.proj 0 : E →L[ℝ] ℝ).smulRight
      (coordinateForm (n := 4) ![0, 1]))) (v : Fin 3 → E) = 0
  rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  simp [coordinateForm_apply, Matrix.det_fin_two, Fin.removeNth, Fin.sum_univ_succ]
  ring

theorem magneticExcitation_derivative :
    smoothExteriorDerivative magneticExcitation = spatialCurrent := by
  ext x v
  change nativeExteriorDerivative (fun y : E => y 0 • coordinateForm ![2, 3]) x v =
    coordinateForm ![0, 2, 3] v
  rw [nativeExteriorDerivative_flat]
  have hd : fderiv ℝ (fun y : E => y 0 • coordinateForm (n := 4) ![2, 3]) x =
      (ContinuousLinearMap.proj 0 : E →L[ℝ] ℝ).smulRight (coordinateForm (n := 4) ![2, 3]) :=
    ((ContinuousLinearMap.proj 0 : E →L[ℝ] ℝ).smulRight (coordinateForm (n := 4) ![2, 3])).fderiv
  simp only [extDeriv, hd]
  change (ContinuousAlternatingMap.alternatizeUncurryFin (n := 2)
    ((ContinuousLinearMap.proj 0 : E →L[ℝ] ℝ).smulRight
      (coordinateForm (n := 4) ![2, 3]))) (v : Fin 3 → E) =
      coordinateForm ![0, 2, 3] (v : Fin 3 → E)
  rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  simp [coordinateForm_apply, Matrix.det_fin_two, Matrix.det_fin_three, Fin.removeNth,
    Fin.sum_univ_succ]
  ring

theorem spatialCurrent_nonzero : spatialCurrent ≠ 0 := by
  intro h
  have he := congrArg (fun α : CurrentForm (M := E) =>
    α 0 ![Pi.single 0 1, Pi.single 2 1, Pi.single 3 1]) h
  change coordinateForm ![0, 2, 3] ![Pi.single 0 1, Pi.single 2 1, Pi.single 3 1] = 0 at he
  norm_num [coordinateForm_apply, Matrix.det_fin_three, Pi.single_apply] at he

theorem electric_maxwell : Maxwell g o electric (source g o electric) :=
  (maxwell_iff g o _ _).mpr ⟨electric_closed, rfl⟩

theorem electric_current : currentForm g o (source g o electric) = spatialCurrent := by
  rw [source_spec, electric_excitation, magneticExcitation_derivative]

theorem electric_source_nonzero : source g o electric ≠ 0 := by
  intro h
  apply spatialCurrent_nonzero
  rw [← electric_current, h]
  have hz : currentOneForm g (0 : CurrentVector (M := E)) = 0 := by
    ext x v
    simp
  simp [currentForm, hz]

end ProjectAInos.Electrodynamics.Curved.Examples
