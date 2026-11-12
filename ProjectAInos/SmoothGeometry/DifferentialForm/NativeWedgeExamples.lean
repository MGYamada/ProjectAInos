/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.DifferentialForm.NativeExteriorExamples
public import ProjectAInos.SmoothGeometry.DifferentialForm.NativeWedgeCalculus

/-! # Native wedge normalization, nonlinear charts and the Leibniz sign -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff

namespace ProjectAInos.SmoothGeometry.DifferentialForm.NativeExamples
open LorentzianCharts

def temporal : SmoothForm 𝓘(ℝ, Plane) Plane 1 :=
  ofFlat (fun _ => coordinateForm ![0]) contDiff_const

theorem temporal_wedge_spatial : smoothWedge temporal spatial = area := by
  ext x : 1
  change nativeWedge (fun _ => coordinateForm ![0]) (fun _ => coordinateForm ![1]) x =
    coordinateForm ![0, 1]
  rw [nativeWedge_flat]
  exact wedge_ofCovectors _ _

/-- The product of the two pulled-back covectors has determinant normalization one. -/
theorem shear_wedge (p v w : Plane) :
    smoothWedge
      (smoothPullback 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shearDiffeomorph.toContMDiffMap temporal)
      (smoothPullback 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shearDiffeomorph.toContMDiffMap spatial) p ![v, w] =
      v 0 * w 1 - w 0 * v 1 := by
  rw [← smoothPullback_wedge, temporal_wedge_spatial]
  exact area_shear p v w

/-- Wedge agrees in the actual nonlinear maximal-atlas chart. -/
theorem inertial_chart_wedge (p : Plane) :
    wedge (chartCoefficients inertialChart (fun x => temporal x))
      (chartCoefficients inertialChart (fun x => spatial x)) p =
      chartCoefficients inertialChart (fun x => area x) p := by
  rw [← chartCoefficients_smoothWedge temporal spatial inertialChart_mem_maximalAtlas
    (show p ∈ inertialChart.target from by simp [inertialChart]), temporal_wedge_spatial]

/-- A nonconstant singular map annihilates the product of its pulled-back covectors. -/
theorem timeProjection_wedge (p v w : Plane) :
    smoothWedge
      (smoothPullback 𝓘(ℝ, Plane) 𝓘(ℝ, Plane)
        (timeProjection : C^∞⟮𝓘(ℝ, Plane), Plane; 𝓘(ℝ, Plane), Plane⟯) temporal)
      (smoothPullback 𝓘(ℝ, Plane) 𝓘(ℝ, Plane)
        (timeProjection : C^∞⟮𝓘(ℝ, Plane), Plane; 𝓘(ℝ, Plane), Plane⟯) spatial) p ![v, w] = 0 := by
  rw [← smoothPullback_wedge, temporal_wedge_spatial]
  exact area_timeProjection p v w

/-- The time-axis inclusion, using the one-dimensional finite coordinate model. -/
def oneTimeAxis : (Fin 1 → ℝ) →L[ℝ] Plane := timeAxis.comp (ContinuousLinearMap.proj 0)

theorem oneTimeAxis_wedge (t v w : Fin 1 → ℝ) :
    smoothWedge
      (smoothPullback 𝓘(ℝ, Fin 1 → ℝ) 𝓘(ℝ, Plane)
        (oneTimeAxis : C^∞⟮𝓘(ℝ, Fin 1 → ℝ), (Fin 1 → ℝ); 𝓘(ℝ, Plane), Plane⟯) temporal)
      (smoothPullback 𝓘(ℝ, Fin 1 → ℝ) 𝓘(ℝ, Plane)
        (oneTimeAxis : C^∞⟮𝓘(ℝ, Fin 1 → ℝ), (Fin 1 → ℝ); 𝓘(ℝ, Plane), Plane⟯) spatial) t ![v, w] = 0 := by
  rw [← smoothPullback_wedge, temporal_wedge_spatial, smoothPullback_apply]
  change coordinateForm ![0, 1]
    (fun i => mfderiv 𝓘(ℝ, Fin 1 → ℝ) 𝓘(ℝ, Plane) oneTimeAxis t (![v, w] i)) = 0
  have hd : mfderiv 𝓘(ℝ, Fin 1 → ℝ) 𝓘(ℝ, Plane) oneTimeAxis t = oneTimeAxis := by
    rw [mfderiv_eq_fderiv, oneTimeAxis.fderiv]
    rfl
  rw [hd]
  simp only [coordinateForm_apply, Matrix.det_fin_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  change (v 0 * 1) * (w 0 * 0) - (v 0 * 0) * (w 0 * 1) = 0
  ring

abbrev ThreeSpace := Fin 3 → ℝ

def axisZero : SmoothForm 𝓘(ℝ, ThreeSpace) ThreeSpace 1 :=
  ofFlat (fun _ => coordinateForm ![0]) contDiff_const

def secondPotentialCoefficients : Form ThreeSpace 1 := fun x => x 1 • coordinateForm ![2]

def secondPotential : SmoothForm 𝓘(ℝ, ThreeSpace) ThreeSpace 1 :=
  ofFlat secondPotentialCoefficients
    ((ContinuousLinearMap.proj 1 : ThreeSpace →L[ℝ] ℝ).smulRight (coordinateForm ![2])).contDiff

def standardVolume : SmoothForm 𝓘(ℝ, ThreeSpace) ThreeSpace 3 :=
  ofFlat (fun _ => coordinateForm ![0, 1, 2]) contDiff_const

theorem standardVolume_nonzero : standardVolume ≠ 0 := by
  intro h
  have he := congrArg (fun α : SmoothForm 𝓘(ℝ, ThreeSpace) ThreeSpace 3 =>
    α 0 ![Pi.single 0 1, Pi.single 1 1, Pi.single 2 1]) h
  change coordinateForm ![0, 1, 2] ![Pi.single 0 1, Pi.single 1 1, Pi.single 2 1] = 0 at he
  norm_num [coordinateForm_apply, Matrix.det_fin_three, Pi.single_apply] at he

/-- A direct derivative computation detects the minus sign in `d(dx⁰ ∧ x¹ dx²)`. -/
theorem negative_leibniz_example :
    smoothExteriorDerivative (smoothWedge axisZero secondPotential) = -standardVolume := by
  have hw : wedge (fun _ : ThreeSpace => coordinateForm ![0]) secondPotentialCoefficients =
      fun x => x 1 • coordinateForm ![0, 2] := by
    funext x
    change wedgeFiber (coordinateForm ![0]) (x 1 • coordinateForm ![2]) = _
    rw [map_smul]
    congr 1
    exact wedge_ofCovectors _ _
  ext x v
  change nativeExteriorDerivative
    (nativeWedge (fun _ : ThreeSpace => coordinateForm ![0]) secondPotentialCoefficients) x v =
      -coordinateForm ![0, 1, 2] v
  rw [nativeWedge_flat, hw, nativeExteriorDerivative_flat]
  have hd : fderiv ℝ (fun y : ThreeSpace => y 1 • coordinateForm (n := 3) ![0, 2]) x =
      (ContinuousLinearMap.proj 1 : ThreeSpace →L[ℝ] ℝ).smulRight (coordinateForm (n := 3) ![0, 2]) :=
    ((ContinuousLinearMap.proj 1 : ThreeSpace →L[ℝ] ℝ).smulRight (coordinateForm (n := 3) ![0, 2])).fderiv
  simp only [extDeriv, hd]
  change (ContinuousAlternatingMap.alternatizeUncurryFin (n := 2)
    ((ContinuousLinearMap.proj 1 : ThreeSpace →L[ℝ] ℝ).smulRight
      (coordinateForm (n := 3) ![0, 2]))) (v : Fin 3 → ThreeSpace) = _
  rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  simp [coordinateForm_apply, Matrix.det_fin_two, Matrix.det_fin_three, Fin.removeNth,
    Fin.sum_univ_succ]
  ring

end ProjectAInos.SmoothGeometry.DifferentialForm.NativeExamples
