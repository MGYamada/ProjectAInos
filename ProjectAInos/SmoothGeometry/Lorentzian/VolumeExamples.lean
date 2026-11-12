/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.VolumeForm
public import ProjectAInos.SmoothGeometry.Lorentzian.ChartExamples
public import ProjectAInos.SmoothGeometry.Lorentzian.ConformalExample
public import ProjectAInos.SmoothGeometry.Minkowski.Matrix
public import ProjectAInos.SmoothGeometry.DifferentialForm.NativeExamples

/-! # Exact Lorentz density and oriented-volume examples

Both metric signatures, a genuine nonlinear chart, orientation reversal and
the curved conformal plane fix the normalization without assuming flatness.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff

namespace ProjectAInos.SmoothGeometry.LorentzianVolumeExamples
open LorentzMetric DifferentialForm

/-- The absolute determinant of the Minkowski matrix is one in either signature. -/
theorem minkowski_abs_det (σ : LorentzConvention) (d : ℕ) :
    |(Minkowski.metricMatrix σ d).det| = 1 := by
  rw [Minkowski.metricMatrix, Matrix.det_diagonal, Finset.abs_prod]
  apply Finset.prod_eq_one
  intro i _
  cases σ <;> by_cases h : i = 0 <;> simp [lorentzSign, h]

/-- Standard Minkowski density has no dimension-dependent factorial or sign. -/
theorem minkowski_density (σ : LorentzConvention) (d : ℕ) (x : MinkowskiModel d) :
    (minkowskiMetric σ d).chartDensity (OpenPartialHomeomorph.refl (MinkowskiModel d)) x = 1 := by
  rw [chartDensity_refl]
  have h : (fun i j => (minkowskiMetric σ d).form x (Pi.single i 1) (Pi.single j 1)) =
      Minkowski.metricMatrix σ d := by
    rw [← Minkowski.metricMatrix_eq]
    ext i j
    rfl
  rw [h, minkowski_abs_det, Real.sqrt_one]

theorem minkowski_volume (σ : LorentzConvention) (d : ℕ) (x : MinkowskiModel d) :
    (minkowskiMetric σ d).volumeForm (OrientedAtlas.standard (d + 1)) x = coordinateForm id := by
  rw [volumeForm_standard, minkowski_density, one_smul]

theorem minkowski_reverse_volume (σ : LorentzConvention) (d : ℕ) (x : MinkowskiModel d) :
    (minkowskiMetric σ d).volumeForm (OrientedAtlas.standard (d + 1)).reverse x =
      -coordinateForm id := by
  rw [volumeForm_reverse]
  change -((minkowskiMetric σ d).volumeForm (OrientedAtlas.standard (d + 1)) x) = _
  rw [minkowski_volume]

open LorentzianCharts

/-- The nonconstant shear metric still has unit density in its original chart. -/
theorem shear_density (x : Plane) : metric.chartDensity standardChart x = 1 := by
  rw [show standardChart = OpenPartialHomeomorph.refl Plane from rfl, chartDensity_refl]
  have h : Matrix.det (fun i j => metric.form x (Pi.single i 1) (Pi.single j 1)) = -1 := by
    rw [Matrix.det_fin_two (fun i j => metric.form x (Pi.single i 1) (Pi.single j 1))]
    simp [metric_coordinates]
  rw [h]
  norm_num

theorem shear_volume (x : Plane) :
    metric.volumeForm (OrientedAtlas.standard 2) x = NativeExamples.area x := by
  rw [volumeForm_standard]
  change metric.chartDensity standardChart x • coordinateForm id = NativeExamples.area x
  rw [shear_density, one_smul]
  rfl

theorem shear_jacobian_det (x : Plane) :
    Matrix.det (fun i j => fderiv ℝ shear x (Pi.single j 1) i) = 1 := by
  rw [Matrix.det_fin_two (fun i j => fderiv ℝ shear x (Pi.single j 1) i),
    (hasFDerivAt_shear x).fderiv]
  simp [shearLinear]

/-- The actual inertial chart has the same unit coefficient, using its transition Jacobian. -/
theorem shear_inertial_density (x : Plane) : metric.chartDensity inertialChart x = 1 := by
  have h := metric.chartDensity_transition standardChart_mem_maximalAtlas
    inertialChart_mem_maximalAtlas (x := x) (by trivial) (by trivial)
  change metric.chartDensity standardChart x =
    |Matrix.det (fun i j => fderiv ℝ shear x (Pi.single j 1) i)| *
      metric.chartDensity inertialChart x at h
  rw [shear_density, shear_jacobian_det, abs_one, one_mul] at h
  exact h.symm

/-- A different oriented atlas, consisting of the nonlinear inertial charts. -/
def shearOrientation : OrientedAtlas 2 Plane where
  chart _ := inertialChart
  mem_atlas _ := inertialChart_mem_maximalAtlas
  mem_source _ := by trivial
  sign _ := 1
  sign_sq _ := one_pow 2
  compatible p q x _ _ := by
    have h : (inertialChart ∘ inertialChart.symm : Plane → Plane) = id :=
      funext shear_unshear
    change 1 * Matrix.det (fun i j => fderiv ℝ (inertialChart ∘ inertialChart.symm)
      (inertialChart x) (Pi.single j 1) i) =
      1 * |Matrix.det (fun i j => fderiv ℝ (inertialChart ∘ inertialChart.symm)
        (inertialChart x) (Pi.single j 1) i)|
    rw [h]
    exact (OrientedAtlas.standard 2).compatible p q (inertialChart x) (by trivial) (by trivial)

theorem shear_orientation_compatible : (OrientedAtlas.standard 2).Compatible shearOrientation := by
  intro _ _ x _ _
  change 1 * Matrix.det (fun i j => fderiv ℝ shear x (Pi.single j 1) i) =
    1 * |Matrix.det (fun i j => fderiv ℝ shear x (Pi.single j 1) i)|
  rw [shear_jacobian_det, abs_one]

/-- Changing the signed chart cover does not change the constructed native volume. -/
theorem shear_volume_atlas :
    metric.volumeForm shearOrientation = metric.volumeForm (OrientedAtlas.standard 2) :=
  (metric.volumeForm_eq_of_compatible _ _ shear_orientation_compatible).symm

/-- An orientation-reversing, non-unit change of tangent basis has signed volume `-6`. -/
theorem scaled_reversed_volume (x : Plane) :
    (minkowskiMetric .timeNegative 1).volumeForm (OrientedAtlas.standard 2) x
      ![![2, 0], ![0, -3]] = -6 := by
  rw [minkowski_volume]
  change coordinateForm (n := 2) (k := 2) id ![![2, 0], ![0, -3]] = -6
  rw [coordinateForm_apply]
  norm_num [coordinateForm_apply, Matrix.det_fin_two]

/-- The same basis change has positive density `6`, not signed volume `-6`. -/
theorem scaled_reversed_density (x : Plane) :
    (minkowskiMetric .timeNegative 1).volumeDensity x ![![2, 0], ![0, -3]] = 6 := by
  rw [← abs_volumeForm _ (OrientedAtlas.standard 2), scaled_reversed_volume]
  norm_num

/-- The conformal density is position-dependent and strictly positive. -/
theorem conformal_density (x : Plane) :
    LorentzianConformalExample.metric.chartDensity (OpenPartialHomeomorph.refl Plane) x =
      Real.exp (2 * (x 1) ^ 2) := by
  rw [chartDensity_refl]
  have h : Matrix.det (fun i j => LorentzianConformalExample.metric.form x
      (Pi.single i 1) (Pi.single j 1)) = -(Real.exp (2 * (x 1) ^ 2)) ^ 2 := by
    rw [Matrix.det_fin_two (fun i j => LorentzianConformalExample.metric.form x
      (Pi.single i 1) (Pi.single j 1))]
    simp [LorentzianConformalExample.metric_coordinates]
    ring
  rw [h, abs_neg, abs_of_nonneg (sq_nonneg _), Real.sqrt_sq_eq_abs,
    abs_of_pos (Real.exp_pos _)]

theorem conformal_volume (x : Plane) :
    LorentzianConformalExample.metric.volumeForm (OrientedAtlas.standard 2) x =
      Real.exp (2 * (x 1) ^ 2) • NativeExamples.area x := by
  rw [volumeForm_standard, conformal_density]
  congr 1

end ProjectAInos.SmoothGeometry.LorentzianVolumeExamples
