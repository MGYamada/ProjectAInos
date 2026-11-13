/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.GeneralRelativity.VariationStationary
public import ProjectAInos.GeneralRelativity.ClockExamples
public import ProjectAInos.GeneralRelativity.ManifoldMotion
public import ProjectAInos.GeneralRelativity.ParticleExamples

/-! # A nonlinear family in the nonlinear Minkowski chart

The family is nonlinear in both time and the variation parameter. Its actual
action derivatives are supplied by the native manifold-family theorems.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace ProjectAInos.GeneralRelativity.VariationExamples
open SmoothGeometry LorentzMetric LorentzianCharts

/-- In inertial coordinates: `T=t+εt(1-t)`, `X=ε²t(1-t)`. -/
def nonlinearFamily (p : ℝ × ℝ) : Plane :=
  ![p.2 + p.1 * (p.2 * (1 - p.2)),
    p.1 ^ 2 * (p.2 * (1 - p.2)) - (p.2 + p.1 * (p.2 * (1 - p.2))) ^ 2]

theorem nonlinearFamily_contDiff : ContDiff ℝ ∞ nonlinearFamily := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.2 + p.1 * (p.2 * (1 - p.2)))
    fun_prop
  · change ContDiff ℝ ∞ (fun p : ℝ × ℝ =>
      p.1 ^ 2 * (p.2 * (1 - p.2)) - (p.2 + p.1 * (p.2 * (1 - p.2))) ^ 2)
    fun_prop

theorem nonlinearFamily_reference : (fun t => nonlinearFamily (0, t)) = inertialTimePath := by
  funext t
  simp [nonlinearFamily, inertialTimePath]

theorem nonlinearFamily_left (ε : ℝ) : nonlinearFamily (ε, 0) = nonlinearFamily (0, 0) := by
  simp [nonlinearFamily]

theorem nonlinearFamily_right (ε : ℝ) : nonlinearFamily (ε, 1) = nonlinearFamily (0, 1) := by
  simp [nonlinearFamily]

theorem nonlinearFamily_quadratic_stationary :
    HasDerivAt (fun ε => quadraticAction metric (fun t => nonlinearFamily (ε, t)) 0 1) 0 0 := by
  apply quadraticAction_family_stationary_of_geodesic metric (by norm_num)
    (fun _ _ => (nonlinearFamily_contDiff.of_le (by simp)).contMDiff.contMDiffAt)
    (Filter.Eventually.of_forall nonlinearFamily_left)
    (Filter.Eventually.of_forall nonlinearFamily_right)
  rw [nonlinearFamily_reference]
  exact fun t _ => inertialTimePath_geodesic t (mem_univ _)

theorem nonlinearFamily_free_stationary (m : ℝ) :
    HasDerivAt (fun ε => freeAction metric m (fun t => nonlinearFamily (ε, t)) 0 1) 0 0 := by
  apply freeAction_family_stationary_of_tangential metric m (by norm_num)
    (fun _ _ => (nonlinearFamily_contDiff.of_le (by simp)).contMDiff.contMDiffAt) ?_
    (Filter.Eventually.of_forall nonlinearFamily_left)
    (Filter.Eventually.of_forall nonlinearFamily_right)
  · intro t _
    refine ⟨0, ?_⟩
    rw [nonlinearFamily_reference, (inertialTimePath_geodesic t (mem_univ _)).2, zero_smul]

  · intro t _
    unfold Timelike
    rw [nonlinearFamily_reference, congrFun nonlinearFamily_reference t]
    apply (properSpeed_pos_iff metric _).mp
    simpa only [speedAlong] using!
      (show 0 < speedAlong metric inertialTimePath t by
        rw [ClockExamples.shear_speed]
        norm_num)

/-- A concrete smooth cutoff supported in `[1/4,3/4]` and equal to one
near the midpoint. -/
def localCutoff : ContDiffBump (1 / 2 : ℝ) :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

theorem localCutoff_support : tsupport localCutoff ⊆ Ioo (0 : ℝ) 1 := by
  rw [localCutoff.tsupport_eq]
  intro t ht
  have h := abs_le.mp (show |t - 1 / 2| ≤ 1 / 4 from by
    simpa only [Metric.mem_closedBall, Real.dist_eq, localCutoff] using ht)
  constructor <;> linarith

theorem localCutoff_center : localCutoff (1 / 2) = 1 :=
  localCutoff.one_of_mem_closedBall (by simp [localCutoff])

/-- An actual fixed-endpoint chart family with arbitrary midpoint tangent data. -/
def localTest (w : Plane) :
    Variational.ManifoldCurveVariation (E := Plane) inertialTimePath 0 1 :=
  Variational.chartCurveVariation inertialChart_mem_maximalAtlas isOpen_Ioo Subset.rfl
    (by intro t _; trivial)
    ((tsupport_comp_subset (g := fun c : ℝ => c • w) (zero_smul ℝ w) localCutoff).trans
      localCutoff_support)
    (fun _ _ => (inertialTimePath_contDiff.of_le (by simp)).contMDiff.contMDiffAt)
    (localCutoff.contDiff.smul contDiff_const)

theorem localTest_field_center (w : Plane) :
    variationField (localTest w) (1 / 2) =
      chartField inertialChart w (inertialTimePath (1 / 2)) := by
  rw [localTest, variationField_chart _ _ _ _ _ _ _ (by norm_num)]
  simp only [Function.comp_apply, localCutoff_center, one_smul]

/-- Every actual admissible family, including the compact chart tests,
leaves the quadratic shear-geodesic action stationary. -/
theorem shear_quadratic_stationary {a b : ℝ} (hab : a < b) :
    QuadraticStationary metric inertialTimePath a b :=
  (quadraticStationary_iff_geodesic metric hab
    (fun _ _ => (inertialTimePath_contDiff.of_le (by simp)).contMDiff.contMDiffAt)).mpr
      (fun t _ => inertialTimePath_geodesic t (mem_univ _))

theorem localTest_quadratic_stationary (w : Plane) :
    HasDerivAt (fun ε => quadraticAction metric (fun t => (localTest w).family (ε, t)) 0 1)
      0 0 := shear_quadratic_stationary (by norm_num) (localTest w)

/-- The exponential clock is stationary under all native manifold families,
not just affine coordinate perturbations. -/
theorem exponentialClock_native_free_stationary {m a b : ℝ} (hm : 0 < m) (hab : a < b) :
    FreeStationary metric m ParticleExamples.exponentialClock a b := by
  apply (freeStationary_iff_tangential metric hm hab
    (fun _ _ => (ParticleExamples.exponentialClock_contDiff.of_le (by simp)).contMDiff.contMDiffAt)
    (fun t _ => ParticleExamples.exponentialClock_timelike t)).mpr
  intro t _
  exact ⟨1, by simpa only [one_smul] using ParticleExamples.exponentialClock_acceleration t⟩

theorem exponentialClock_not_native_quadratic_stationary {a b : ℝ} (hab : a < b) :
    ¬QuadraticStationary metric ParticleExamples.exponentialClock a b := by
  intro hs
  have hg := (quadraticStationary_iff_geodesic metric hab
    (fun _ _ => (ParticleExamples.exponentialClock_contDiff.of_le (by simp)).contMDiff.contMDiffAt)).mp hs
  have ht : (a + b) / 2 ∈ Ioo a b := by constructor <;> linarith
  have hz := (hg _ ht).2
  rw [ParticleExamples.exponentialClock_acceleration] at hz
  have hv := ParticleExamples.exponentialClock_timelike ((a + b) / 2)
  unfold Timelike at hv
  simp only [hz, map_zero, lt_self_iff_false] at hv

end ProjectAInos.GeneralRelativity.VariationExamples
