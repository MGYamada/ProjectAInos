/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.GeneralRelativity.VariationStationary
public import ProjectAInos.GeneralRelativity.ClockExamples

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

end ProjectAInos.GeneralRelativity.VariationExamples
