/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.ODE.FlatFrame
public import ProjectAInos.SmoothGeometry.Lorentzian.LocalInertialExamples
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-! # Radial parallel coframes for the nonlinear Minkowski chart

The nonzero shear connection is flat. Its constructed radial frame has the
expected inverse-Jacobian formula, and the general flat-frame theorem gives
a smooth invertible coframe parallel in all directions near the origin.
-/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Set Filter Metric ContinuousLinearMap
open scoped ContDiff Topology

namespace ProjectAInos.SmoothGeometry.LorentzianCharts

open LorentzMetric LinearODE

/-- The constant but nonzero connection of the nonlinear shear chart. -/
def shearRadialConnection (_ : Plane) : Plane →L[ℝ] Plane →L[ℝ] Plane :=
  metric.chartChristoffelBilinear standardChart 0

theorem shearRadialConnection_contDiff : ContDiff ℝ ∞ shearRadialConnection := contDiff_const

theorem shearRadialConnection_apply (p u v : Plane) :
    shearRadialConnection p u v = ![0, 2 * u 0 * v 0] := by
  ext k
  simp only [shearRadialConnection, chartChristoffelBilinear_apply, chartChristoffel_standard]
  fin_cases k <;> simp [Fin.sum_univ_succ]

theorem shearRadialConnection_eq_native (p : Plane) :
    shearRadialConnection p = metric.chartChristoffelBilinear standardChart p := by
  ext u v k
  simp only [shearRadialConnection, chartChristoffelBilinear_apply, chartChristoffel_standard]

theorem shearRadialConnection_flat : IsFlatConnectionOn shearRadialConnection univ := by
  intro p _ u v w
  have hd : fderiv ℝ shearRadialConnection p = 0 := fderiv_const_apply _
  rw [hd]
  simp only [zero_apply, zero_sub, shearRadialConnection_apply,
    Matrix.cons_val_zero, mul_zero]
  simp

/-- The resolvent-defined radial frame agrees with the inverse shear
Jacobian wherever its coefficient curve is small. -/
theorem shear_radialEndpoint (x v : Plane)
    (hx : ‖radialCoefficient shearRadialConnection shearRadialConnection_contDiff 0 x‖ < 1) :
    radialEndpoint shearRadialConnection shearRadialConnection_contDiff 0 x v =
      ![v 0, v 1 - 2 * x 0 * v 0] := by
  let f : Curve Plane := ⟨fun t => ![v 0, v 1 - 2 * (t : ℝ) * x 0 * v 0], by fun_prop⟩
  have hf : f = solutionOperator
      (radialCoefficient shearRadialConnection shearRadialConnection_contDiff 0 x) v := by
    apply eq_solution_of_hasDerivAt hx v f
    · ext k
      fin_cases k <;> simp [f]
    · intro t ht
      have hd : HasDerivAt (fun z : ℝ => ![v 0, v 1 - 2 * z * x 0 * v 0])
          (![0, -(2 * x 0 * v 0)] : Plane) t := by
        apply hasDerivAt_pi.mpr
        intro k
        fin_cases k
        · simpa using hasDerivAt_const t (v 0)
        · simpa using (((hasDerivAt_id t).const_mul 2).mul_const (x 0)).mul_const (v 0)
            |>.const_sub (v 1)
      have hfeq : extend f =ᶠ[𝓝 t] fun z => ![v 0, v 1 - 2 * z * x 0 * v 0] := by
        filter_upwards [isOpen_Ioo.mem_nhds ht] with z hz
        simp [LinearODE.extend, projIcc_of_mem zero_le_one (mem_Icc_of_Ioo hz), f]
      have hv : extend f t = ![v 0, v 1 - 2 * t * x 0 * v 0] := hfeq.self_of_nhds
      have hA : extend (radialCoefficient shearRadialConnection
          shearRadialConnection_contDiff 0 x) t = -(shearRadialConnection (t • x) x) := by
        change extend (radialCoefficient shearRadialConnection
          shearRadialConnection_contDiff 0 x) ((⟨t, mem_Icc_of_Ioo ht⟩ : unitInterval) : ℝ) = _
        rw [extend_coe, radialCoefficient_apply, zero_add]
      rw [hA, hv]
      convert hd.congr_of_eventuallyEq hfeq using 1
      ext k
      fin_cases k <;> simp [shearRadialConnection_apply]
  have h := congrArg (fun c : Curve Plane => c 1) hf
  simpa [f, radialEndpoint] using h.symm

/-- Flatness constructs, rather than assumes, the invertible parallel
coframe for this nontrivial two-dimensional connection. -/
theorem exists_shear_radialCoframe :
    ∃ r : ℝ, 0 < r ∧
      ContDiffOn ℝ ∞ (radialCoframe shearRadialConnection shearRadialConnection_contDiff 0)
        (ball 0 r) ∧
      (∀ x ∈ ball (0 : Plane) r,
        (radialCoframe shearRadialConnection shearRadialConnection_contDiff 0 x).IsInvertible) ∧
      ∀ x ∈ ball (0 : Plane) r, ∀ u v,
        fderiv ℝ (radialCoframe shearRadialConnection shearRadialConnection_contDiff 0) x u v =
          radialCoframe shearRadialConnection shearRadialConnection_contDiff 0 x
            (metric.chartChristoffelBilinear standardChart x u v) := by
  obtain ⟨r, hr, _, hθ, hi, _, hp⟩ := exists_parallel_radialCoframe shearRadialConnection
    shearRadialConnection_contDiff (U := univ) (by simp) shearRadialConnection_flat
  refine ⟨r, hr, hθ, hi, ?_⟩
  simpa only [shearRadialConnection_eq_native] using hp

end ProjectAInos.SmoothGeometry.LorentzianCharts
