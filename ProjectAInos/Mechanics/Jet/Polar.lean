/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Jet.Metric
public import ProjectAInos.Mechanics.Jet.Standard
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Plane polar co-ordinates

In the standard jet ring on two co-ordinates `r` and `φ`, the Lagrangian of a
particle of unit mass in the plane is `½ (ṙ² + r² φ̇²) − U`. Its kinetic form
depends on the position, so this is a model of the general natural Lagrangian
that is not of the constant-mass form. Lagrange's equations are

`E_r = −r̈ + r φ̇² − ∂U/∂r` and `E_φ = −(r² φ̈ + 2 r ṙ φ̇) − ∂U/∂φ`,

with the centrifugal term `r φ̇²`. The momentum conjugate to `φ` is the angular
momentum `r² φ̇`, and it is conserved when `U` does not depend on `φ`.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics.StandardJet.Polar

open SmoothAlgebra SmoothRing Matrix

local notation "R" => jetRing (Fin 2)

/-- The radial co-ordinate `r`. -/
def radius : StandardJet (Fin 2) := (R).q 0 0

/-- The kinetic coefficients of plane polar co-ordinates: `diag(1, r²)`. -/
def metric : Fin 2 → Fin 2 → StandardJet (Fin 2) := ![![1, 0], ![0, radius * radius]]

theorem orderLE_radius : (R).OrderLE radius 0 := JetRing.orderLE_q 0 0

theorem orderLE_metric (i k : Fin 2) : (R).OrderLE (metric i k) 0 := by
  have h1 : (R).OrderLE (1 : StandardJet (Fin 2)) 0 := by
    have h : (R).OrderLE (algebraMap ℝ (StandardJet (Fin 2)) 1) 0 :=
      JetRing.orderLE_algebraMap 1 0
    rwa [map_one] at h
  have h0 : (R).OrderLE (0 : StandardJet (Fin 2)) 0 := fun _ _ _ => map_zero _
  fin_cases i <;> fin_cases k
  · exact h1
  · exact h0
  · exact h0
  · exact orderLE_radius.mul orderLE_radius

theorem metric_symm (i k : Fin 2) : metric i k = metric k i := by
  fin_cases i <;> fin_cases k <;> rfl

theorem dt_metric (i k : Fin 2) : (R).dt (metric i k) = 0 := by
  have hr : (R).dt radius = 0 := (R).dt_q 0 0
  fin_cases i <;> fin_cases k
  · exact SmoothDerivation.map_one _
  · exact map_zero _
  · exact map_zero _
  · change (R).dt (radius * radius) = 0
    rw [SmoothDerivation.map_mul, hr, smul_zero, add_zero]

theorem d_zero_zero_radius : (R).d 0 0 radius = 1 := (R).d_q_self 0 0

theorem d_one_zero_radius : (R).d 1 0 radius = 0 := (R).d_q_ne 0 0 1 0 (by simp)

theorem metric_zero_zero : metric 0 0 = 1 := rfl

theorem metric_zero_one : metric 0 1 = 0 := rfl

theorem metric_one_zero : metric 1 0 = 0 := rfl

theorem metric_one_one : metric 1 1 = radius * radius := rfl

/-- The only nonzero derivative of the kinetic coefficients is `∂ᵣ(r²) = 2r`. -/
theorem d_zero_zero_metric_one_one : (R).d 0 0 (metric 1 1) = 2 * radius := by
  rw [metric_one_one, SmoothDerivation.map_mul, d_zero_zero_radius, smul_eq_mul, mul_one,
    two_mul]

theorem d_one_zero_metric_one_one : (R).d 1 0 (metric 1 1) = 0 := by
  rw [metric_one_one, SmoothDerivation.map_mul, d_one_zero_radius, smul_zero, add_zero]

theorem d_zero_metric_zero (j k : Fin 2) : (R).d j 0 (metric 0 k) = 0 := by
  fin_cases k
  · exact SmoothDerivation.map_one _
  · exact map_zero _

theorem d_zero_metric_one_zero (j : Fin 2) : (R).d j 0 (metric 1 0) = 0 := map_zero _

/-- The polar Lagrangian `½ (ṙ² + r² φ̇²) − U`. -/
def lagrangian (U : StandardJet (Fin 2)) : StandardJet (Fin 2) := (R).metricLagrangian metric U

/-- The radial equation: `E_r = −r̈ + r φ̇² − ∂U/∂r`. The term `r φ̇²` is the
centrifugal force. -/
theorem euler_radial {U : StandardJet (Fin 2)} (hU : (R).OrderLE U 0) :
    (R).euler 0 (lagrangian U) =
      -(R).q 0 2 + radius * ((R).q 1 1 * (R).q 1 1) - (R).d 0 0 U := by
  have half2 : algebraMap ℝ (StandardJet (Fin 2)) (1 / 2) * 2 = 1 := by
    rw [mul_two]
    exact JetRing.algebraMap_half_add_half
  rw [lagrangian, JetRing.euler_metricLagrangian_eq orderLE_metric metric_symm hU]
  simp only [Fin.sum_univ_two, d_zero_metric_zero, d_zero_metric_one_zero,
    d_zero_zero_metric_one_one, dt_metric]
  simp only [metric_zero_zero, metric_zero_one]
  linear_combination (radius * ((R).q 1 1 * (R).q 1 1)) * half2

/-- The angular equation: `E_φ = −(r² φ̈ + 2 r ṙ φ̇) − ∂U/∂φ`. -/
theorem euler_angular {U : StandardJet (Fin 2)} (hU : (R).OrderLE U 0) :
    (R).euler 1 (lagrangian U) =
      -(radius * radius * (R).q 1 2 + 2 * radius * ((R).q 0 1 * (R).q 1 1)) -
        (R).d 1 0 U := by
  rw [lagrangian, JetRing.euler_metricLagrangian_eq orderLE_metric metric_symm hU]
  simp only [Fin.sum_univ_two, d_zero_metric_zero, d_zero_metric_one_zero,
    d_zero_zero_metric_one_one, d_one_zero_metric_one_one, dt_metric]
  simp only [metric_one_zero, metric_one_one]
  ring

/-- The momentum conjugate to `φ` is the angular momentum `r² φ̇`. -/
theorem momentum_angular {U : StandardJet (Fin 2)} (hU : (R).OrderLE U 0) :
    (R).momentum (lagrangian U) 1 = radius * radius * (R).q 1 1 := by
  rw [lagrangian, JetRing.momentum_metricLagrangian orderLE_metric metric_symm hU,
    Fin.sum_univ_two, metric_one_zero, metric_one_one]
  ring

/-- Conservation of angular momentum: if the potential does not depend on `φ`,
`r² φ̇` is conserved. -/
theorem conserved_angularMomentum {U : StandardJet (Fin 2)} (hU : (R).OrderLE U 0)
    (hφ : (R).d 1 0 U = 0) : (R).Conserved (lagrangian U) (radius * radius * (R).q 1 1) := by
  have hcyclic : (R).d 1 0 (lagrangian U) = 0 := by
    rw [lagrangian, JetRing.metricLagrangian, map_sub, SmoothDerivation.map_mul,
      SmoothDerivation.map_algebraMap, JetRing.d_zero_kineticForm, hφ]
    simp only [Fin.sum_univ_two, d_zero_metric_zero, d_zero_metric_one_zero,
      d_one_zero_metric_one_one, zero_mul, add_zero, smul_zero, sub_zero]
  rw [← momentum_angular hU]
  exact JetRing.conserved_momentum_of_cyclic
    (JetRing.orderLE_metricLagrangian orderLE_metric hU) 1 hcyclic

end ProjectAInos.Mechanics.StandardJet.Polar
