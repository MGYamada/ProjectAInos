/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.Multipole
public import ProjectAinos.SpecialFunctions.NewtonHarmonics
public import ProjectAinos.SpecialFunctions.SphericalBasis
import Mathlib.Tactic

/-! # The `2n+1` spherical moments of a localized charge

Integrating the separated Newton derivative against the charge density identifies the
existing Cartesian Taylor multipole term of every order with the spherical expansion.
The coefficients are integrals of solid polynomials, so they include the origin directly.
-/

@[expose] public section
noncomputable section

open MeasureTheory MvPolynomial Real
open ProjectAinos.SpecialFunctions.SphericalHarmonics
open ProjectAinos.SmoothGeometry.Potential

namespace ProjectAinos.Electrodynamics.Multipole

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The charge moment against the `i`-th degree-`n` orthonormal real solid harmonic. -/
def sphericalMoment (ρ : E3 → ℝ) (n : ℕ) (i : Fin (2 * n + 1)) : ℝ :=
  ∫ y, ρ y * eval y (solidRepresentative n (realBasis n i)).val.val

/-- The order-`n` Taylor multipole of §41 consists of `2n+1` spherical components.
Each charge moment is independent of the observation direction and radius. -/
theorem multipoleTerm_eq_sphericalMoments {ρ : E3 → ℝ} (hρ : Continuous ρ)
    (hcomp : HasCompactSupport ρ) (n : ℕ) (u : UnitSphere 3) {r : ℝ} (hr : 0 < r) :
    multipoleTerm ρ n (r • u.val) = ((2 * (n : ℝ) + 1) * r ^ (n + 1))⁻¹ *
      ∑ i, representative 3 n (realBasis n i) u * sphericalMoment ρ n i := by
  let Y (i : Fin (2 * n + 1)) := representative 3 n (realBasis n i) u
  let H (i : Fin (2 * n + 1)) (y : E3) := eval y (solidRepresentative n (realBasis n i)).val.val
  let c := ((2 * (n : ℝ) + 1) * r ^ (n + 1))⁻¹
  have hi i : Integrable (fun y => ρ y * H i y) :=
    integrable_density_mul hρ hcomp ((MvPolynomial.continuous_eval _).comp
      (continuous_pi fun j => (EuclideanSpace.proj (𝕜 := ℝ) j).continuous))
  change (n.factorial : ℝ)⁻¹ * (∫ y, ρ y * _) = c * ∑ i, Y i * sphericalMoment ρ n i
  rw [← integral_const_mul]
  calc
    _ = ∫ y, c * ∑ i, Y i * (ρ y * H i y) := by
      apply integral_congr_ae
      filter_upwards with y
      rw [mul_left_comm, newtonKernel_derivative_addition (realBasis n) u hr y]
      change ρ y * (c * ∑ i, Y i * H i y) = _
      rw [mul_left_comm, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => mul_left_comm ..
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum _ (fun i _ => (hi i).const_mul (Y i))]
      simp only [integral_const_mul, H, sphericalMoment]

end ProjectAinos.Electrodynamics.Multipole
