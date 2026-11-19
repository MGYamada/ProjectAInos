/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Mechanics.Scattering.SmallAngleExpansion
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The deflection of light as a problem of small-angle scattering

Landau–Lifshitz §101, (101.9). For a ray in the Schwarzschild field of a mass `M` with
the impact parameter `ρ`, the variable `v = ρ/r` satisfies
`(dv/dφ)² = 1 − v² + (2M/ρ) v³` (units `G = c = 1`). This is the radicand
`1 − u² − ε f(u)` of the small-angle scattering library with the profile `f(u) = −u³`
and the strength `ε = 2M/ρ`. This file is pure analysis on top of that library; the
connection with the null geodesics of the Schwarzschild metric is not made here.

* `integral_sin_mul_deriv_neg_cube`: the first-order integral
  `∫₀^{π/2} sin ψ f′(sin ψ) dψ = −3 ∫₀^{π/2} sin³ψ dψ = −2`.
* `exists_abs_deflectionAngle_add_le`: for `|ε| ≤ δ` the closest approach exists and the
  angle of deflection is `−2ε` up to a term `C ε²`.
* `exists_abs_deflectionAngle_schwarzschild_add_le`: in Schwarzschild variables, the angle of
  deflection is `−4M/ρ` up to a term `C (M/ρ)²`. The library measures the angle with the sign
  of Landau–Lifshitz §20, negative for an attraction, so the ray is bent towards the mass by
  `4M/ρ`, (101.9).
-/

@[expose] public section

noncomputable section

open scoped Real

namespace ProjectAinos.GeneralRelativity.LightDeflection

open Mechanics.Scattering Mechanics.Scattering.SmallAngle

/-- The first-order integral for the profile `f(u) = −u³`:
`∫₀^{π/2} sin ψ f′(sin ψ) dψ = −2`. -/
theorem integral_sin_mul_deriv_neg_cube :
    ∫ ψ in (0 : ℝ)..π / 2, Real.sin ψ * deriv (fun u : ℝ => -u ^ 3) (Real.sin ψ) = -2 := by
  have hd : ∀ x : ℝ, deriv (fun u : ℝ => -u ^ 3) x = -(3 * x ^ 2) := fun x => by
    simp
  have e : (fun ψ : ℝ => Real.sin ψ * deriv (fun u : ℝ => -u ^ 3) (Real.sin ψ)) =
      fun ψ => -3 * Real.sin ψ ^ (1 + 2) := by
    funext ψ
    rw [hd]
    ring
  rw [e, intervalIntegral.integral_const_mul, integral_sin_pow]
  norm_num

/-- The deflection for the profile `f(u) = −u³` of a ray in the Schwarzschild field: for
`|ε| ≤ δ` there is a closest approach `ρ/c` (unique by `IsClosest.unique`), and for all
positive `ρ` and `v∞` the angle of deflection is `−2ε` up to `C ε²`. -/
theorem exists_abs_deflectionAngle_add_le :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ ε : ℝ, |ε| ≤ δ → ∃ c : ℝ, IsClosest (fun u => -u ^ 3) ε c ∧
      ∀ ρ vinf : ℝ, 0 < ρ → 0 < vinf →
        |deflectionAngle (ρ * vinf) (speedSq (fun u => -u ^ 3) ρ vinf ε) (ρ / c) + 2 * ε| ≤
          C * ε ^ 2 := by
  obtain ⟨δ, hδ, C, hC⟩ := exists_abs_deflectionAngle_sub_le_of_contDiff
    (f := fun u : ℝ => -u ^ 3) (by fun_prop)
  refine ⟨δ, hδ, C, fun ε hε => ?_⟩
  obtain ⟨c, hc, hmot⟩ := hC ε hε
  refine ⟨c, hc, fun ρ vinf hρ hv => ?_⟩
  have h1 := (hmot ρ vinf hρ hv).2
  rw [integral_sin_mul_deriv_neg_cube] at h1
  convert h1 using 2
  ring

/-- **The deflection of light**, Landau–Lifshitz (101.9), in units `G = c = 1`: for a mass
`M ≥ 0` and an impact parameter `ρ` with `2M/ρ ≤ δ`, the ray `(dv/dφ)² = 1 − v² + (2M/ρ) v³`
has a closest approach, and its angle of deflection is `−4M/ρ` up to `C (M/ρ)²`. -/
theorem exists_abs_deflectionAngle_schwarzschild_add_le :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ M ρ : ℝ, 0 < ρ → 0 ≤ M → 2 * M / ρ ≤ δ →
      ∃ c : ℝ, IsClosest (fun u => -u ^ 3) (2 * M / ρ) c ∧ ∀ vinf : ℝ, 0 < vinf →
        |deflectionAngle (ρ * vinf) (speedSq (fun u => -u ^ 3) ρ vinf (2 * M / ρ)) (ρ / c) +
          4 * M / ρ| ≤ C * (M / ρ) ^ 2 := by
  obtain ⟨δ, hδ, C, hC⟩ := exists_abs_deflectionAngle_add_le
  refine ⟨δ, hδ, 4 * C, fun M ρ hρ hM hε => ?_⟩
  have hε0 : 0 ≤ 2 * M / ρ := by positivity
  obtain ⟨c, hc, hmot⟩ := hC (2 * M / ρ) (by rwa [abs_of_nonneg hε0])
  refine ⟨c, hc, fun vinf hv => ?_⟩
  have h1 := hmot ρ vinf hρ hv
  have e1 : 2 * (2 * M / ρ) = 4 * M / ρ := by ring
  have e2 : C * (2 * M / ρ) ^ 2 = 4 * C * (M / ρ) ^ 2 := by ring
  rwa [e1, e2] at h1

end ProjectAinos.GeneralRelativity.LightDeflection
