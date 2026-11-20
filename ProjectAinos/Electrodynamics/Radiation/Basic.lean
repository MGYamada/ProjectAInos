/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.RetardedPotential
public import ProjectAinos.Electrodynamics.EnergyMomentum
public import ProjectAinos.SmoothGeometry.Euclidean.SphereIntegral

/-!
# The radiation of a localized source

Definitions shared by the files on radiation (Landau–Lifshitz, *The Classical Theory of Fields*,
§§66–77). Space is `ℝ³ = EuclideanSpace ℝ (Fin 3)`, `v ↦ (v⁰, 𝐯)` splits space-time, and
`σ = sphereMeasure` is the surface measure of the unit sphere.

* `sphereFlux S t R`: the flux `R² ∫ S(t, Rn) · n dσ(n)` of a vector field `S` through the sphere
  of radius `R` about the origin at the time `t`.
* `currentRate k`: the time derivative `∂₀k` of a current.
* `radiationAmplitude k u n`: the amplitude `(1/4π) ∫ k(u + ⟨n, y⟩, y) dy` of the far field in
  the direction `n` at the retarded time `u`; the retarded potential is `Ã(t − R, n)/R` to leading
  order at the distance `R`.
* `radiatedPower k u`: the power `∫ |n × ∂ᵤÃ(u, n)|² dσ(n)` radiated at the retarded time `u`,
  written as `∫ (|∂ᵤÃ|² − ⟨n, ∂ᵤÃ⟩²) dσ` with the spatial components of the amplitude of `∂₀k`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric Real

namespace ProjectAinos.Electrodynamics.Radiation

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.Sphere SpecialRelativity

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The flux `R² ∫ S(t, Rn) · n dσ(n)` of a vector field through the sphere of radius `R` about
the origin at the time `t`. -/
def sphereFlux (S : Fin 3 → Spacetime → ℝ) (t R : ℝ) : ℝ :=
  R ^ 2 * ∫ n : sphere (0 : E3) 1, ∑ i : Fin 3, S i (vector t (R • (n : E3))) * (n : E3) i
    ∂sphereMeasure

/-- The time derivative `∂₀k` of a current. -/
def currentRate (k : Spacetime → Spacetime) : Spacetime → Spacetime := fun v μ =>
  partialAt (fun w => k w μ) 0 v

/-- The amplitude `Ã_μ(u, n) = (1/4π) ∫ k_μ(u + ⟨n, y⟩, y) dy` of the far field of a current in
the direction `n` at the retarded time `u`. -/
def radiationAmplitude (k : Spacetime → Spacetime) (u : ℝ) (n : E3) (μ : Fin 4) : ℝ :=
  (4 * π)⁻¹ * ∫ y : E3, k (vector (u + inner ℝ n y) y) μ

/-- The power `∫ |n × ∂ᵤÃ|² dσ = ∫ (|∂ᵤÃ|² − ⟨n, ∂ᵤÃ⟩²) dσ` radiated by a current at the
retarded time `u`, with the spatial components `∂ᵤÃᵢ` of the amplitude of `∂₀k`. -/
def radiatedPower (k : Spacetime → Spacetime) (u : ℝ) : ℝ :=
  ∫ n : sphere (0 : E3) 1,
    ((∑ i : Fin 3, radiationAmplitude (currentRate k) u n i.succ ^ 2) -
      (∑ i : Fin 3, (n : E3) i * radiationAmplitude (currentRate k) u n i.succ) ^ 2)
    ∂sphereMeasure

end ProjectAinos.Electrodynamics.Radiation
