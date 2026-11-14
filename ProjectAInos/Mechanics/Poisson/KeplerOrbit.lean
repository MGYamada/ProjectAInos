/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Poisson.KeplerMotion
public import ProjectAInos.Mechanics.Oscillations.Harmonic
public import ProjectAInos.Mechanics.Similarity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The orbit of a Kepler motion and Kepler's third law

Along a Kepler motion the Runge–Lenz vector `A` and the angular momentum `M`
are constant, so the identity `A · q = |M|² − m α r` is the equation of the
orbit: a conic with a focus at the centre (Landau–Lifshitz §15).

The equations of a Kepler motion permit similar motions: if `q(t)` is a
motion, so is `λ q(βt)` whenever `β² λ³ = 1`. The periods of similar orbits
are in the ratio `1/β`, so their squares are as the cubes of the linear
dimensions: Kepler's third law, in the form of Landau–Lifshitz §10.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics.KeplerModel

open SmoothAlgebra SmoothRing FreeSmoothRing Matrix

namespace IsKeplerMotion

variable {m α : ℝ} {Q Pm : Fin 3 → TimeFunction} {R : TimeFunction}

/-- The orbit is a conic (Landau–Lifshitz §15): with the constant vectors
`A = A(0)` and `M = M(0)`, `A · q(t) = |M|² − m α r(t)` at every time. -/
theorem conic (h : IsKeplerMotion m α Q Pm R) (hm : m ≠ 0) (t : ℝ) :
    ∑ a, Kepler.rungeLenz m α Q Pm R a (fun _ => 0) * Q a (fun _ => t) =
      ∑ a, Kepler.angularMomentum Q Pm a (fun _ => 0) ^ 2 -
        m * α * Kepler.distance Q R fun _ => t := by
  have hid := congrArg (fun f : TimeFunction => f fun _ => t)
    (Kepler.rungeLenz_dotProduct_q m α Q Pm R)
  simp only [dotProduct, Fin.sum_univ_three, TimeFunction.add_apply, TimeFunction.mul_apply,
    TimeFunction.sub_apply, TimeFunction.algebraMap_apply] at hid
  rw [h.rungeLenz_eq hm 0 (fun _ => t) (fun _ => 0),
    h.rungeLenz_eq hm 1 (fun _ => t) (fun _ => 0),
    h.rungeLenz_eq hm 2 (fun _ => t) (fun _ => 0),
    h.angularMomentum_eq 0 (fun _ => t) (fun _ => 0),
    h.angularMomentum_eq 1 (fun _ => t) (fun _ => 0),
    h.angularMomentum_eq 2 (fun _ => t) (fun _ => 0)] at hid
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  linear_combination hid

/-- Similar Kepler motions: if `q(t)` is a Kepler motion, so is `λ q(βt)` with
the momenta `λ β p(βt)`, whenever `β² λ³ = 1`. -/
theorem similar (h : IsKeplerMotion m α Q Pm R) {lam β : ℝ} (hlam : lam ≠ 0)
    (hβ : β ^ 2 * lam ^ 3 = 1) :
    IsKeplerMotion m α
      (fun i => algebraMap ℝ TimeFunction lam * TimeFunction.scale β (Q i))
      (fun i => algebraMap ℝ TimeFunction (lam * β) * TimeFunction.scale β (Pm i))
      (algebraMap ℝ TimeFunction lam⁻¹ * TimeFunction.scale β R) where
  constraint := by
    have hinv : algebraMap ℝ TimeFunction lam⁻¹ * algebraMap ℝ TimeFunction lam = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hlam, map_one]
    have hc := congrArg (fun f => TimeFunction.scale β f) h.constraint
    simp only [dotProduct, Fin.sum_univ_three, SmoothRingHom.map_mul, SmoothRingHom.map_add,
      SmoothRingHom.map_one] at hc
    simp only [dotProduct, Fin.sum_univ_three]
    linear_combination (algebraMap ℝ TimeFunction lam⁻¹ * algebraMap ℝ TimeFunction lam) ^ 2 * hc +
      (algebraMap ℝ TimeFunction lam⁻¹ * algebraMap ℝ TimeFunction lam + 1) * hinv
  velocity i := by
    rw [SmoothDerivation.map_algebraMap_mul, TimeFunction.timeDerivative_scale, h.velocity i,
      SmoothRingHom.map_mul, SmoothRingHom.map_algebraMap, smul_eq_mul, map_mul]
    ring
  force i := by
    have hreal : β * β = lam⁻¹ * lam⁻¹ * lam⁻¹ := by
      field_simp
      linear_combination hβ
    have hB : algebraMap ℝ TimeFunction β * algebraMap ℝ TimeFunction β =
        algebraMap ℝ TimeFunction lam⁻¹ * algebraMap ℝ TimeFunction lam⁻¹ *
          algebraMap ℝ TimeFunction lam⁻¹ := by
      rw [← map_mul, ← map_mul, ← map_mul, hreal]
    rw [SmoothDerivation.map_algebraMap_mul, TimeFunction.timeDerivative_scale, h.force i,
      smul_eq_mul, map_mul]
    simp only [SmoothRingHom.map_mul, SmoothRingHom.map_neg, SmoothRingHom.map_algebraMap]
    linear_combination (-(algebraMap ℝ TimeFunction α * (TimeFunction.scale β R *
      TimeFunction.scale β R * TimeFunction.scale β R * TimeFunction.scale β (Q i)) *
      algebraMap ℝ TimeFunction lam)) * hB

end IsKeplerMotion

/-- Kepler's third law for similar orbits (Landau–Lifshitz §10): if the orbit
`q(t)` has the period `T` and `β² λ³ = 1`, the similar orbit `λ q(βt)` has the
period `T/β`, and `(T/β)² = λ³ T²`. -/
theorem similar_period {Q : Fin 3 → TimeFunction} {T lam β : ℝ}
    (hT : ∀ i (t : ℝ), Q i (fun _ => t + T) = Q i fun _ => t) (hβ : β ^ 2 * lam ^ 3 = 1) :
    (∀ i (t : ℝ),
      (algebraMap ℝ TimeFunction lam * TimeFunction.scale β (Q i)) (fun _ => t + T / β) =
        (algebraMap ℝ TimeFunction lam * TimeFunction.scale β (Q i)) fun _ => t) ∧
      (T / β) ^ 2 = lam ^ 3 * T ^ 2 := by
  have hβ0 : β ≠ 0 := by
    rintro rfl
    simp at hβ
  refine ⟨fun i t => similar_apply_add_period (hT i) lam hβ0 t, ?_⟩
  field_simp
  linear_combination (-(T ^ 2)) * hβ

end ProjectAInos.Mechanics.KeplerModel
