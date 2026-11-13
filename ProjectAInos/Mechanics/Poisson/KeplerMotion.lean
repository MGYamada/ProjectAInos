/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Poisson.KeplerModel
public import ProjectAInos.Mechanics.Poisson.Trajectory
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Kepler motions

A Kepler motion consists of smooth functions of time `Q`, `P` and `R` with
`R² |Q|² = 1`, `Q̇ = P / m` and `Ṗ = −α R³ Q`: Newton's equations for the
inverse-square force, with `R` the inverse distance. Such a motion is a
trajectory of the Kepler Hamiltonian in the phase space with `ρ` adjoined, and
it lies on the locus of the constraint. Hence the Runge–Lenz vector, the angular
momentum and the energy, computed from `Q`, `P` and `R`, take the same value at
all times, and the orbit identity `A · Q = |M|² − m α r` holds at every time
(Landau–Lifshitz §15). The uniform circular motion of unit radius is a Kepler
motion.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics.KeplerModel

open SmoothAlgebra SmoothRing FreeSmoothRing Matrix

/-- The curve in the Kepler phase space with positions `Q`, momenta `Pm` and
inverse distance `R`. -/
def curve (Q Pm : Fin 3 → TimeFunction) (R : TimeFunction) : Index → TimeFunction
  | none => R
  | some (Sum.inl i) => Q i
  | some (Sum.inr i) => Pm i

@[simp] theorem lift_curve_q (Q Pm : Fin 3 → TimeFunction) (R : TimeFunction) (i : Fin 3) :
    FreeSmoothRing.lift (curve Q Pm R) (q i) = Q i :=
  lift_generator _ _

@[simp] theorem lift_curve_p (Q Pm : Fin 3 → TimeFunction) (R : TimeFunction) (i : Fin 3) :
    FreeSmoothRing.lift (curve Q Pm R) (p i) = Pm i :=
  lift_generator _ _

@[simp] theorem lift_curve_ρ (Q Pm : Fin 3 → TimeFunction) (R : TimeFunction) :
    FreeSmoothRing.lift (curve Q Pm R) ρ = R :=
  lift_generator _ _

/-- A Kepler motion: `R² |Q|² = 1`, `Q̇ = P / m` and `Ṗ = −α R³ Q`. -/
structure IsKeplerMotion (m α : ℝ) (Q Pm : Fin 3 → TimeFunction) (R : TimeFunction) :
    Prop where
  constraint : R * R * (Q ⬝ᵥ Q) = 1
  velocity : ∀ i, timeDerivative (Q i) = algebraMap ℝ TimeFunction m⁻¹ * Pm i
  force : ∀ i, timeDerivative (Pm i) = -(algebraMap ℝ TimeFunction α * (R * R * R * Q i))

namespace IsKeplerMotion

variable {m α : ℝ} {Q Pm : Fin 3 → TimeFunction} {R : TimeFunction}

/-- The inverse distance evolves by `Ṙ = −R³ (Q · P) / m`. This follows from the
constraint and the equation for `Q`. -/
theorem timeDerivative_R (h : IsKeplerMotion m α Q Pm R) :
    timeDerivative R = -(algebraMap ℝ TimeFunction m⁻¹ * (R * R * R) * (Q ⬝ᵥ Pm)) := by
  have half : algebraMap ℝ TimeFunction (1 / 2) * 2 = 1 := by
    have h2 : (2 : TimeFunction) = algebraMap ℝ TimeFunction 2 := (map_ofNat _ 2).symm
    rw [h2, ← map_mul, ← map_one (algebraMap ℝ TimeFunction)]
    congr 1
    norm_num
  have hR := h.constraint
  have E := congrArg timeDerivative hR
  simp only [dotProduct, Fin.sum_univ_three, SmoothDerivation.map_mul, map_add,
    SmoothDerivation.map_one, smul_eq_mul, h.velocity] at E
  simp only [dotProduct, Fin.sum_univ_three] at hR ⊢
  linear_combination (algebraMap ℝ TimeFunction (1 / 2) * R) * E + (-timeDerivative R) * hR +
    (-(algebraMap ℝ TimeFunction m⁻¹ * (R * R * R) * (Q 0 * Pm 0 + Q 1 * Pm 1 + Q 2 * Pm 2) +
      R * R * (Q 0 * Q 0 + Q 1 * Q 1 + Q 2 * Q 2) * timeDerivative R)) * half

/-- Along a Kepler motion `r = ρ |q|²` is the inverse of `ρ`. -/
theorem R_mul_distance (h : IsKeplerMotion m α Q Pm R) : R * Kepler.distance Q R = 1 := by
  rw [Kepler.ρ_mul_distance, Kepler.constraint, h.constraint, sub_self, add_zero]

/-- Along a Kepler motion `r² = |Q|²`: `r` is the distance. -/
theorem distance_mul_distance (h : IsKeplerMotion m α Q Pm R) :
    Kepler.distance Q R * Kepler.distance Q R = Q ⬝ᵥ Q := by
  rw [Kepler.distance_mul_distance, Kepler.constraint, h.constraint, sub_self, mul_zero,
    add_zero]

/-- A Kepler motion is a trajectory of the Kepler Hamiltonian. -/
theorem isTrajectory (h : IsKeplerMotion m α Q Pm R) :
    IsTrajectory poisson (Kepler.hamiltonian m α p ρ) (curve Q Pm R) := by
  intro a
  rcases a with _ | a | a
  · have hb : poisson.bracket (generator none) (Kepler.hamiltonian m α p ρ) =
        -(algebraMap ℝ PhaseSpace m⁻¹ * (ρ * ρ * ρ) * (q ⬝ᵥ p)) := isFrame.ρ_hamiltonian m α
    rw [hb]
    simp only [dotProduct, SmoothRingHom.map_neg, SmoothRingHom.map_mul,
      SmoothRingHom.map_algebraMap, SmoothRingHom.map_sum, lift_curve_q, lift_curve_p,
      lift_curve_ρ]
    exact h.timeDerivative_R
  · have hb : poisson.bracket (generator (some (Sum.inl a))) (Kepler.hamiltonian m α p ρ) =
        algebraMap ℝ PhaseSpace m⁻¹ * p a := isFrame.q_hamiltonian m α a
    rw [hb, SmoothRingHom.map_mul, SmoothRingHom.map_algebraMap, lift_curve_p]
    exact h.velocity a
  · have hb : poisson.bracket (generator (some (Sum.inr a))) (Kepler.hamiltonian m α p ρ) =
        -(algebraMap ℝ PhaseSpace α * (ρ * ρ * ρ * q a)) := isFrame.p_hamiltonian m α a
    rw [hb]
    simp only [SmoothRingHom.map_neg, SmoothRingHom.map_mul, SmoothRingHom.map_algebraMap,
      lift_curve_q, lift_curve_ρ]
    exact h.force a

/-- A Kepler motion lies on the locus of the constraint: every element of the
constraint ideal vanishes along it. -/
theorem lift_eq_zero_of_mem (h : IsKeplerMotion m α Q Pm R) {x : PhaseSpace}
    (hx : x ∈ constraintIdeal) : FreeSmoothRing.lift (curve Q Pm R) x = 0 := by
  obtain ⟨k, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  have hc : FreeSmoothRing.lift (curve Q Pm R) (Kepler.constraint q ρ) = 0 := by
    rw [Kepler.map_constraint]
    simp only [lift_curve_q, lift_curve_ρ, Kepler.constraint, h.constraint, sub_self]
  rw [SmoothRingHom.map_mul, hc, mul_zero]

/-- The Runge–Lenz vector of a Kepler motion takes the same value at all times
(Landau–Lifshitz §15). -/
theorem rungeLenz_eq (h : IsKeplerMotion m α Q Pm R) (hm : m ≠ 0) (a : Fin 3)
    (s t : Fin 1 → ℝ) :
    Kepler.rungeLenz m α Q Pm R a s = Kepler.rungeLenz m α Q Pm R a t := by
  have hA : FreeSmoothRing.lift (curve Q Pm R) (Kepler.rungeLenz m α q p ρ a) =
      Kepler.rungeLenz m α Q Pm R a := by
    rw [Kepler.map_rungeLenz]
    simp only [lift_curve_q, lift_curve_p, lift_curve_ρ]
  rw [← hA]
  exact h.isTrajectory.lift_eq_of_bracket_mem (fun x hx => h.lift_eq_zero_of_mem hx)
    (isFrame.rungeLenz_hamiltonian_mem hm α a) s t

/-- The angular momentum of a Kepler motion takes the same value at all times. -/
theorem angularMomentum_eq (h : IsKeplerMotion m α Q Pm R) (a : Fin 3) (s t : Fin 1 → ℝ) :
    Kepler.angularMomentum Q Pm a s = Kepler.angularMomentum Q Pm a t := by
  have hM : FreeSmoothRing.lift (curve Q Pm R) (Kepler.angularMomentum q p a) =
      Kepler.angularMomentum Q Pm a := by
    rw [Kepler.map_angularMomentum]
    simp only [lift_curve_q, lift_curve_p]
  rw [← hM]
  exact h.isTrajectory.lift_eq_of_isIntegral (isFrame.angularMomentum_hamiltonian m α a) s t

/-- The energy of a Kepler motion takes the same value at all times. -/
theorem hamiltonian_eq (h : IsKeplerMotion m α Q Pm R) (s t : Fin 1 → ℝ) :
    Kepler.hamiltonian m α Pm R s = Kepler.hamiltonian m α Pm R t := by
  have hH : FreeSmoothRing.lift (curve Q Pm R) (Kepler.hamiltonian m α p ρ) =
      Kepler.hamiltonian m α Pm R := by
    rw [Kepler.map_hamiltonian]
    simp only [lift_curve_p, lift_curve_ρ]
  rw [← hH]
  exact h.isTrajectory.lift_hamiltonian_eq s t

end IsKeplerMotion

/-- The uniform circular motion of unit radius, with `m = α = 1`, is a Kepler
motion. Kepler motions exist. -/
theorem isKeplerMotion_circular :
    IsKeplerMotion 1 1 ![TimeFunction.cos, TimeFunction.sin, 0]
      ![-TimeFunction.sin, TimeFunction.cos, 0] 1 where
  constraint := by
    simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, one_mul, mul_zero, add_zero]
    exact TimeFunction.cos_mul_cos_add_sin_mul_sin
  velocity i := by
    rw [inv_one, map_one, one_mul]
    fin_cases i
    · exact TimeFunction.timeDerivative_cos
    · exact TimeFunction.timeDerivative_sin
    · exact map_zero _
  force i := by
    rw [map_one, one_mul, one_mul, one_mul, one_mul]
    fin_cases i
    · change timeDerivative (-TimeFunction.sin) = -TimeFunction.cos
      rw [map_neg, TimeFunction.timeDerivative_sin]
    · change timeDerivative TimeFunction.cos = -TimeFunction.sin
      exact TimeFunction.timeDerivative_cos
    · change timeDerivative (0 : TimeFunction) = -0
      rw [map_zero, neg_zero]

end ProjectAInos.Mechanics.KeplerModel
