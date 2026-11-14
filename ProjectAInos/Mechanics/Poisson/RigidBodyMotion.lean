/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Oscillations.Linearization
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Motions of the free rigid body

Trajectories of Euler's equations on the Lie–Poisson phase space of the rigid
body (Landau–Lifshitz §§36, 37).

* A rotation about a principal axis is an equilibrium.
* For a symmetric top the angular momentum in the body frame turns uniformly
  about the axis of the top.
* `2 Iₐ E − |L|² = Σᵢ (Iₐ/Iᵢ − 1) Lᵢ²` is an integral. For the axis of the
  greatest or of the least moment it is a definite quadratic form in the other
  two components, so they stay bounded by their initial values: these
  rotations are stable.
* The linearized equations at a rotation about the axis `1` couple the
  components `0` and `2` with the coefficients `(1/I₂ − 1/I₁) ℓ` and
  `(1/I₁ − 1/I₀) ℓ`. Their product is positive for the middle moment and
  negative for an extreme one.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics.RigidBody

open SmoothAlgebra SmoothRing FreeSmoothRing

/-- Euler's equations along a curve. -/
theorem isTrajectory_kineticEnergy_iff (I : Fin 3 → ℝ) (c : Fin 3 → TimeFunction) :
    IsTrajectory poisson (kineticEnergy I) c ↔
      timeDerivative (c 0) = algebraMap ℝ TimeFunction ((I 2)⁻¹ - (I 1)⁻¹) * (c 1 * c 2) ∧
      timeDerivative (c 1) = algebraMap ℝ TimeFunction ((I 0)⁻¹ - (I 2)⁻¹) * (c 2 * c 0) ∧
      timeDerivative (c 2) = algebraMap ℝ TimeFunction ((I 1)⁻¹ - (I 0)⁻¹) * (c 0 * c 1) := by
  have h0 : poisson.bracket (generator 0) (kineticEnergy I) =
      algebraMap ℝ PhaseSpace ((I 2)⁻¹ - (I 1)⁻¹) * (generator 1 * generator 2) :=
    euler_equation_zero I
  have h1 : poisson.bracket (generator 1) (kineticEnergy I) =
      algebraMap ℝ PhaseSpace ((I 0)⁻¹ - (I 2)⁻¹) * (generator 2 * generator 0) :=
    euler_equation_one I
  have h2 : poisson.bracket (generator 2) (kineticEnergy I) =
      algebraMap ℝ PhaseSpace ((I 1)⁻¹ - (I 0)⁻¹) * (generator 0 * generator 1) :=
    euler_equation_two I
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · have := h 0
      rwa [h0, SmoothRingHom.map_mul, SmoothRingHom.map_algebraMap, SmoothRingHom.map_mul,
        lift_generator, lift_generator] at this
    · have := h 1
      rwa [h1, SmoothRingHom.map_mul, SmoothRingHom.map_algebraMap, SmoothRingHom.map_mul,
        lift_generator, lift_generator] at this
    · have := h 2
      rwa [h2, SmoothRingHom.map_mul, SmoothRingHom.map_algebraMap, SmoothRingHom.map_mul,
        lift_generator, lift_generator] at this
  · rintro ⟨e0, e1, e2⟩ a
    fin_cases a
    · change timeDerivative (c 0) = FreeSmoothRing.lift c (poisson.bracket (generator 0) _)
      rw [h0, SmoothRingHom.map_mul, SmoothRingHom.map_algebraMap, SmoothRingHom.map_mul,
        lift_generator, lift_generator]
      exact e0
    · change timeDerivative (c 1) = FreeSmoothRing.lift c (poisson.bracket (generator 1) _)
      rw [h1, SmoothRingHom.map_mul, SmoothRingHom.map_algebraMap, SmoothRingHom.map_mul,
        lift_generator, lift_generator]
      exact e1
    · change timeDerivative (c 2) = FreeSmoothRing.lift c (poisson.bracket (generator 2) _)
      rw [h2, SmoothRingHom.map_mul, SmoothRingHom.map_algebraMap, SmoothRingHom.map_mul,
        lift_generator, lift_generator]
      exact e2

/-- A rotation about a principal axis is an equilibrium of Euler's equations. -/
theorem isTrajectory_principalRotation (I : Fin 3 → ℝ) (a : Fin 3) (ℓ : ℝ) :
    IsTrajectory poisson (kineticEnergy I)
      fun i => algebraMap ℝ TimeFunction ((Pi.single a ℓ : Fin 3 → ℝ) i) := by
  rw [isTrajectory_kineticEnergy_iff]
  fin_cases a <;> simp

/-- The free symmetric top (Landau–Lifshitz (36.6), (36.7)): for `I₀ = I₁` the
angular momentum in the body frame turns uniformly about the axis of the top,
with the angular velocity `(1/I₀ − 1/I₂) ℓ`. -/
theorem isTrajectory_symmetricTop {I : Fin 3 → ℝ} (hI : I 0 = I 1) (a ℓ : ℝ) :
    IsTrajectory poisson (kineticEnergy I)
      ![algebraMap ℝ TimeFunction a * TimeFunction.cosMul (((I 0)⁻¹ - (I 2)⁻¹) * ℓ),
        algebraMap ℝ TimeFunction a * TimeFunction.sinMul (((I 0)⁻¹ - (I 2)⁻¹) * ℓ),
        algebraMap ℝ TimeFunction ℓ] := by
  rw [isTrajectory_kineticEnergy_iff]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons, SmoothDerivation.map_algebraMap_mul, SmoothDerivation.map_algebraMap,
    TimeFunction.timeDerivative_cosMul, TimeFunction.timeDerivative_sinMul, smul_eq_mul, ← hI,
    sub_self, map_zero, zero_mul]
  refine ⟨?_, ?_, trivial⟩
  · refine TimeFunction.ext_apply_const fun t => ?_
    simp only [TimeFunction.mul_apply, TimeFunction.neg_apply, TimeFunction.algebraMap_apply,
      TimeFunction.sinMul_apply]
    ring
  · refine TimeFunction.ext_apply_const fun t => ?_
    simp only [TimeFunction.mul_apply, TimeFunction.algebraMap_apply,
      TimeFunction.cosMul_apply]
    ring

/-! ### Stability of the rotations about the extreme axes -/

/-- The integral `2 Iₐ E − |L|²`. -/
def stabilityForm (I : Fin 3 → ℝ) (a : Fin 3) : PhaseSpace :=
  algebraMap ℝ PhaseSpace (2 * I a) * kineticEnergy I - casimir

theorem isIntegral_stabilityForm (I : Fin 3 → ℝ) (a : Fin 3) :
    poisson.IsIntegral (kineticEnergy I) (stabilityForm I a) := by
  unfold PoissonStructure.IsIntegral stabilityForm
  rw [AlmostPoissonStructure.bracket_sub_left, AlmostPoissonStructure.bracket_mul_left,
    poisson_casimir_left, AlmostPoissonStructure.bracket_self,
    AlmostPoissonStructure.bracket_algebraMap_left, mul_zero, mul_zero, add_zero, sub_zero]

/-- The value of the integral along a curve:
`Σᵢ (Iₐ/Iᵢ − 1) Lᵢ²`. -/
theorem lift_stabilityForm {I : Fin 3 → ℝ} (hI : ∀ i, I i ≠ 0) (a : Fin 3)
    (c : Fin 3 → TimeFunction) (t : ℝ) :
    FreeSmoothRing.lift c (stabilityForm I a) (fun _ => t) =
      ∑ i, (I a / I i - 1) * c i (fun _ => t) ^ 2 := by
  have h0 := hI 0
  have h1 := hI 1
  have h2 := hI 2
  simp only [stabilityForm, kineticEnergy, casimir, L, Fin.sum_univ_three,
    SmoothRingHom.map_sub, SmoothRingHom.map_add, SmoothRingHom.map_mul,
    SmoothRingHom.map_algebraMap, lift_generator, TimeFunction.sub_apply,
    TimeFunction.add_apply, TimeFunction.mul_apply, TimeFunction.algebraMap_apply]
  field_simp
  ring

/-- Along every trajectory of the free rigid body, `Σᵢ (Iₐ/Iᵢ − 1) Lᵢ²` keeps
its value. -/
theorem sum_mul_sq_eq {I : Fin 3 → ℝ} (hI : ∀ i, I i ≠ 0) (a : Fin 3)
    {c : Fin 3 → TimeFunction} (h : IsTrajectory poisson (kineticEnergy I) c) (t : ℝ) :
    ∑ i, (I a / I i - 1) * c i (fun _ => t) ^ 2 =
      ∑ i, (I a / I i - 1) * c i (fun _ => 0) ^ 2 := by
  rw [← lift_stabilityForm hI a c t, ← lift_stabilityForm hI a c 0]
  exact h.lift_eq_of_isIntegral (isIntegral_stabilityForm I a) _ _

/-- Stability of the rotation about the axis of the greatest moment
(Landau–Lifshitz §37): each component of the angular momentum across the axis
stays bounded by the initial deviation. -/
theorem mul_sq_le_of_greatest {I : Fin 3 → ℝ} (hI : ∀ i, 0 < I i) {a : Fin 3}
    (ha : ∀ i, I i ≤ I a) {c : Fin 3 → TimeFunction}
    (h : IsTrajectory poisson (kineticEnergy I) c) (j : Fin 3) (t : ℝ) :
    (I a / I j - 1) * c j (fun _ => t) ^ 2 ≤
      ∑ i, (I a / I i - 1) * c i (fun _ => 0) ^ 2 := by
  rw [← sum_mul_sq_eq (fun i => (hI i).ne') a h t]
  have hnn (i : Fin 3) : 0 ≤ (I a / I i - 1) * c i (fun _ => t) ^ 2 :=
    mul_nonneg (sub_nonneg.mpr ((one_le_div (hI i)).mpr (ha i))) (sq_nonneg _)
  exact Finset.single_le_sum (f := fun i => (I a / I i - 1) * c i (fun _ => t) ^ 2)
    (fun i _ => hnn i) (Finset.mem_univ j)

/-- Stability of the rotation about the axis of the least moment. -/
theorem mul_sq_le_of_least {I : Fin 3 → ℝ} (hI : ∀ i, 0 < I i) {a : Fin 3}
    (ha : ∀ i, I a ≤ I i) {c : Fin 3 → TimeFunction}
    (h : IsTrajectory poisson (kineticEnergy I) c) (j : Fin 3) (t : ℝ) :
    (1 - I a / I j) * c j (fun _ => t) ^ 2 ≤
      ∑ i, (1 - I a / I i) * c i (fun _ => 0) ^ 2 := by
  have hsum := sum_mul_sq_eq (fun i => (hI i).ne') a h t
  have hneg (s : ℝ) : ∑ i, (1 - I a / I i) * c i (fun _ => s) ^ 2 =
      -∑ i, (I a / I i - 1) * c i (fun _ => s) ^ 2 := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hneg 0, ← hsum, ← hneg t]
  have hnn (i : Fin 3) : 0 ≤ (1 - I a / I i) * c i (fun _ => t) ^ 2 :=
    mul_nonneg (sub_nonneg.mpr ((div_le_one (hI i)).mpr (ha i))) (sq_nonneg _)
  exact Finset.single_le_sum (f := fun i => (1 - I a / I i) * c i (fun _ => t) ^ 2)
    (fun i _ => hnn i) (Finset.mem_univ j)

/-! ### The linearized equations at a rotation about the axis `1` -/

/-- The linearized equation for the component `0` at the rotation
`L = (0, ℓ, 0)`: the coefficient of the component `2` is `(1/I₂ − 1/I₁) ℓ`. -/
theorem linearization_zero_two (I : Fin 3 → ℝ) (ℓ : ℝ) :
    linearization poisson (kineticEnergy I) (Pi.single 1 ℓ) 0 2 = ((I 2)⁻¹ - (I 1)⁻¹) * ℓ := by
  have h0 : poisson.bracket (generator 0) (kineticEnergy I) =
      algebraMap ℝ PhaseSpace ((I 2)⁻¹ - (I 1)⁻¹) * (L 1 * L 2) := euler_equation_zero I
  have d1 : partialDerivation 2 (L 1) = 0 := partialDerivation_generator_of_ne (by decide)
  have d2 : partialDerivation 2 (L 2) = 1 := partialDerivation_generator_self 2
  rw [linearization, h0, SmoothDerivation.map_algebraMap_mul, SmoothDerivation.map_mul, d1, d2,
    smul_zero, add_zero, smul_eq_mul, smul_eq_mul, mul_one, SmoothRingHom.map_mul,
    SmoothRingHom.map_algebraMap, L, lift_generator, Pi.single_eq_same]
  rfl

/-- The linearized equation for the component `2` at the rotation
`L = (0, ℓ, 0)`: the coefficient of the component `0` is `(1/I₁ − 1/I₀) ℓ`. -/
theorem linearization_two_zero (I : Fin 3 → ℝ) (ℓ : ℝ) :
    linearization poisson (kineticEnergy I) (Pi.single 1 ℓ) 2 0 = ((I 1)⁻¹ - (I 0)⁻¹) * ℓ := by
  have h2 : poisson.bracket (generator 2) (kineticEnergy I) =
      algebraMap ℝ PhaseSpace ((I 1)⁻¹ - (I 0)⁻¹) * (L 0 * L 1) := euler_equation_two I
  have d0 : partialDerivation 0 (L 0) = 1 := partialDerivation_generator_self 0
  have d1 : partialDerivation 0 (L 1) = 0 := partialDerivation_generator_of_ne (by decide)
  rw [linearization, h2, SmoothDerivation.map_algebraMap_mul, SmoothDerivation.map_mul, d0, d1,
    smul_zero, zero_add, smul_eq_mul, smul_eq_mul, mul_one, SmoothRingHom.map_mul,
    SmoothRingHom.map_algebraMap, L, lift_generator, Pi.single_eq_same]
  rfl

/-- The rotation about the axis of the middle moment is linearly unstable
(Landau–Lifshitz §37): the product of the two coefficients is positive. -/
theorem linearization_mul_pos_of_middle {I : Fin 3 → ℝ} (hI : ∀ i, 0 < I i) (h01 : I 0 < I 1)
    (h12 : I 1 < I 2) {ℓ : ℝ} (hℓ : ℓ ≠ 0) :
    0 < linearization poisson (kineticEnergy I) (Pi.single 1 ℓ) 0 2 *
      linearization poisson (kineticEnergy I) (Pi.single 1 ℓ) 2 0 := by
  rw [linearization_zero_two, linearization_two_zero]
  have a1 : (I 2)⁻¹ - (I 1)⁻¹ < 0 := sub_neg.mpr (inv_strictAnti₀ (hI 1) h12)
  have a2 : (I 1)⁻¹ - (I 0)⁻¹ < 0 := sub_neg.mpr (inv_strictAnti₀ (hI 0) h01)
  have hsq : 0 < ℓ ^ 2 := sq_pos_of_ne_zero hℓ
  nlinarith [mul_pos_of_neg_of_neg a1 a2]

/-- The rotation about the axis of the greatest moment is linearly stable: the
product of the two coefficients is negative. -/
theorem linearization_mul_neg_of_greatest {I : Fin 3 → ℝ} (hI : ∀ i, 0 < I i)
    (h01 : I 0 < I 1) (h21 : I 2 < I 1) {ℓ : ℝ} (hℓ : ℓ ≠ 0) :
    linearization poisson (kineticEnergy I) (Pi.single 1 ℓ) 0 2 *
      linearization poisson (kineticEnergy I) (Pi.single 1 ℓ) 2 0 < 0 := by
  rw [linearization_zero_two, linearization_two_zero]
  have a1 : 0 < (I 2)⁻¹ - (I 1)⁻¹ := sub_pos.mpr (inv_strictAnti₀ (hI 2) h21)
  have a2 : (I 1)⁻¹ - (I 0)⁻¹ < 0 := sub_neg.mpr (inv_strictAnti₀ (hI 0) h01)
  have hsq : 0 < ℓ ^ 2 := sq_pos_of_ne_zero hℓ
  nlinarith [mul_neg_of_pos_of_neg a1 a2]

/-- The rotation about the axis of the least moment is linearly stable. -/
theorem linearization_mul_neg_of_least {I : Fin 3 → ℝ} (hI : ∀ i, 0 < I i) (h10 : I 1 < I 0)
    (h12 : I 1 < I 2) {ℓ : ℝ} (hℓ : ℓ ≠ 0) :
    linearization poisson (kineticEnergy I) (Pi.single 1 ℓ) 0 2 *
      linearization poisson (kineticEnergy I) (Pi.single 1 ℓ) 2 0 < 0 := by
  rw [linearization_zero_two, linearization_two_zero]
  have a1 : (I 2)⁻¹ - (I 1)⁻¹ < 0 := sub_neg.mpr (inv_strictAnti₀ (hI 1) h12)
  have a2 : 0 < (I 1)⁻¹ - (I 0)⁻¹ := sub_pos.mpr (inv_strictAnti₀ (hI 1) h10)
  have hsq : 0 < ℓ ^ 2 := sq_pos_of_ne_zero hℓ
  nlinarith [mul_neg_of_neg_of_pos a1 a2]

end ProjectAInos.Mechanics.RigidBody
