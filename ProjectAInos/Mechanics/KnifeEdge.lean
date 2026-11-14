/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Constants
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# A non-holonomic constraint: the knife edge

Landau–Lifshitz §38. A blade touches a plane at the point `(x, y)` and makes
the angle `θ` with the `x`-axis. It can slide along itself and turn, but it
cannot move sideways: `ẋ sin θ − ẏ cos θ = 0`.

The admissible velocities are spanned by the vector fields
`cos θ ∂ₓ + sin θ ∂_y` and `∂_θ`. Their commutator is the forbidden direction
`−sin θ ∂ₓ + cos θ ∂_y` (`commutator_turn_along`), so the admissible fields are
not closed under the commutator, and a function annihilated by them is a
constant (`eq_algebraMap_of_along_eq_zero_of_turn_eq_zero`): no equation
`f(x, y, θ) = const` follows from the constraint. A holonomic constraint is of
the opposite kind: it is an ideal of the ring of the configuration space, and
its tangent vectors are those of `FreeSmoothRing.presentedTangentPointEquiv`.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics.KnifeEdge

open SmoothAlgebra SmoothRing FreeSmoothRing

/-- The functions of the point of contact `(x, y)` and of the angle `θ`. -/
abbrev Configuration := FreeSmoothRing (Fin 3)

/-- The angle of the blade. -/
def θ : Configuration := generator 2

/-- `cos θ`. -/
def cosθ : Configuration := op TimeFunction.cos fun _ => θ

/-- `sin θ`. -/
def sinθ : Configuration := op TimeFunction.sin fun _ => θ

theorem cos_mul_cos_add_sin_mul_sin : cosθ * cosθ + sinθ * sinθ = 1 := by
  rw [cosθ, sinθ, ← op_mul, ← op_mul, ← op_add, TimeFunction.cos_mul_cos_add_sin_mul_sin, op_one]

theorem partialDerivation_cosθ : partialDerivation 2 cosθ = -sinθ := by
  have h : SmoothOperation.partialDeriv 0 TimeFunction.cos = -TimeFunction.sin :=
    TimeFunction.timeDerivative_cos
  rw [cosθ, SmoothDerivation.chain, Fin.sum_univ_one, h, op_neg, θ,
    partialDerivation_generator_self, smul_eq_mul, mul_one]
  rfl

theorem partialDerivation_sinθ : partialDerivation 2 sinθ = cosθ := by
  have h : SmoothOperation.partialDeriv 0 TimeFunction.sin = TimeFunction.cos :=
    TimeFunction.timeDerivative_sin
  rw [sinθ, SmoothDerivation.chain, Fin.sum_univ_one, h, θ, partialDerivation_generator_self,
    smul_eq_mul, mul_one]
  rfl

/-- The motion along the blade: `cos θ ∂ₓ + sin θ ∂_y`. -/
def along : SmoothDerivation Configuration Configuration :=
  FreeSmoothRing.derivation ![cosθ, sinθ, 0]

/-- The rotation of the blade: `∂_θ`. -/
def turn : SmoothDerivation Configuration Configuration :=
  partialDerivation 2

/-- The motion across the blade: `−sin θ ∂ₓ + cos θ ∂_y`. The constraint
forbids it. -/
def across : SmoothDerivation Configuration Configuration :=
  FreeSmoothRing.derivation ![-sinθ, cosθ, 0]

/-- The constraint `ẋ sin θ − ẏ cos θ` on a velocity `(ẋ, ẏ, θ̇)`. -/
def constraint (v : Fin 3 → Configuration) : Configuration :=
  v 0 * sinθ - v 1 * cosθ

theorem constraint_along : constraint (fun c => along (generator c)) = 0 := by
  simp only [constraint, along, derivation_generator, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem constraint_turn : constraint (fun c => turn (generator c)) = 0 := by
  simp [constraint, turn, partialDerivation_generator]

theorem constraint_across : constraint (fun c => across (generator c)) = -1 := by
  simp only [constraint, across, derivation_generator, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination -cos_mul_cos_add_sin_mul_sin

/-- The commutator of the two admissible fields is the forbidden direction:
`[∂_θ, cos θ ∂ₓ + sin θ ∂_y] = −sin θ ∂ₓ + cos θ ∂_y`. -/
theorem commutator_turn_along : ⁅turn, along⁆ = across :=
  derivation_ext fun c => by
    rw [SmoothDerivation.commutator_apply, along, across, derivation_generator,
      derivation_generator, turn, partialDerivation_generator]
    fin_cases c
    · change partialDerivation 2 cosθ - FreeSmoothRing.derivation ![cosθ, sinθ, 0] 0 = -sinθ
      rw [partialDerivation_cosθ, map_zero, sub_zero]
    · change partialDerivation 2 sinθ - FreeSmoothRing.derivation ![cosθ, sinθ, 0] 0 = cosθ
      rw [partialDerivation_sinθ, map_zero, sub_zero]
    · change partialDerivation 2 (0 : Configuration) -
        FreeSmoothRing.derivation ![cosθ, sinθ, 0] 1 = 0
      rw [map_zero, SmoothDerivation.map_one, sub_zero]

/-- A vector field of the configuration space in terms of the partial
derivatives. -/
theorem derivation_apply (w : Fin 3 → Configuration) (f : Configuration) :
    FreeSmoothRing.derivation w f =
      partialDerivation 0 f * w 0 + partialDerivation 1 f * w 1 + partialDerivation 2 f * w 2 := by
  have h := apply_eq_sum_partialDerivation (FreeSmoothRing.derivation w) f
  have hsub : ∑ a ∈ Finset.univ.image (presentation f).indices,
      partialDerivation a f • FreeSmoothRing.derivation w (generator a) =
        ∑ a, partialDerivation a f • FreeSmoothRing.derivation w (generator a) := by
    refine Finset.sum_subset (Finset.subset_univ _) fun a _ ha => ?_
    have h0 : partialDerivation a f = 0 := by
      conv_lhs => rw [presentation_eq f]
      exact partialDerivation_op_eq_zero a _ _ fun j hj =>
        ha (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩)
    rw [h0, zero_smul]
  rw [h, hsub, Fin.sum_univ_three]
  simp only [derivation_generator, smul_eq_mul]

/-- A function annihilated by the admissible motions is a constant: the
constraint of the knife edge is not holonomic. -/
theorem eq_algebraMap_of_along_eq_zero_of_turn_eq_zero {f : Configuration}
    (h1 : along f = 0) (h2 : turn f = 0) :
    f = algebraMap ℝ Configuration (FreeSmoothRing.lift (fun _ => 0) f) := by
  have h3 : across f = 0 := by
    rw [← commutator_turn_along, SmoothDerivation.commutator_apply, h1, h2, map_zero, map_zero,
      sub_zero]
  have ha : partialDerivation 0 f * cosθ + partialDerivation 1 f * sinθ = 0 := by
    have h := derivation_apply ![cosθ, sinθ, 0] f
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons, mul_zero, add_zero] at h
    rw [← h]
    exact h1
  have hc : partialDerivation 0 f * -sinθ + partialDerivation 1 f * cosθ = 0 := by
    have h := derivation_apply ![-sinθ, cosθ, 0] f
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons, mul_zero, add_zero] at h
    rw [← h]
    exact h3
  refine eq_algebraMap_of_partialDerivation_eq_zero (fun c => ?_) _
  fin_cases c
  · change partialDerivation 0 f = 0
    linear_combination cosθ * ha - sinθ * hc -
      partialDerivation 0 f * cos_mul_cos_add_sin_mul_sin
  · change partialDerivation 1 f = 0
    linear_combination sinθ * ha + cosθ * hc -
      partialDerivation 1 f * cos_mul_cos_add_sin_mul_sin
  · exact h2

end ProjectAInos.Mechanics.KnifeEdge
