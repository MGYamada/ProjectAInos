/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothAlgebra.FreeDerivation

/-!
# The chain rule for a substitution

A morphism out of a free C-infinity ring on finitely many generators is a
substitution `xₐ ↦ yₐ`. For a derivation `E` of the target,
`E (s(y)) = Σₐ (∂ₐ s)(y) • E (yₐ)`.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.SmoothAlgebra.FreeSmoothRing

open SmoothRing SmoothOperation

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [Fintype κ] in
/-- The substitution of a partial derivative, in terms of a presentation of the
element. -/
theorem lift_partialDerivation_eq_sum {B : Type*} [CommRing B] [Algebra ℝ B] [SmoothRing B]
    (y : κ → B) (a : κ) (s : FreeSmoothRing κ) :
    lift y (partialDerivation a s) =
      ∑ i, op (partialDeriv i (presentation s).operation)
        (fun j => y ((presentation s).indices j)) *
          (if (presentation s).indices i = a then 1 else 0) := by
  conv_lhs => rw [presentation_eq s]
  rw [SmoothDerivation.chain, SmoothRingHom.map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul, SmoothRingHom.map_mul, SmoothRingHom.map_op, partialDerivation_generator]
  simp only [lift_generator]
  split_ifs
  · rw [SmoothRingHom.map_one]
  · rw [SmoothRingHom.map_zero]

/-- The chain rule for a substitution: for a derivation `E` of the target of
`lift y`, `E (lift y s) = Σₐ lift y (∂ₐ s) • E (yₐ)`. -/
theorem derivation_lift {B M : Type*} [CommRing B] [Algebra ℝ B] [SmoothRing B]
    [AddCommGroup M] [Module B M] (y : κ → B) (E : SmoothDerivation B M)
    (s : FreeSmoothRing κ) :
    E (lift y s) = ∑ a, lift y (partialDerivation a s) • E (y a) := by
  have hE : E (lift y s) = ∑ i, op (partialDeriv i (presentation s).operation)
      (fun j => y ((presentation s).indices j)) • E (y ((presentation s).indices i)) := by
    conv_lhs => rw [presentation_eq s]
    rw [SmoothRingHom.map_op, E.chain]
    simp only [lift_generator]
  rw [hE]
  simp only [lift_partialDerivation_eq_sum, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single ((presentation s).indices i)]
  · simp only [↓reduceIte, mul_one]
  · intro a _ ha
    simp only [Ne.symm ha, ↓reduceIte, mul_zero, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The chain rule for a substitution, for a vector field of the target. -/
theorem derivation_lift_mul {B : Type*} [CommRing B] [Algebra ℝ B] [SmoothRing B]
    (y : κ → B) (E : SmoothDerivation B B) (s : FreeSmoothRing κ) :
    E (lift y s) = ∑ a, lift y (partialDerivation a s) * E (y a) :=
  derivation_lift y E s

end ProjectAInos.SmoothAlgebra.FreeSmoothRing
