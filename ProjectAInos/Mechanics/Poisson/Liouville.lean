/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Oscillations.Dissipation
import Mathlib.Tactic.Ring

/-!
# Liouville's theorem in infinitesimal form

The divergence of a vector field `X` on a free C-infinity ring with finitely
many generators is `Σₐ ∂ₐ (X xₐ)`. A Hamiltonian vector field of the canonical
bracket has zero divergence (Landau–Lifshitz §46): the phase volume is
preserved to first order. With friction the divergence is `−Σᵢ ∂fᵢ/∂pᵢ`; for
the oscillator with the friction coefficients `aᵢ` it is the negative constant
`−Σᵢ aᵢ/mᵢ`, so the phase volume contracts.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics

open SmoothAlgebra SmoothRing FreeSmoothRing PhaseSpace

/-- The divergence `Σₐ ∂ₐ (X xₐ)` of a vector field on a free C-infinity ring
with finitely many generators. -/
def divergence {κ : Type*} [Fintype κ] [DecidableEq κ]
    (X : SmoothDerivation (FreeSmoothRing κ) (FreeSmoothRing κ)) : FreeSmoothRing κ :=
  ∑ a, partialDerivation a (X (generator a))

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- The divergence on the canonical phase space:
`Σᵢ (∂(X qᵢ)/∂qᵢ + ∂(X pᵢ)/∂pᵢ)`. -/
theorem divergence_eq (X : SmoothDerivation (PhaseSpace ι) (PhaseSpace ι)) :
    divergence X =
      ∑ i, partialDerivation (Sum.inl i) (X (PhaseSpace.q i)) +
        ∑ i, partialDerivation (Sum.inr i) (X (PhaseSpace.p i)) := by
  rw [divergence, Fintype.sum_sum_type]
  rfl

/-- Liouville's theorem in infinitesimal form (Landau–Lifshitz §46): a
Hamiltonian vector field of the canonical bracket has zero divergence. -/
theorem divergence_hamiltonian (H : PhaseSpace ι) :
    divergence ((canonical ι).hamiltonian H) = 0 := by
  rw [divergence_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [AlmostPoissonStructure.hamiltonian_apply, AlmostPoissonStructure.hamiltonian_apply,
    canonical_q_bracket, canonical_p_bracket, map_neg,
    partialDerivation_comm (Sum.inr i) (Sum.inl i) H, add_neg_cancel]

/-- With friction the divergence is `−Σᵢ ∂fᵢ/∂pᵢ`. -/
theorem divergence_dissipativeField (α : Matrix ι ι ℝ) (H : PhaseSpace ι) :
    divergence (dissipativeField α H) =
      -∑ i, partialDerivation (Sum.inr i) (frictionalForce α H i) := by
  rw [divergence_eq, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dissipativeField_q, dissipativeField_p, map_sub, map_neg, velocity,
    partialDerivation_comm (Sum.inr i) (Sum.inl i) H]
  ring

/-- The phase volume of the oscillator with friction contracts at the constant
rate `Σᵢ aᵢ/mᵢ`. -/
theorem Oscillator.divergence_dissipativeField (m a : ι → ℝ) (k : ℝ) :
    divergence (dissipativeField (Matrix.diagonal a) (Oscillator.hamiltonian m k)) =
      -algebraMap ℝ (PhaseSpace ι) (∑ i, a i * (m i)⁻¹) := by
  rw [Mechanics.divergence_dissipativeField, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Oscillator.frictionalForce_diagonal, Oscillator.velocity_hamiltonian,
    SmoothDerivation.map_algebraMap_mul, SmoothDerivation.map_algebraMap_mul, PhaseSpace.p,
    partialDerivation_generator_self, smul_eq_mul, smul_eq_mul, mul_one, ← map_mul]

end ProjectAInos.Mechanics
