/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Poisson.CompleteIntegral

/-!
# The action along a curve

Landau–Lifshitz §43. For a solution `S(q, α, t)` of the Hamilton–Jacobi
equation and any curve `q(t)`, the derivative of the action along the curve is
`dS/dt = Σ pᵢ q̇ᵢ − H(q, p)` with `pᵢ = ∂S/∂qᵢ`: the relation
`dS = p dq − H dt`.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics.CompleteIntegral

open SmoothAlgebra SmoothRing FreeSmoothRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- The action along a curve (Landau–Lifshitz §43): for a solution `S` of the
Hamilton–Jacobi equation, `dS/dt = Σ pᵢ q̇ᵢ − H(q, p)` with `pᵢ = ∂S/∂qᵢ`. -/
theorem IsHamiltonJacobi.timeDerivative_along {H : PhaseSpace ι} {S : ActionSpace ι}
    (h : IsHamiltonJacobi H S) (Q : ι → TimeFunction) (α : ι → ℝ) :
    timeDerivative (along Q α S) =
      ∑ k, momentum S Q α k * timeDerivative (Q k) -
        FreeSmoothRing.lift (Sum.elim Q (momentum S Q α)) H := by
  have ht : partialDerivation tIndex S = -substitution S H := eq_neg_of_add_eq_zero_left h
  rw [CompleteIntegral.timeDerivative_along, ht, SmoothRingHom.map_neg, along_substitution,
    sub_eq_add_neg]
  rfl

end ProjectAInos.Mechanics.CompleteIntegral
