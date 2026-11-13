/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The structure constants of `so(3)` as a matrix

For a vector `x` with entries in a commutative ring, `epsilon x a b` is
`Σ_c εₐ_bc x_c`. Generator brackets of angular momenta have this form. It is the
matrix of the cross product: `Σ_b epsilon x a b · v_b = (v × x)ₐ`.
-/

@[expose] public section

namespace ProjectAInos.Mechanics

open Matrix

variable {A : Type*} [CommRing A]

/-- The matrix `(a, b) ↦ Σ_c εₐ_bc x_c` of a vector `x`. -/
def epsilon (x : Fin 3 → A) : Fin 3 → Fin 3 → A :=
  ![![0, x 2, -x 1], ![-x 2, 0, x 0], ![x 1, -x 0, 0]]

theorem epsilon_skew (x : Fin 3 → A) (a b : Fin 3) : epsilon x a b = -epsilon x b a := by
  fin_cases a <;> fin_cases b <;> simp [epsilon]

theorem sum_epsilon_mul (x v : Fin 3 → A) (a : Fin 3) :
    ∑ b, epsilon x a b * v b = (v ⨯₃ x) a := by
  rw [Fin.sum_univ_three, cross_apply]
  fin_cases a <;> simp [epsilon] <;> ring

end ProjectAInos.Mechanics
