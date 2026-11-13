/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothAlgebra.FreeDerivation
public import ProjectAInos.SmoothAlgebra.Poisson.Basic
import Mathlib.Tactic.Ring

/-!
# Poisson structures on free C-infinity rings

On the free C-infinity ring over finitely many generators, a bracket is
determined by its values `w a b` on pairs of generators:
`{f, g} = Σ_{a,b} ∂ₐf ∂_b g w a b`. For a skew family `w` this is an
almost-Poisson structure, an instance of the bracket of a family of vector
fields. The Jacobi identity holds for all elements as soon as it holds for
generators, because the Jacobiator is a derivation in each argument. The
canonical bracket and the Lie–Poisson brackets are of this form.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.SmoothAlgebra.FreeSmoothRing

open SmoothRing SmoothOperation

variable {κ : Type*}

/-- In a free ring, the Jacobi identity holds if it holds on generators. -/
theorem jacobiator_eq_zero (π : AlmostPoissonStructure (FreeSmoothRing κ))
    (h : ∀ a b c, π.jacobiator (generator a) (generator b) (generator c) = 0)
    (f g k : FreeSmoothRing κ) : π.jacobiator f g k = 0 := by
  have step (g k : FreeSmoothRing κ) (hgk : ∀ a, π.jacobiator (generator a) g k = 0)
      (f : FreeSmoothRing κ) : π.jacobiator f g k = 0 := by
    rw [presentation_eq f, π.jacobiator_op]
    exact Finset.sum_eq_zero fun i _ => by rw [hgk, mul_zero]
  refine step g k (fun a => ?_) f
  rw [π.jacobiator_cyclic]
  refine step k (generator a) (fun b => ?_) g
  rw [π.jacobiator_cyclic]
  exact step (generator a) (generator b) (fun c => h c a b) k

variable [Fintype κ] [DecidableEq κ]

/-- The almost-Poisson structure on the free ring with prescribed brackets
`w a b` of the generators. -/
def almostPoisson (w : κ → κ → FreeSmoothRing κ) (hw : ∀ a b, w a b = -w b a) :
    AlmostPoissonStructure (FreeSmoothRing κ) :=
  AlmostPoissonStructure.ofDerivations partialDerivation w hw

theorem almostPoisson_bracket (w : κ → κ → FreeSmoothRing κ) (hw : ∀ a b, w a b = -w b a)
    (f g : FreeSmoothRing κ) :
    (almostPoisson w hw).bracket f g =
      ∑ a, ∑ b, partialDerivation a f * partialDerivation b g * w a b := rfl

/-- Bracket with a generator on the right. -/
theorem almostPoisson_bracket_generator_right (w : κ → κ → FreeSmoothRing κ)
    (hw : ∀ a b, w a b = -w b a) (f : FreeSmoothRing κ) (c : κ) :
    (almostPoisson w hw).bracket f (generator c) = ∑ a, partialDerivation a f * w a c := by
  rw [almostPoisson_bracket]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single c]
  · rw [partialDerivation_generator_self, mul_one]
  · intro b _ hbc
    rw [partialDerivation_generator_of_ne (Ne.symm hbc), mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ c) h

/-- Bracket with a generator on the left. -/
theorem almostPoisson_bracket_generator_left (w : κ → κ → FreeSmoothRing κ)
    (hw : ∀ a b, w a b = -w b a) (c : κ) (g : FreeSmoothRing κ) :
    (almostPoisson w hw).bracket (generator c) g = ∑ b, partialDerivation b g * w c b := by
  rw [almostPoisson_bracket, Finset.sum_eq_single c]
  · exact Finset.sum_congr rfl fun b _ => by rw [partialDerivation_generator_self, one_mul]
  · intro a _ hac
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [partialDerivation_generator_of_ne (Ne.symm hac), zero_mul, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ c) h

/-- The bracket in terms of the brackets of the generators with the second
argument: `{f, g} = Σₐ ∂ₐf {xₐ, g}`. -/
theorem almostPoisson_bracket_eq_sum_left (w : κ → κ → FreeSmoothRing κ)
    (hw : ∀ a b, w a b = -w b a) (f g : FreeSmoothRing κ) :
    (almostPoisson w hw).bracket f g =
      ∑ a, partialDerivation a f * (almostPoisson w hw).bracket (generator a) g := by
  rw [almostPoisson_bracket]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [almostPoisson_bracket_generator_left, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- The prescribed values are the brackets of the generators. -/
@[simp] theorem almostPoisson_bracket_generator (w : κ → κ → FreeSmoothRing κ)
    (hw : ∀ a b, w a b = -w b a) (a b : κ) :
    (almostPoisson w hw).bracket (generator a) (generator b) = w a b := by
  rw [almostPoisson_bracket_generator_right, Finset.sum_eq_single a]
  · rw [partialDerivation_generator_self, one_mul]
  · intro c _ hca
    rw [partialDerivation_generator_of_ne (Ne.symm hca), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ a) h

/-- An element with vanishing partial derivatives has vanishing brackets. -/
theorem almostPoisson_bracket_eq_zero_left (w : κ → κ → FreeSmoothRing κ)
    (hw : ∀ a b, w a b = -w b a) {f : FreeSmoothRing κ}
    (hf : ∀ a, partialDerivation a f = 0) (g : FreeSmoothRing κ) :
    (almostPoisson w hw).bracket f g = 0 := by
  rw [almostPoisson_bracket]
  exact Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => by
    rw [hf a, zero_mul, zero_mul]

/-- The Poisson structure on a free ring with prescribed generator brackets.
The Jacobi identity is required on generators only. -/
def poissonOfCoordinates (w : κ → κ → FreeSmoothRing κ) (hw : ∀ a b, w a b = -w b a)
    (hjac : ∀ a b c, (almostPoisson w hw).bracket (w a b) (generator c) +
      (almostPoisson w hw).bracket (w b c) (generator a) +
      (almostPoisson w hw).bracket (w c a) (generator b) = 0) :
    PoissonStructure (FreeSmoothRing κ) where
  toAlmostPoissonStructure := almostPoisson w hw
  jacobi f g k := jacobiator_eq_zero (almostPoisson w hw) (fun a b c => by
    unfold AlmostPoissonStructure.jacobiator
    rw [almostPoisson_bracket_generator, almostPoisson_bracket_generator,
      almostPoisson_bracket_generator]
    exact hjac a b c) f g k

/-- Generator brackets with vanishing partial derivatives always satisfy the
Jacobi identity. Constant brackets are of this kind. -/
def poissonOfConstants (w : κ → κ → FreeSmoothRing κ) (hw : ∀ a b, w a b = -w b a)
    (hconst : ∀ a b c, partialDerivation c (w a b) = 0) :
    PoissonStructure (FreeSmoothRing κ) :=
  poissonOfCoordinates w hw fun a b c => by
    rw [almostPoisson_bracket_eq_zero_left w hw (hconst a b),
      almostPoisson_bracket_eq_zero_left w hw (hconst b c),
      almostPoisson_bracket_eq_zero_left w hw (hconst c a), add_zero, add_zero]

end ProjectAInos.SmoothAlgebra.FreeSmoothRing
