/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothAlgebra.Poisson.Basic
public import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Ideals in Poisson C-infinity rings

Constraints and reductions are ideals. An ideal `I` is a Poisson ideal when
`{I, P} ⊆ I` and coisotropic when `{I, I} ⊆ I`. The normalizer
`N(I) = {f | {f, I} ⊆ I}` is closed under the ring operations, every smooth
operation and the bracket, and the bracket of `N(I)` is well defined modulo
`I`. This is the algebraic content of coisotropic reduction; the quotient
C-infinity ring itself needs quotients by ordinary ideals and is not built
here.

Two classical statements are one line each in this language. Hamilton–Jacobi:
if `I` is coisotropic and `H − E ∈ I`, the Hamiltonian vector field of `H`
preserves `I`. Maupertuis–Jacobi: if `H' − E' = u (H − E)`, then
`{g, H'} ≡ u {g, H}` modulo `(H − E)`.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.SmoothAlgebra.PoissonStructure

open SmoothRing SmoothOperation

variable {P : Type*} [CommRing P] [Algebra ℝ P] [SmoothRing P] (π : PoissonStructure P)

/-- A Poisson ideal: `{I, P} ⊆ I`. -/
def IsPoissonIdeal (I : Ideal P) : Prop := ∀ f ∈ I, ∀ g, π.bracket f g ∈ I

/-- A coisotropic (first-class) ideal: `{I, I} ⊆ I`. -/
def IsCoisotropic (I : Ideal P) : Prop := ∀ f ∈ I, ∀ g ∈ I, π.bracket f g ∈ I

/-- The normalizer `N(I) = {f | {f, I} ⊆ I}`, a real subalgebra. -/
def normalizer (I : Ideal P) : Subalgebra ℝ P where
  carrier := {f | ∀ g ∈ I, π.bracket f g ∈ I}
  mul_mem' {f f'} hf hf' g hg := by
    rw [π.toAlmostPoissonStructure.bracket_mul_left]
    exact add_mem (Ideal.mul_mem_left _ _ (hf' g hg)) (Ideal.mul_mem_left _ _ (hf g hg))
  add_mem' {f f'} hf hf' g hg := by
    rw [π.toAlmostPoissonStructure.bracket_add_left]
    exact add_mem (hf g hg) (hf' g hg)
  algebraMap_mem' r g _ := by
    rw [π.toAlmostPoissonStructure.bracket_algebraMap_left]
    exact zero_mem _

variable {π}

theorem mem_normalizer {I : Ideal P} {f : P} :
    f ∈ π.normalizer I ↔ ∀ g ∈ I, π.bracket f g ∈ I := Iff.rfl

theorem IsPoissonIdeal.isCoisotropic {I : Ideal P} (h : π.IsPoissonIdeal I) :
    π.IsCoisotropic I := fun f hf g _ => h f hf g

/-- A principal ideal is a Poisson ideal if the brackets of its generator lie
in it. -/
theorem isPoissonIdeal_span_singleton {c : P}
    (h : ∀ g, π.bracket c g ∈ Ideal.span {c}) : π.IsPoissonIdeal (Ideal.span {c}) := by
  intro f hf g
  obtain ⟨k, rfl⟩ := Ideal.mem_span_singleton'.mp hf
  rw [π.toAlmostPoissonStructure.bracket_mul_left]
  exact add_mem (Ideal.mul_mem_left _ _ (h g))
    (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))

/-- A coisotropic ideal lies in its normalizer. -/
theorem IsCoisotropic.le_normalizer {I : Ideal P} (h : π.IsCoisotropic I) {f : P}
    (hf : f ∈ I) : f ∈ π.normalizer I := fun g hg => h f hf g hg

/-- Inside the normalizer, `I` behaves as a Poisson ideal. -/
theorem bracket_mem_of_mem_normalizer {I : Ideal P} {j f : P} (hj : j ∈ I)
    (hf : f ∈ π.normalizer I) : π.bracket j f ∈ I := by
  rw [π.antisymm]
  exact neg_mem (hf j hj)

/-- The normalizer is closed under the bracket. -/
theorem bracket_mem_normalizer {I : Ideal P} {f g : P} (hf : f ∈ π.normalizer I)
    (hg : g ∈ π.normalizer I) : π.bracket f g ∈ π.normalizer I := fun j hj => by
  rw [π.bracket_bracket]
  exact add_mem (bracket_mem_of_mem_normalizer (hf j hj) hg) (hf _ (hg j hj))

/-- The normalizer is closed under every smooth operation. -/
theorem op_mem_normalizer {I : Ideal P} {n : ℕ} (f : SmoothOperation n) {c : Fin n → P}
    (hc : ∀ i, c i ∈ π.normalizer I) : op f c ∈ π.normalizer I := fun j hj => by
  rw [π.chain]
  exact sum_mem fun i _ => Ideal.mul_mem_left _ _ (hc i j hj)

/-- Coisotropic reduction: the bracket on the normalizer is well defined modulo
the ideal. -/
theorem bracket_sub_bracket_mem {I : Ideal P} {f f' g g' : P} (hf' : f' ∈ π.normalizer I)
    (hg : g ∈ π.normalizer I) (hff' : f - f' ∈ I) (hgg' : g - g' ∈ I) :
    π.bracket f g - π.bracket f' g' ∈ I := by
  have h : π.bracket f g - π.bracket f' g' =
      π.bracket (f - f') g + π.bracket f' (g - g') := by
    rw [π.toAlmostPoissonStructure.bracket_sub_left,
      π.toAlmostPoissonStructure.bracket_sub_right]
    abel
  rw [h]
  exact add_mem (bracket_mem_of_mem_normalizer hff' hg) (hf' _ hgg')

/-- Hamilton–Jacobi (Landau–Lifshitz §47): if `I` is coisotropic and
`H − E ∈ I` for a constant `E`, then `{I, H} ⊆ I`. The Hamiltonian vector field
of `H` is tangent to the zero locus of `I`. -/
theorem hamiltonJacobi {I : Ideal P} (hI : π.IsCoisotropic I) {H : P} {E : ℝ}
    (hH : H - algebraMap ℝ P E ∈ I) {f : P} (hf : f ∈ I) : π.bracket f H ∈ I := by
  have h := hI f hf _ hH
  rwa [π.toAlmostPoissonStructure.bracket_sub_right,
    π.toAlmostPoissonStructure.bracket_algebraMap_right, sub_zero] at h

/-- The exact form of the Maupertuis–Jacobi identity:
`{g, u (H − E)} = u {g, H} + (H − E) {g, u}`. -/
theorem bracket_mul_sub_algebraMap (g u H : P) (E : ℝ) :
    π.bracket g (u * (H - algebraMap ℝ P E)) =
      u * π.bracket g H + (H - algebraMap ℝ P E) * π.bracket g u := by
  rw [π.toAlmostPoissonStructure.bracket_mul_right,
    π.toAlmostPoissonStructure.bracket_sub_right,
    π.toAlmostPoissonStructure.bracket_algebraMap_right, sub_zero]

/-- Maupertuis–Jacobi (Landau–Lifshitz §44): if `H' − E' = u (H − E)`, then
`{g, H'} ≡ u {g, H}` modulo the ideal `(H − E)`. On the energy surface the two
Hamiltonian vector fields are proportional: the trajectories of energy `E`
depend only on the ideal, and the generator fixes the time parametrization. -/
theorem maupertuis {H H' u : P} {E E' : ℝ}
    (h : H' - algebraMap ℝ P E' = u * (H - algebraMap ℝ P E)) (g : P) :
    π.bracket g H' - u * π.bracket g H ∈ Ideal.span {H - algebraMap ℝ P E} := by
  have h' : π.bracket g H' = π.bracket g (H' - algebraMap ℝ P E') := by
    rw [π.toAlmostPoissonStructure.bracket_sub_right,
      π.toAlmostPoissonStructure.bracket_algebraMap_right, sub_zero]
  rw [h', h, bracket_mul_sub_algebraMap, add_sub_cancel_left]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

end ProjectAInos.SmoothAlgebra.PoissonStructure
