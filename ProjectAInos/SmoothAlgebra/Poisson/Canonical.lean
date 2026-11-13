/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothAlgebra.Poisson.Free
import Mathlib.Tactic.Ring

/-!
# The canonical Poisson structure

The canonical phase space over coordinates `ι` is the free C-infinity ring on
positions `qᵢ` and momenta `pᵢ`. Its Poisson structure is determined by
`{qᵢ, pⱼ} = δᵢⱼ` and `{qᵢ, qⱼ} = {pᵢ, pⱼ} = 0`; the Jacobi identity holds
because these brackets are constants. In coordinates the bracket is
`{f, g} = Σᵢ (∂f/∂qᵢ ∂g/∂pᵢ − ∂f/∂pᵢ ∂g/∂qᵢ)`, and Hamilton's equations are
`{qᵢ, H} = ∂H/∂pᵢ`, `{pᵢ, H} = −∂H/∂qᵢ`.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.SmoothAlgebra

open SmoothRing FreeSmoothRing

/-- The canonical phase space over coordinates `ι`: the free C-infinity ring on
positions `Sum.inl i` and momenta `Sum.inr i`. -/
abbrev PhaseSpace (ι : Type*) := FreeSmoothRing (ι ⊕ ι)

namespace PhaseSpace

variable {ι : Type*}

/-- The position coordinate `qᵢ`. -/
def q (i : ι) : PhaseSpace ι := generator (Sum.inl i)

/-- The momentum coordinate `pᵢ`. -/
def p (i : ι) : PhaseSpace ι := generator (Sum.inr i)

variable [DecidableEq ι]

/-- The canonical brackets of the generators. -/
def canonicalMatrix : ι ⊕ ι → ι ⊕ ι → PhaseSpace ι
  | Sum.inl i, Sum.inr j => if i = j then 1 else 0
  | Sum.inr i, Sum.inl j => if i = j then -1 else 0
  | Sum.inl _, Sum.inl _ => 0
  | Sum.inr _, Sum.inr _ => 0

theorem canonicalMatrix_inl_inl (i j : ι) :
    (canonicalMatrix (Sum.inl i) (Sum.inl j) : PhaseSpace ι) = 0 := rfl

theorem canonicalMatrix_inr_inr (i j : ι) :
    (canonicalMatrix (Sum.inr i) (Sum.inr j) : PhaseSpace ι) = 0 := rfl

theorem canonicalMatrix_inl_inr (i j : ι) :
    (canonicalMatrix (Sum.inl i) (Sum.inr j) : PhaseSpace ι) = if i = j then 1 else 0 := rfl

theorem canonicalMatrix_inr_inl (i j : ι) :
    (canonicalMatrix (Sum.inr i) (Sum.inl j) : PhaseSpace ι) = if i = j then -1 else 0 := rfl

theorem canonicalMatrix_skew (a b : ι ⊕ ι) :
    (canonicalMatrix a b : PhaseSpace ι) = -canonicalMatrix b a := by
  rcases a with i | i <;> rcases b with j | j
  · exact neg_zero.symm
  · rw [canonicalMatrix_inl_inr, canonicalMatrix_inr_inl]
    split_ifs with h1 h2 h2
    · exact (neg_neg _).symm
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · exact neg_zero.symm
  · rw [canonicalMatrix_inl_inr, canonicalMatrix_inr_inl]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · exact neg_zero.symm
  · exact neg_zero.symm

theorem partialDerivation_canonicalMatrix (c a b : ι ⊕ ι) :
    partialDerivation c (canonicalMatrix a b : PhaseSpace ι) = 0 := by
  rcases a with i | i <;> rcases b with j | j
  · exact map_zero _
  · rw [canonicalMatrix_inl_inr]
    split_ifs
    · exact SmoothDerivation.map_one _
    · exact map_zero _
  · rw [canonicalMatrix_inr_inl]
    split_ifs
    · rw [map_neg, SmoothDerivation.map_one, neg_zero]
    · exact map_zero _
  · exact map_zero _

variable [Fintype ι]

variable (ι) in
/-- The canonical Poisson structure on phase space. -/
def canonical : PoissonStructure (PhaseSpace ι) :=
  poissonOfConstants canonicalMatrix canonicalMatrix_skew
    fun a b c => partialDerivation_canonicalMatrix c a b

theorem canonical_bracket_eq_sum (f g : PhaseSpace ι) :
    (canonical ι).bracket f g =
      ∑ a, ∑ b, partialDerivation a f * partialDerivation b g * canonicalMatrix a b := rfl

/-- The canonical bracket in coordinates:
`{f, g} = Σᵢ (∂f/∂qᵢ ∂g/∂pᵢ − ∂f/∂pᵢ ∂g/∂qᵢ)`. -/
theorem canonical_bracket (f g : PhaseSpace ι) :
    (canonical ι).bracket f g =
      ∑ i, (partialDerivation (Sum.inl i) f * partialDerivation (Sum.inr i) g -
        partialDerivation (Sum.inr i) f * partialDerivation (Sum.inl i) g) := by
  rw [canonical_bracket_eq_sum]
  simp only [Fintype.sum_sum_type, canonicalMatrix_inl_inl, canonicalMatrix_inr_inr,
    canonicalMatrix_inl_inr, canonicalMatrix_inr_inl, mul_zero, Finset.sum_const_zero, zero_add,
    add_zero, mul_ite, mul_one, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.sum_sub_distrib, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

theorem canonical_bracket_generator (a b : ι ⊕ ι) :
    (canonical ι).bracket (generator a) (generator b) = canonicalMatrix a b :=
  almostPoisson_bracket_generator canonicalMatrix canonicalMatrix_skew a b

/-- `{qᵢ, pⱼ} = δᵢⱼ`. -/
theorem canonical_q_p (i j : ι) : (canonical ι).bracket (q i) (p j) = if i = j then 1 else 0 :=
  canonical_bracket_generator _ _

/-- `{pᵢ, qⱼ} = −δᵢⱼ`. -/
theorem canonical_p_q (i j : ι) : (canonical ι).bracket (p i) (q j) = if i = j then -1 else 0 :=
  canonical_bracket_generator _ _

/-- `{qᵢ, qⱼ} = 0`. -/
theorem canonical_q_q (i j : ι) : (canonical ι).bracket (q i) (q j) = 0 :=
  canonical_bracket_generator _ _

/-- `{pᵢ, pⱼ} = 0`. -/
theorem canonical_p_p (i j : ι) : (canonical ι).bracket (p i) (p j) = 0 :=
  canonical_bracket_generator _ _

/-- Hamilton's equation for a position: `{qᵢ, H} = ∂H/∂pᵢ`. -/
theorem canonical_q_bracket (i : ι) (H : PhaseSpace ι) :
    (canonical ι).bracket (q i) H = partialDerivation (Sum.inr i) H := by
  rw [canonical_bracket, Finset.sum_eq_single i]
  · rw [q, partialDerivation_generator_self,
      partialDerivation_generator_of_ne (c := Sum.inr i) (i := Sum.inl i) (by simp), one_mul,
      zero_mul, sub_zero]
  · intro j _ hji
    rw [q, partialDerivation_generator_of_ne (c := Sum.inl j) (i := Sum.inl i)
        (fun h => hji (Sum.inl.inj h).symm),
      partialDerivation_generator_of_ne (c := Sum.inr j) (i := Sum.inl i) (by simp), zero_mul,
      zero_mul, sub_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- Hamilton's equation for a momentum: `{pᵢ, H} = −∂H/∂qᵢ`. -/
theorem canonical_p_bracket (i : ι) (H : PhaseSpace ι) :
    (canonical ι).bracket (p i) H = -partialDerivation (Sum.inl i) H := by
  rw [canonical_bracket, Finset.sum_eq_single i]
  · rw [p, partialDerivation_generator_self,
      partialDerivation_generator_of_ne (c := Sum.inl i) (i := Sum.inr i) (by simp), one_mul,
      zero_mul, zero_sub]
  · intro j _ hji
    rw [p, partialDerivation_generator_of_ne (c := Sum.inr j) (i := Sum.inr i)
        (fun h => hji (Sum.inr.inj h).symm),
      partialDerivation_generator_of_ne (c := Sum.inl j) (i := Sum.inr i) (by simp), zero_mul,
      zero_mul, sub_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The time derivative of an observable along the Hamiltonian flow in
coordinates: `{f, H} = Σᵢ (∂f/∂qᵢ ∂H/∂pᵢ − ∂f/∂pᵢ ∂H/∂qᵢ)`, with Hamilton's
equations as the special cases `f = qᵢ` and `f = pᵢ`. -/
theorem canonical_hamiltonian_apply (H f : PhaseSpace ι) :
    (canonical ι).hamiltonian H f =
      ∑ i, (partialDerivation (Sum.inl i) f * (canonical ι).bracket (q i) H +
        partialDerivation (Sum.inr i) f * (canonical ι).bracket (p i) H) := by
  rw [AlmostPoissonStructure.hamiltonian_apply, canonical_bracket]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [canonical_q_bracket, canonical_p_bracket]
  ring

end PhaseSpace

end ProjectAInos.SmoothAlgebra
