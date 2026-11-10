module

public import ProjectAInos.Thermodynamics.HasCalibratorsOfAxioms
public import ProjectAInos.Thermodynamics.AtomicSystems

/-!
# Entropy principles from physical premises

These endpoints discharge calibrator existence using A1--A7, S1--S3 and
T1--T4 as encoded by `Accessibility`, `SimpleSystem` and `ThermalFamily`.
Finite-product comparison and entropy calibration are conclusions rather than
additional hypotheses. For reactions, the only extra physical premise is
absence of sinks in the actual transition graph.

All primitive systems used here satisfy transversality. T5 is therefore not
needed for these results; extension to systems without T4 is a different task.
-/

@[expose] public section

open scoped NNReal

namespace ProjectAInos.Thermodynamics.Physical.ThermalFamily

section Products

variable {X : Type*} [AddCommMonoid X] [DistribMulAction ℝ≥0 X]
    {P : Accessibility X} (F : ThermalFamily P)

/-- LY 4.8: all states of every finite scaled product of admitted simple systems
are comparable, including empty products and zero physical amounts. -/
theorem product_comparison {ι : Type*} [Fintype ι]
    (n : ι → ℕ) (S : ∀ i, SimpleSystem P (n i)) (hS : ∀ i, F.admitted (S i))
    (weight : ι → ℝ≥0) (x y : ∀ i, (S i).domain) :
    P.relation (∑ i, weight i • (S i).represent (x i))
        (∑ i, weight i • (S i).represent (y i)) ∨
      P.relation (∑ i, weight i • (S i).represent (y i))
        (∑ i, weight i • (S i).represent (x i)) :=
  F.scaled_products_comparable F.hasCalibrators_of_axioms n S hS weight x y

end Products

section Composites

variable {Γ : Type*} {State : Γ → Type*}
    {P : Accessibility (CompositeState (Σ g, State g))} (F : ThermalFamily P)

/-- Physical comparison gives ECH on the adiabatic quotient when accessibility
preserves primitive composition labels. Common products are constructed from
the formal syntax; their existence is not a premise. -/
theorem exchangeComparison_of_physical_axioms
    (n : Γ → ℕ) (S : ∀ g, SimpleSystem P (n g))
    (hS : ∀ g, F.admitted (S g)) (chart : ∀ g, State g → (S g).domain)
    (hrepresent : ∀ g z, (S g).represent (chart g z) = CompositeState.mk (.atom ⟨g, z⟩))
    (hpreserved : ∀ {x y}, P.relation x y →
      Nonreactive.compositionLabel State x = Nonreactive.compositionLabel State y) :
    ExchangeComparison P.StateSpace :=
  F.exchangeComparison_of_calibrators F.hasCalibrators_of_axioms n S hS chart hrepresent hpreserved

/-- Additive extensive entropy characterizes accessibility within each
composition label, derived from the physical axioms without CH or ECH input. -/
theorem exists_entropy_of_physical_axioms
    (n : Γ → ℕ) (S : ∀ g, SimpleSystem P (n g))
    (hS : ∀ g, F.admitted (S g)) (hnonempty : ∀ g, (S g).domain.Nonempty)
    (chart : ∀ g, State g → (S g).domain)
    (hrepresent : ∀ g z, (S g).represent (chart g z) = CompositeState.mk (.atom ⟨g, z⟩)) :
    ∃ entropy : CompositeState (Σ g, State g) →+ ℝ,
      (∀ (r : ℝ≥0) x, entropy (r • x) = (r : ℝ) * entropy x) ∧
      ∀ x y, Nonreactive.compositionLabel State x = Nonreactive.compositionLabel State y →
        (P.relation x y ↔ entropy x ≤ entropy y) :=
  F.exists_calibrated_entropy F.hasCalibrators_of_axioms n S hS hnonempty chart hrepresent

/-- A weak entropy principle for mixtures and reactions, from the physical
axioms and M expressed without entropy or costs. The resulting entropy is
additive, extensive, monotone for every accessible process, and a complete
accessibility criterion when primitive composition labels match. -/
theorem exists_weak_entropy_of_physical_axioms
    (n : Γ → ℕ) (S : ∀ g, SimpleSystem P (n g))
    (hS : ∀ g, F.admitted (S g)) (hnonempty : ∀ g, (S g).domain.Nonempty)
    (hstate : ∀ g, Nonempty (State g)) (chart : ∀ g, State g → (S g).domain)
    (hrepresent : ∀ g z, (S g).represent (chart g z) = CompositeState.mk (.atom ⟨g, z⟩))
    (hM : Reactions.RawNoSinks (Nonreactive.compositionLabel State) P.relation) :
    ∃ (entropy totalEntropy : CompositeState (Σ g, State g) →+ ℝ)
      (B : (Γ →₀ ℝ≥0) →ₗ[ℝ≥0] ℝ),
      (∀ x, totalEntropy x = entropy x + B (Nonreactive.compositionLabel State x)) ∧
      (∀ (r : ℝ≥0) x, entropy (r • x) = (r : ℝ) * entropy x) ∧
      (∀ x y, Nonreactive.compositionLabel State x = Nonreactive.compositionLabel State y →
        (P.relation x y ↔ entropy x ≤ entropy y)) ∧
      (∀ (r : ℝ≥0) x, totalEntropy (r • x) = (r : ℝ) * totalEntropy x) ∧
      (∀ x y, P.relation x y → totalEntropy x ≤ totalEntropy y) ∧
      (∀ x y, Nonreactive.compositionLabel State x = Nonreactive.compositionLabel State y →
        (P.relation x y ↔ totalEntropy x ≤ totalEntropy y)) :=
  F.exists_weak_entropy_of_calibrators F.hasCalibrators_of_axioms n S hS hnonempty
    hstate chart hrepresent hM

end Composites

end ProjectAInos.Thermodynamics.Physical.ThermalFamily
