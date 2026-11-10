module

public import ProjectAInos.Thermodynamics.Cone
public import ProjectAInos.Thermodynamics.Conservation

/-!
# Entropy of stable, exchange-comparable states

The entropy principle follows from the state-level hypotheses, with the
universal conserved quantities specifying the sectors on which it reflects
accessibility.
-/

@[expose] public section

open scoped NNReal

namespace ProjectAInos.Thermodynamics

variable {M : Type*} [AddCommMonoid M] [PartialOrder M] [Module ℝ≥0 M]
  [IsOrderedAddMonoid M] [PosSMulMono ℝ≥0 M]

open Completion

/-- The entropy coordinate on the space of thermodynamic processes. -/
noncomputable def entropyCoordinate (hS : Stability M) (hECH : ExchangeComparison M)
    (e : Completion M) (he : e ∈ processCone M) (hne : e ≠ 0) :
    processSpan M ≃ₗ[ℝ] ℝ :=
  coneEntropyEquiv (processCone M) (processCone_sequentialOrderClosed hS)
    (processCone_salient hS) ((exchangeComparison_iff_coneTotal hS).mp hECH) e he hne

/-- An entropy extension restricts to an additive and extensive state function. -/
noncomputable def EntropyExtension.state {s : processSpan M ≃ₗ[ℝ] ℝ}
    (S : EntropyExtension s) : M →ₗ[ℝ≥0] ℝ :=
  (S.val.restrictScalars ℝ≥0).comp ofLinear

/-- Accessibility is characterized by entropy in each universal conserved sector. -/
theorem EntropyExtension.state_le_iff (hS : Stability M) (hECH : ExchangeComparison M)
    (e : Completion M) (he : e ∈ processCone M) (hne : e ≠ 0)
    (S : EntropyExtension (entropyCoordinate hS hECH e he hne))
    {x y : M} (hsector : (processSpan M).mkQ (of x) = (processSpan M).mkQ (of y)) :
    S.state x ≤ S.state y ↔ x ≤ y := by
  have hxy := (conservation_eq_iff (processSpan M) (of x) (of y)).mp hsector
  exact (S.le_iff (processCone M)
    (coneEntropyEquiv_nonneg_iff (processCone M) (processCone_sequentialOrderClosed hS)
      (processCone_salient hS) ((exchangeComparison_iff_coneTotal hS).mp hECH) e he hne)
    hxy).trans (processCone_reflects hS x y)

/-- Every entropy extension is monotone even when compared states are supplied
without an explicit sector equality. -/
theorem EntropyExtension.state_monotone (hS : Stability M) (hECH : ExchangeComparison M)
    (e : Completion M) (he : e ∈ processCone M) (hne : e ≠ 0)
    (S : EntropyExtension (entropyCoordinate hS hECH e he hne)) : Monotone S.state := by
  intro x y hxy
  have hp := (processCone_reflects hS x y).mpr hxy
  have hw := Submodule.subset_span (R := ℝ) hp
  have hsector := (conservation_eq_iff (processSpan M) (of x) (of y)).mpr hw
  exact (S.state_le_iff hS hECH e he hne hsector).mpr hxy

/-- A strict process fixes an entropy unit and yields a normalized, additive,
extensive entropy which reflects accessibility on matched sectors. -/
theorem exists_normalized_entropy (hS : Stability M) (hECH : ExchangeComparison M)
    {x₀ x₁ : M} (hstrict : x₀ < x₁) :
    ∃ S : M →ₗ[ℝ≥0] ℝ, Monotone S ∧ S x₁ - S x₀ = 1 ∧
      ∀ x y, (processSpan M).mkQ (of x) = (processSpan M).mkQ (of y) →
        (x ≤ y ↔ S x ≤ S y) := by
  let e : Completion M := of x₁ - of x₀
  have he : e ∈ processCone M := ⟨x₀, x₁, hstrict.le, rfl⟩
  have hne : e ≠ 0 := by
    intro hz
    have heq := of_injective hS (sub_eq_zero.mp hz)
    exact hstrict.ne heq.symm
  obtain ⟨S⟩ := entropyExtension_nonempty (entropyCoordinate hS hECH e he hne)
  refine ⟨S.state, S.state_monotone hS hECH e he hne, ?_, ?_⟩
  · change S.val (of x₁) - S.val (of x₀) = 1
    rw [← map_sub]
    change S.val (⟨e, Submodule.subset_span he⟩ : processSpan M) = 1
    rw [S.apply_subtype]
    exact coneEntropyEquiv_generator _ _ _ _ _ _ _
  · intro x y hsector
    exact (S.state_le_iff hS hECH e he hne hsector).symm

end ProjectAInos.Thermodynamics
