module

public import ProjectAInos.Thermodynamics.ComparableCuts
public import ProjectAInos.Thermodynamics.Cone

/-!
# Mixture comparison and reference-state representation

Within a comparable reference interval, stability turns comparison with all
mixtures into equality with one mixture. This uses no exchange-comparison
hypothesis on unrelated states.
-/

@[expose] public section

open Set
open scoped NNReal

namespace ProjectAInos.Thermodynamics

variable {M : Type*} [AddCommMonoid M] [PartialOrder M] [Module ℝ≥0 M]
    [IsOrderedAddMonoid M] [PosSMulMono ℝ≥0 M]

/-- A state between strict references has a reference coordinate if it
is comparable with every nonnegative mixture of those references. -/
theorem exists_reference_coordinate_of_comparable (hS : Stability M)
    {x₀ x₁ x : M} (hstrict : x₀ < x₁) (hlower : x₀ ≤ x) (hupper : x ≤ x₁)
    (hcompare : ∀ t : ℝ≥0, t ≤ 1 →
      (1 - t) • x₀ + t • x₁ ≤ x ∨ x ≤ (1 - t) • x₀ + t • x₁) :
    ∃ r ∈ Icc (0 : ℝ) 1,
      Completion.of x - Completion.of x₀ =
        r • (Completion.of x₁ - Completion.of x₀) := by
  let e := Completion.of x₁ - Completion.of x₀
  let w := Completion.of x - Completion.of x₀
  have he : e ∈ processCone M := (processCone_reflects hS _ _).mpr hstrict.le
  have hne : e ≠ 0 := by
    intro h
    exact hstrict.ne ((Completion.of_injective hS) (sub_eq_zero.mp h)).symm
  have hw : w ∈ processCone M := (processCone_reflects hS _ _).mpr hlower
  have hew : e - w ∈ processCone M := by
    simpa [e, w] using (processCone_reflects hS _ _).mpr hupper
  apply exists_smul_eq_of_comparable_interval (processCone M)
    (processCone_sequentialOrderClosed hS) (processCone_salient hS) he hne hw hew
  intro r hr
  let t : ℝ≥0 := ⟨r, hr.1⟩
  have ht : t ≤ 1 := hr.2
  have hm : Completion.of ((1 - t) • x₀ + t • x₁) =
      Completion.of x₀ + r • e := by
    simp only [map_add, Completion.of_nnreal_smul, NNReal.smul_def,
      NNReal.coe_sub ht, NNReal.coe_one]
    change (1 - r) • Completion.of x₀ + r • Completion.of x₁ = _
    dsimp [e]
    module
  rcases hcompare t ht with h | h
  · left
    have h' := (processCone_reflects hS _ _).mpr h
    rw [hm] at h'
    simpa [w, sub_add_eq_sub_sub] using h'
  · right
    have h' := (processCone_reflects hS _ _).mpr h
    rw [hm] at h'
    convert h' using 1
    dsimp [w]
    abel

/-- The completed-space coordinate is realized by an actual nonnegative
mixture, after passing to states with antisymmetric accessibility. -/
theorem exists_reference_mixture_of_comparable (hS : Stability M)
    {x₀ x₁ x : M} (hstrict : x₀ < x₁) (hlower : x₀ ≤ x) (hupper : x ≤ x₁)
    (hcompare : ∀ t : ℝ≥0, t ≤ 1 →
      (1 - t) • x₀ + t • x₁ ≤ x ∨ x ≤ (1 - t) • x₀ + t • x₁) :
    ∃ t : ℝ≥0, t ≤ 1 ∧ x = (1 - t) • x₀ + t • x₁ := by
  obtain ⟨r, hr, heq⟩ :=
    exists_reference_coordinate_of_comparable hS hstrict hlower hupper hcompare
  let t : ℝ≥0 := ⟨r, hr.1⟩
  have ht : t ≤ 1 := hr.2
  refine ⟨t, ht, Completion.of_injective hS ?_⟩
  simp only [map_add, Completion.of_nnreal_smul, NNReal.smul_def,
    NNReal.coe_sub ht, NNReal.coe_one]
  change Completion.of x = (1 - r) • Completion.of x₀ + r • Completion.of x₁
  have h := eq_add_of_sub_eq heq
  rw [h]
  module

end ProjectAInos.Thermodynamics
