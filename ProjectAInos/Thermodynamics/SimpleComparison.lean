module

public import ProjectAInos.Thermodynamics.BoundaryReversibility
public import ProjectAInos.Thermodynamics.AdiabatUniqueness
public import ProjectAInos.Thermodynamics.EnergyReflection
public import ProjectAInos.Thermodynamics.ThermalFamily

/-!
# Comparison for simple systems

Local uniqueness of adiabat graphs, boundary connectedness, and convex segment
crossing yield the comparison hypothesis from the simple-system premises.
Energy-coordinate reflection discharges the orientation convention.
-/

@[expose] public section

open Set Filter
open scoped NNReal Topology

namespace ProjectAInos.Thermodynamics.Physical.SimpleSystem

variable {X : Type*} [AddCommMonoid X] [DistribMulAction ℝ≥0 X]
    {P : Accessibility X} {n : ℕ}

/-- LY 3.6 under the positive coordinate convention. The local graph equality
premise of the topological propagation lemma is discharged by the ODE proof. -/
theorem boundary_reversibility_of_positive (S : SimpleSystem P n)
    (hpositive : ∀ z ∈ S.domain, S.Positive z)
    {x y : SimpleCoordinates n} (hx : x ∈ S.domain) (hy : y ∈ S.boundary x) :
    P.relation (S.represent y) (S.represent x) := by
  apply S.boundary_reversibility_of_local_agreement hpositive hx hy
  intro v hvx hvy heq
  exact S.boundaryEnergy_eventually_eq hpositive hx hy.1 hvx hvy heq

/-- LY 3.6 without a preferred orientation of the energy coordinate. -/
theorem boundary_reversibility (S : SimpleSystem P n)
    {x y : SimpleCoordinates n} (hx : x ∈ S.domain) (hy : y ∈ S.boundary x) :
    P.relation (S.represent y) (S.represent x) := by
  obtain hp | hp := S.positive_or_reflected_positive
  · exact S.boundary_reversibility_of_positive hp hx hy
  · have hxr : energyReflection n x ∈ S.reflected.domain := by simpa using hx
    have hyr : energyReflection n y ∈ S.reflected.boundary (energyReflection n x) := by
      rw [S.reflected_boundary]
      simpa only [mem_preimage, energyReflection_involutive] using hy
    simpa using S.reflected.boundary_reversibility_of_positive hp hxr hyr

/-- LY 3.7, comparison of any two equilibrium states of a simple system. -/
theorem comparison_of_mem (S : SimpleSystem P n)
    {x y : SimpleCoordinates n} (hx : x ∈ S.domain) (hy : y ∈ S.domain) :
    P.relation (S.represent x) (S.represent y) ∨
      P.relation (S.represent y) (S.represent x) :=
  S.comparison_of_boundary_reversibility (fun _ hx _ hy => S.boundary_reversibility hx hy) hx hy

/-- Subtype form of the comparison hypothesis, ready for thermal-family use. -/
theorem comparison (S : SimpleSystem P n) (x y : S.domain) :
    P.relation (S.represent x) (S.represent y) ∨
      P.relation (S.represent y) (S.represent x) :=
  S.comparison_of_mem x.property y.property

/-- Boundary points are precisely the states adiabatically equivalent to the
anchor. -/
theorem mem_boundary_iff_equivalent (S : SimpleSystem P n)
    {x y : SimpleCoordinates n} (hx : x ∈ S.domain) (hy : y ∈ S.domain) :
    y ∈ S.boundary x ↔
      P.relation (S.represent x) (S.represent y) ∧
        P.relation (S.represent y) (S.represent x) := by
  constructor
  · intro hb
    exact ⟨(S.boundary_subset_sector hx hb).2, S.boundary_reversibility hx hb⟩
  · intro heq
    have hsectors := (S.sector_eq_iff_equivalent hx hy).mpr heq
    have hmem := S.mem_boundary_self hy
    change y ∈ S.domain ∩ frontier (S.sector y) at hmem
    change y ∈ S.domain ∩ frontier (S.sector x)
    rwa [hsectors]

/-- Strict accessibility is exactly membership in the forward interior. -/
theorem strict_iff_mem_interior (S : SimpleSystem P n)
    {x y : SimpleCoordinates n} (hx : x ∈ S.domain) (hy : y ∈ S.domain) :
    (P.relation (S.represent x) (S.represent y) ∧
      ¬ P.relation (S.represent y) (S.represent x)) ↔ y ∈ interior (S.sector x) :=
  S.strict_iff_interior_of_boundary_reversibility
    (fun _ hx _ hy => S.boundary_reversibility hx hy) hx hy

/-- The strict nesting alternative in LY 3.7. -/
theorem strict_iff_sector_subset_interior (S : SimpleSystem P n)
    {x y : SimpleCoordinates n} (hx : x ∈ S.domain) (hy : y ∈ S.domain) :
    (P.relation (S.represent x) (S.represent y) ∧
      ¬ P.relation (S.represent y) (S.represent x)) ↔
      S.sector y ⊆ interior (S.sector x) :=
  S.strict_iff_sector_subset_interior_of_boundary_reversibility
    (fun _ hx _ hy => S.boundary_reversibility hx hy) hx hy

/-- Every pair of forward sectors is equal or strictly nested. The preceding
iff theorems identify these as mutually exclusive accessibility alternatives. -/
theorem sectors_nested (S : SimpleSystem P n)
    {x y : SimpleCoordinates n} (hx : x ∈ S.domain) (hy : y ∈ S.domain) :
    S.sector x = S.sector y ∨ S.sector y ⊆ interior (S.sector x) ∨
      S.sector x ⊆ interior (S.sector y) := by
  obtain hxy | hyx := S.comparison_of_mem hx hy
  · by_cases hyx : P.relation (S.represent y) (S.represent x)
    · exact Or.inl ((S.sector_eq_iff_equivalent hx hy).mpr ⟨hxy, hyx⟩)
    · exact Or.inr (Or.inl ((S.strict_iff_sector_subset_interior hx hy).mp ⟨hxy, hyx⟩))
  · by_cases hxy : P.relation (S.represent x) (S.represent y)
    · exact Or.inl ((S.sector_eq_iff_equivalent hx hy).mpr ⟨hxy, hyx⟩)
    · exact Or.inr (Or.inr ((S.strict_iff_sector_subset_interior hy hx).mp ⟨hyx, hxy⟩))

/-- Strict reference strips are open, with no comparison or orientation premise
left over. This is the interface used by the thermal transversality argument. -/
theorem strict_strips_open (S : SimpleSystem P n) :
    ∀ a b : S.domain, IsOpen {y : S.domain |
      (P.relation (S.represent a) (S.represent y) ∧
        ¬ P.relation (S.represent y) (S.represent a)) ∧
      (P.relation (S.represent y) (S.represent b) ∧
        ¬ P.relation (S.represent b) (S.represent y))} :=
  S.strict_strips_open_of_boundary_reversibility
    (fun _ hx _ hy => S.boundary_reversibility hx hy)

end ProjectAInos.Thermodynamics.Physical.SimpleSystem

namespace ProjectAInos.Thermodynamics.Physical.ThermalFamily

variable {X : Type*} [AddCommMonoid X] [DistribMulAction ℝ≥0 X]
    {P : Accessibility X}

/-- Every admitted simple system, including every thermal join, satisfies
comparison by its geometric axioms. -/
theorem simpleComparison (F : ThermalFamily P) : F.SimpleComparison := by
  intro n S _
  exact S.comparison

/-- Thermal transversality and joining produce local mixture intervals after
all geometric comparison and openness obligations have been discharged. -/
theorem localMixtureIntervals_of_axioms (F : ThermalFamily P)
    {n : ℕ} (S : SimpleSystem P n) (hS : F.admitted S) : S.LocalMixtureIntervals :=
  F.localMixtureIntervals F.simpleComparison S hS S.strict_strips_open

end ProjectAInos.Thermodynamics.Physical.ThermalFamily
