import ProjectAInos

open ProjectAInos.Thermodynamics
open ProjectAInos.Thermodynamics.Physical
open scoped NNReal

section LogarithmicThermal

open LogarithmicThermal

example : family.Nontrivial := family_nontrivial

example : family.admitted (join 1 1 1 1 one_pos one_pos).system ∧
    ∃ x y : (join 1 1 1 1 one_pos one_pos).system.domain,
      ¬ family.thermal ((join 1 1 1 1 one_pos one_pos).system.represent x)
        ((join 1 1 1 1 one_pos one_pos).system.represent y) :=
  joined_nonthermal

example (n m : ℕ) (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
    (x : (system n r hr).domain) (y : (system m s hs).domain) :
    (contact n m r s hr hs).Equilibrium x y ↔ x.val.1 / r = y.val.1 / s :=
  equilibrium_iff n m r s hr hs x y

end LogarithmicThermal

#check Nonreactive.Generated.eval_le
#check AtomicDomains.exchangeComparison_nonreactive
#check AtomicDomains.exchangeComparison_atomicOnly
#check AtomicReservoir.normal_form
#check AtomicReservoir.relation_iff

example : (AtomicReservoir.system 0 1 (by norm_num)).represent ≠
    AtomicReservoir.domains.represent () := AtomicReservoir.canonical_represent_ne

example : AtomicReservoir.family.Nontrivial := AtomicReservoir.family_nontrivial
example : ExchangeComparison AtomicReservoir.accessibility.StateSpace :=
  AtomicReservoir.exchangeComparison

example : ¬ AtomicReservoir.atomicHeating.relation
    ((1/2 : ℝ≥0) • AtomicReservoir.atom AtomicReservoir.energyOne +
      (1/2 : ℝ≥0) • AtomicReservoir.atom AtomicReservoir.energyThree)
    (AtomicReservoir.atom AtomicReservoir.energyTwo) := AtomicReservoir.atomicOnly_mixing_impossible

#check AtomicReservoir.mixing_example
#check AtomicReservoir.mixing_raw_distinct
#check AtomicReservoir.heating_irreversible

section Reacting

open ReactingReservoir

example : Reactions.RawNoSinks domains.label accessibility.relation := noSinks

example :
    Reactions.calibratedDirectCost domains.label energy accessibility.relation
      (domains.label (atom false unitEnergy)) (domains.label (atom true unitEnergy)) = 0 :=
  unitConversion.2.2

example : ∃ (S total : Raw →+ ℝ) (B : Composition →ₗ[ℝ≥0] ℝ),
    WeakEntropyPrinciple domains.label accessibility.relation S total B :=
  exists_weak_entropy

example : ∃ total : Raw →+ ℝ, total (atom false unitEnergy) ≤ total (atom true unitEnergy) ∧
    CalibratedEntropyPrinciple domains.label accessibility.relation total :=
  exists_monotone_conversion

end Reacting
