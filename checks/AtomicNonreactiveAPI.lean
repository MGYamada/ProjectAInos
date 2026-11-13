import ProjectAInos

open ProjectAInos.Thermodynamics
open ProjectAInos.Thermodynamics.Physical
open scoped NNReal

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
