# Thermodynamics Implementation Checklist

This checklist maps the eight-stage implementation plan to machine-checked
results. The [mathematical guide](thermodynamics.md) gives the statements,
proof explanations, and the L01–L12 map from the former specification.
The research outline remains in the [README](../README.md), and
mathematical distinctions exposed by the proofs are recorded in the
[formalization notes](thermodynamics-notes.md).

| Stage | Implemented result | Main proof modules |
| --- | --- | --- |
| 1. Stability and cancellation | A6 implies order cancellation and equality cancellation; the ordered cancellation instance is constructed from that proof | [Cancellation](../ProjectAInos/Thermodynamics/Cancellation.lean) |
| 2. Completion and the process cone | The Grothendieck completion carries a real module structure extending nonnegative scaling, with uniqueness and a universal linear map; the state embedding is injective and reflects process order; the cone is salient | [Completion](../ProjectAInos/Thermodynamics/Completion.lean), [Cone](../ProjectAInos/Thermodynamics/Cone.lean) |
| 3. Comparison and one-dimensional representation | A6 gives sequential order closedness and the Archimedean property; ECH is equivalent to totality on the process span; real cuts give the normalized coordinate, its uniqueness up to a positive factor, and the zero-cone case | [Comparison](../ProjectAInos/Thermodynamics/Comparison.lean), [Representation](../ProjectAInos/Thermodynamics/Representation.lean), [Cone](../ProjectAInos/Thermodynamics/Cone.lean) |
| 4. Entropy, cutoff, conservation | Additive extensive monotone entropy, the matched-sector criterion, the relative cutoff for every real parameter, the exact conservation sequence, and classification of entropy extensions; the conservation quotient needs no ECH | [Entropy](../ProjectAInos/Thermodynamics/Entropy.lean), [Cutoff](../ProjectAInos/Thermodynamics/Cutoff.lean), [Conservation](../ProjectAInos/Thermodynamics/Conservation.lean) |
| 5. Models and counterexamples | Nonnegative reals, the two-coordinate failure of ECH, lexicographic failure of sequential closedness, equality-only accessibility, and a conserved amount coordinate | [Models](../ProjectAInos/Thermodynamics/Models.lean), [ConeModels](../ProjectAInos/Thermodynamics/ConeModels.lean), [DegenerateModel](../ProjectAInos/Thermodynamics/DegenerateModel.lean), [ModelConnections](../ProjectAInos/Thermodynamics/ModelConnections.lean) |
| 6. Physical comparison | Finite composites and both quotients, stability on adiabatic classes, simple-system comparison, thermal scaling and orientation, isotherm dichotomy, calibrators, arbitrary finite-product CH, nonreactive composition conservation, common products and ECH | [Physical](../ProjectAInos/Thermodynamics/Physical.lean), [SimpleComparison](../ProjectAInos/Thermodynamics/SimpleComparison.lean), [HasCalibratorsOfAxioms](../ProjectAInos/Thermodynamics/HasCalibratorsOfAxioms.lean), [PhysicalEntropyPrinciple](../ProjectAInos/Thermodynamics/PhysicalEntropyPrinciple.lean), [AtomicSystems](../ProjectAInos/Thermodynamics/AtomicSystems.lean) |
| 7. Mixtures and reactions | Extended-real direct, chain and catalytic costs; positive homogeneity, composition subadditivity and catalytic invariance; actual no-sinks connectivity; finite-cost subspace and Hahn–Banach constants; weak entropy from physical calibration; stoichiometric conservation and a water-reaction example | [Reactions](../ProjectAInos/Thermodynamics/Reactions.lean), [ReactionCalibration](../ProjectAInos/Thermodynamics/ReactionCalibration.lean), [PhysicalEntropyPrinciple](../ProjectAInos/Thermodynamics/PhysicalEntropyPrinciple.lean), [Stoichiometry](../ProjectAInos/Thermodynamics/Stoichiometry.lean) |
| 8. Ideal gas | The logarithmic formula, extensivity, full concavity and fixed-amount strict concavity, separate-box additivity, entropy level curves, the reversible-curve/free-expansion operational criterion, and the composite entropy–amount model with computed completion and conservation quotient | [IdealGas](../ProjectAInos/Thermodynamics/IdealGas.lean), [IdealGasModel](../ProjectAInos/Thermodynamics/IdealGasModel.lean) |

## Public physical endpoints

- `ThermalFamily.product_comparison` derives finite-product CH. It does not take CH, ECH, or calibrator existence as a premise.
- `ThermalFamily.exchangeComparison_of_physical_axioms` derives ECH when accessibility preserves primitive composition labels. `AtomicDomains.exchangeComparison_nonreactive` accepts composite generators and their label-preservation proof; conservation for the full closure and physical ECH are derived. `AtomicReservoir.exchangeComparison` instantiates it with a nonempty canonical-atomic thermal family. The old restricted endpoint is named `exchangeComparison_atomicOnly`.
- `ThermalFamily.exists_entropy_of_physical_axioms` gives an additive extensive entropy and the complete accessibility criterion within each composition label.
- `ThermalFamily.exists_weak_entropy_of_physical_axioms` adds `RawNoSinks` and returns the corrected entropy, monotone for all accessible processes and still a complete criterion within matching labels.
- `AtomicDomains` constructs actual coordinate atoms, their finite composites, and their labels before an accessibility relation is supplied. Its entropy endpoints derive the charts and full-domain label laws from the coordinate presentation.
- `ThermalFamily.Nontrivial` asserts existence of a represented member state. [ReservoirModel](../ProjectAInos/Thermodynamics/ReservoirModel.lean) constructs a nontrivial smooth family with positive scaling and thermal joins, and proves its `family_nontrivial` witness. The thermal relation is universal in this example.

The physical premises remain explicit in `Accessibility`, `SimpleSystem`,
`ThermalFamily`, and `RawNoSinks`. All primitive systems in these endpoints
satisfy transversality T4, so T1–T4 suffice; adding T5 is unnecessary for this
scope. Entropy extension to systems without T4 and temperature regularity are
subsequent topics. The ideal-gas composite construction is an algebraic
consistency model for stability and ECH, not a model of the full geometric and
thermal-family premises; a microscopic phase-volume derivation belongs to README
item 4, statistical mechanics.

The [join assumption audit](thermodynamics-join-audit.md) lists the geometric
premises required of every admitted join. Contact and splitting alone do not
imply all those regularity properties.

## Boundary cases

The library covers zero scalar and empty product cases, empty atomic families,
degenerate process cones, unmatched conserved sectors, and signed cutoff
parameters outside `[0,1]`. Thermal equilibrium with scaled copies requires
positive scales. Unreachable reaction costs remain `+∞`; negative infinite
costs are excluded from the final physical cost laws by cycles and no sinks,
not by assuming every transition is reachable.

## Verification

The required checks are:

```sh
lake build --wfail ProjectAInos
lake exe mk_all --check --lib ProjectAInos
```

The CI also audits transitive axiom dependencies of project declarations. The
only permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.
Every module is exported by [ProjectAInos.lean](../ProjectAInos.lean).
