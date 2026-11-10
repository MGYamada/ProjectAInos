# P⊗AI (Project AInos)

*Final answer to Hilbert's sixth problem*

Project AInos aims to formalize the whole of theoretical physics in Lean 4. Its planned proof library will make each theory's assumptions explicit, derive its central results, and formalize how theories relate through special cases and limits.

## Table of Contents

1. **Thermodynamics**
   1. **Algebraic Foundations**
      1. Ordered semimodules and the stability axiom (A6)
      2. Cancellation of spectators
      3. Grothendieck completion and extension of real scalar multiplication
      4. The process cone and order reflection
      5. Sequential order closedness (SC) and the Archimedean property
   2. **Entropy and Conservation**
      1. Exchange comparison (ECH) and totality of the process order
      2. The rank-one representation by a real supremum
      3. Entropy on matched sectors and the Lieb–Yngvason cutoff formula
      4. The conservation quotient, exact sequence, and entropy splittings
   3. **Models and Counterexamples**
      1. The nonnegative real numbers as a rank-one model
      2. Coordinatewise order and failure of ECH
      3. Lexicographic order and failure of SC
   4. **Physical Systems and Extensions**
      1. Physical states, adiabatic equivalence, and the ordered semimodule
      2. Composition sectors and the passage from physical comparison (CH) to ECH
      3. Mixing, chemical reactions, and the weak entropy principle
   5. **The Ideal Gas as an Entropy Model**
      1. The monatomic ideal-gas entropy `S(U, V, N)` on equilibrium states
      2. Extensivity, concavity, and entropy additivity for separate subsystems
      3. Entropy level sets and comparison at fixed particle number
2. **Mechanics**
   1. **Smooth Algebra and Infinitesimal Geometry**
      1. Smooth operations, C∞-rings, and quotients
      2. Dual numbers, tangent functors, derivations, and differential forms
   2. **Variational Mechanics and Conservation Laws**
      1. Jet rings, total derivatives, and null Lagrangians
      2. Action, first variation, and the Euler–Lagrange equations
      3. Galilean symmetry and Noether's theorem for energy, momentum, and angular momentum
   3. **Hamiltonian Mechanics and Reduction**
      1. Poisson brackets, symplectic structures, and cotangent bundles
      2. Legendre transforms, constraints, and Dirac brackets
      3. Canonical transformations, Hamilton–Jacobi theory, and action–angle variables
      4. Momentum maps and reduction at regular and singular values
   4. **Classical Models and Analytic Extensions**
      1. Quadratures, central forces, Kepler motion, and scattering
      2. Oscillations, resonance, rigid bodies, and rotating frames
      3. Averaging and mechanical adiabatic invariants
      4. Dissipation and nonholonomic constraints
3. **Electrodynamics**
4. **Classical Statistical Mechanics**
   1. **Ensembles and Thermodynamic Limits**
      1. Liouville measure, regular energy shells, and conditioning
      2. Microcanonical and canonical ensembles, independent products, and thermal contact
      3. Coarse-graining, thermodynamic limits, and ensemble equivalence
   2. **The Bridge to Thermodynamics**
      1. Derivation of the ideal-gas entropy from phase volume in the thermodynamic limit
      2. Macroscopic adiabatic protocols, stability, and comparison within composition sectors
      3. Identification of statistical entropy with the thermodynamic entropy on matched sectors

The order of subsequent topics is yet to be determined.

## Thermodynamics Proof Development

The Lean library derives spectator cancellation from A6, constructs the real Grothendieck completion and its process cone, and proves order reflection and sequential order closedness. Under exchange comparison and a nonzero process direction, the real-cut construction gives an entropy coordinate. Linear extension then gives the entropy principle on matched conservation sectors, the relative cutoff formula, and the classification of entropy extensions by conserved linear quantities.

Concrete models cover nonnegative real states, two independent monotones, lexicographic failure of sequential order closedness, equality-only accessibility, and a conserved amount coordinate. The ideal-gas development proves homogeneity, concavity, and the fixed-amount operational entropy principle. Its composite algebraic consistency model identifies the completion with entropy-amount pairs and the conservation quotient with amount. Composition in this model uses the sum of separate-box entropies; this construction does not supply a geometric simple system or thermal family.

The [reservoir model](ProjectAInos/Thermodynamics/ReservoirModel.lean) supplies a nonempty family satisfying the full simple-system and thermal interfaces, closed under positive scaling and thermal joins. Entropy equals energy and pressure is zero, so it exercises the universal-isotherm case. The [join assumption audit](docs/thermodynamics-join-audit.md) distinguishes contact and splitting from the geometric regularity required of joined systems.

The physical development constructs coherent finite composites and their adiabatic quotient. It proves composition-label conservation for the A1–A6 closure of nonreactive elementary processes and constructs common scaled products for states with equal composition labels. Forward sectors are convex and relatively closed in an open convex finite-dimensional equilibrium domain. Irreversibility and unique finite-slope support imply nonempty interior; the supporting plane is inherited at every relative-boundary point. Energy orientation is constant throughout each simple system, giving the fixed-work accessibility criterion. The boundary is a differentiable graph whose derivative is the negative pressure form. Locally Lipschitz pressure gives local uniqueness of these graphs, and boundary connectedness propagates reversibility. These results establish simple-system comparison, strict nesting of distinct forward sectors, and openness of strict reference strips. Energy reflection handles the opposite orientation without changing the physical premises.

Typed thermal families connect actual scaled coordinate domains, thermal joins, and the positive scaled-copy clause of T2. Thermal contact fixes a common energy orientation across systems, and the zeroth law gives independent scaling invariance. Simple-system comparison and transversality establish local mixture intervals; connectedness joins their affine reference lines. These results give single-system product comparison and normalized concave continuous entropy. Thermal equilibrium between two copies is equivalent to fixed-total-energy entropy maximization, or intersection of their supporting-slope intervals. This criterion requires no extra differentiability assumption on entropy.

The location-of-isotherms dichotomy and crossed-calibrator existence are proved, including the universal-isotherm case. A concrete splitting and mixing cycle establishes thermal equilibrium between a joined state and each component. Pairwise calibrators align all simple-system reference directions, giving comparison in every finite scaled product. Canonical coordinate atoms provide the finite composite presentation and fixed-composition labels. Common-product realization then gives ECH for nonreactive accessibility. The final physical entropy endpoints take the explicit geometric and thermal premises, with no CH, ECH, or calibrator-existence assumption.

The reaction development defines direct, chained, and catalytic transition costs, proves their positive homogeneity, and selects compatible entropy constants by Hahn–Banach. The physical entropy theorem supplies the required calibrated monotonicity within each composition label. Absence of sinks is expressed using actual transitions, independently of entropy or costs. The resulting total entropy is additive, extensive, monotone for all accessible transformations, and characterizes accessibility when composition labels match. Infinite costs for unreachable labels remain allowed, including after adding catalysts.

The current physical endpoints use A1–A7, S1–S3 and T1–T4, with M added for reactions. Every admitted primitive simple system satisfies transversality T4; no extra T5 assumption is needed for this scope. Extending the theory to systems without T4, or proving temperature regularity, belongs to subsequent work. The ideal-gas phase-volume derivation remains in the statistical-mechanics stage of the research plan.

The public physical endpoints are in [PhysicalEntropyPrinciple](ProjectAInos/Thermodynamics/PhysicalEntropyPrinciple.lean); [AtomicSystems](ProjectAInos/Thermodynamics/AtomicSystems.lean) specializes them to canonical coordinate atoms. The [mathematical guide](docs/thermodynamics.md) presents the algebraic theory, physical comparison, reactions, and models with proof links. The [implementation checklist](docs/thermodynamics-status.md) maps the eight planned stages to their proof modules and scope.

Every completed stage must pass the warning-free Lean build, root-import check, and transitive axiom audit. Physical premises remain explicit in theorem statements. [Lean library entry point](ProjectAInos.lean)

[Thermodynamics formalization notes](docs/thermodynamics-notes.md) record the mathematical distinctions and modeling decisions exposed by the proofs, together with their current proof status.

See the [Landau–Lifshitz correspondence](docs/landau-lifshitz.md) for the Mechanics proof targets and reference volumes for the other subjects.

See the [documentation index](docs/README.md) for the Lean API reference build instructions.

## License

Copyright 2026 Masahiko G. Yamada.

Licensed under the [Apache License, Version 2.0](LICENSE). See [NOTICE](NOTICE)
for the copyright notice.
