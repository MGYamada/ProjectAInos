# Project AInos

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

Concrete models cover nonnegative real states, two independent monotones, lexicographic failure of sequential order closedness, equality-only accessibility, and a conserved amount coordinate. The ideal-gas development proves homogeneity, concavity, and the fixed-amount operational entropy principle. Its composite consistency model identifies the completion with entropy-amount pairs and the conservation quotient with amount. Composition in this model uses the sum of separate-box entropies.

The physical development constructs coherent finite composites and their adiabatic quotient. It proves composition-label conservation for the A1–A6 closure of nonreactive elementary processes. Forward sectors are convex and relatively closed in an open convex finite-dimensional equilibrium domain; irreversibility and unique finite-slope support imply nonempty interior. Positive scaled-copy thermal equilibrium and the zeroth law give invariance under independent positive scaling.

The reaction development defines direct, chained, and catalytic transition costs, descends catalytic costs to the system completion, and selects compatible entropy constants by Hahn–Banach. Its raw-state theorem derives the cost laws from composition, invertible positive scaling, calibrated entropy monotonicity within each label, and actual no-sinks connectivity. It returns an additive, extensive entropy monotone for all accessible transformations. A separate model verifies that unreachable labels retain infinite cost after adding catalysts.

The remaining physical derivation proceeds through the following obligations.

1. **Forward-sector geometry.** Establish a common energy orientation and supporting graphs, prove local uniqueness using the locally Lipschitz pressure field in S2, and use S3 path-connectedness of the relative boundary to obtain nesting and simple-system comparison. Supporting-plane uniqueness identifies kernels of nonzero linear forms; it does not identify their signs.
2. **Physical comparison.** Use thermal joins, the full T2 splitting clauses, T3, and T4 to construct entropy calibrators and comparison on arbitrary scaled products. Assemble the proved finite refinement identities into common-product realizations for equal composition labels, including thermal joins, and discharge the ECH hypothesis of the algebraic entropy theorem. Empty endpoints belong to adiabatic splitting; raw thermal equilibrium concerns positive scaled systems.
3. **Physical calibration for reactions.** Construct compatible additive, extensive entropy across nonreactive product labels from the physical comparison theorem, including the T5 thermal-join compatibility. Supply these calibration premises and the physical no-sinks axiom M to `exists_weak_entropy_from_raw_states`.

The next geometry unit is inheritance of the supporting plane at every relative-boundary point. It uses relative closedness, separation, and transitivity. The subsequent units are a local vertical-interior lemma, extension to vertical half-lines, constancy of the energy orientation, and a differentiable boundary graph with derivative determined by pressure. Local ODE uniqueness along work-coordinate segments then gives boundary reversibility; segment crossing yields comparison. Each implication must be proved before the physical comparison hypothesis can be removed.

Every completed stage must pass the warning-free Lean build, root-import check, and transitive axiom audit. Physical premises remain explicit in theorem statements. [Lean library entry point](ProjectAInos.lean)

[Thermodynamics formalization notes](docs/thermodynamics-notes.md) record the mathematical distinctions and modeling decisions exposed by the proofs, together with their current proof status.

See the [Landau–Lifshitz correspondence](docs/landau-lifshitz.md) for the Mechanics proof targets and reference volumes for the other subjects.

See the [documentation index](docs/README.md) for the Lean API reference build instructions.
