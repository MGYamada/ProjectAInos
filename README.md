# P⊗AI (Project Ainos)

*Final answer to Hilbert's sixth problem*

P⊗AI is pronounced `poai`.

**P⊗AI (Project Ainos)** is a *proof of artificial intelligence* project that seeks to demonstrate AI's capacity for rigorous scientific reasoning through machine-checked proofs.
Taking Hilbert's sixth problem as its starting point, it aims to formalize the whole of theoretical physics in Lean 4.
Its planned proof library will make each theory's assumptions explicit, derive its central results, and formalize how theories relate through special cases and limits.

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
   1. **Configuration Spaces and Infinitesimal Geometry**
      1. Configuration spaces over the shared smooth-geometry foundation
      2. Tangent and cotangent geometry for mechanical systems
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
3. **Special Relativity**
   1. **Minkowski Geometry and Relativistic Kinematics**
      1. Explicit Lorentz signatures, invariant quadratic form, and metric duality
      2. Affine spacetime, causal cones, and Lorentz and Poincaré groups
      3. Observers, rest spaces, boosts, velocity transformations, and rapidity
      4. Proper time of timelike curves and normalized four-velocity
      5. Flat differential forms, exterior derivatives, wedge products, and pullbacks
      6. Oriented Lorentzian Hodge duality and observer decomposition of two-forms
   2. **Dynamics of Relativistic Particles**
      1. Free-particle action, energy, and momentum
      2. Conservation laws and relativistic collision kinematics
4. **Electrodynamics**
   1. **Charged Particles and Electromagnetic Fields**
      1. Electromagnetic potentials, gauge symmetry, and the field tensor
      2. Charged-particle action and Lorentz-force dynamics
   2. **Maxwell Theory and Conservation Laws**
      1. Field action, Maxwell equations, and charge conservation
      2. Stress-energy and energy-momentum exchange between fields and matter
   3. **Static Fields, Waves, and Optics**
      1. Electrostatics and magnetostatics
      2. Vacuum wave propagation, polarization, and geometric optics
   4. **Moving Sources and Radiation**
      1. Retarded fields of moving charges
      2. Radiation flux, radiated power, and radiation-reaction models
5. **General Relativity**
   1. **Geometry and Motion in Gravitational Fields**
      1. Lorentzian metrics, covariant derivatives, and curvature
      2. Geodesic motion and the weak-field limit
   2. **Einstein Dynamics and Gravitating Systems**
      1. Gravitational action, Einstein equations, and energy-momentum
      2. Fields of gravitating bodies and spherically symmetric solutions
   3. **Gravitational Radiation**
      1. Linearized gravity, wave propagation, and gravitational-wave emission
   4. **Relativistic Cosmology**
      1. Cosmological models, their evolution, and singularities
6. **Classical Statistical Mechanics**
   1. **Ensembles and Thermodynamic Limits**
      1. Liouville measure, regular energy shells, and conditioning
      2. Microcanonical and canonical ensembles, independent products, and thermal contact
      3. Coarse-graining, thermodynamic limits, and ensemble equivalence
   2. **The Bridge to Thermodynamics**
      1. Derivation of the ideal-gas entropy from phase volume in the thermodynamic limit
      2. Macroscopic adiabatic protocols, stability, and comparison within composition sectors
      3. Identification of statistical entropy with the thermodynamic entropy on matched sectors

Topics 3, 4, and 5 follow Chapters I–II, III–IX, and X–XIV, respectively, of
Landau–Lifshitz Volume 2, *The Classical Theory of Fields*. See the
[chapter correspondence](docs/landau-lifshitz.md#special-relativity).
The C∞ research trilogy gives section-level targets, mathematical assumptions,
Lean architecture, and the distinction between proved results and future work:
[Special Relativity, §§1–14](docs/cinfty-special-relativity.md),
[Electrodynamics, §§15–80](docs/cinfty-electrodynamics.md), and
[General Relativity, §§81–119](docs/cinfty-general-relativity.md).
The plans carry forward [issue #8](https://github.com/MGYamada/ProjectAinos/issues/8)
and identify the next proofs for free relativistic particles, the Maxwell
action with a prescribed current, and the differential Bianchi identity.
The order of topics after 6 is yet to be determined.

## Shared smooth algebra and geometry

The smooth algebra, smooth geometry, and variational libraries provide
the mathematical foundations for mechanics, special relativity,
electrodynamics, and general relativity. The foundation’s implementation
plan and the Lean results for these subjects are documented in
[Shared smooth algebra and geometry](docs/shared-smooth-algebra-and-geometry.md).

See the [proof development record](docs/proof-development.md) for the history of the Lean formalization.

## Quantum prototypes

The [scalar smeared-field prototype](docs/quantum-field-theory-prototype.md)
formalizes a common dense domain, operator closability, and positivity of
finite vacuum words for the prospective QFT program in
[#46](https://github.com/MGYamada/ProjectAinos/issues/46). Its locality
predicate has causality-sensitive regressions: bump tests with explicit
spacelike and timelike supports, and a two-point field with noncommuting
insertions that is local exactly when its two points are not spacelike to
each other. These are regression models, not Wightman fields.
The [qubit comparison prototype](docs/quantum-mechanics-prototype.md) is a
provisional finite-dimensional study for
[#45](https://github.com/MGYamada/ProjectAinos/issues/45).

The documentation index links to the guides and the build instructions for the HTML handbook and Lean API reference. [Documentation index](docs/README.md)

## License

Copyright 2026 Masahiko G. Yamada.

Licensed under the [Apache License, Version 2.0](LICENSE). See [NOTICE](NOTICE)
for the copyright notice.
