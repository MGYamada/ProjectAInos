# P⊗AI (Project Ainos)

*Final answer to Hilbert's sixth problem*

P⊗AI is pronounced `poai`.

**P⊗AI (Project Ainos)** is a *proof of artificial intelligence* project that seeks to demonstrate AI's capacity for rigorous scientific reasoning through machine-checked proofs.
Taking Hilbert's sixth problem as its starting point, it aims to formalize the whole of theoretical physics in Lean 4.
Its planned proof library will make each theory's assumptions explicit, derive its central results, and formalize how theories relate through special cases and limits.

## Table of Contents

1. **Thermodynamics (Lieb-Yngvason 2.0)**
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
2. **Mechanics (Landau-Lifshitz 2.0)**
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
3. **Special Relativity (Landau-Lifshitz 2.0)**
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
4. **Electrodynamics (Landau-Lifshitz 2.0)**
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
5. **General Relativity (Landau-Lifshitz 2.0)**
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
6. **Classical Statistical Mechanics (Goldstein–Lebowitz 2.0)**
   1. **Hamiltonian Phase Volume and Microcanonical Conditioning**
      1. Hamiltonian phase spaces, Liouville volume, and measure-preserving flows
      2. Normalized microcanonical measures on finite energy windows and their invariance
      3. Conserved quantities, composition sectors, and extensions to regular exact-energy shells
   2. **Macrostates, Coarse-Graining, and Boltzmann Entropy**
      1. Measurable macroscopic observables and macroregions
      2. Boltzmann entropy from macroregion volume, reference-volume normalization, and additivity for independent products
      3. Gibbs entropy of phase-space distributions and comparison with Boltzmann entropy in and out of equilibrium
   3. **Equilibrium Typicality and Concentration of Measure**
      1. Phase-volume dominance of equilibrium macroregions and finite-volume concentration bounds
      2. Particle occupancy in a divided box as a quantitative model
      3. Additional conserved quantities, disconnected invariant components, and phase coexistence
   4. **Dynamics, Typical Histories, and Conditional H-Theorems**
      1. Finite-time equilibrium residence bounds for microcanonical initial states
      2. Relaxation from low-entropy macroregions and entropy bounds under approximate macroscopic autonomy
      3. Fine-grained Gibbs entropy invariance, time reversal, recurrence, and nonergodic counterexamples
   5. **Ensembles, Thermal Contact, and Thermodynamic Limits**
      1. Microcanonical and canonical ensembles, subsystem marginals, weak coupling, and thermal contact
      2. Ensemble equivalence under explicit hypotheses, finite-size estimates, and thermodynamic limits
      3. Interacting systems and phase transitions
   6. **The Bridge to Axiomatic Thermodynamics**
      1. Ideal-gas entropy from phase volume, including particle-number and normalization conventions
      2. Extensivity, additivity, scaling, and stability in the thermodynamic limit
      3. Macroscopic adiabatic protocols and order comparison on matched equilibrium composition sectors
      4. Statistical and thermodynamic entropy correspondence, with a positive entropy scale and a linear calibration in the conserved quantities

The “2.0” labels name Project Ainos's research programs. Topic 1 draws on
E. H. Lieb and J. Yngvason, *The Physics and Mathematics of the Second Law of
Thermodynamics*, *Physics Reports* 310(1) (1999), pp. 1–96.
[Published article](https://doi.org/10.1016/S0370-1573(98)00082-9) ·
[Open preprint](https://arxiv.org/abs/cond-mat/9708200)

Topic 2 follows L. D. Landau and E. M. Lifshitz's *Mechanics*, Volume 1 of the
*Course of Theoretical Physics*, 3rd English edition (1976).
[Publisher's catalogue](https://shop.elsevier.com/books/mechanics/landau/978-0-08-050347-9)

Topics 3, 4, and 5 follow Chapters I–II, III–IX, and X–XIV, respectively, of
Landau and Lifshitz's *The Classical Theory of Fields*, Volume 2 of the
*Course of Theoretical Physics*, 4th revised English edition.
[Publisher's catalogue](https://shop.elsevier.com/books/the-classical-theory-of-fields/landau/978-0-08-025072-4) ·
[Chapter correspondence](docs/landau-lifshitz.md#special-relativity)

The C∞ research trilogy gives section-level targets, mathematical assumptions,
Lean architecture, and the distinction between proved results and future work:
[Special Relativity, §§1–14](docs/cinfty-special-relativity.md),
[Electrodynamics, §§15–80](docs/cinfty-electrodynamics.md), and
[General Relativity, §§81–119](docs/cinfty-general-relativity.md).
The plans carry forward [issue #8](https://github.com/MGYamada/ProjectAinos/issues/8)
and identify the next proofs for free relativistic particles, the Maxwell
action with a prescribed current, and the differential Bianchi identity.
Each plan has a ledger with one status for each section;
[issue #135](https://github.com/MGYamada/ProjectAinos/issues/135) tracks the proofs.
For the free relativistic particle the library proves the coordinate-time
Hamiltonian `√(m² + Σ pᵢ²)` with its trajectories and its flow, the Poincaré
algebra of the orbital charges with its contraction to the Galilei algebra,
and the reduction of the future sheet of the mass shell to the phase space of
the initial data.
[Guide](docs/special-relativity.md#relativistic-particle-mechanics-the-algebraic-layer)
It also proves that the inertial clock measures the greatest proper time, that
the stationary curves of the free action are the inertial motions, the energy
and the momentum measured by an observer, the Legendre transformation on the
ball of velocities, and the expansion in `1/c` with uniform remainders.
[Guide](docs/special-relativity.md#the-motion-of-a-free-particle)
For the Lorentz group and for collisions it proves that every orthochronous
transformation is a rotation after a boost in one way only, the invariance of
a relation of signals that is contained in the causal order, the energies and
the momenta of a decay into two particles, and the invariants of an elastic
collision.
[Guide](docs/special-relativity.md#signals-the-factorization-of-a-lorentz-transformation-and-collisions)

Topic 6 follows the provisional Boltzmannian typicality plan in
[issue #55](https://github.com/MGYamada/ProjectAinos/issues/55). Its guiding references are

- S. Goldstein and J. L. Lebowitz, *On the (Boltzmann) entropy of non-equilibrium systems*,
  *Physica D* 193(1–4) (2004), pp. 53–66.
  [Published article](https://doi.org/10.1016/j.physd.2004.01.008) ·
  [Open preprint (2003)](https://arxiv.org/abs/cond-mat/0304251)
- S. Goldstein, J. L. Lebowitz, R. Tumulka, and N. Zanghì, *Gibbs and Boltzmann
  Entropy in Classical and Quantum Mechanics*, in V. Allori (ed.), *Statistical
  Mechanics and Scientific Explanation: Determinism, Indeterminism and Laws of
  Nature*, World Scientific (2020), pp. 519–581.
  [Published chapter](https://doi.org/10.1142/9789811211720_0014) ·
  [Open preprint (2019)](https://arxiv.org/abs/1903.11870)

For complementary background on equilibrium typicality, see
[H. Tasaki's revised §4.1 of *Statistical Mechanics I*](https://haltasaki.github.io/books/SM/section41.html).
For phase volume, ensembles, and the ideal gas, see
[Landau and Lifshitz, *Statistical Physics*, Vol. 5, Part 1, Chs. I and III–IV](https://shop.elsevier.com/books/course-of-theoretical-physics/landau/978-0-08-023039-9).

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
