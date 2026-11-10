# P⊗AI (Project AInos)

*Final answer to Hilbert's sixth problem*

P⊗AI is pronounced `poai`.

**P⊗AI (Project AInos)** aims to formalize the whole of theoretical physics in Lean 4. Its planned proof library will make each theory's assumptions explicit, derive its central results, and formalize how theories relate through special cases and limits.

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
3. **Classical Theory of Fields (Landau–Lifshitz)**
   1. Spacetime and fields over the shared smooth-geometry foundation
   2. Relativistic mechanics and electrodynamics
   3. Gravitation and general relativity
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

## Shared smooth algebra and geometry

`ProjectAInos/SmoothAlgebra/` and `ProjectAInos/SmoothGeometry/` are independent
mathematical foundations shared by topics 2 and 3. They must not import
`Mechanics`, `Variational`, or a field-theory module. `Variational` contains
variational calculus; physical models belong to their respective topics.

The construction follows Joyce, *Algebraic Geometry over C∞-rings*, §§2 and 4,
and the architecture of the pinned mathlib v4.35.0 (commit `56a005855ea17e0b0958f73ec801ae140b0a1679`).
The source review covered `Algebra/Category/CommAlgCat/Basic`,
`Geometry/RingedSpace/{PresheafedSpace,SheafedSpace,LocallyRingedSpace,OpenImmersion}`,
`Topology/Sheaves/{LocalPredicate,Stalks,Forget}`, and
`AlgebraicGeometry/{StructureSheaf,Spec,Scheme,AffineScheme,GammaSpecAdjunction}`.

Implementation order:

1. Move the existing five smooth-algebra modules and their namespace out of
   `Variational`; update consumers, documentation, root imports, and axiom audit.
2. Bundle smooth rings and their morphisms. Construct quotients by smooth
   congruences and localizations at real points, proving the C∞ universal
   property. Use these point localizations for the first spectrum construction;
   arbitrary localizations and arbitrary ideal quotients are subsequent algebraic
   extensions.
3. Define `RealSpectrum A` with points `SmoothRingHom A ℝ` and basic opens
   `D(a) = {x | x(a) ≠ 0}`. Prove the basis and contravariant maps.
4. Construct the structure sheaf from sections in the point localizations
   that locally come from elements of `A`, using mathlib's `LocalPredicate`
   machinery. Prove the stalk comparison and real local-ring property.
5. Build the parallel `Spec` and `Scheme` layers. A C∞ scheme is a local
   C∞-ringed space locally isomorphic to an actual constructed `Spec A`.
   Reuse mathlib's underlying sheafed and locally ringed spaces while retaining
   all smooth operations on sections and requiring morphisms to preserve them.
6. Extend the foundation with open subschemes and gluing, the Γ–Spec adjunction,
   complete/fair rings, manifold comparison, and cotangent modules. Mechanics
   and classical field theory consume these constructions independently.

Stages 1–5 are implemented, including the spectrum functor, the category of
C∞ schemes, affine schemes, global sections, affine spaces, and the empty
scheme. The [smooth-geometry guide](docs/smooth-geometry.md) maps these
constructions to mathlib and records the scope of stage 6.

The parallel architecture does not identify the two theories: Joyce's points
are real points, his local rings have residue field ℝ, and the canonical map
`A → Γ(Spec A)` need not be an isomorphism for an arbitrary C∞-ring.
Equivalences with affine C∞ schemes require the appropriate completeness
condition. Nilpotents must remain in the structure sheaf. Scheme definitions
must not assume an unconstructed spectrum functor or an arbitrary family of
affine models. See [Joyce, Definitions 2.10, 2.13, 4.13, 4.16, 4.23 and §4.6](https://arxiv.org/pdf/1001.0023).

Each stage is checked by `lake build --wfail ProjectAInos`, the root-import
check, and the transitive axiom audit. Only `propext`, `Classical.choice`, and
`Quot.sound` are allowed.

See the [proof development record](docs/proof-development.md) for the history of the Lean formalization.

The documentation index links to the guides and the build instructions for the HTML handbook and Lean API reference. [Documentation index](docs/README.md)

## License

Copyright 2026 Masahiko G. Yamada.

Licensed under the [Apache License, Version 2.0](LICENSE). See [NOTICE](NOTICE)
for the copyright notice.
