# P⊗AI (Project AInos)

*Final answer to Hilbert's sixth problem*

P⊗AI is pronounced `poai`.

**P⊗AI (Project AInos)** is a *proof of artificial intelligence* project that seeks to demonstrate AI's capacity for rigorous scientific reasoning through machine-checked proofs.
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
The order of topics after 6 is yet to be determined.

## Shared smooth algebra and geometry

`ProjectAInos/SmoothAlgebra/` and `ProjectAInos/SmoothGeometry/` are independent
mathematical foundations shared by topics 2–5. They must not import
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

Section 3.1 uses natural units `c = 1` and signature `(-+++)` in the physics
layer. Shared geometry accepts both Lorentz conventions explicitly; causal
classification, boosts, and proper time use the convention-independent quadratic
form. [Issue #40](https://github.com/MGYamada/ProjectAInos/issues/40) tracks this
foundation for [electrodynamics #8](https://github.com/MGYamada/ProjectAInos/issues/8).
The [Minkowski geometry and kinematics guide](docs/special-relativity.md) maps the
formal APIs and exact examples.

Section 4.1 now includes local electromagnetic potentials, gauge invariance,
the homogeneous Bianchi identity, observer reconstruction, and both Lorentz
invariants with their orientation signs. The charged-particle action uses the
minimal free-particle action from 3.2 and a compact-interval variational theorem
on open timelike jet domains. Its stationarity yields the Lorentz force;
gauge changes produce the endpoint term. Homogeneous polynomial Maxwell jets
are connected to the pinned upstream radial-gauge reconstruction through an
explicit time-first/time-last coordinate equivalence. Nonzero fields, degrees
0 and 1, and a uniformly accelerated worldline are checked in Lean and SymPy.
See the [electrodynamics API and proof map](docs/electrodynamics.md).
The sourced Maxwell equations and field action in 4.2, collision theory,
and QFT remain outside this implementation.

Section 5.1 has begun with smooth metric duality on the actual tangent and
cotangent bundles: `flat`, `sharp`, smooth lowering/raising of sections, and
their coordinate compatibility. Iterated hom bundles construct finite mixed
tensor types; full/partial trace contraction and inverse-metric contraction
are smooth and coordinate compatible. Tensor-field pullback along
diffeomorphisms preserves smoothness and commutes with contraction.
Covariant tensors of every finite rank also pull back along arbitrary smooth
maps, including dimension-changing maps and singular derivatives. Smoothness,
identity/composition laws, constant-map vanishing in positive rank, and agreement
with diffeomorphism pullback are proved. The induced two-tensor may be degenerate,
as checked by restricting the nonlinear metric to a time axis.
A two-chart regression uses
`(T,X) = (t,x+t²)` to obtain nonconstant coefficients for the Minkowski
metric and proves covariance using the manifold derivative. Both charts
belong to the smooth maximal atlas. The Lorentz Levi-Civita connection is
constructed on the actual tangent bundle using Koszul and `sharp`, with
proved metric compatibility, vanishing torsion, uniqueness on differentiable
sections, finite regularity (`C^(n+1)` fields give `C^n` derivatives),
smoothness, and invariance under metric-sign reversal. On arbitrary smooth
manifold charts, the inverse-metric Christoffel formula, smooth coefficients,
and the coordinate action on differentiable fields are proved. The coefficient
transformation law on chart overlaps includes the actual second derivative
of the transition. The nonlinear chart has `Γˣ_tt = 2`, while the same metric
has zero coefficients in its inertial chart; both instantiate the general law.
Smooth metric-preserving maps intertwine the native connections; derivative
invertibility follows from equal dimension and nondegeneracy. Pullback
metrics and restriction to open submanifolds preserve the Lorentz signature,
and the restricted connection agrees with the ambient connection on
restricted differentiable fields.
The curvature commutator is now a smooth trilinear tensor on the actual
tangent bundle, with extension independence for locally `C²` fields,
both pair antisymmetries, pair interchange, and the algebraic first Bianchi
identity. Its Christoffel formula and tensor transformation law hold on
arbitrary smooth chart overlaps. Smooth metric-preserving maps intertwine
curvature. Ricci and
scalar curvature are smooth intrinsic contractions, with coordinate-trace
and metric-sign laws. Standard Minkowski and the nonlinear shear example
have proved zero Riemann, Ricci and scalar curvature. Ricci is symmetric.
The curved metric `exp(2x²)(-dt²+dx²)` has proved scalar curvature
`-4 exp(-2x²)`: all connection coefficients vanish at the origin, while
the native curvature tensor is nonzero there.
Covariant differentiation along arbitrary differentiable curves now takes
values in the actual tangent fibres, with chart independence, the Leibniz
rule, ambient-field compatibility and metric compatibility proved.
Parallel fields preserve their metric pairing. Affine geodesics have the
usual coordinate ODE, constant velocity norm, and a proved local
initial-value existence/uniqueness theorem. Reparametrization includes the
second-derivative acceleration term; affine changes preserve the geodesic
equation. Flat lines and the nonlinear-chart parabola have native proofs.
Parallel fields now have local and finite-segment existence and uniqueness.
The resulting endpoint linear equivalences preserve the metric and obey
subdivision, reversal and reparametrization laws. Finite concatenations of
regular segments admit matching parallel fields and continuous tangent-bundle
lifts, with uniquely characterized transport, composition and reversal.
Nonzero null geodesic velocities stay nonzero. A chosen Lorentz basis at any
point now extends to a smooth local chart with `g = η`, `Γ = 0` and `∂g = 0`
there, using a quadratic correction and the inverse function theorem.
The curved conformal example has such a chart at the origin despite nonzero
curvature. Local Minkowski geometry now implies zero native curvature.
A smooth invertible parallel coframe integrates to a Minkowski chart,
with metric normalization needed only at its base point. A Banach-space
Volterra construction now proves linear-ODE existence, uniqueness and smooth
dependence on continuous coefficient curves of supremum norm less than one,
with an exact time-dependent example. Jointly smooth coefficients now lift
to smooth curve-valued families. Radial endpoint maps and their inverses are
smooth and invertible near the base point, with rescaling and the radial
differential equation proved. Native chart coefficients admit smooth local
extensions for this construction. Zero coordinate curvature now makes the
radial frame parallel in every direction and constructs a smooth invertible
parallel coframe on a smaller ball. The nonzero shear connection has a
proved inverse-Jacobian endpoint formula. Native curvature is now identified
with the coordinate condition, and the constructed coframe integrates to a
Minkowski chart wherever curvature vanishes on a neighborhood. This proves
`IsLocallyMinkowski ↔ ∀ p, curvature p = 0` and completes stage D's principal
proof endpoints, pending review and merge. Transport is proved independent
of the piecewise path inside a flat neighborhood. The conclusion is local; it
does not assert a global inertial chart or geodesic completeness.
The [shared geometry guide](docs/smooth-geometry.md)
records the public API and exact checks. [Issue #52](https://github.com/MGYamada/ProjectAInos/issues/52)
tracks review of the connection and curvature stages, further tensor operations,
motion, curved forms, and time-dependent Newton-limit stages;
[#43](https://github.com/MGYamada/ProjectAInos/issues/43)
is the first chart-regression gate. Einstein dynamics belongs to 5.2.

See the [proof development record](docs/proof-development.md) for the history of the Lean formalization.

The documentation index links to the guides and the build instructions for the HTML handbook and Lean API reference. [Documentation index](docs/README.md)

## License

Copyright 2026 Masahiko G. Yamada.

Licensed under the [Apache License, Version 2.0](LICENSE). See [NOTICE](NOTICE)
for the copyright notice.
