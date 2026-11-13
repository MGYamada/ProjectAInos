# Landau–Lifshitz Correspondence

This cross-reference connects the Project AInos research plan to the English editions of the *Course of Theoretical Physics*. Mechanics has section-level proof targets, and the other subjects are mapped by chapter or volume. The implementation order follows the [research plan](../README.md).

## Mechanics

Section numbers refer to Volume 1, *Mechanics*, third edition. The targets use the project's smooth algebra over C∞-rings, with analytic hypotheses tracked separately. [Volume 1 contents](https://www.sciencedirect.com/book/9780750628969/mechanics)

The tiers describe proof prerequisites. **A** uses abstract algebra, **A\*** uses explicit algebraic identities, **B** needs analytic interface lemmas, and **C** needs geometric infrastructure. **D** marks a deeper theorem to state with explicit hypotheses. **P** marks a physical or asymptotic argument that needs a precise theorem statement. When two tiers appear, the first applies to the main target.

| Chapter | § | Planned Lean target | Tier |
| --- | ---: | --- | --- |
| I · Equations of motion | 1 | Configuration spaces, tangent states, and coordinate changes | A |
| I | 2 | First variation, Euler–Lagrange equations, and null Lagrangians | A, B |
| I | 3 | Galilean symmetry on jets and quasi-invariance of the free-particle Lagrangian under boosts | A, A\* |
| I | 4 | The quadratic free-particle Lagrangian from boost quasi-invariance and isotropy | B |
| I | 5 | Natural Lagrangians for particle systems and Newton's equations | A\* |
| II · Conservation | 6 | Energy conservation from time-translation symmetry | A |
| II | 7 | Linear momentum from spatial translations | A |
| II | 8 | The Galilean boost integral and centre-of-mass motion | A |
| II | 9 | Angular momentum from rotations and the momentum map | A |
| II | 10 | Scaling for homogeneous potentials and the time-averaged virial theorem | A\*, B |
| III · Integration | 11 | One-dimensional energy quadrature and the oscillation period T(E) from the turning points | B |
| III | 12 | Abel inversion for the turning-point separation and conditions for recovering the potential | B |
| III | 13 | Canonical centre-of-mass and relative coordinates with reduced mass | A\* |
| III | 14 | Central-force reduction and the orbit integral | A\*, B |
| III | 15 | Kepler conics, the Runge–Lenz vector, and the period law | A\*, B |
| IV · Collisions | 16 | Decay kinematics on joint energy and momentum level sets | A\* |
| IV | 17 | Post-collision velocities from elastic conservation laws | A\* |
| IV | 18 | Deflection as a function of impact parameter and cross-section as a pushforward measure | B, C |
| IV | 19 | Rutherford deflection and differential cross-section | A\*, B |
| IV | 20 | Large-impact-parameter asymptotics for small deflections | P |
| V · Oscillations | 21 | Linearization about a nondegenerate minimum and the quadratic flow | B |
| V | 22 | Duhamel's formula for the driven oscillator and energy transfer | B |
| V | 23 | Normal modes by diagonalizing the mass and stiffness forms | A |
| V | 24 | Molecular vibration modes and their decomposition under symmetry | A |
| V | 25 | Damped linear motion and the energy balance | B, A |
| V | 26 | Linear response and resonance with damping | B |
| V | 27 | Floquet trace criterion for monodromy in SL(2, ℝ) (at trace ±2, all solutions are bounded exactly when the monodromy is ±I), plus leading-order estimates of the instability band width and growth rate near primary parametric resonance under weak modulation | B, P |
| V | 28 | Formal Birkhoff normal form and the leading anharmonic frequency shift | A\*, P |
| V | 29 | Amplitude equation for driven, damped nonlinear resonance | P |
| V | 30 | Averaging in a rapidly driven system, effective potential, and error bounds | P, D |
| VI · Rigid bodies | 31 | Angular velocity and the rigid velocity field | A |
| VI | 32 | Inertia tensor, principal axes, and the parallel-axis theorem | A |
| VI | 33 | Angular momentum and precession of the symmetric top | A, B |
| VI | 34 | Spatial-frame rigid-body balance laws and reduction of `T*SO(3)` by spatial rotations to the body-frame Poisson structure | A, C |
| VI | 35 | Euler-angle coordinates and the kinetic energy in those coordinates | A\* |
| VI | 36 | Euler's equations from the body-frame Lie–Poisson bracket | A\* |
| VI | 37 | Integrals, principal-axis stability, and elliptic-function solutions for the asymmetric top | A\*, D |
| VI | 38 | Holonomic constraints via ideals and Lagrange–d’Alembert dynamics on velocity distributions for nonholonomic contact | A, C |
| VI | 39 | Rotating-frame Hamiltonian, Coriolis force, and centrifugal force | A\* |
| VII · Canonical mechanics | 40 | The regular Legendre transform and Hamilton's equations | B |
| VII | 41 | Partial Legendre transform and the Routhian | B |
| VII | 42 | Poisson brackets, the Jacobi identity, and conversion between sign conventions | A |
| VII | 43 | Boundary derivatives of the action along families of solutions | B |
| VII | 44 | Maupertuis reparametrization and the Jacobi metric | A, B |
| VII | 45 | Canonical maps, generating functions, and symplectic evolution | A, B |
| VII | 46 | Preservation of the symplectic form and phase-space volume | A, B |
| VII | 47 | Hamilton–Jacobi equation and complete integrals | A, B |
| VII | 48 | Separated solutions in spherical, parabolic, and elliptic coordinates | A\* |
| VII | 49 | Action integral and the period relation ∂I/∂E = T/(2π) at fixed parameters, plus an adiabatic drift estimate with explicit hypotheses | B, D |
| VII | 50 | Action–angle coordinates in one degree of freedom | B |
| VII | 51 | Exponentially small drift of a suitably corrected adiabatic invariant under analytic hypotheses | P, D |
| VII | 52 | Liouville–Arnold theorem, invariant tori, and degenerate cases | D |

Momentum-map reduction at singular values and Dirac brackets for second-class constraints extend the Mechanics plan beyond the Volume 1 section map. E7 checks Poisson identities in examples of singular reduction, and E8 checks Dirac bracket identities for a particle constrained to a circle. [Symbolic checks](../experiments/ainos_experiments/verify_identities.py)

## Special Relativity

Topic 3 follows Volume 2, *The Classical Theory of Fields*, fourth edition,
Chapters I–II. Topics 4 and 5 continue with Chapters III–IX and X–XIV,
respectively. [Volume 2 contents](https://shop.elsevier.com/books/the-classical-theory-of-fields/landau/978-0-08-025072-4)

| Landau–Lifshitz reference | Research-plan topic |
| --- | --- |
| Vol. 2, Ch. I | 3.1: Minkowski geometry, Lorentz transformations, and relativistic kinematics |
| Vol. 2, Ch. II | 3.2: Relativistic particle dynamics, energy, momentum, and conservation laws |

## Electrodynamics

Topic 4 follows Volume 2, Chapters III–IX, using Special Relativity from topic 3.
Volume 8, *Electrodynamics of Continuous Media*, second edition, supplies the
additional macroscopic-matter extension proposed in [issue #8](https://github.com/MGYamada/ProjectAInos/issues/8).
[Volume 8 contents](https://www.sciencedirect.com/book/monograph/9780080302751/electrodynamics-of-continuous-media)

| Landau–Lifshitz reference | Candidate formalization topics |
| --- | --- |
| Vol. 2, Ch. III | 4.1: Charged-particle action, electromagnetic potentials, field tensor, and Lorentz force |
| Vol. 2, Ch. IV | 4.2: Maxwell equations and conservation laws |
| Vol. 2, Ch. V–VII | 4.3: Static fields, vacuum waves, and optics |
| Vol. 2, Ch. VIII–IX | 4.4: Fields of moving charges and radiation |
| Vol. 8 | Macroscopic Maxwell equations, constitutive relations, and propagation in matter |

## General Relativity

Topic 5 follows Volume 2, Chapters X–XIV. It treats the metric as a dynamical
field and develops gravitational motion, Einstein's equations, gravitational
radiation, and cosmology.

| Landau–Lifshitz reference | Research-plan topic |
| --- | --- |
| Vol. 2, Ch. X | 5.1: Geometry and particle motion in gravitational fields |
| Vol. 2, Ch. XI–XII | 5.2: Einstein dynamics and fields of gravitating systems |
| Vol. 2, Ch. XIII | 5.3: Gravitational radiation |
| Vol. 2, Ch. XIV | 5.4: Relativistic cosmology |

The first 5.1 implementation provides smooth metric duality on the actual
tangent bundle, finite mixed tensor bundles with smooth contraction and
field pullback along diffeomorphisms, covariant pullback along arbitrary smooth
maps between possibly different dimensions, and a nonlinear two-chart Minkowski
regression. Covariant pullback has proved smoothness, functoriality and singular-map
examples; its induced tensor need not remain a Lorentz metric. Its
[API and proof map](smooth-geometry.md#gr-51-metric-duality-and-the-first-chart-regression)
also records the Lorentz Levi-Civita construction: metric compatibility,
vanishing torsion, uniqueness on differentiable sections, finite and smooth
regularity, and metric-sign invariance are proved. The Christoffel formula,
smoothness and coefficient transformation law with the transition Hessian
hold on arbitrary smooth manifold charts. The nonlinear shear verifies this
general law in two actual charts. Metric pullback, intrinsic connection
naturality under smooth metric-preserving maps and compatibility with open
restriction are proved. The curvature increment constructs the smooth native
Riemann tensor, proves local `C²` extension independence, both pair
antisymmetries, pair interchange, algebraic first Bianchi and naturality,
and constructs smooth Ricci/scalar contractions with symmetric Ricci.
The Christoffel curvature formula and tensor transformation law hold in
arbitrary smooth charts. Both Minkowski presentations have proved zero
curvature. The curved metric `exp(2x²)(-dt²+dx²)` has proved scalar curvature
`-4 exp(-2x²)`, including zero connection but nonzero curvature at the origin.
Stage C's proof endpoints are implemented and awaiting review/merge.
Stage D constructs chart-independent covariant differentiation along
curves, proves metric preservation for parallel fields and geodesic
velocity, and derives the coordinate geodesic ODE. The local geodesic
initial-value problem has proved existence and uniqueness on the actual
tangent bundle. Reparametrization, both-signature Minkowski lines and the
nonlinear-chart geodesic/parallel-field examples are proved. Parallel fields
exist uniquely along prescribed finite segments, and endpoint transport
preserves the metric, composes under subdivision, reverses by inversion,
and respects parameter changes. Nonzero null velocities are preserved.
Finite piecewise-path concatenation has matching native parallel fields,
continuous lifts, uniquely characterized transport and reversal laws;
the Minkowski right-angle path is a proved example. Local inertial charts
now exist at every point with a prescribed Lorentz basis, zero connection
coefficients and zero first metric derivatives. Their quadratic construction
is compatible with nonzero curvature at the chosen point. Local Minkowski
geometry implies zero native curvature. Smooth parallel coframes now
integrate to local Minkowski charts, with normalization propagated from
one point. The supporting Volterra solver now proves smooth dependence on
small continuous coefficient curves and initial values, including a
time-dependent exact example. Smooth coordinate coefficients lift to
curve-valued families; radial frames and their inverses are smooth near
the center, with rescaling and the radial differential equation proved.
Native chart coefficients admit suitable local extensions. Zero coordinate
curvature now gives parallelness in every direction and a smooth invertible
parallel coframe. Native curvature now supplies that coordinate condition,
and integrating the constructed normalized coframe gives a Minkowski chart
wherever curvature vanishes near a point. The equivalence
`IsLocallyMinkowski ↔ ∀ p, curvature p = 0` is proved. Stage D's principal
proof endpoints, including path independence for finite piecewise paths
inside a flat neighborhood, are implemented, pending review and merge; global inertial
coordinates and geodesic completeness are not conclusions.
Stage E now supplies intrinsic proper time and particle actions, subdivision
and chart formulas, reparametrization invariance and exact SR specialization.
Curved stationary-clock rates and integrals are proved. For an arbitrary smooth
Lorentz metric on the model manifold, the actual quadratic-action first
variation retains the endpoint term, and fixed-endpoint stationarity is
equivalent to the native affine geodesic equation. Causal constraints are not
imposed on variations. The [GR guide](general-relativity.md) records the native
manifold generalizations below. Massive timelike
stationarity in model coordinates is now equivalent to regular local
affine-geodesic reparametrization. A single C² proper-time inverse now covers
the full finite timelike segment on arbitrary Lorentz manifolds, with both
endpoints, unit rate and affine-geodesic consequences proved. An exponential
shear clock distinguishes massive from quadratic stationarity and has the
expected logarithmic inverse. Genuine C² manifold curve families now have
proved actual-action derivatives, intrinsic endpoint formulas, and subdivision
laws. Fixed endpoints eliminate the boundary terms, proving the motion-to-
stationarity direction on arbitrary manifolds, including null reference
geodesics for the quadratic action. Actual localized manifold test families
now prove the converse directions and both complete native equivalences.
Local affine reparametrization, unit proper speed, one finite proper-time
inverse and closed-segment preservation of nonzero null initial velocity are
proved. Stage E's principal endpoints await review. Stage F has a smooth
native alternating bundle, coefficient overlap laws, open-cover gluing,
arbitrary smooth pullback and exact flat specialization, with nonlinear and
singular-map examples. The native exterior derivative is constructed and
proved chart-independent, smooth, linear, local, square-zero and natural
under every smooth pullback. A nonzero exact two-form, nonlinear charts and
a dimension-changing map test its normalization. The native wedge on finite
coordinate models now has chart independence, smoothness, general pullback
naturality, bilinearity, associativity, graded commutativity, units and the
graded Leibniz rule. Actual nonlinear charts and a nonzero three-form check
fix normalization and signs. Intrinsic volume density now has positive,
smooth chart coefficients with absolute-Jacobian covariance. Signed local
orientations glue a smooth nonzero volume form, with proved cover independence,
orientation reversal and exact flat/nonlinear/conformal normalizations.
Native Hodge now has a proved wedge identity, uniqueness, sign laws,
metric/volume-preserving naturality and exact flat API agreement. Native
four-dimensional signs and nonlinear shear transport test its normalization.
The local inverse-metric formula proves smooth-section regularity, and the
general Lorentz square identity holds without flatness or a global frame.
The curved conformal plane verifies the one-form operator and its square.
Intrinsic divergence and its positive-density formula are now proved in all
smooth charts, including a nonzero curved example. Fixed-background Maxwell
forms, invertible vector/three-form current identification, sourced current
closedness and orientation invariance are implemented. A time-dependent
nonzero-current example fixes the physical vector sign. Pointwise volume
contraction and `dJ = (div j) vol` now prove vector-divergence conservation.
Native two-form covariant differentiation and the homogeneous Maxwell
component equivalence are now proved, with curved and nonclosed examples.
The smooth native two-form divergence and its density expression are also
proved, including the nonzero electric-source sign and a curved example.
The general identification with the source from `dH` and the
Newtonian motion limit remain in the work
tracked by [#52](https://github.com/MGYamada/ProjectAInos/issues/52).
Einstein equations and their Newtonian field-equation limit remain in 5.2;
the Maxwell field action remains in 4.2.

## Thermodynamics, Statistical Mechanics, and Later Topics

Thermodynamics and Classical Statistical Mechanics are items 1 and 6 in the research plan. The other subjects in this table have an open implementation order after topic 6. [Elsevier series catalogue](https://legacyfileshare.elsevier.com/assets/pdf_file/0006/796479/Landau_CTP_180529.pdf) · [Volume 5 contents](https://www.sciencedirect.com/book/monograph/9780080570464/statistical-physics) · [Volume 9 contents](https://www.sciencedirect.com/book/9780080503509/statistical-physics)

| Landau–Lifshitz reference | Subject |
| --- | --- |
| Vol. 3, *Quantum Mechanics* | Nonrelativistic quantum mechanics |
| Vol. 4, *Quantum Electrodynamics* | Quantum electrodynamics |
| Vol. 5, *Statistical Physics*, Part 1, Ch. II (background) | Thermodynamics. The Lean development follows the Lieb–Yngvason approach, starting with the stability axiom for adiabatic accessibility. |
| Vol. 5, *Statistical Physics*, Part 1, Ch. I and III–IV | Classical Statistical Mechanics, including ensembles, the ideal gas, and the bridge to thermodynamics |
| Vol. 5, *Statistical Physics*, Part 1, Ch. V | Quantum statistical physics, including the Fermi and Bose distributions |
| Vol. 6, *Fluid Mechanics* | Fluid mechanics |
| Vol. 7, *Theory of Elasticity* | Elasticity |
| Vol. 9, *Statistical Physics*, Part 2 (*Theory of the Condensed State*) | Quantum theory of condensed matter |
| Vol. 10, *Physical Kinetics* | Kinetic theory and transport |
