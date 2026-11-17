# Shared smooth algebra and geometry

`ProjectAinos/SmoothAlgebra/` and `ProjectAinos/SmoothGeometry/` are independent
mathematical foundations shared by topics 2–5. The shared `Variational/`
layer currently imports only Mathlib and its own modules. The Lorentzian
variation lemmas use its generic manifold-variation machinery. These
shared modules may import one another and external mathematical libraries.
Their import graph excludes project physics and the vendored Yang–Mills
theory.

`ProjectAinos/Integrations/` owns the project-authored Yang–Mills coordinate
and first-jet adapters. They depend on the shared cores and the pinned upstream
modules. Their declaration names are preserved and their new module paths are
imported by `ProjectAinos`. The `checks/CoreImports.lean` CI check enforces the
project-local import boundary.

## Foundation implementation plan

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
scheme. The [smooth-geometry guide](smooth-geometry.md) maps these
constructions to mathlib and records the scope of stage 6. Open subschemes
and gluing are implemented, and the gluing of two overlapping half-lines is
proved isomorphic to the smooth affine line as a C∞ scheme.
The algebra layer also has partial derivatives of smooth operations, the
C∞-ring of dual numbers, and C∞-derivations with their commutator: the first
algebraic stage of the [mechanics plan](cinfty-mechanics.md), tracked in
[#74](https://github.com/MGYamada/ProjectAinos/issues/74). The [smooth-algebra guide](smooth-algebra.md) gives the
statements.

The parallel architecture does not identify the two theories: Joyce's points
are real points, his local rings have residue field ℝ, and the canonical map
`A → Γ(Spec A)` need not be an isomorphism for an arbitrary C∞-ring.
Equivalences with affine C∞ schemes require the appropriate completeness
condition. Nilpotents must remain in the structure sheaf. Scheme definitions
must not assume an unconstructed spectrum functor or an arbitrary family of
affine models. See [Joyce, Definitions 2.10, 2.13, 4.13, 4.16, 4.23 and §4.6](https://arxiv.org/pdf/1001.0023).

Each stage is checked by `lake build --wfail ProjectAinos`, the root-import
check, and the transitive axiom audit. Only `propext`, `Classical.choice`, and
`Quot.sound` are allowed.

## Mechanics

Section 2 has two parts so far. In the real analytic model, on a finite time
interval, fixed-endpoint stationarity of the actual action is equivalent to the
Euler–Lagrange equation, including Lagrangians defined on an open jet domain.
Adding the total time derivative of a boundary function `F(t, q)` changes the
action by an endpoint difference and leaves the Euler–Lagrange residual
unchanged. The natural scalar Lagrangian yields Newton's equation, and
Lagrangians can be taken from the shared C∞-ring of smooth operations.
In the algebraic model, jet C∞-rings carry a total derivative and Euler
operators. Total derivatives are null Lagrangians, the energy and Noether
identities hold in every jet ring, and the conservation laws of energy,
momentum, the centre of mass and angular momentum follow for natural
Lagrangians as membership in the Euler–Lagrange ideal. Natural Lagrangians with
a position-dependent kinetic form have their Lagrange equations and energy, with
plane polar co-ordinates as a model. The standard jet ring is
the nondegenerate model. The prolongation of a smooth path turns the total
derivative into `d/dt`, so a conserved element is constant along every smooth
solution, in particular the energy along solutions of Newton's equations. A
smooth path is a solution in the jet ring exactly when the action of the real
analytic model is stationary on every interval. For 2.3, Poisson structures on C∞-rings are implemented with
Poisson's theorem, the normalizer of a coisotropic ideal, the Hamilton–Jacobi
and Maupertuis–Jacobi statements, the canonical bracket with Hamilton's
equations, the rigid body with Euler's equations, the angular momentum of a
particle with its momentum map, the heavy top, the Galilei algebra of a free
particle, the virial identity, and the equations of motion in a uniformly
rotating frame. Kepler's problem is treated with a formal inverse radius as a
generator: the Runge–Lenz identities are proved, and the Runge–Lenz vector is
constant along smooth solutions of the inverse-square law. The constraint
allows both signs: `r = ρ |q|²` is a signed radius, with `|r| = |q|`;
`r` is the ordinary distance on the branch `ρ > 0`. The kinematics of a
rigid body is proved by linear algebra:
`so(3) ≅ ℝ³`, the angular velocity, the inertia tensor of point masses with
its principal moments, Eulerian angles, the regular precession of the symmetric
top, and the stability of the permanent rotations. The algebra of two bodies is proved: the reduced mass,
disintegration, and elastic collisions. Free oscillations in one dimension are
proved: the general solution of `ẍ + ω² x = 0`, the flow of the oscillator, and
the linearization at an equilibrium. Damped oscillations are proved in their
three cases, with the loss of energy `−2F` for a dissipative function `F`.
Forced oscillations under friction are proved with the approach to the steady
state and the exact resonance curve, and without friction with Duhamel's
formula and the energy transfer. Normal modes, the normal form of a quadratic
Hamiltonian as a linear canonical transformation, and the stability criterion
of parametric resonance are proved. Integrals of the motion are constant along
trajectories of a Hamiltonian on a free C∞-ring. The Legendre correspondence
for natural Lagrangians, Jacobi's theorem on complete integrals and Liouville's
theorem in infinitesimal form are proved, as are the description of states as
morphisms to the dual numbers, mechanical similarity and the
virial theorem for time averages. The Lagrangian of a free particle is
characterized by quasi-invariance under boosts and isotropy, and the Galilei
algebra acts on the jet ring by vector fields that preserve the Euler–Lagrange
ideal of a quasi-invariant Lagrangian. The Legendre correspondence is proved
for every Lagrangian whose Legendre transformation has an inverse morphism,
and the transformation given by a free generating function `F(q, Q)` is
canonical. Hadamard's lemma is proved, so quotients of C∞-rings by ideals and
the reduced Poisson rings `N(I)/I` exist; the reduced mass is proved as the
reduction of two particles by translations, and the Routhian with its
equations of motion and cyclic co-ordinates is proved. Motion in a central
field is proved in polar co-ordinates: the radial Hamiltonian with the
centrifugal energy, and the time and the angle as integrals over the radius.
The integrals up to simple turning points are proved as Lebesgue integrals:
the time between two turning points, the motion between two apsides, and the
period `2π a^{3/2} √(m/α)` of Kepler's problem. A linear differential
equation with a continuous coefficient has a propagator for all real times,
with no bound on the coefficient, so the equation `ẍ + p(t) x = 0` has a
unique solution for given initial data and every smooth `p`; for a periodic
`p` all solutions are bounded exactly when the trace of the monodromy matrix
has absolute value less than two or the matrix is `±1`. For
`ẍ + ω₀² (1 + h cos γt) x = 0` the trace is known to second order with an
explicit remainder, which gives the instability zone
`|ω₀² − γ²/4| < ω₀² |h|/2` to first order and parametric resonance at
`γ = 2ω₀`. A smooth vector field on a Banach space has a flow with an open
domain and smooth dependence on the time and the point; the determinant of
its derivative in the initial point is `exp ∫ tr DX`. Hence the flow of every
Hamiltonian of the free C∞-ring on finitely many canonical co-ordinates
preserves the Lebesgue measure of the phase space (Liouville's theorem), the
flows of the oscillator and of the pendulum are defined for all times, and
with friction the phase volume of the oscillator contracts as
`exp (−Σ aᵢ/mᵢ · t)`. For a family of paths with moving end times whose
reference path solves the equations of motion, the derivative of the action
is `p dq − E dt` at the two ends; for the solutions of the flow of a
Hamiltonian this is `dS = p dq − H dt`, the flow preserves the symplectic
form, and away from conjugate points the action is a differentiable function
of the time and the end point that satisfies the Hamilton–Jacobi equation.
For one degree of freedom, the motion in a well between two simple turning
points is periodic, its period is the derivative of the area `∮ p dx` with
respect to the energy, Abel's formula gives the width of the well from the
period, and the action and the angle variable are canonical.
For a rigid motion of point masses, Newton's equations give `Ṗ = F` and
`Ṁ = K`, and in the body frame Euler's equations with the moment of the
forces; these are the Lie–Poisson equations of the free body and of the heavy
top, and Hamilton's principle on the curves of rotations is equivalent to
them. The rotation is recovered from the angular velocity for all times.
Jacobi's elliptic functions are constructed from the amplitude, and every
motion of the asymmetrical top off the separatrix is given by them.
The space of the normal modes is the direct sum of the spaces of the modes of
each frequency, each a representation of the group of symmetries, and the
number of the modes of a symmetry type is a scalar product of characters; for
a molecule the character of the displacements is `N_g · tr O_g`, and the
vibrations of two molecules of three atoms are decomposed.
The method of averaging is proved to the first order with an error bound: a
motion under a rapidly oscillating force stays within `C/ω` of the motion in
the effective potential `U + g²/4m`, and the amplitudes of the forced
oscillator with a cubic term stay within `C/γ` of the solution of the averaged
equations, whose equilibria satisfy the equation of the amplitude at
resonance.
The Birkhoff normal form is proved in one degree of freedom: a formal
Hamiltonian `ω (q² + p²)/2 + ⋯` in `ℝ[[q, p]]` is carried to a power series in
the action by an automorphism that preserves the Poisson bracket. For the
anharmonic oscillator `ẍ + ν² x = −α x² − β x³` the coefficient of the square
of the action is `3β/8ν² − 5α²/12ν⁴`, and the frequency of the oscillation of
half-width `ρ` is `ν + (3β/8ν − 5α²/12ν³) ρ² + o(ρ²)`, proved from the period.
The adiabatic theorem is proved for one degree of freedom: for
`H = p²/2m + V(λ, x)` with `λ = Λ(εt)` the action variable `(1/2π) ∮ p dx`
changes by at most `C ε` up to the time `T/ε` along a motion that stays in a
compact set of closed level curves, and for the oscillator with the frequency
`Ω(εt)` by at most `C ε I(0)` for every motion. For the exponential estimate,
the frequency is `ω = exp q(εθ)` with `ε > 0` and `θ̇ = ω`. Half the derivative of `q`
extends holomorphically to a neighborhood of the strip `0 ≤ Im z ≤ σ`.
Its norm on the strip is bounded by a continuous function of `Re z` that tends to
zero at both ends and whose integrals on finite intervals are bounded by `G`.
Under these conditions the action has limits at `t → ±∞`. The absolute
difference is at most `e^{G}(4e^{G} + 2) e^{−2σ/ε}` times the incoming action.
See §51 in the [mechanics ledger](cinfty-mechanics.md#ledger).
Scattering in a central field is proved for motions in polar co-ordinates:
the angle described from the closest approach to infinity is the integral
(18.4), the velocities before and after the scattering have the scalar
product `v∞² cos (π − 2φ₀)` and make the angle `|π − 2φ₀|` when this is at
most `π`, and the cross-section is the push-forward of the measure
`2πρ dρ` of the impact parameter. For the Coulomb field `cot (χ/2) = m v∞² ρ/α`,
and Rutherford's formula is the density `(α/2m v∞²)²/sin⁴ (χ/2)` of the
cross-section with respect to the solid angle. For a potential energy
`U = ε r⁻ⁿ w(1/r)` with `w` smooth the angle of deflection is
`−(2ρ/m v∞²) ∫_ρ^∞ U′(r) dr/√(r² − ρ²)` up to a remainder of at most
`M (ε/ρⁿ)²`, uniformly for impact parameters and asymptotic speeds bounded
below. The radial equation uses `U(r) − U(∞)`.
Maupertuis' principle is proved for a Lagrangian `T − U` at a fixed energy in
the region `U < E`: a curve of that energy is a motion exactly when it makes
`∫ 2 √((E − U) T) dt` stationary, and exactly when it is a geodesic of the
Jacobi metric in the parameter with `dσ/dt = 2 (E − U)`.
The separation of the variables is proved on a box of co-ordinates for
Hamiltonians of Stäckel's form: the separated action is given by quadratures,
it satisfies the Hamilton–Jacobi equation, it is complete, and Jacobi's
theorem gives Hamilton's equations; spherical, parabolic and elliptic
co-ordinates are instances.
For integrals in involution on the canonical phase space, a compact connected
level set with independent differentials is a torus: the joint flow of the
Hamiltonian fields is transitive on it, its periods form a lattice, and the
motion is conditionally periodic. Near the torus there are action–angle
variables: a continuously differentiable chart `Ψ(J, φ)` with the period `2π`
in the angles, injective up to these periods, in which the symplectic form is
`Σₖ dφₖ ∧ dJₖ`, the integrals are functions of the actions, the flow of each
integral moves the angles with the velocities `∂Hᵢ/∂Jₖ`, and
`Jₖ = (1/2π) ∮ p dq` over the cycles of the tori (the theorem of Liouville and
Arnold); a system of oscillators is the instance.
Open topics include mechanics on general configuration manifolds, symplectic
forms on manifolds, Dirac brackets, Galilean symmetry as a group action, and
general nonholonomic dynamics. The
[ledger](cinfty-mechanics.md#ledger) gives the status of each section of
Landau–Lifshitz. [#78](https://github.com/MGYamada/ProjectAinos/issues/78) recorded the first
delivery, and [#114](https://github.com/MGYamada/ProjectAinos/issues/114) tracks the proofs of the
remaining rows. See the
[mechanics guide](mechanics.md) and the
[C∞ mechanics research plan](cinfty-mechanics.md).

## Special relativity

Section 3.1 uses natural units `c = 1` and signature `(-+++)` in the physics
layer. Shared geometry accepts both Lorentz conventions explicitly; causal
classification, boosts, and proper time use the convention-independent quadratic
form. [Issue #40](https://github.com/MGYamada/ProjectAinos/issues/40) tracks this
foundation for the [classical-field research trilogy](cinfty-special-relativity.md).
The [Minkowski geometry and kinematics guide](special-relativity.md) maps the
formal APIs and exact examples.

## Electrodynamics

Section 4.1 now includes local electromagnetic potentials, gauge invariance,
the homogeneous Bianchi identity, observer reconstruction, and both Lorentz
invariants with their orientation signs. The charged-particle action uses the
minimal free-particle action from 3.2 and a compact-interval variational theorem
on open timelike jet domains. Its stationarity yields the Lorentz force;
gauge changes produce the endpoint term. Homogeneous polynomial Maxwell jets
are connected to the pinned upstream radial-gauge reconstruction through an
explicit time-first/time-last coordinate equivalence. Nonzero fields, degrees
0 and 1, and a uniformly accelerated worldline are checked in Lean and SymPy.
See the [electrodynamics API and proof map](electrodynamics.md).
Section 4.2 includes the flat vacuum Maxwell action and the equivalence of
compactly supported stationarity with the vacuum field equation. The proof
uses the signed four-form density, and a uniform nonzero electric field
checks its sign and stationarity on a finite-volume domain. Fixed-background
Maxwell forms are part of the 5.1 progress recorded below.

## General relativity

Section 5.1 has begun with smooth metric duality on the actual tangent and
cotangent bundles: `flat`, `sharp`, smooth lowering/raising of sections, and
their coordinate compatibility. Iterated hom bundles construct finite mixed
tensor types; full/partial trace contraction and inverse-metric contraction
are smooth and coordinate compatible. Smooth tensor products, permutations of
typed slots, and contraction of any selected tangent/cotangent pair use the
same bundles. All three operations commute with diffeomorphism pullback, and
the selected contraction has a basis–dual-basis component formula.
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
proof endpoints, merged through [#52](https://github.com/MGYamada/ProjectAinos/issues/52).
Transport is proved independent
of the piecewise path inside a flat neighborhood. The conclusion is local; it
does not assert a global inertial chart or geodesic completeness.
The first stage E increment defines proper time and particle actions on the
actual tangent bundle of a curved spacetime. Integrability, interval
subdivision, chart formulas, parameter invariance and exact SR specialization
are proved. Fixed-position clocks in the curved conformal example have proper
time `(b-a) exp(x²)`. On the model manifold with an arbitrary smooth Lorentz
metric, the actual quadratic action has the first-variation formula including
endpoint terms; fixed-endpoint stationarity is equivalent to the native affine
geodesic equation. This theorem allows null reference velocities and imposes
no causal constraint on variations. Positive-mass timelike stationarity is now
equivalent to local affine-geodesic reparametrization in model coordinates.
The actual proper-time integral has one constructed C² inverse covering a full
finite timelike segment on arbitrary Lorentz manifolds. Both endpoints, unit
rate and the removal of tangential acceleration are proved. An exponentially
parametrized shear worldline is stationary for the massive action but not for
the quadratic action; its finite inverse is logarithmic. For genuine C²
manifold-valued curve families, mixed covariant derivatives commute. The actual
actions now have intrinsic first-variation formulas with endpoint terms,
derived from local C² regularity on the finite reference segment. Their
derivatives glue over subdivisions, and fixed-endpoint families make affine
geodesics stationary for the quadratic action and timelike tangential motion
stationary for the massive action. Localized chart families now realize the
compact test fields used in the fundamental lemma. Both variational
equivalences are proved on arbitrary Lorentz manifolds, including regular
local reparametrization, unit proper speed, and one finite proper-time inverse.
Nonzero null initial velocity is preserved on the entire closed quadratic-
stationary segment, with no causal restriction on variations. A smooth compact
test in the nonlinear chart realizes arbitrary midpoint tangent data.
The stage E principal endpoints are implemented and merged into `main`.
Stage F now has smooth alternating bundles on actual tangent fibres, local
coefficient transition laws, open-cover gluing and arbitrary-smooth-map
pullback, including different dimensions and singular derivatives. Flat API
agreement and nonlinear one-/two-form examples are proved. Native exterior
differentiation is now chart-independent, linear and local, squares to zero,
and commutes with arbitrary smooth pullback. Its flat specialization and
nonzero nonlinear-chart examples are proved. On finite coordinate models,
native wedge is chart-independent and smooth, preserves arbitrary smooth
pullback, and satisfies bilinearity, associativity, graded commutativity,
unit laws and graded Leibniz. Exact flat normalization, nonlinear/singular
and dimension-changing examples, and a nonzero three-form sign check are
proved. Intrinsic Gram-determinant volume density is positive on tangent
bases, smooth in charts and transforms by the absolute Jacobian. Compatible
signed local charts now construct a smooth, nowhere-zero oriented volume
form, independent of the chosen cover. Its absolute value is the density;
orientation reversal negates the form, while whole-metric sign reversal
preserves both. Minkowski, nonlinear-chart and curved conformal examples
fix its normalization. The inverse metric and this volume now construct
Lorentz Hodge on native fibres, with its wedge identity, uniqueness,
orientation and metric-sign laws, and naturality under metric/volume-preserving
tangent equivalences proved. Exact Minkowski API agreement, the six
four-dimensional two-form signs and nonlinear shear transport are proved.
The local inverse-metric formula proves smoothness, yielding a linear map
on smooth native forms. The general Lorentz square identity is proved using
only pointwise signature witnesses; a curved conformal example verifies it.
The actual connection trace now defines smooth divergence and yields
`div V = ρ⁻¹ ∂ᵢ(ρ Vⁱ)` in every smooth chart, with `ρ = sqrt(abs(det g))`.
On a fixed four-dimensional `(-+++)` background, Maxwell forms use
`H = -⋆F` and `J = ⋆(j♭)`. The current identification is invertible;
the sourced equation implies `dJ = 0`, and orientation reversal preserves
the equations. Pointwise Lorentz frames prove `⋆(j♭) = ιⱼ vol` with no flatness
or global-frame assumption. Chart differentiation proves `dJ = (div j) vol`,
so current closedness is equivalent to vanishing covariant vector divergence.
A time-dependent field has the proved nonzero vector source `j = -∂x`, fixing
the sign of the public source convention `∇ᵢFⁱʲ = jʲ`. The matter current
compatible with the flat particle coupling `+e∫A` is `-j`; that bridge is a
[recorded proof obligation](cinfty-electrodynamics.md#sourced-variation-and-the-matter-current).
Native two-form covariant differentiation is now constructed,
smooth and independent of local extensions. Its chart formula has both
Christoffel corrections; `dF = 0` is equivalent to the cyclic covariant component
equation in every smooth chart. The native two-form divergence is a smooth vector,
with both raised indices and the density formula `∇ᵢFⁱʲ = ρ⁻¹ ∂ᵢ(ρ Fⁱʲ)` proved.
The source defined by `dH` is now proved equal to this native divergence.
Both Maxwell equations are equivalent to their covariant component equations
in every smooth chart. Stage F’s principal endpoints are implemented and merged into `main`.
Stage G now has the full time-dependent coefficient-family contract, proved
bounded-velocity negativity and spatial positivity, and the native
coordinate-time equation including its non-affine correction. A polynomial
family has proved C² bounds and nonzero time/mixed/spatial data. The native
Lorentz metric and its coordinate connection are constructed.
Uniform inverse bounds and coefficient derivatives give the uniform
`O(c⁻²)` acceleration error. A Gronwall estimate controls position and velocity
on a common interval where both solutions exist and their connecting segments
stay in the domain. A uniform relativistic Lipschitz estimate and a compact tube about the
Newtonian solution give a common finite interval for nearby initial data.
Position and velocity converge uniformly, with order `c⁻²` for an initial
error of that order. The time-dependent polynomial family exercises the
trajectory theorem with mixed and spatial corrections.
The [GR guide](general-relativity.md)
records the exact scope and typed contracts.
The [shared geometry guide](smooth-geometry.md)
records the public API and exact checks. [Issue #52](https://github.com/MGYamada/ProjectAinos/issues/52)
records the completed delivery of the geometry, particle variation, curved forms
and time-dependent Newtonian limit.
[#43](https://github.com/MGYamada/ProjectAinos/issues/43)
is the first chart-regression gate. Einstein dynamics belongs to 5.2.
