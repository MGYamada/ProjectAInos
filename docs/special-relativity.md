# Minkowski geometry and relativistic kinematics

This is the implemented foundation for README §3.1 and
[issue #40](https://github.com/MGYamada/ProjectAinos/issues/40).
The [electrodynamics research plan](cinfty-electrodynamics.md) consumes
its form calculus and observer decomposition. Particle actions and equations
of motion belong to §3.2; charged-particle actions also require the shared
variational foundation tracked by #7. Maxwell's equations are not premises or
conclusions of this geometry library.
The [C∞ special relativity research plan](cinfty-special-relativity.md)
sets out the full §§1–14 program and the remaining §3.2 targets.

## Conventions and layers

The physics layer uses natural units `c = 1` and `(-+++)`.
`SpecialRelativity.metric` and `spacetimeManifold` choose `.timeNegative`.
The common APIs `minkowskiForm σ d`, `LorentzMetric σ d M`, and
`LorentzManifold σ d` always receive a `LorentzConvention` explicitly:

| Convention | Time sign s | Metric | Negative directions q |
|---|---:|---|---:|
| `timePositive` | +1 | `(+,-,…,-)` | d |
| `timeNegative` | −1 | `(-,+,…,+)` | 1 |

`MinkowskiModel d` remains `Fin (d+1) → ℝ`. `Minkowski.space` takes values in
`EuclideanSpace ℝ (Fin d)`. Only its Euclidean norm represents spatial length;
the norm of the ambient coordinate-function space does not.

The common normalized pairing and quadratic form are

\[
\operatorname{pair}(v,w)=v^0w^0-\langle\mathbf v,\mathbf w\rangle,
\qquad Q(v)=s_\sigma g_\sigma(v,v)=(v^0)^2-\|\mathbf v\|^2.
\]

`intervalQuadratic_convention` proves this equality. Metric negation uses
`LorentzMetric.opposite` and `LorentzManifold.opposite`, preserving symmetry,
nondegeneracy, smoothness and local Minkowski coordinates. The underlying
C∞ scheme is unchanged. General Lorentz manifolds require no global frame,
and local Minkowski coordinates remain a predicate, not a general premise.

## Proof map

Paths in this table are relative to `ProjectAinos/`.

| Stage | Modules | Main public results |
|---|---|---|
| 1 | `SmoothGeometry/Minkowski/{Convention,Basic,Dual}`, `SmoothGeometry/Lorentzian` | Explicit signs, normalized Q, metric negation, continuous `flat`/`sharp` inverses |
| 2 | `SmoothGeometry/Minkowski/{Causal,Isometry,Matrix,Affine}` | Convex future cone, affine causal partial order, Lorentz subgroup and matrix identities, determinant ±1, proper/orthochronous subgroups, translated Poincaré maps and scheme isomorphisms |
| 3 | `SmoothGeometry/Minkowski/{Observer,Reflection,ReflectionDeterminant}`, `SpecialRelativity/{Boost,Velocity,Rapidity}` | Rest-space positivity and dimension, unique observer split, passive boosts and inverse, future preservation, velocity-ball action and collinear composition |
| 4 | `SpecialRelativity/ProperTime` | Local integrability, Poincaré and reparameterization invariance, null proper time, unit four-velocity, inertial time dilation |
| 5 | `SmoothGeometry/DifferentialForm/{Flat,Exterior,Coordinates,Calculus,Naturality}` | Open-domain locality, d²=0, wedge normalization, graded Leibniz, pullback composition, d/pullback and wedge/pullback compatibility |
| 6 | `SmoothGeometry/DifferentialForm/{Hodge,HodgeBasis}`, `SmoothGeometry/Minkowski/{Hodge,HodgeNaturality,HodgeFour,TwoForm}` | Wedge-normalized Hodge, mathlib comparison, square/sign/naturality, six coordinate signs, observer reconstruction |
| 7 | `SmoothAlgebra/{RelEnergy,Poisson/LinearMomentum,Poisson/OrbitalCharge}`, `SpecialRelativity/{Hamiltonian,PoincareAlgebra,MassShellReduction}` | The energy `√(m² + Σ pᵢ²)` in a C∞-ring, the coordinate-time Hamiltonian of a free particle with its trajectories and its flow, the Poincaré algebra of the orbital charges and its family in `1/c`, the mass shell as a coisotropic ideal and the reduction of its future sheet |
| 8 | `SmoothGeometry/Minkowski/ReverseCauchySchwarz`, `SpecialRelativity/{MaximalProperTime,FreeMotion,ObserverEnergy,SpatialLegendre,NewtonianExpansion}` | The reverse Cauchy–Schwarz inequality, the greatest proper time of the inertial clock, the stationary curves of the free action as inertial motions and the Hessian in the velocity, the energy measured by an observer, the Legendre transformation on the ball of velocities, the expansion in `1/c` |
| Examples | `SpecialRelativity/{Examples,FormExamples}` | Nonzero boost and inverse, subluminality, clock rate, nonzero exact field and gauge identity |

All shared modules are independent of `SpecialRelativity`. Every library
module is imported by `ProjectAinos.lean`.

## Causality, symmetry and observers

`Timelike`, `Spacelike`, and `Lightlike` mean respectively `Q > 0`, `Q < 0`,
and `v ≠ 0 ∧ Q = 0`. `Causal` includes zero. `FutureCausal` is the closed cone
`‖space v‖ ≤ time v`; every nonzero member has positive time component.
`CausallyPrecedes p q` uses the affine displacement `q -ᵥ p`, and is reflexive,
transitive and antisymmetric. `intervalSq σ p q` is the signed metric interval;
it is distinct from Q.

`LorentzGroup d` is a subgroup of linear equivalences preserving `pair`.
`mem_lorentzGroup_iff σ` identifies it with the isometries of either metric.
The matrix API proves `Lᵀ g L = g` and `det L = ±1`. Proper transformations
have determinant +1. Orthochronous transformations preserve the future cone;
this is separate from spacetime orientation. `flat_natural` uses the inverse
Lorentz map on covectors, whereas vectors transform by the map itself.

`PoincareGroup.ofLinearTranslation L a` constructs `v ↦ L v + a` as an affine
isometry, including pure translations. `toSchemeIso` uses
`Manifold.schemeMap` and its composition laws for the corresponding smooth
scheme automorphism.

An `Observer d` has future-directed velocity u with `Q(u)=1`. Its `clock` is
`θᵤ(v)=pair(u,v)=sσ gσ(u,v)`. `restSpace` is the kernel of this functional,
`project` removes `θᵤ(v)u`, and `split` is a linear equivalence
`V ≃ ℝ × restSpace`. The rest space has dimension d, and its metric
`-pair = -sσ gσ` is positive definite. Clock and projection commute with
orthochronous transformations.

## Boosts, velocity and proper time

`Velocity d` is the Euclidean open unit ball. `boost β` is defined at zero
velocity as well as at nonzero velocity, using two metric reflections. Its
proved coordinate formula is the passive transformation

\[
t'=\gamma(t-\boldsymbol\beta\cdot\mathbf x),\qquad
\mathbf x'=\mathbf x+
\left(\frac{\gamma^2}{1+\gamma}\boldsymbol\beta\cdot\mathbf x-\gamma t\right)
\boldsymbol\beta.
\]

The factor has no division by `‖β‖²`. The boost is proper and orthochronous;
`boost_neg_inverse` proves its inverse. Future unit observers are equivalent
to velocities. This supplies a `MulAction` of the orthochronous Lorentz group
on the velocity ball and proves that transformed speeds remain below one.
`transform_collinear` gives `(a-b)/(1-ba)` for a passive boost;
`rapidity_add` gives the additive `artanh` law for `(a+b)/(1+ab)`.
No theorem identifies a product of non-collinear boosts with a single boost.

`properTime γ a b` is the interval integral of `sqrt (Q (deriv γ t))`.
`TimelikeSegment γ a b` records `a ≤ b`, C¹ regularity in a neighbourhood
of every point of the closed interval, and future timelike derivatives.
The integral is total as a Lean definition; its physical interpretation uses
these hypotheses. Integrability needs the local C¹ condition.

Poincaré invariance only needs differentiability on the interval.
`properTime_reparametrize` assumes C¹ regularity of f near each source point
and of γ near its image, and `deriv f ≥ 0` on the interval. It therefore
includes orientation-preserving C¹ reparameterizations and proves equality
with the integral between `f a` and `f b`. `fourVelocity_unit` and
`fourVelocity_metric` require a timelike tangent and prove Q=1 and g(U,U)=−1.
Null proper time is proved separately by `properTime_null`; no null
four-velocity normalization theorem is asserted.

## Flat forms and Hodge normalization

`Form E k := E → E [⋀^Fin k]→L[ℝ] ℝ` is metric independent.
`exteriorDerivative` reuses mathlib's `extDeriv`. The calculus on open domains
uses regularity and equalities on the domain; locality and restriction
lemmas remove dependence on ambient extensions. Pullbacks use `fderiv`, with
explicit differentiability hypotheses in their laws. Interior product inserts
the vector into the first slot.

For finite coordinate spaces, `toExterior` identifies continuous alternating
forms with `Λᵏ E*` through the determinant pairing. `wedgeFiber` and `wedge`
use this proved equivalence, and `wedge_one_one` fixes
`(a ∧ b)(v,w) = a(v)b(w) - a(w)b(v)`. The graded Leibniz theorem is expressed
in the full exterior algebra, where all terms have degree k+l+1, avoiding
casts between different parenthesizations of this degree. The equality is
proved at each point under differentiability there.

`SpacetimeOrientation.standard` means `dt ∧ dx ∧ dy ∧ dz` in four dimensions;
`reversed` is the opposite orientation. `hodgeFiber` and `hodgeForm` receive
both orientation and signature explicitly, with `hkl : k+l=d+1`.
`hodgeFiber_pairing` proves the defining equation

\[
\alpha\wedge\star\beta=\langle\alpha,\beta\rangle_{g^{-1}}\operatorname{vol}.
\]

The implementation uses the perfect wedge pairing and the inverse metric.
`hodge_eq_mathlib_inverse` proves that this normalization equals
`(-1)^(k*l)` times the inverse of mathlib's opposite-degree Hodge map.
The exterior-power map is transported to continuous forms through
`toExterior_hodgeFiber`, not identified without proof.

The proved laws are `star² = (-1)^(k*l+q)`, reversal of orientation changing
star's sign, and `star_{-g} = (-1)^k star_g` for the same orientation.
`hodgeFiber_pullback` and `hodgeForm_pullback` prove compatibility with proper
Lorentz pullbacks. In four dimensions on two-forms, `star² = -1` and
`star_{-g} = star_g`. All six basis signs are checked; in particular,

\[
\star(dt\wedge dx)=-dy\wedge dz,\qquad
\star(dy\wedge dz)=dt\wedge dx.
\]

For an observer u, `reconstructTwoForm_contractions` proves

\[
F=\theta_u\wedge\iota_u F-\star(\theta_u\wedge\iota_u\star F).
\]

It works for both signatures and orientations, and for arbitrary u and F
satisfying the bundled observer hypotheses. This is #8's entry point for
electric/magnetic decomposition; sign conventions for naming those physical
fields remain with electrodynamics. `coordinateField_reconstruction` applies
it to the nonzero field `d(t dx) = dt ∧ dx`. The gauge check allows any C²
zero-form χ and proves `d(A+dχ)=dA`.

The [shared geometry guide](smooth-geometry.md) describes the native curved
extensions for forms, Hodge, connections and curvature. No global-frame
assumption is added to the manifold interface.

## Relativistic particle mechanics: the algebraic layer

These statements use the canonical Poisson structure of the
[shared algebra](smooth-algebra.md#poisson-structures) and no chart of
velocities. They are the targets SR-D7, SR-D8 and SR-C6 of the
[research plan](cinfty-special-relativity.md), for every number `d` of space
dimensions and for a mass `m ≠ 0`.

**The energy in a C∞-ring.** The function `√(1 + Σ wᵢ²)` is smooth on all of
`ℝᵈ`, so it is an operation of every C∞-ring.
`relEnergy m π = m · √(1 + Σ (πᵢ/m)²)` is the energy of the momenta `π`, and
`relEnergyInv m π` is its inverse. The proofs use `relEnergy_mul_self`
(`E² = m² + Σ πᵢ²`), `relEnergy_mul_relEnergyInv` (`E E⁻¹ = 1`) and
`SmoothDerivation.apply_relEnergy` (`D E = E⁻¹ Σ πᵢ D πᵢ`); after these three
no derivative of a square root appears. On real numbers and for `m > 0`,
`relEnergy_real` gives `√(m² + Σ πᵢ²)`, and `sum_sq_relEnergyInv_mul_lt_one`
gives `Σ (πᵢ/E)² < 1`.

**The Hamiltonian of a free particle (SR-D7).**
`FreeParticle.hamiltonian d m` is `relEnergy m p` in `PhaseSpace (Fin d)`.

| Statement | Declarations in `FreeParticle` |
| --- | --- |
| `{qᵢ, H} = pᵢ/H` and `{pᵢ, H} = 0` | `canonical_q_hamiltonian`, `canonical_p_hamiltonian` |
| A curve is a trajectory if and only if `ṗ = 0` and `q̇ = p/H` | `isTrajectory_iff` |
| `Σ (pᵢ/H)² = 1 − m²/H²`, and the speed is less than one at every point | `sum_velocity_mul_self`, `sum_sq_hamiltonianField_lt_one` |
| The momentum and `qᵢ pⱼ − qⱼ pᵢ` are integrals, and `{H qᵢ, H} = pᵢ` | `isIntegral_p`, `isIntegral_angularMomentum`, `canonical_centreOfEnergy_hamiltonian` |
| `q₀ + t p₀/H(p₀)`, `p₀` is a trajectory, and every trajectory has this form | `isTrajectory_motion`, `realCurve_eq_motion` |
| The flow is defined for all times and points, it preserves the volume, and it is `(q, p) ↦ (q + t p/H, p)` | `flowDomain_hamiltonianField`, `measurePreserving_hamiltonianFlow`, `flow_hamiltonianField` |

The Hamiltonian field is bounded by one, so completeness follows from the
criterion of linear growth of the shared geometry. The comparison with the
Lagrangian `−m√(1 − Σ vᵢ²)` on the ball of velocities, and through it with
`free_stationary_iff`, is SR-D4 and is not proved.

**The Poincaré algebra (SR-C6).** For a matrix `η`,
`PhaseSpace.orbitalCharge η μ ν` is `x_μ p_ν − x_ν p_μ` with
`x_μ = Σ η μ α q α`. For a symmetric `η`,
`canonical_orbitalCharge_orbitalCharge` is
`{J_μν, J_ρσ} = η_μρ J_νσ − η_νρ J_μσ + η_νσ J_μρ − η_μσ J_νρ`, and
`canonical_orbitalCharge_p` is `{J_μν, p_ρ} = η_μρ p_ν − η_νρ p_μ`; the
matrix may be degenerate. If `G` is the inverse of `η`, the charges have zero
bracket with `Σ G σ τ p_σ p_τ` (`canonical_orbitalCharge_momentumQuadratic`).
`Poincare.lorentzCharge σ d μ ν` is the case of the Minkowski metric of the
convention `σ` on `PhaseSpace (Fin (d + 1))`, with the time at the index `0`.
For all matrices, `PhaseSpace.linearMomentum A = Σ A μ ν q μ p ν` satisfies
`{ℓ_A, ℓ_B} = ℓ_{BA − AB}`.

On the phase space of the initial data and with `ε = 1/c`, the charges are
`pᵢ`, `Poincare.angularMomentum d i j` and
`Poincare.boostCharge d m ε i = inertia · qᵢ`, where
`Poincare.inertia d m ε = √(m² + ε² Σ pᵢ²)` is the energy divided by `c²`.
For every real `ε`,

`{Kᵢ, pⱼ} = δᵢⱼ · inertia`, `{Kᵢ, Kⱼ} = −ε² Mᵢⱼ`,
`{Kᵢ, inertia} = ε² pᵢ`, `{Mᵢⱼ, Kₖ} = δₖᵢ Kⱼ − δₖⱼ Kᵢ`.

At `ε = 0` the inertia is the mass (`inertia_zero`), so these are the
relations of the Galilei algebra, with the mass as the central term of
`{K, p}`. The family is indexed by a real number; that it is smooth in `ε` is
not stated.

**The mass shell (SR-D8).** In `MassShell`, the phase space of an event and
its momentum covector is `PhaseSpace (Fin (d + 1))`.

| Statement | Declarations in `MassShell` |
| --- | --- |
| The ideal of `η⁻¹(p, p) − σ m²` is coisotropic, for both conventions | `isCoisotropic_shellIdeal` |
| The momenta and the Lorentz charges are in its normalizer | `p_mem_normalizer_shellIdeal`, `lorentzCharge_mem_normalizer_shellIdeal` |
| For `(−+++)`, `η⁻¹(p, p) + m² = (E − p₀)(p₀ + E)` | `shellFunction_eq` |
| The normalizer of the shell is contained in the normalizer of the future sheet `(p₀ + E)` | `normalizer_shellIdeal_le` |
| `Qᵢ = xᵢ − x⁰ pᵢ/E`, `Q⁰ = x⁰`, `Pᵢ = pᵢ`, `P₀ = p₀ + E` is canonical and has an inverse | `isPoissonHom_toShellCoordinates`, `toShellCoordinates_ofShellCoordinates`, `ofShellCoordinates_toShellCoordinates` |
| The reduced ring of the future sheet is the phase space of the initial data, as a Poisson C∞-ring | `reductionHom_bijective`, `isPoissonHom_reductionHom` |
| The class of `p₀` is `−H`, the class of `J₀ᵢ` is `H qᵢ`, and the class of `Jᵢⱼ` is `qᵢ pⱼ − qⱼ pᵢ` | `reductionHom_initialData`, `initialData_p_zero`, `initialData_lorentzCharge_zero_succ`, `initialData_lorentzCharge_succ_succ` |

The change of variables is canonical because the matrix of the second
derivatives of the energy is symmetric (`bracket_velocity_q_succ`). In the new
variables the future sheet is `P₀ = 0`, and the theorem on cyclic
co-ordinates of [mechanics](mechanics.md) gives the reduced ring. The
quotient ring is not compared with the shell as a manifold (SR-D5). The
[notes](special-relativity-notes.md) SR03–SR06 record the decisions.

## The motion of a free particle

**The reverse Cauchy–Schwarz inequality.** For two vectors of the closed
future cone, `sqrt_mul_sqrt_le_pair` is `√Q(v) √Q(w) ≤ pair v w` and
`sqrt_add_sqrt_le` is the reverse triangle inequality
`√Q(v) + √Q(w) ≤ √Q(v + w)`. For an observer `u`,
`Observer.intervalQuadratic_eq` is `Q(w) = (u.clock w)² − restForm(w⊥, w⊥)`,
`Observer.sqrt_le_clock` is `√Q(w) ≤ u.clock w`, and
`Observer.eq_smul_of_clock_eq_sqrt` is the case of equality.

**The inertial clock (SR-K4, §3).** Let `γ` be `C¹` near every point of
`[a, b]` with a future timelike velocity there, and `a < b`.
`TimelikeSegment.futureTimelike_displacement` shows that `γ b − γ a` is future
timelike, and `TimelikeSegment.properTime_le_properSpeed` is
`τ[γ] ≤ √Q(γ b − γ a)`; the right-hand side is the proper time of the inertial
motion between the two events (`properTime_inertialSegment`).
`TimelikeSegment.properTime_eq_properSpeed_iff` shows that equality holds if
and only if the unit four-velocity is that of the displacement at every time
of `[a, b]`. `sum_properTime_le_properSpeed` is the inequality for finitely
many such pieces with matching endpoints. The proof integrates
`√Q(γ̇) ≤ u.clock γ̇` for the observer `u` in the direction of the displacement.

**The stationary curves (SR-D2, §8).** For a `C²` curve in three space
dimensions with a timelike velocity on `[a, b]` and `a < b`:

| Statement | Declaration |
| --- | --- |
| The action is stationary iff the momentum covector `m U♭` has zero derivative on `(a, b)` | `free_stationary_iff_deriv_kineticMomentum` |
| For `m ≠ 0`, iff the unit four-velocity is constant on `[a, b]` | `free_stationary_iff_fourVelocity_const` |
| For `m ≠ 0`, iff `γ t = γ a + τ(t) • U` on `[a, b]`, with `τ(t)` the proper time from `a` | `free_stationary_iff_inertial` |
| The acceleration is orthogonal to the velocity | `pair_fourVelocity_deriv` |
| The Hessian in the velocity is `w ↦ −(m/√Q(v)) (w♭ − (⟨v, w⟩/Q(v)) v♭)` | `hasFDerivAt_kineticMomentum`, `velocityHessian_apply` |
| For `m ≠ 0` its kernel is the line of the velocity and its rank is three | `ker_velocityHessian`, `finrank_range_velocityHessian` |

The parameter of a stationary curve is arbitrary: the curve is inertial in
its proper time. The degenerate Hessian is the infinitesimal form of this
freedom, and it is the reason why the Legendre transformation is taken in the
time of an observer.

**The energy measured by an observer (SR-D3).** For an observer `u` and a
momentum vector `p`, in any number of space dimensions:
`observerEnergy u p = pair u p`, `observerMomentum u p = p − E u` in the rest
space of `u`, and `observerVelocity u p = p⊥/E`. `observerEnergy_pos` and
`properSpeed_le_observerEnergy` show `E ≥ √Q(p) > 0` for a future timelike
`p`; `observerEnergy_sq` is `E² = Q(p) + |p⊥|²`, with the length of the rest
space; `restForm_observerVelocity_lt_one` is `|v| < 1`;
`observerEnergy_transform` is the invariance under a transformation of both
the observer and the particle; and `observerEnergy_change` is
`E' = γ E − ⟨γ w, p⊥⟩` for a second observer.

**The Legendre transformation (SR-D4).** In `FreeParticle`,
`lagrangian d m = −m √(1 − Σ vᵢ²)` on the ball `Σ vᵢ² < 1`, for every `d`.

| Statement | Declarations in `FreeParticle` |
| --- | --- |
| `legendre m v = m γ v` and `velocityOfMomentum m p = p/√(m² + Σ pᵢ²)` are inverse to each other, for `m > 0` | `velocityOfMomentum_legendre`, `legendre_velocityOfMomentum` |
| The energy `Σ pᵢ vᵢ − L` is `√(m² + Σ pᵢ²)` | `energy_eq_relEnergy` |
| The momentum covector of the Lagrangian is `Σ (m γ vᵢ) dvᵢ` | `hasFDerivAt_lagrangian`, `momentum_lagrangian` |
| The action is stationary iff the velocity is constant on `[a, b]`, for `m > 0` | `stationary_iff_deriv_const` |
| A curve of the phase space is a trajectory of `√(m² + Σ pᵢ²)` iff its speed is less than one, its momentum is the Legendre transform of its velocity, and the momentum has zero derivative | `isTrajectory_iff_legendre` |
| In three dimensions the Lagrangian of space-time on a graph `t ↦ (t, x(t))` is this Lagrangian, and the two actions are stationary together | `freeLagrangian_graph`, `free_stationary_graph_iff` |

**The expansion in `1/c` (SR-K5).** In `Newtonian` the speed of light is a
parameter: `energy m c v = m c²/√(1 − v²/c²)`, `lagrangian`, `momentum` and
`clockRate`. For `Σ vᵢ² ≤ V²`, `c ≥ 2V` and `c > 0`:

`|E − m c² − ½ m v²| ≤ |m| V⁴/(2c²)`, `|L + m c² − ½ m v²| ≤ |m| V⁴/(2c²)`,
`|pᵢ − m vᵢ| ≤ |m| V³/c²`, `|√(1 − v²/c²) − (1 − v²/(2c²))| ≤ V⁴/(2c⁴)`

(`abs_energy_sub_le`, `abs_lagrangian_sub_le`, `abs_momentum_sub_le`,
`abs_clockRate_sub_le`). They follow from the exact identities for
`s = √(1 − x)`, `sqrt_one_sub_bounds` and `inv_sqrt_one_sub_bounds`. These are
estimates for functions of the velocity; the convergence of trajectories is
not stated. The [notes](special-relativity-notes.md) SR07–SR09 record the
decisions.

## Verification

The required **Lean build** CI job builds with warnings as errors, checks root
imports and public consumer APIs, and audits transitive axiom dependencies.
The local counterparts are:

```sh
lake build --wfail ProjectAinos
lake exe mk_all --check --lib ProjectAinos
lake env lean -DwarningAsError=true checks/SmoothGeometryAPI.lean
lake env lean -DwarningAsError=true checks/SpecialRelativityAPI.lean
lake env lean -DwarningAsError=true checks/RelativisticEnergyAPI.lean
lake env lean -DwarningAsError=true checks/RelativisticHamiltonianAPI.lean
lake env lean -DwarningAsError=true checks/RelativisticFreeMotionAPI.lean
lake env lean -DwarningAsError=true checks/AxiomAudit.lean
```

The public API checks use default elaborator options. Exact examples distinguish
timelike, spacelike, lightlike and zero vectors; use velocity 3/5, factor 5/4
and clock rate 4/5; and check the nonzero field and Hodge signs. The axiom
allowlist is `propext`, `Classical.choice`, `Quot.sound`. No additional axioms
or unfinished proofs are used.
