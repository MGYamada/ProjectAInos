# Proof Development

This record traces the development of the Lean proofs. The research plan and subject outline are in the [project README](../README.md).

The classical-field design from [issue #8](https://github.com/MGYamada/ProjectAInos/issues/8)
is now maintained in three research manuscripts:
[C∞ special relativity](cinfty-special-relativity.md),
[C∞ electrodynamics](cinfty-electrodynamics.md), and
[C∞ general relativity](cinfty-general-relativity.md).
Their dictionaries cover all 119 sections of L&L Volume 2 and separate existing
proofs from future targets. This documentation migration adds no Lean proofs;
the completion of the design issue refers to that migration.

## Thermodynamics Proof Development

Issue #27 replaces the physical atomic-only ECH specialization with composite
generators whose label conservation survives A1–A6. `AtomicProcesses` proves
normal forms and the exact energy/amount accessibility criterion for heating,
mixing and separation. `AtomicReservoir` constructs all simple-system and
thermal-family premises on the canonical atoms and invokes that specialization.
`AtomicObstruction` proves the old relation cannot perform the explicit A7
mixing example. Build success alone was not the nonvacuity criterion.

The Lean library derives spectator cancellation from A6, constructs the real Grothendieck completion and its process cone, and proves order reflection and sequential order closedness. Under exchange comparison and a nonzero process direction, the real-cut construction gives an entropy coordinate. Linear extension then gives the entropy principle on matched conservation sectors, the relative cutoff formula, and the classification of entropy extensions by conserved linear quantities.

Concrete models cover nonnegative real states, two independent monotones, lexicographic failure of sequential order closedness, equality-only accessibility, and a conserved amount coordinate. The ideal-gas development proves homogeneity, concavity, and the fixed-amount operational entropy principle. Its composite algebraic consistency model identifies the completion with entropy-amount pairs and the conservation quotient with amount. Composition in this model uses the sum of separate-box entropies; this construction does not supply a geometric simple system or thermal family.

The [reservoir model](../ProjectAInos/Thermodynamics/ReservoirModel.lean) supplies a nonempty family satisfying the full simple-system and thermal interfaces, closed under positive scaling and thermal joins. Entropy equals energy and pressure is zero, so it exercises the universal-isotherm case. The [join assumption audit](thermodynamics-join-audit.md) distinguishes contact and splitting from the geometric regularity required of joined systems.

The physical development constructs coherent finite composites and their adiabatic quotient. It proves composition-label conservation for the A1–A6 closure of nonreactive elementary processes and constructs common scaled products for states with equal composition labels. Forward sectors are convex and relatively closed in an open convex finite-dimensional equilibrium domain. Irreversibility and unique finite-slope support imply nonempty interior; the supporting plane is inherited at every relative-boundary point. Energy orientation is constant throughout each simple system, giving the fixed-work accessibility criterion. The boundary is a differentiable graph whose derivative is the negative pressure form. Locally Lipschitz pressure gives local uniqueness of these graphs, and boundary connectedness propagates reversibility. These results establish simple-system comparison, strict nesting of distinct forward sectors, and openness of strict reference strips. Energy reflection handles the opposite orientation without changing the physical premises.

Typed thermal families connect actual scaled coordinate domains, thermal joins, and the positive scaled-copy clause of T2. Thermal contact fixes a common energy orientation across systems, and the zeroth law gives independent scaling invariance. Simple-system comparison and transversality establish local mixture intervals; connectedness joins their affine reference lines. These results give single-system product comparison and normalized concave continuous entropy. Thermal equilibrium between two copies is equivalent to fixed-total-energy entropy maximization, or intersection of their supporting-slope intervals. This criterion requires no extra differentiability assumption on entropy.

The location-of-isotherms dichotomy and crossed-calibrator existence are proved, including the universal-isotherm case. A concrete splitting and mixing cycle establishes thermal equilibrium between a joined state and each component. Pairwise calibrators align all simple-system reference directions, giving comparison in every finite scaled product. Canonical coordinate atoms provide the finite composite presentation and fixed-composition labels. Common-product realization then gives ECH for nonreactive accessibility. The final physical entropy endpoints take the explicit geometric and thermal premises, with no CH, ECH, or calibrator-existence assumption.

The reaction development defines direct, chained, and catalytic transition costs, proves their positive homogeneity, and selects compatible entropy constants by Hahn–Banach. The physical entropy theorem supplies the required calibrated monotonicity within each composition label. Absence of sinks is expressed using actual transitions, independently of entropy or costs. The resulting total entropy is additive, extensive, monotone for all accessible transformations, and characterizes accessibility when composition labels match. Infinite costs for unreachable labels remain allowed, including after adding catalysts.

The current physical endpoints use A1–A7, S1–S3 and T1–T4, with M added for reactions. Every admitted primitive simple system satisfies transversality T4; no extra T5 assumption is needed for this scope. Extending the theory to systems without T4, or proving temperature regularity, belongs to subsequent work. The ideal-gas phase-volume derivation remains in the statistical-mechanics stage of the research plan.

The public physical endpoints are in [PhysicalEntropyPrinciple](../ProjectAInos/Thermodynamics/PhysicalEntropyPrinciple.lean); [AtomicSystems](../ProjectAInos/Thermodynamics/AtomicSystems.lean) specializes them to canonical coordinate atoms. The [mathematical guide](thermodynamics.md) presents the algebraic theory, physical comparison, reactions, and models with proof links. The [implementation checklist](thermodynamics-status.md) maps the eight planned stages to their proof modules and scope.

Every completed stage must pass the warning-free Lean build, root-import check, and transitive axiom audit. Physical premises remain explicit in theorem statements. [Lean library entry point](../ProjectAInos.lean)

[Thermodynamics formalization notes](thermodynamics-notes.md) record the mathematical distinctions and modeling decisions exposed by the proofs, together with their current proof status.

See the [Landau–Lifshitz correspondence](landau-lifshitz.md) for the Mechanics proof targets and reference volumes for the other subjects.

## Shared Smooth Algebra and Geometry

The shared mathematical layers for Mechanics, Special Relativity, Electrodynamics, and General Relativity (research-plan topics 2–5) live in `ProjectAInos/SmoothAlgebra` and `ProjectAInos/SmoothGeometry`, independently of the physics. Together with the shared `Variational` layer, they have an acyclic import graph excluding project physics and vendored Yang–Mills. C∞-rings have finite smooth operations, substitution laws, and compatibility with a commutative real algebra. Morphisms preserve every smooth operation; their real-algebra homomorphisms are derived. The concrete models are ℝ, products, and C∞(ℝⁿ), including dimension zero. The smooth-function ring is proved free on its coordinate functions, with evaluation and pullback as morphisms. A nonpolynomial check proves `exp(a + b) = exp(a) * exp(b)` in every C∞-ring.

The geometry follows mathlib's progression from ringed spaces through `Spec` to `Scheme`, with Joyce's real points and C∞ operations. Smooth congruence quotients and cutoff functions construct point localizations with their universal property. Locally represented sections form the structure sheaf, and its stalks are identified with the localizations. The resulting spectrum functor supplies the actual affine models in the local-affine definition of a C∞ scheme. Affine schemes are the essential image of this functor. Examples include affine spaces and the empty scheme.

Free C∞-rings on arbitrary sets give general localizations with their smooth universal property. Their spectra are identified with the surviving-point subspaces; principal localizations give open immersions. These supply open subschemes and pullbacks along open immersions. Open gluing data construct actual C∞ schemes, with descent and uniqueness of compatible morphisms proved as a categorical colimit. The manifold comparison identifies the Euclidean smooth-function sheaf with its affine spectrum, then proves local affineness for boundaryless finite-dimensional smooth manifolds using coordinate charts. Smooth maps induce scheme morphisms with identity and composition laws.

The algebra layer also differentiates. Partial derivatives of smooth operations are again operations, with the chain rule as an identity between operations and commuting second partial derivatives. Dual numbers `A[ε]` over any C∞-ring carry the smooth operations whose infinitesimal part is the first-order Taylor term. C∞-derivations have the chain rule as their only law; the Leibniz rule and real linearity follow. Vector fields form a Lie ring under the commutator and correspond to the morphisms `A → A[ε]` lifting the identity, and derivations of `C∞(ℝⁿ)` correspond to tuples of values on the coordinates. This is the first algebraic stage of the mechanics plan ([issue #74](https://github.com/MGYamada/ProjectAInos/issues/74)). [Smooth-algebra guide](smooth-algebra.md#partial-derivatives-dual-numbers-and-derivations)

`LorentzMetric` equips the actual tangent bundle with a smooth bilinear form of Lorentz signature, without requiring a global frame. `LorentzManifold.toScheme` uses the same manifold construction for every such metric. Minkowski space is an instance with constant coefficients, a proved affine scheme comparison, and proved local inertial coordinates. The [smooth-geometry guide](smooth-geometry.md) and [formalization notes](smooth-geometry-notes.md) record these constructions and their scope. The Γ–Spec adjunction, full faithfulness of the manifold construction and universal cotangent modules are subsequent stages; connection and curvature progress is recorded below.

The first GR 5.1 increment adds metric duality on tangent/cotangent fibres.
Bijectivity follows from the existing pointwise Lorentz signature. The
inverse metric's smoothness is proved by expressing it as inversion in
hom-bundle coordinates, so no smooth frame is an extra hypothesis.
Smooth section lowering/raising, inverse pairing, coordinate naturality,
and compatibility with the flat API and sign reversal are proved.
Fibrewise bilinear pullback and contraction supply the initial tensor API.
Finite mixed tensors are constructed by recursively taking native smooth
hom bundles, retaining the actual tangent/cotangent fibres. Coordinate
coefficients come from geometric sections and obey the atlas transition
law. Composition and intrinsic trace have smooth-bundle proofs; the trace
functional itself is smooth, so partial contraction retains uncontracted
arguments. Coordinate naturality of partial contraction and the
inverse-metric component formula are proved. Smooth field pullback along
diffeomorphisms is constructed using the actual derivative and smooth
inversion in bundle charts. Identity/composition/inverse laws and
commutation with full and partial contraction are proved. Covariant pullback
now also works for arbitrary smooth maps between independent finite-dimensional
models. Fixed-map pre/postcomposition constructs continuous linear maps on the
native iterated hom fibres. A coordinate identity proves smoothness without
putting norms on those fibres or assuming an inverse derivative. Induction gives
all ranks, identity/composition laws, constant-map vanishing in positive rank,
and agreement with the diffeomorphism API. Time-axis restriction, its degenerate
points, a constant map, and a nonconstant singular projection are proved examples.
Default-option typed examples fix the independent models and the main contracts.
Exact SymPy checks additionally test nonlinear composition with a nonsymmetric
tensor. Tensor products and typed slot permutations now use the same hom
bundles. Testing on local smooth arguments proves regularity and gives
pointwise evaluation formulas. Opposite-variance contraction moves the
selected slots to the end and takes the trace of the cotangent endomorphism.
A basis–dual-basis sum gives its components. Each operation commutes with
diffeomorphism pullback, and the shear regression uses a nonsymmetric
covector product to check the slot order.

For the chart regression, the shear `(t,x) ↦ (t,x+t²)` and its inverse are
proved smooth and turned into an actual chart in the maximal atlas.
Pulling back the Minkowski metric constructs a smooth `LorentzMetric` with
nonconstant coefficients. Lean verifies its derivative, coefficient
transformation, duality and opposite-sign covariance. A nonconstant
`dX ⊗ dX` tensor has metric contraction 1 in both charts. Typed API examples
are required CI checks; exact SymPy computations run separately. This
increment addresses #43 within #52.

The next increment constructs the Lorentz Levi-Civita connection from the
Koszul formula and `sharp`, using mathlib's native `CovariantDerivative`.
Tensoriality of Koszul in its direction/test fields supplies the continuous
linear map on each actual tangent fibre. Covariant-derivative laws, metric
compatibility and vanishing torsion are proved. Nondegeneracy and local
extensions of arbitrary tangent vectors prove uniqueness on differentiable
sections. No positive-definite metric or global frame is introduced.

Regularity is proved separately: local smooth-field tests characterize
`C^n` finite-rank hom sections, the Koszul terms lose at most one derivative,
and the smooth inverse metric raises the result. The connection takes
`C^(n+1)` fields to `C^n` hom sections and satisfies mathlib's
`ContMDiffCovariantDerivative` at every finite order and at ∞. Negating the
metric leaves the constructed connection unchanged.

On the coordinate model, Lean derives the Christoffel formula from this
connection and proves its smoothness, symmetry and action on arbitrary
differentiable fields. The standard Minkowski coefficients vanish. The
nonlinear two-chart example now has Lean proofs of all eight connection
coefficients (`Γˣ_tt = 2` is the only nonzero one), the actual transition's
Hessian, and the corresponding connection transformation identity. Typed
examples fix the finite-regularity and coordinate contracts. Exact SymPy
checks also cover the conformal metric's coefficients; that curved example
still needs Lean proofs.

Koszul and Levi-Civita naturality hold under
smooth metric-preserving maps, without global bijectivity. The native
connection theorem derives tangent invertibility from nondegeneracy and equal
dimension, and needs only pointwise differentiability of the target field.
Pullback metrics have proved smoothness, signature and identity/composition/sign
laws. Open inclusions are proved local diffeomorphisms, yielding an actual
restricted metric and the compatibility of its connection with the ambient
one. The nonlinear shear metric and arbitrary-field connection identity now
also instantiate these general results.

The manifold-chart interface now derives the inverse-metric Christoffel
formula, smoothness, lower-index symmetry and sign invariance in every smooth
chart. Local coordinate-field expansions and the Leibniz rule prove the
coefficient transformation law on arbitrary chart overlaps, including the
actual transition Hessian. The nonlinear two-chart regression specializes
this general theorem: the standard chart has `Γˣ_tt = 2`, while the same
metric has zero coefficients in the inertial chart. Typed API examples fix
the full law with only atlas and overlap hypotheses. Stage B's proof endpoints
are implemented and merged through [#52](https://github.com/MGYamada/ProjectAInos/issues/52).

The stage C increment constructs `LorentzMetric.curvature` as a continuous
trilinear map on the actual tangent fibre. The generic
`Tensor.ContMDiffTensorialAt` API proves that linearity over locally `Cⁿ`
scalar germs forces dependence only on the fibre value. This handles the
two derivatives in curvature without requiring global smooth extensions.
The local `C²` commutator formula, first-pair antisymmetry and algebraic
first Bianchi identity are proved. Testing on local smooth fields establishes
native hom-bundle smoothness. Metric-preserving smooth maps intertwine
curvature; invertibility follows from the metric, and global bijectivity is
unnecessary. Ricci uses `trace (w ↦ R(w,u)v)` and scalar curvature uses the
inverse metric. Their smoothness, tangent-coordinate contraction formulas,
coordinate naturality and sign-reversal laws are proved. The standard and
nonlinear Minkowski metrics have zero Riemann, Ricci and scalar curvature
in Lean.

The completed stage C endpoints now include the full Christoffel curvature
formula and tensor overlap law on arbitrary smooth charts. Local scalar
derivative commutation and differentiated metric compatibility prove
curvature's skew adjointness, last-pair antisymmetry and pair interchange.
Pointwise Lorentz signature coordinates then prove Ricci symmetry without
a global frame. A smooth positive conformal rescaling constructs the native
metric `exp(2x²)(-dt²+dx²)`; its connection, all curvature components,
Ricci matrix `diag(2,-2)` and scalar `-4 exp(-2x²)` are proved. At the
origin its connection coefficients vanish but its curvature does not.
Exact SymPy checks independently cover the same examples and covariance
of nonzero conformal curvature under the shear.

Stage C is merged into `main`. The stage D increment constructs
`covariantAlong` on the actual tangent fibres using chart components and
the native Levi-Civita connection. A transition-Jacobian product rule and
the connection's chart decomposition prove chart independence without
assuming immersion, nonzero velocity or an ambient extension. Locality,
linearity, Leibniz, ambient compatibility and metric compatibility are
proved. The metric proof uses normed models only for coordinate bilinear
forms; it adds no normed or positive-definite structure to tangent fibres.

`IsParallelOn` and `IsGeodesicOn` include regularity at each parameter,
including regular extensions when a closed interval is used. Parallel
metric pairings and geodesic velocity norms are constant on convex sets.
The arbitrary-chart affine ODE equivalence and the full acceleration
reparametrization formula are proved, including zero parameter speed.
Affine changes, including reversal, preserve the affine geodesic equation.

`MotionODE` derives a smooth phase field `(q,v) ↦ (v,−Γ(q)(v,v))`
from the constructed connection. Mathlib's Picard–Lindelöf theorem supplies
a local solution; a smaller interval keeps it in the chart target.
The ODE improves its regularity to `C²`, and the inverse chart lifts it
to a native geodesic with the prescribed actual tangent velocity.
Local Lipschitzness follows from smoothness, giving germ uniqueness for
both the phase equation and intrinsic geodesics. No existence, Lipschitz
or tangent-trivialization premise is added to the public theorem.

The standard Minkowski affine lines work for both signatures and all
dimensions. In the nonlinear shear chart, the path `(s,−s²)` is a geodesic,
and `(a,b−2sa)` is a parallel field with constant inertial components `(a,b)`.
`AlongCurveRegularity` reconstructs native regularity from chart components.
`ParallelLocal` derives the time-dependent linear equation
`V' = -Γ(γ)(γ',V)` and its local existence and uniqueness from the ODE API.
Solving for finitely many basis vectors produces a common local frame for
all initial vectors. Pairing against this frame propagates equality on
convex sets without a global Hausdorff premise. In particular, nonzero null
geodesic velocity cannot become zero.

Overlapping frames agree after matching their initial values. Gluing them
and using connectedness proves existence along each prescribed finite
`C²` segment, with regular extensions at its endpoints. The resulting
`parallelTransport` is a continuous linear equivalence of actual tangent
fibres. Its characterization by every parallel field proves metric
preservation, identity, reversal, subdivision and parameter-change laws.
The nonlinear-chart example evaluates this intrinsic map as
`(v₀,v₁) ↦ (v₀,v₁−2(s₁−s₀)v₀)`.
Exact SymPy checks also cover endpoint transport, subdivision, reversal,
a nowhere-zero null parallel field, and the full nonaffine acceleration
transformation.

`RegularPath` packages a `C²` segment with named endpoints and its actual
continuous `Path`. Canonical equality casts identify tangent fibres.
`PiecewisePath` retains a finite decomposition and constructs its continuous
path through ordinary path concatenation. `HasParallelLift` is defined
independently of transport by native parallel fields on the pieces with
matching junction values. Its equivalence with the composed endpoint map
proves existence, endpoint uniqueness and uniqueness of the transport map.
The fields concatenate to a continuous path in the actual tangent bundle
projecting exactly to the underlying path. Reversal and regrouping preserve
the corresponding transport laws, without requiring matching velocities.
Model affine segments and a time-axis/space-axis corner have native proofs
for Minkowski geometry. The separate symbolic experiment also checks
segment ODEs, composition and reversal around a rectangle in the conformal
curved metric; that rectangle holonomy is not yet a Lean theorem.
`Manifold.QuadraticChart` realizes an invertible Jacobian and a symmetric
Hessian by a polynomial local coordinate change. Its analytic inverse is
restricted to a common smooth neighborhood, then composed with a manifold
chart; the manifold itself needs only a smooth structure. `LocalInertial`
bundles the existing Christoffel coefficients as a bilinear map on the
coordinate model. A chosen Lorentz basis gives `L`, and the correction
`L(q-q₀) + ½ L(Γ(q-q₀,q-q₀))` cancels the connection coefficients at the
center by the proved transition law. Metric compatibility then proves all
first metric derivatives vanish there. The public existence theorem needs
no global frame, analytic metric, Hausdorffness or completeness premise.
The shear correction recovers `(t,x+t²)` exactly. The conformal origin is
an explicit local inertial chart with nonzero native curvature and scalar
curvature `-4`. Exact calculations also check nonzero base points, a
nontrivial Lorentz basis and both metric-sign conventions.
`Manifold.OpenTangent` identifies the derivative of open inclusions in the
inherited chart coordinates and turns arbitrary smooth maximal-atlas charts
into diffeomorphisms of open submanifolds. `LocalFlatness` transports native
curvature through these maps, proving `IsLocallyMinkowski` implies vanishing
curvature. Consequently the conformal plane is not locally Minkowski,
although it has a pointwise inertial chart everywhere.

`Manifold.ClosedCoframe` uses the convex-domain Poincaré lemma to integrate
a smooth closed vector-valued one-form. Its derivative is the original
form, so the primitive is smooth; invertibility supplies a smooth local
chart. `ParallelCoframe` derives closedness from torsion-freeness and the
parallel equation `∂θ = θ Γ`. The connection transformation law then gives
zero coefficients throughout the constructed chart. Shrinking its target
to a convex ball and using metric compatibility propagates metric
normalization from one point. The nonconstant shear coframe instantiates
the full integration theorem in Lean. Exact checks also integrate it from
an arbitrary base point and check the conformal curvature obstruction.
`ODE.Volterra` constructs a bounded linear integral operator on
`C([0,1], E)`. Its norm is bounded by the coefficient supremum norm. For
coefficients of norm less than one, a Neumann inverse constructs the unique
solution; the solution is smooth jointly in the whole coefficient curve and
initial value. The proof includes the ODE at endpoints as a within derivative,
uniqueness from the interior differential equation, and a supremum-norm bound.
`VolterraExamples` proves the constructed solution for `A(t) = (t/2) id` is
`exp(t²/4) y₀`. The exact Python check also tests its parameter-variation
equation; the latter is not yet a general Lean variational-equation theorem.
`ODE.ContinuousFamily` now lifts joint finite or smooth regularity to the
supremum-norm space after restriction to a fixed compact continuous family.
A mean-value estimate uniform over the compact index gives strict
Fréchet differentiability, and induction supplies higher derivatives.
`ODE.Radial` applies this to `A_x(t) = -Γ(p + t x)(x, ·)`: its norm is small
near zero displacement, and endpoint maps and their inverses are smooth and
invertible on a common ball. `RadialReparam` uses ODE uniqueness to prove
`P(s x)v = solution_x(v)(s)` and `DP(x)(x)v = -Γ(p+x)(x, P(x)v)`.
`RadialExamples` proves the nonconstant real connection `Γ(q)(u,v) = -(q/2)uv`
has endpoint `exp(x²/4)v` on all prefixes of the unit ray.
`Manifold.SmoothExtension` supplies vector-valued cutoffs near compact sets;
`Lorentzian.RadialFrame` proves bundled native chart coefficients are smooth
and have an extension agreeing near any selected chart point. No global
chart or analyticity of the metric is required.
`ODE.FlatFrame` proves that zero coordinate curvature makes the constructed
radial frame parallel in every direction. The defect `Q = DP + ΓP` obeys
an antisymmetric derivative identity from Hessian symmetry and flatness.
Differentiating `Q(x)(x) = 0` then makes `t Q(t x)(u)v` a transport solution
with zero initial value. Uniqueness kills the defect, without division by
time at the center. Differentiating the inverse gives the coframe equation.
`exists_parallel_radialCoframe` supplies a smooth invertible parallel coframe
on a smaller ball inside any flat neighborhood, with identity at the center.
`FlatFrameExamples` verifies the native nonzero shear coefficients and the
constructed endpoint `P(x)v = (v₀, v₁ - 2x₀v₀)` in Lean. Exact checks also
test both coordinate directions and retain the curvature term in the
defect identity for the curved conformal example.
`ODE.CoordinateCurvature` bundles the coordinate expression as a trilinear
map and proves basis tests and germ locality. `Lorentzian.FlatConnection`
identifies its basis coefficients with the native curvature tensor using
the existing arbitrary-chart Christoffel formula. Thus native zero curvature
gives the precise compatibility condition of the radial construction.
`LocalFlatnessConverse` uses a pointwise inertial chart to normalize the
center, extends its coefficients without changing their germ, and constructs
the parallel coframe on a ball inside the flat neighborhood. The coframe
integration theorem yields a Minkowski chart on its whole source.
The local theorem assumes only curvature zero near the selected point;
the global predicate equivalence is `IsLocallyMinkowski ↔ ∀ p, curvature p = 0`.
The shear example now invokes this construction directly from its native
curvature theorem. Stage D's principal proof endpoints are implemented
and merged. `FlatTransport` identifies transport in a flat
chart with its endpoint tangent equivalences, first for regular segments,
then for finite piecewise paths using their actual path ranges. Native zero
curvature near a point consequently yields an open neighborhood with
path-independent transport; arbitrary nonlinear-shear piecewise paths
instantiate the theorem. No global inertial chart or completeness follows.
Differential/contracted Bianchi and Einstein dynamics belong to 5.2.

### Intrinsic clocks and the first quadratic-action variation

The first stage E increment uses the physical negative-time signature.
`GeneralRelativity.ProperTime` constructs the intrinsic proper-speed rate,
proper-time integral and normalized timelike velocity. Local C¹ regularity
gives integrability, including at null velocities. Subdivision and smooth-chart
formulas are proved without a global chart. Parameter substitution allows zero
parameter speed. Metric preservation along a curve gives invariance even for
maps between different dimensions. Metric compatibility supplies the derivative
of the proper-speed rate for locally C² timelike curves.

`ParticleAction` defines quadratic and square-root actions and proves their
subdivision, geodesic evaluations and appropriate parameter-change laws.
`SpecialRelativity` identifies the Minkowski specializations with the existing
SR functionals. The shear parabola has unit rate; clocks at fixed `x` in the
curved conformal metric have rate `exp(x²)` and the corresponding exact
proper-time and quadratic-action integrals.

`QuadraticLagrangian` differentiates the position-dependent metric and velocity
slots on an open coordinate domain, reusing `Mechanics.OpenDomain` for the
derivative of the actual action and the stationarity equivalence.
`QuadraticGeodesic` uses the native metric and Koszul formula on the model
manifold to identify the Euler–Lagrange covector with minus lowered covariant
acceleration. The first variation includes its endpoint pairing. Nondegeneracy
then proves quadratic stationarity iff the native affine geodesic equation,
without restricting variations to any causal class.

This is a model-manifold variational endpoint, with an arbitrary curved metric;
the native manifold equivalences proved below now remove that restriction.
Those variation gluing arguments remain in E. F–G are subsequent work.
The [GR guide](general-relativity.md) records the hypotheses. New typed GR
contracts run under default elaborator settings in the required Lean job;
the audit includes the namespace. Exact SymPy checks independently test the
clock rates, Euler–Lagrange signs and nonzero endpoint variations in flat,
nonlinear flat and curved examples.

The massive-action increment now differentiates the square-root density on
its open timelike jet domain. `FreeLagrangian` proves the momentum's speed-factor
derivative and actual-action stationarity equivalence using the existing
open-domain calculus. `FreeGeodesic` identifies the Euler–Lagrange covector
with `-(m/s)` times the metric dual of acceleration minus `(s'/s)` velocity.
For positive mass and timelike reference curves, stationarity is equivalent
to tangential native acceleration and to regular local affine-geodesic
reparametrization. The unit-speed specialization is affine in the given
parameter. These coordinate results remain available alongside the native results below.

`ProperTimeParameter` works on arbitrary Lorentz manifolds. C² timelike curves
have C¹ clock rates; the actual clock integral is C² with positive derivative.
The inverse function theorem constructs a local C² parameter inverse with
derivative `1/s` and unit proper-speed rate. Metric compatibility determines
the tangential acceleration factor, and the full second-derivative parameter
law proves that this inverse yields an affine geodesic. The converse law also
proves that regular reparametrization of affine motion forces tangential
acceleration. `FiniteProperTime` now extends this to one inverse over a full
finite timelike segment. C² regularity and timelikeness at all points of the
closed segment supply a larger open interval, and positive derivative gives
global injectivity there. The scalar construction belongs to `Variational.Parameter`.
Both closed-interval images, endpoint correspondence, inverse regularity and
unit rate are proved; tangential acceleration on the original interior gives
affine motion on the whole proper-time interior.

`ParticleExamples` proves that the exponential shear worldline has nonzero
covariant acceleration equal to velocity. Its massive action is stationary
on every nontrivial finite interval; its quadratic action is not. Proper time
is `exp(b)-exp(a)`. Typed contracts fix both the native construction and the
model variational scope. Exact SymPy checks differentiate the massive density
independently and verify the explicit inverse parameter and cancellation.
The finite-segment example now proves the logarithmic inverse and both
endpoints in Lean.

`CurveFamily` supplies native parameter velocities, their C¹ bundle regularity,
and the mixed covariant derivative interchange law for jointly C² families.
The proof uses local second-derivative symmetry and zero torsion, with no
immersion or global chart assumption. `VariationDensity` differentiates both
actual particle densities on arbitrary manifolds. Timelikeness is local at the
point of the square-root density derivative. Typed contracts and exact flat,
shear and conformal family calculations cover these new laws.

`VariationAction` now differentiates the actual actions on arbitrary Lorentz
manifolds from joint C² regularity only along the finite reference segment.
`Variational.IntervalParameter` localizes the scalar parameter-plane density
and obtains domination from compactness. No single chart for the full curve,
global family regularity or caller-supplied integral bound is required.
`VariationBoundary` uses metric compatibility to retain the intrinsic endpoint
pairings and the massive residual's full proper-speed derivative. Actual
derivatives add over subdivisions, including across chart changes.

`VariationStationary` derives vanishing endpoint variation fields from actual
locally fixed endpoints. Affine geodesics are stationary for all such quadratic
families without causal restrictions, and timelike tangential acceleration
implies massive stationarity. `ManifoldCurve` now constructs actual localized
chart families; `LocalizedVariation` identifies their native test vectors.
`VariationTesting` applies the fundamental lemma on small interior time
patches and metric nondegeneracy. `ManifoldStationary` consequently proves both
full native equivalences, with positive mass and timelikeness only for the
massive action. `ManifoldMotion` supplies local reparametrization, unit-rate,
finite proper-time and closed-segment nonzero null preservation corollaries.
`AccelerationRegularity` proves C² curves have continuous native acceleration
and extends the affine equation to interval endpoints. `VariationExamples` verifies a
genuine nonlinear fixed-endpoint family in the shear chart using the native
theorems. Exact checks additionally test curved endpoint/residual terms and
subdivision with a nonzero junction pairing.

## Minkowski Geometry and Relativistic Kinematics

Section 3.1 now has an explicit two-signature geometry layer and a `(-+++)`,
`c = 1` physics layer. The Lean library proves causal-cone convexity and affine
causal order, Lorentz matrix and determinant identities, Poincaré scheme
automorphisms, observer decompositions, passive boosts, velocity composition,
proper-time invariance, and normalized four-velocity. Regularity and causal
premises are hypotheses, including local C¹ assumptions for reparameterization.

Flat forms use mathlib's exterior derivative and a proved comparison with
exterior powers. The wedge normalization, graded Leibniz rule, pullback laws,
and exterior-derivative locality are proved. Hodge duality has explicit metric
and orientation parameters, a proved signed-inverse comparison with mathlib's
operator, square/sign/naturality laws, and observer reconstruction of arbitrary
two-forms. Exact examples include a nonzero boost, time dilation, `A = t dx`,
and all six coordinate two-form Hodge signs. The [guide](special-relativity.md)
records the API, scope, and verification commands for
[issue #40](https://github.com/MGYamada/ProjectAInos/issues/40), the shared
prerequisite of [issue #8](https://github.com/MGYamada/ProjectAInos/issues/8).

## Shared Variational Foundation

The electrodynamics development adds compact localization for C² Lagrangians
on open jet domains. A smooth cutoff gives a global representative agreeing
near the reference jet; a compact tube argument keeps small variations in
that neighborhood. The actual action derivative and the equivalence between
fixed-endpoint stationarity and Euler–Lagrange therefore apply to the
square-root timelike Lagrangian without asserting global C² regularity.

The shared variational calculus uses sections of a trivial bundle over a finite-dimensional real coordinate space. For a jointly C² Lagrangian and a C² field with integrable density, Lean proves the action derivative for smooth variations with compact support inside an open region. It then proves that stationarity is equivalent to the pointwise Euler–Lagrange equation. The theorem covers time and four-dimensional bases and keeps the choice of Haar measure explicit. The interval integration-by-parts identity also retains the endpoint term for fixed-endpoint applications.

This supplies the common local foundation for [issue #7](https://github.com/MGYamada/ProjectAInos/issues/7), building on [PR #29](https://github.com/MGYamada/ProjectAInos/pull/29). The [variational guide](variational.md) describes the endpoint and its hypotheses. The [smooth-algebra guide](smooth-algebra.md) describes the free smooth-function rings and their directional chain rule. Compact base regions now also supply domination without a support condition on the variation, and the interval identity handles covector–vector pairings.

[Shared variational formalization notes](variational-notes.md) record the measure, regularity, and smooth-algebra distinctions exposed by these proofs.

## Mechanics Proof Development

The [C∞ mechanics research plan](cinfty-mechanics.md) preserves the mathematical blueprint, the 52 Landau–Lifshitz targets, proposed proofs, experiment ledger, and references from the former local TeX manuscript. It distinguishes the implemented real analytic model from the planned abstract C∞-ring constructions.

`ProjectAInos/Mechanics` uses the shared foundation for a real time interval and a real normed position space, including any finite number of generalized coordinates. For a jointly C² Lagrangian `L(t,q,v)` and a C² path, Lean proves the derivative of the actual action, its first-variation formula with the endpoint momentum pairing, and the equivalence between fixed-endpoint stationarity and the Euler–Lagrange equations on `(a,b)` for `a < b`. Variations may have nonzero derivatives at the endpoints. Smooth operations from the shared C∞-ring give mechanical Lagrangians with the required regularity automatically. The natural scalar Lagrangian yields `m q'' = −V'(q)`.

Adding the total time derivative of a function of time and position changes the action by its endpoint difference. Lean proves that fixed-endpoint stationarity is preserved and that the Euler–Lagrange covector agrees pointwise. [Total time derivatives](mechanics.md#total-time-derivatives)

The mechanics guide gives the assumptions and proof map. The formalization notes record distinctions and design decisions exposed by the proofs. The algebraic core of the plan is in the shared algebra layer: partial derivatives of smooth operations, dual numbers and C∞-derivations ([issue #74](https://github.com/MGYamada/ProjectAInos/issues/74)). `Mechanics/Jet` then proves, in every jet C∞-ring, that total derivatives are null Lagrangians, the energy and Noether identities, Newton's equations for natural Lagrangians, and conservation of energy, momentum, the centre-of-mass integral and angular momentum as membership in the Euler–Lagrange ideal. `Mechanics/Jet/FreeParticle` characterizes the Lagrangian of a free particle: a function of the velocities is quasi-invariant under infinitesimal boosts exactly when it is a polynomial of degree at most two, and with isotropy it is `½ μ |v|²` up to a constant. `Mechanics/Jet/Metric` extends this to natural Lagrangians with a position-dependent kinetic form: momenta, Lagrange's equations, the energy and its conservation, with plane polar co-ordinates as a model. The standard jet ring, the free C∞-ring on time and the jet coordinates, is a jet ring; its vector fields are built from the dual numbers without analysis. [Jet rings and conservation laws](mechanics.md#jet-rings-and-conservation-laws) · [Ledger](cinfty-mechanics.md#ledger) `SmoothAlgebra/Poisson` defines Poisson structures on a C∞-ring with antisymmetry, the chain rule and the Jacobi identity as the only laws. It proves Poisson's theorem, Noether's theorem in Hamiltonian form, the normalizer of a coisotropic ideal, Hamilton–Jacobi and Maupertuis–Jacobi, and that the Jacobi identity on a free ring is a condition on generators. The models are the canonical bracket with Hamilton's equations, the rigid body with Euler's equations and the Casimir `|L|²`, the angular momentum of a particle with its `so(3)` momentum map as a Poisson morphism, the heavy top with its equations of motion and Casimirs, the Galilei algebra of a free particle, the virial identity, the Coriolis and centrifugal terms of a uniformly rotating frame, and Kepler's problem with the inverse distance adjoined as a generator: the six identities of the Runge–Lenz vector with their dependence on the relation `ρ² |q|² = 1`, and conservation of the Runge–Lenz vector along smooth solutions of the inverse-square law. Along a trajectory of a Hamiltonian on a free C∞-ring every observable evolves by its bracket with the Hamiltonian, so integrals of the motion are constant along trajectories. [Poisson structures](smooth-algebra.md#poisson-structures) · [Poisson models](mechanics.md#poisson-models) `Mechanics/Jet/Prolongation` connects the jet-ring identities to trajectories: the prolongation of a smooth path turns the total derivative into `d/dt`, and a conserved element is constant along every smooth solution, in particular the energy along solutions of Newton's equations. `Mechanics/Jet/Analytic` proves that, for a Lagrangian given by a smooth function of time, position and velocity, a smooth path is a solution in this sense exactly when the action of the real analytic model is stationary on every interval, so the jet-ring conservation laws hold along stationary paths. `Mechanics/Rigid` proves the kinematics of a rigid body by linear algebra: `so(3) ≅ ℝ³` as Lie algebras, the angular velocity of a family of rotations and its independence of the origin, and the inertia tensor of point masses with `M = I Ω`, the parallel-axis theorem and the triangle inequality for the principal moments, and Eulerian angles with the angular velocity in the body frame and the kinetic energy of the symmetric top. It proves the regular precession of the free symmetric top, and on the Lie–Poisson phase space the permanent rotations, their stability about the axes of the greatest and the least moment by an integral of the motion, and the signs of the linearized equations. `Mechanics/TwoBody` proves the algebra of two bodies: the reduced mass, disintegration in the centre-of-mass frame, the characterization of elastic collisions with the formulas for a target at rest, and the canonical centre-of-mass variables. `Mechanics/Oscillations` proves the general solution of `ẍ + ω² x = 0` with its amplitude, phase, energy and period, the flow of the oscillator, and the linearization of a Hamiltonian vector field at an equilibrium as the vector field of the quadratic part of the Hamiltonian. It also proves the three cases of the damped equation `ẍ + 2γ ẋ + ω₀² x = 0` and, for friction with a dissipative function `F`, the identity `X(H) = −2F` with the energy not increasing along the motion. For the forced equation it proves that every solution approaches the steady state when the damping is positive, the amplitude and phase of the steady state for a periodic force, and the exact resonance curve with its maximum at `Ω = ω₀` and its width `2γ`. Without friction it proves Duhamel's formula for an arbitrary smooth force, with existence and uniqueness for all initial data, the energy transferred in a finite time, and the unbounded growth at resonance. For several degrees of freedom it proves the simultaneous diagonalization of the two quadratic forms and the separation of the equations in normal co-ordinates, and for a periodic coefficient the monodromy relation and stability when the trace of the monodromy matrix is less than two. The equations `M ẍ + K x = 0` are the Euler–Lagrange equations of the Lagrangian of small oscillations and Hamilton's equations of the quadratic Hamiltonian; quadratic Hamiltonians correspond to the matrices of `sp(2n, ℝ)` with linear Hamiltonian vector fields, and the normal co-ordinates are an invertible linear canonical transformation that brings the Hamiltonian to a sum of oscillators. For the canonical formalism it proves the chain rule for a substitution out of a free C∞-ring, the Legendre correspondence for natural Lagrangians, Jacobi's theorem on complete integrals for a given curve, and Liouville's theorem in infinitesimal form. `Mechanics/Similarity` proves the mechanical similarity of the solutions for a homogeneous potential, the virial theorem for time averages, and for Kepler's problem the equation of the orbit and the third law for similar orbits. In the shared algebra layer, `SmoothAlgebra/Point` identifies the states of a system with the morphisms of its ring of functions to the dual numbers: pairs of a position and a velocity for a free ring, and the states tangent to the equations for a presented ring. The Legendre transformation, momentum maps, quotients by ordinary ideals and cotangent modules remain stages of [issue #78](https://github.com/MGYamada/ProjectAInos/issues/78). [Mechanics guide](mechanics.md) · [Formalization notes](mechanics-notes.md)

## Electrodynamics 4.1

Local potentials and curvature use the existing flat exterior derivative.
Gauge invariance, Bianchi in components, Lorentz/Poincaré compatibility,
observer reconstruction, and both field invariants are proved with time
first and signature (-+++). The pseudoscalar transforms by the Lorentz
determinant. The charged action combines the free proper-time action with
the potential line integral; its actual fixed-endpoint stationarity yields
the Lorentz force, including the proper-time component equation. The gauge
action difference is an endpoint term even for locally regular potentials;
C³ gauge functions preserve the C² assumptions of the local action theorem.

The pinned upstream Maxwell jet closure is independently compiled, preserving
its `YM` statements and provenance. A generic normed-target radial proof
specializes to scalars and the original color space, commutes with linear
component extraction, and connects to the project's exterior derivative
through the explicit coordinate swap. Nonzero degrees 0 and 1 and the
hyperbolic charged worldline are regression proofs. The
[electrodynamics guide](electrodynamics.md) records the full theorem map,
regularity conditions, experiment runner, and boundaries of §4.1.


## GR 5.1 native differential-form foundation

The first stage F increment constructs the smooth structure on mathlib's
native continuous-alternating-map bundle, then proves arbitrary smooth
pullback, coefficient overlap/recovery and open-cover gluing. No native
fibre receives an artificial norm, and local gluing representatives only
need regularity on their own domains. Flat smooth forms and pullback agree
exactly with the existing API. Nonlinear shear, time-axis and singular
projection examples are formal proofs, with independent exact SymPy checks.
Typed contracts cover the general interfaces at default elaborator settings.
Native exterior differentiation is now constructed by differentiating
actual chart coefficients and proving the overlap law before assembling the
global section. Local chart maps need no global smooth extension. Smoothness,
chart independence, linearity, locality, `d² = 0`, arbitrary smooth pullback
naturality across different model spaces and exact flat specialization are
proved. The nonzero exact plane area form, nonlinear shear and time-axis
inclusion are Lean examples; exact SymPy also checks mixed-partial cancellation
and a nonlinear two-to-three-dimensional pullback.

`NativeWedge` lifts the established normalized coordinate product through
actual charts on manifolds modeled on `Fin n → ℝ`. Its overlap theorem is
proved for arbitrary native forms, before the smooth product is bundled.
The flat pullback law now allows different source and target dimensions;
the native law inherits this generality. Bilinearity, associativity, graded
commutativity, a degree-zero unit and graded Leibniz are section equalities.
`smoothDegreeCast` makes degree arithmetic explicit in these identities.
No norm is introduced on native fibres. Lean examples cover nonlinear
charts, singular and dimension-changing maps, and the nonzero signed identity
`d(dx⁰ ∧ x¹ dx²) = -dx⁰ ∧ dx¹ ∧ dx²`. Independent exact SymPy checks use
variable forms and a nonlinear immersion.

`MetricDensity` proves the Gram-determinant density law even for singular
changes of vector family. `Lorentzian/VolumeDensity` specializes it to actual
tangent fibres and proves positive basis volumes, the chart formula,
absolute-Jacobian covariance and local smoothness. The determinant is a
finite polynomial on the coordinate model; no native fibre norm is added.
`OrientedAtlas` supplies only signed local chart data. `VolumeForm` proves
overlap compatibility before gluing, then proves nonvanishing, equality of
the absolute volume with density, reversal of orientation, invariance under
whole-metric sign reversal, and independence of compatible chart covers.
Exact Lean examples cover either Minkowski convention in every dimension,
both actual shear charts, a different compatible oriented cover, the curved
conformal plane, and a basis change with volume `-6` but density `6`.
Default-option typed contracts and independent exact SymPy checks accompany
the construction.

`FiniteDual` identifies continuous alternating forms on finite topological
fibres with exterior powers of their algebraic duals, without introducing a
norm. `FiniteWedge` proves exact agreement with the native chart-based wedge.
`VolumeNormalization` constructs the top-covector functional as division by
a nonzero volume vector: scaling the volume by `r` scales the functional by
`1/r`. `FiniteHodge` and `HodgeTransport` then prove the actual wedge equation,
uniqueness, volume and metric scaling, and transport between independent
finite topological fibres. `HodgeFiber` applies these results to the native
Lorentz inverse metric and constructed volume form. The operator is an actual
linear equivalence on each fibre, with the expected orientation and metric-sign
laws. `HodgeFlat` proves exact agreement with the existing Minkowski API;
`HodgeExamples` transfers all six two-form signs and square `-1`, and proves
nonlinear shear transport using the actual metric and volume identities.
Typed contracts use default elaborator settings. Independent exact SymPy
checks all degrees under nonlinear positive/negative-Jacobian chart changes,
metric sign reversal, and the conformal plane.

`HodgeFormula` proves the native/reference comparison with inverse-metric
precomposition and a volume coefficient. `ChartDuality` identifies the actual
coordinate metric with a continuous linear equivalence and proves smooth
inversion locally. `HodgeCoordinates` derives `⋆g α = sρ ⋆η (α ∘ (G⁻¹η))`,
where precomposition acts in every slot and `ρ = sqrt(abs(det G))`.
`HodgeSmooth` uses this formula and smooth chart coefficients to construct
`smoothHodge` on the actual alternating tangent bundle. No norm is added to
native fibres. `HodgeSquare` uses a pointwise signature witness and proves
its volume has square one, transferring the flat square law without a global
frame or a flatness premise. `HodgeCurvedExamples` proves that the curved
conformal plane's one-form Hodge equals flat Hodge, including smooth sections,
and checks its square alongside the known nonzero scalar curvature.
The exact runner independently checks the inverse-metric formula for all
degrees in nonconstant coordinates and both metric signs.

`OneForm` proves regularity equivalence for native covectors and alternating
one-forms, giving a smooth linear equivalence. `Electrodynamics.Curved` uses
it with metric lowering and Hodge to construct `J = ⋆(j♭)` and its inverse,
sets `H = -⋆F`, and proves current closedness from the sourced equation alone.
The actual derivative `dH` determines a unique vector source. Orientation
reversal preserves the equations, and a directly differentiated field
`F=t dt∧dx` verifies `H=t dy∧dz` and the nonzero source three-form.

`Divergence` defines the intrinsic trace of Levi-Civita and proves smoothness
and its derivative-plus-Christoffel expression. `MetricDensityDerivative`
derives determinant/density directional derivatives by row multilinearity,
transposition and nonzero-determinant calculus. `DensityDerivative` applies
metric compatibility and the product rule to obtain the chart-density
derivative and `div V = ρ⁻¹ ∂ᵢ(ρVⁱ)`. A curved conformal constant field has
proved nonzero divergence `4x`; exact calculations also check nonconstant
fields in curved, time-dependent, non-diagonal metrics of either signature.

`Interior` constructs first-slot contraction on native topological fibres and
proves linear-map naturality without native norms. `Minkowski/HodgeCurrent`
derives all one-form signs and the coordinate volume contraction identity;
`Lorentzian/HodgeCurrent` transfers it through pointwise signature witnesses.
`Current` obtains the signed chart-density expression and proves the actual
native equality `dJ=(div j) vol`. Nonvanishing volume makes current closedness
equivalent to vanishing vector divergence. The sourced Maxwell equation alone
therefore gives covariant current conservation. `CurrentExamples` proves the
nonzero source vector `-∂x` and its divergence. Exact checks include curved
mixed-coordinate metrics and nonzero current divergence in both signatures
and orientations.

`Tensor/CovariantDerivative` now applies the local tensoriality criterion to
the Leibniz-corrected derivative of native bilinear tensors. `TwoForm` proves
smooth currying from the alternating bundle without installing fibre norms.
`TwoFormDerivative` derives both Christoffel corrections from the actual
Levi-Civita connection and proves smoothness by testing on local smooth fields.
Its packaged iterated-hom model retains the recursively constructed coordinate
norms/topologies. `TwoFormExterior` uses actual chart coefficients and
torsion-freeness to identify the exterior derivative with the alternating
covariant sum. Basis extensionality proves the reverse implication from
component equations; no coordinate transformation law is assumed.

Lean examples include closed coordinate area with nonzero covariant derivative
on the curved conformal plane and a nonclosed four-dimensional form with
nonzero cyclic sum. Exact calculations test all three covariant slots under
a nonlinear chart change in a curved metric.

`TwoFormDivergence` constructs a smooth vector by contracting and raising the
native derivative. `DualDerivative` proves the raising product rule from metric
compatibility. `TwoFormRaised` derives the local dual-frame connection rule,
the two positive Christoffel corrections, and the vanishing symmetric/skew
contraction. The resulting density formula is proved for every smooth chart.
The conformal area example has nonzero divergence, and the physical electric
example agrees exactly with its source from `dH`. Exact checks also verify
the vector transformation law under the nonlinear change of chart.

`BivectorVolume` proves the local coordinate identity for differentiating the
volume dual of an antisymmetric coefficient matrix. `ExcitationChart` derives
that matrix from the actual Hodge operator as `ρ Fⁱʲ`, with the oriented chart
sign. `CurvedComponents` then uses local chart recovery, the density divergence
formula and current-volume identification to prove `dH = currentForm (div F)`.
No chart is assumed globally smooth. Both directions of the sourced equation
and of the complete Maxwell component equations follow. The source is
orientation independent; every native two-form divergence is conserved.
Typed API contracts include the full component iff, and exact SymPy compares
the independently computed Hodge/exterior and covariant-derivative sides in
a curved nonlinear chart with all six field components varying.

Stage F’s principal endpoints are implemented and merged. The controlled
time-dependent Newtonian motion and trajectory limit is proved in stage G. The
[geometry guide](smooth-geometry.md) and [electrodynamics guide](electrodynamics.md)
record the APIs and convention comparison.

The first stage G increment defines `NewtonianMetricFamily` using smooth
coefficient data on a common open physical-coordinate domain and uniform
bounds through two spacetime derivatives. It preserves time dependence and
all three correction types. Finite contractions give an explicit uniform
upper bound for the norm of `(1,v)`, implying eventual negativity for bounded
velocities. They also prove positivity on the spatial hyperplane. These
properties are derived, not fields of the family structure.

`CoordinateTime` works separately with the existing native Lorentz connection.
The physical-clock germ fixes the first and second time derivatives. The time
component then determines the tangential acceleration factor, proving both
directions of the spatial ODE with its non-affine correction. A regular affine
geodesic reparametrization implies that equation. Local smoothness follows
from the actual connection. The polynomial family example has proved compact
C² bounds and nonzero time/mixed/spatial data.

Completing the square along the negative time line yields a positive
quadratic form on its orthogonal complement. Its Euclidean coordinates
combine with the normalized time line to give the signature witness. The
tangent-bundle trivializations of the common open domain identify the smooth
coefficient form with a native Lorentz metric. The coordinate connection is
derived from this metric. Rescaling the time row and estimating each inverse
column gives the uniform temporal and spatial inverse bounds.
The lower-index Christoffel formula isolates the potential derivative in
the leading spatial time-time slot. The inverse bounds control the raised
components and retain the time-component correction in coordinate time.
Contracting with bounded physical-time velocities gives a uniform
`O(c⁻²)` acceleration error. The potential Hessian bound gives the
Newtonian phase-field Lipschitz estimate along contained segments. These
results yield the Gronwall phase error on a common interval of existence.
The inverse difference identity and the coefficient Hessian bound give a
uniform relativistic Lipschitz estimate on contained segments and bounded
velocity ranges. A compact tube supplies a single radius for clipping the
deviation in an auxiliary ODE. Boundedness and Lipschitz continuity give
Picard–Lindelöf on the full interval. Gronwall keeps the solution inside the
tube, where clipping is the identity. The resulting trajectories converge
uniformly, with a rate from the two terms of the Gronwall bound including
the zero-Lipschitz case. The polynomial example applies the result on
`[0,1]` to a time-dependent potential with mixed and spatial corrections.
