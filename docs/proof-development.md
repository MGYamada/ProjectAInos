# Proof Development

This record traces the development of the Lean proofs. The research plan and subject outline are in the [project README](../README.md).

The classical-field design from [issue #8](https://github.com/MGYamada/ProjectAinos/issues/8)
is now maintained in three research manuscripts:
[C∞ special relativity](cinfty-special-relativity.md),
[C∞ electrodynamics](cinfty-electrodynamics.md), and
[C∞ general relativity](cinfty-general-relativity.md).
Their dictionaries cover all 119 sections of L&L Volume 2 and separate existing
proofs from future targets. This documentation migration adds no Lean proofs;
the completion of the design issue refers to that migration.

The 17 November 2026 design review records the reusable mechanics proofs
after the 52-section delivery. The field plans now point to smooth local
flows and their derivative, the linear propagator, turning-point and
scattering integrals, and finite-dimensional Taylor estimates. Their next
proofs are the SR free-particle comparison, the flat Maxwell action with a
prescribed current, and the curvature derivative and compact metric variation
needed for Einstein dynamics.

The proofs of the three field plans are tracked in
[issue #135](https://github.com/MGYamada/ProjectAinos/issues/135). Each plan now has a
ledger with one status for each section, a count line and the list of rows closed
with a remainder, in the vocabulary of the mechanics ledger:
[special relativity](cinfty-special-relativity.md#ledger) (12 of 14 rows proved),
[electrodynamics](cinfty-electrodynamics.md#ledger) (none of 66) and
[general relativity](cinfty-general-relativity.md#ledger) (5 of 39). The baseline
counts a row as proved only when its whole target is proved; a row with a proved
core names the core and stays *informal*. Observations are recorded in the notes
of [special relativity](special-relativity-notes.md),
[electrodynamics](electrodynamics-notes.md) and
[general relativity](general-relativity-notes.md). This step adds no Lean proofs.

Before the first proofs of the field plans, the library was made to build with the default
elaborator options. 195 files had set `backward.isDefEq.respectTransparency false`, and 52 of
them also `backward.defeqAttrib.useBackward true`. 144 files compile with the lines deleted. In
the other 51, about 120 proof steps passed a `rw` or a `simp` lemma through a term that uses a
definitional identification silently, mostly the tangent space of a vector space with the space;
they now apply the lemma in term mode or restate the goal. No declaration changed its type, with
one helper as the exception, and `tangentSpace_isNormableSpace` restates an instance of Mathlib
that instance search does not find. The one raised heartbeat limit is gone: the computation of
`alternatize_bivectorVolume` is split by the first index. `checks/ForbiddenOptions.lean` keeps
both options out of the library and the checks
([G02](smooth-geometry-notes.md#g02-the-tangent-space-of-a-vector-space-is-the-space-and-lean-has-to-be-told)).

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

The [reservoir model](../ProjectAinos/Thermodynamics/ReservoirModel.lean) supplies a nonempty family satisfying the full simple-system and thermal interfaces, closed under positive scaling and thermal joins. Entropy equals energy and pressure is zero, so it exercises the universal-isotherm case. The [join assumption audit](thermodynamics-join-audit.md) distinguishes contact and splitting from the geometric regularity required of joined systems.

The physical development constructs coherent finite composites and their adiabatic quotient. It proves composition-label conservation for the A1–A6 closure of nonreactive elementary processes and constructs common scaled products for states with equal composition labels. Forward sectors are convex and relatively closed in an open convex finite-dimensional equilibrium domain. Irreversibility and unique finite-slope support imply nonempty interior; the supporting plane is inherited at every relative-boundary point. Energy orientation is constant throughout each simple system, giving the fixed-work accessibility criterion. The boundary is a differentiable graph whose derivative is the negative pressure form. Locally Lipschitz pressure gives local uniqueness of these graphs, and boundary connectedness propagates reversibility. These results establish simple-system comparison, strict nesting of distinct forward sectors, and openness of strict reference strips. Energy reflection handles the opposite orientation without changing the physical premises.

Typed thermal families connect actual scaled coordinate domains, thermal joins, and the positive scaled-copy clause of T2. Thermal contact fixes a common energy orientation across systems, and the zeroth law gives independent scaling invariance. Simple-system comparison and transversality establish local mixture intervals; connectedness joins their affine reference lines. These results give single-system product comparison and normalized concave continuous entropy. Thermal equilibrium between two copies is equivalent to fixed-total-energy entropy maximization, or intersection of their supporting-slope intervals. This criterion requires no extra differentiability assumption on entropy.

The location-of-isotherms dichotomy and crossed-calibrator existence are proved, including the universal-isotherm case. A concrete splitting and mixing cycle establishes thermal equilibrium between a joined state and each component. Pairwise calibrators align all simple-system reference directions, giving comparison in every finite scaled product. Canonical coordinate atoms provide the finite composite presentation and fixed-composition labels. Common-product realization then gives ECH for nonreactive accessibility. The final physical entropy endpoints take the explicit geometric and thermal premises, with no CH, ECH, or calibrator-existence assumption.

The reaction development defines direct, chained, and catalytic transition costs, proves their positive homogeneity, and selects compatible entropy constants by Hahn–Banach. The physical entropy theorem supplies the required calibrated monotonicity within each composition label. Absence of sinks is expressed using actual transitions, independently of entropy or costs. The resulting total entropy is additive, extensive, monotone for all accessible transformations, and characterizes accessibility when composition labels match. Infinite costs for unreachable labels remain allowed, including after adding catalysts.

The current physical endpoints use A1–A7, S1–S3 and T1–T4, with M added for reactions. Every admitted primitive simple system satisfies transversality T4; no extra T5 assumption is needed for this scope. Extending the theory to systems without T4, or proving temperature regularity, belongs to subsequent work. The ideal-gas phase-volume derivation remains in the statistical-mechanics stage of the research plan.

The public physical endpoints are in [PhysicalEntropyPrinciple](../ProjectAinos/Thermodynamics/PhysicalEntropyPrinciple.lean); [AtomicSystems](../ProjectAinos/Thermodynamics/AtomicSystems.lean) specializes them to canonical coordinate atoms. The [mathematical guide](thermodynamics.md) presents the algebraic theory, physical comparison, reactions, and models with proof links. The [implementation checklist](thermodynamics-status.md) maps the eight planned stages to their proof modules and scope.

Every completed stage must pass the warning-free Lean build, root-import check, and transitive axiom audit. Physical premises remain explicit in theorem statements. [Lean library entry point](../ProjectAinos.lean)

[Thermodynamics formalization notes](thermodynamics-notes.md) record the mathematical distinctions and modeling decisions exposed by the proofs, together with their current proof status.

See the [Landau–Lifshitz correspondence](landau-lifshitz.md) for the Mechanics proof targets and reference volumes for the other subjects.

## Shared Smooth Algebra and Geometry

The shared mathematical layers for Mechanics, Special Relativity, Electrodynamics, and General Relativity (research-plan topics 2–5) live in `ProjectAinos/SmoothAlgebra` and `ProjectAinos/SmoothGeometry`, independently of the physics. Together with the shared `Variational` layer, they have an acyclic import graph excluding project physics and vendored Yang–Mills. C∞-rings have finite smooth operations, substitution laws, and compatibility with a commutative real algebra. Morphisms preserve every smooth operation; their real-algebra homomorphisms are derived. The concrete models are ℝ, products, and C∞(ℝⁿ), including dimension zero. The smooth-function ring is proved free on its coordinate functions, with evaluation and pullback as morphisms. A nonpolynomial check proves `exp(a + b) = exp(a) * exp(b)` in every C∞-ring.

The geometry follows mathlib's progression from ringed spaces through `Spec` to `Scheme`, with Joyce's real points and C∞ operations. Smooth congruence quotients and cutoff functions construct point localizations with their universal property. Locally represented sections form the structure sheaf, and its stalks are identified with the localizations. The resulting spectrum functor supplies the actual affine models in the local-affine definition of a C∞ scheme. Affine schemes are the essential image of this functor. Examples include affine spaces and the empty scheme.

Free C∞-rings on arbitrary sets give general localizations with their smooth universal property. Their spectra are identified with the surviving-point subspaces; principal localizations give open immersions. These supply open subschemes and pullbacks along open immersions. Open gluing data construct actual C∞ schemes, with descent and uniqueness of compatible morphisms proved as a categorical colimit. The manifold comparison identifies the Euclidean smooth-function sheaf with its affine spectrum, then proves local affineness for boundaryless finite-dimensional smooth manifolds using coordinate charts. Smooth maps induce scheme morphisms with identity and composition laws.

`SmoothGeometry/OpenCover` proves that a morphism which is an open immersion on each member of a jointly surjective family of open immersions has isomorphisms on stalks and is an open map; it is an open immersion when it is injective on points and an isomorphism when it is bijective on points. `Scheme.GlueData.desc_isIso` is the case of a descent morphism. `GluingExampleIso` applies it to the two half-lines `x < 1` and `-1 < x`: the descent morphism `toLine` is an isomorphism of C∞ schemes, `gluedIsoLine : datum.glued ≅ line`, with inverse `fromLine` and both inverse identities. The coordinate function is followed through the gluing as a section: its restrictions to the pieces take the value of the coordinate, they agree on the overlap, and `gluedCoordinate` is the only global section of the gluing that restricts to them ([issue #71](https://github.com/MGYamada/ProjectAinos/issues/71)). [Smooth-geometry guide](smooth-geometry.md#a-two-piece-gluing-of-the-smooth-affine-line)

The algebra layer also differentiates. Partial derivatives of smooth operations are again operations, with the chain rule as an identity between operations and commuting second partial derivatives. Dual numbers `A[ε]` over any C∞-ring carry the smooth operations whose infinitesimal part is the first-order Taylor term. C∞-derivations have the chain rule as their only law; the Leibniz rule and real linearity follow. Vector fields form a Lie ring under the commutator and correspond to the morphisms `A → A[ε]` lifting the identity, and derivations of `C∞(ℝⁿ)` correspond to tuples of values on the coordinates. This is the first algebraic stage of the mechanics plan ([issue #74](https://github.com/MGYamada/ProjectAinos/issues/74)). [Smooth-algebra guide](smooth-algebra.md#partial-derivatives-dual-numbers-and-derivations)

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
checks also cover the conformal metric's coefficients; the Lean proofs for
that curved example are in the stage C paragraph below.

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
are implemented and merged through [#52](https://github.com/MGYamada/ProjectAinos/issues/52).

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
Those variation gluing arguments are part of stage E. Stages F and G are
recorded in the sections below.
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
[issue #40](https://github.com/MGYamada/ProjectAinos/issues/40), the shared
prerequisite of [issue #8](https://github.com/MGYamada/ProjectAinos/issues/8).

The algebraic layer of relativistic particle mechanics is the first wave of
[issue #135](https://github.com/MGYamada/ProjectAinos/issues/135) for special
relativity. The energy `√(m² + Σ pᵢ²)` is an operation of the momenta in every
C∞-ring, and its statements follow from `E² = m² + Σ pᵢ²`, `E E⁻¹ = 1` and
`D E = E⁻¹ Σ pᵢ D pᵢ`. On the canonical phase space the coordinate-time
Hamiltonian has the equations `q̇ = p/H`, `ṗ = 0`, a speed less than one at
every point, the momentum and the angular momentum as integrals, the
trajectories `q₀ + t p₀/H`, and a flow defined for all times. The orbital
charges `x_μ p_ν − x_ν p_μ` of a symmetric matrix satisfy the brackets of the
affine isometries, which for the Minkowski metric is the Poincaré algebra;
with `ε = 1/c` the charges of the initial data form a family whose member at
`ε = 0` has the relations of the Galilei algebra with the mass as its central
term. The mass shell is a coisotropic ideal with the momenta and the Lorentz
charges in its normalizer, and for `(−+++)` the reduced ring of its future
sheet `p₀ + E` is the phase space of the initial data, with `−H`, `H qᵢ` and
`qᵢ pⱼ − qⱼ pᵢ` as the classes of `p₀`, `J₀ᵢ` and `Jᵢⱼ`. The ledger rows of
§§8, 9 and 14 name these results and stay *informal*: the comparison with the
action, the Legendre transformation and the charges of a system of particles
are not proved. [Guide](special-relativity.md#relativistic-particle-mechanics-the-algebraic-layer) ·
[Notes](special-relativity-notes.md) ·
[Ledger](cinfty-special-relativity.md#ledger)

The second wave proves the motion of a free particle. On the closed future
cone the pairing satisfies the reverse Cauchy–Schwarz inequality, and
integrating it against the observer in the direction of the displacement
gives `τ[γ] ≤ √Q(γ b − γ a)` for a future timelike `C¹` curve, with equality
exactly when the unit four-velocity is constant, and the same inequality for
finitely many pieces. The free action is stationary on a `C²` timelike curve
if and only if the momentum covector is constant; for `m ≠ 0` this is the
constancy of the unit four-velocity, and the curve is `γ a + τ(t) • U` in its
proper time. The Hessian of the Lagrangian in the velocity has the line of the
velocity as its kernel and rank three. For an observer the energy of a future
timelike momentum is positive, `E² = Q(p) + |p⊥|²`, the velocity `p⊥/E` is
shorter than one, and a second observer measures `γ E − ⟨γ w, p⊥⟩`. In the
time of an observer the Lagrangian `−m √(1 − Σ vᵢ²)` on the ball of velocities
has the Legendre transformation `v ↦ m γ v` with the inverse
`p ↦ p/√(m² + Σ pᵢ²)` and the energy `√(m² + Σ pᵢ²)`; its stationary curves
have a constant velocity, they correspond to the trajectories of the
Hamiltonian, and in three dimensions the action of space-time is stationary on
a graph exactly when this action is stationary on the curve. With the speed of
light as a parameter, the energy, the Lagrangian, the momentum and the rate of
a clock differ from their Newtonian values by at most `|m| V⁴/(2c²)`,
`|m| V³/c²` and `V⁴/(2c⁴)` for speeds at most `V` and `c ≥ 2V`. The ledger rows
of §3 and §8 are *proved* in their stated scopes (4 of 14).
[Guide](special-relativity.md#the-motion-of-a-free-particle)

The third wave begins with signals, the Lorentz group and collisions. A
relation between events that is contained in the causal order stays so in
every inertial frame, joins no events with a spacelike separation, and has the
same order in time and a speed at most one for every observer; the
containment is the physical premise. Every orthochronous Lorentz
transformation is a rotation after a boost in one way only: the boost is that
of the observer which the transformation brings to rest. The product of two
boosts is the boost of the composed velocity followed by a rotation, which is
the identity when the velocities have one direction. For momenta of the future
cone the invariant mass satisfies `M(p) + M(q) ≤ M(p + q)`, a null sum occurs
only for parallel null momenta, and a timelike total momentum has exactly one
frame of the centre of momentum. In the decay of a mass `M` into `m₁` and `m₂`
the energies are `(M² + m₁² − m₂²)/2M` and `(M² + m₂² − m₁²)/2M`, the momenta
are opposite with `|𝐩|² = λ(M², m₁², m₂²)/4M²`, and every direction occurs when
`m₁ + m₂ ≤ M`. For a collision `s + t + u` is the sum of the squares of the
masses; an elastic collision keeps the energy and the length of the momentum
of each particle in the frame of the centre of momentum, and for a target at
rest `s = m₁² + m₂² + 2 m₂ E₁` and `t = −2 m₂ (E₄ − m₂)`. The ledger rows of §1,
§4, §11 and §13 are *proved* in their stated scopes (8 of 14).
[Guide](special-relativity.md#signals-the-factorization-of-a-lorentz-transformation-and-collisions)

The wave ends with the mass shell and the massless particle. The future shell
of a mass `m ≥ 0` is the graph of `√(m² + Σ πᵢ²)` over the open set
`m² + Σ πᵢ² > 0` of the space momenta, which omits the origin for `m = 0`; the
graph is smooth there, the orthochronous Lorentz group maps the shell to
itself and acts smoothly in this chart, and for `m > 0` the real zeros of the
function `p₀ + E` of the future sheet are the points whose momentum vector is
on the shell. The action `½ ∫ (−Q(ẋ)/e − e m²)` with an auxiliary positive
function `e` is stationary exactly when `Q(ẋ) = e² m²` and `ẋ/e` is constant.
For a positive mass this is the action `−m ∫ ds` with `e = √Q(ẋ)/m`; for the
mass zero the velocity is null and `ẋ = e k` with a constant null vector, and
the action does not depend on the parameter. The ledger rows of §7 and §9 are
*proved* in their stated scopes (10 of 14); §§10, 12 and 14 belong to the next
wave and §6 to the comparison of cotangent modules.
[Guide](special-relativity.md#the-mass-shell-and-the-massless-particle)

The fourth wave proves the measures and the charges. In the chart of the shell
the measure `dᵈπ/E` is invariant under the orthochronous Lorentz group for
every mass: a rotation acts by a linear map of determinant `±1` that preserves
the energy, a boost has the Jacobian `E′/E` as the determinant of the identity
plus a map of rank one, and the formula for the change of variables applies.
The number current `∫ f p dᵈπ/E` of a distribution is a vector, the number of
particles through a hypersurface with a given surface measure does not change
when the measure, the normal and the distribution are transformed together,
and through a hyperplane of the co-ordinates it is `∫∫ f dᵈπ dᵈx`. The orbital
moment `x ∧ p` is the charge that Noether's theorem assigns to the Lorentz
transformations; for a system of particles the total moment is unchanged by
free motion and by collisions in one event, a shift of the origin adds
`c ∧ P`, and the centre of energy moves with the velocity `P/E`. The flux
factor of two particles is a Lorentz scalar with `F² = λ(s, m₁², m₂²)/4`, and a
cross-section `(1/4F) ∫ W dν` is covariant when the measure of the final
states and the weight are; the measure on the final states with a conserved
momentum is not constructed. The ledger rows of §10 and §14 are *proved*, and
§12 is *proved modulo interface* and closed with this remainder (12 of 14
proved); §6 remains for the comparison of cotangent modules.
[Guide](special-relativity.md#measures-and-charges)

## Shared Variational Foundation

The electrodynamics development adds compact localization for C² Lagrangians
on open jet domains. A smooth cutoff gives a global representative agreeing
near the reference jet; a compact tube argument keeps small variations in
that neighborhood. The actual action derivative and the equivalence between
fixed-endpoint stationarity and Euler–Lagrange therefore apply to the
square-root timelike Lagrangian without asserting global C² regularity.

The shared variational calculus uses sections of a trivial bundle over a finite-dimensional real coordinate space. For a jointly C² Lagrangian and a C² field with integrable density, Lean proves the action derivative for smooth variations with compact support inside an open region. It then proves that stationarity is equivalent to the pointwise Euler–Lagrange equation. The theorem covers time and four-dimensional bases and keeps the choice of Haar measure explicit. The interval integration-by-parts identity also retains the endpoint term for fixed-endpoint applications.

This supplies the common local foundation for [issue #7](https://github.com/MGYamada/ProjectAinos/issues/7), building on [PR #29](https://github.com/MGYamada/ProjectAinos/pull/29). The [variational guide](variational.md) describes the endpoint and its hypotheses. The [smooth-algebra guide](smooth-algebra.md) describes the free smooth-function rings and their directional chain rule. Compact base regions now also supply domination without a support condition on the variation, and the interval identity handles covector–vector pairings.

[Shared variational formalization notes](variational-notes.md) record the measure, regularity, and smooth-algebra distinctions exposed by these proofs.

## Mechanics Proof Development

The [C∞ mechanics research plan](cinfty-mechanics.md) preserves the mathematical blueprint, the 52 Landau–Lifshitz targets, proposed proofs, experiment ledger, and references from the former local TeX manuscript. It distinguishes the implemented real analytic model from the planned abstract C∞-ring constructions.

`ProjectAinos/Mechanics` uses the shared foundation for a real time interval and a real normed position space, including any finite number of generalized coordinates. For a jointly C² Lagrangian `L(t,q,v)` and a C² path, Lean proves the derivative of the actual action, its first-variation formula with the endpoint momentum pairing, and the equivalence between fixed-endpoint stationarity and the Euler–Lagrange equations on `(a,b)` for `a < b`. Variations may have nonzero derivatives at the endpoints. Smooth operations from the shared C∞-ring give mechanical Lagrangians with the required regularity automatically. The natural scalar Lagrangian yields `m q'' = −V'(q)`.

Adding the total time derivative of a function of time and position changes the action by its endpoint difference. Lean proves that fixed-endpoint stationarity is preserved and that the Euler–Lagrange covector agrees pointwise. [Total time derivatives](mechanics.md#total-time-derivatives)

The mechanics guide gives the assumptions and proof map. The formalization notes record distinctions and design decisions exposed by the proofs. The algebraic core of the plan is in the shared algebra layer: partial derivatives of smooth operations, dual numbers and C∞-derivations ([issue #74](https://github.com/MGYamada/ProjectAinos/issues/74)). `Mechanics/Jet` then proves, in every jet C∞-ring, that total derivatives are null Lagrangians, the energy and Noether identities, Newton's equations for natural Lagrangians, and conservation of energy, momentum, the centre-of-mass integral and angular momentum as membership in the Euler–Lagrange ideal. `Mechanics/Jet/FreeParticle` characterizes the Lagrangian of a free particle: a function of the velocities is quasi-invariant under infinitesimal boosts exactly when it is a polynomial of degree at most two, and with isotropy it is `½ μ |v|²` up to a constant. `Mechanics/Jet/Galilei` lets the Galilei algebra act on the standard jet ring by the prolongations of `δq = A q + a + t u` and by `∂/∂t`, proves their commutators, and proves that such a field preserves the Euler–Lagrange ideal of a Lagrangian that it changes by a total derivative. `Mechanics/Jet/Metric` extends this to natural Lagrangians with a position-dependent kinetic form: momenta, Lagrange's equations, the energy and its conservation, with plane polar co-ordinates as a model. The standard jet ring, the free C∞-ring on time and the jet coordinates, is a jet ring; its vector fields are built from the dual numbers without analysis. [Jet rings and conservation laws](mechanics.md#jet-rings-and-conservation-laws) · [Ledger](cinfty-mechanics.md#ledger) `SmoothAlgebra/Poisson` defines Poisson structures on a C∞-ring with antisymmetry, the chain rule and the Jacobi identity as the only laws. It proves Poisson's theorem, Noether's theorem in Hamiltonian form, the normalizer of a coisotropic ideal, Hamilton–Jacobi and Maupertuis–Jacobi, and that the Jacobi identity on a free ring is a condition on generators. The models are the canonical bracket with Hamilton's equations, the rigid body with Euler's equations and the Casimir `|L|²`, the angular momentum of a particle with its `so(3)` momentum map as a Poisson morphism, the heavy top with its equations of motion and Casimirs, the Galilei algebra of a free particle, the virial identity, the Coriolis and centrifugal terms of a uniformly rotating frame, and Kepler's problem with a formal inverse radius adjoined as a generator: the six identities of the Runge–Lenz vector with their dependence on the relation `ρ² |q|² = 1`, and conservation of the Runge–Lenz vector along smooth solutions of the inverse-square law. Along a trajectory of a Hamiltonian on a free C∞-ring every observable evolves by its bracket with the Hamiltonian, so integrals of the motion are constant along trajectories. [Poisson structures](smooth-algebra.md#poisson-structures) · [Poisson models](mechanics.md#poisson-models) `Mechanics/Jet/Prolongation` connects the jet-ring identities to trajectories: the prolongation of a smooth path turns the total derivative into `d/dt`, and a conserved element is constant along every smooth solution, in particular the energy along solutions of Newton's equations. `Mechanics/Jet/Analytic` proves that, for a Lagrangian given by a smooth function of time, position and velocity, a smooth path is a solution in this sense exactly when the action of the real analytic model is stationary on every interval, so the jet-ring conservation laws hold along stationary paths. `Mechanics/Rigid` proves the kinematics of a rigid body by linear algebra: `so(3) ≅ ℝ³` as Lie algebras, the angular velocity of a family of rotations and its independence of the origin, and the inertia tensor of point masses with `M = I Ω`, the parallel-axis theorem and the triangle inequality for the principal moments, and Eulerian angles with the angular velocity in the body frame and the kinetic energy of the symmetric top. It proves the regular precession of the free symmetric top, and on the Lie–Poisson phase space the permanent rotations, their stability about the axes of the greatest and the least moment by an integral of the motion, and the signs of the linearized equations. `Mechanics/TwoBody` proves the algebra of two bodies: the reduced mass, disintegration in the centre-of-mass frame, the characterization of elastic collisions with the formulas for a target at rest, and the canonical centre-of-mass variables. `Mechanics/Oscillations` proves the general solution of `ẍ + ω² x = 0` with its amplitude, phase, energy and period, the flow of the oscillator, and the linearization of a Hamiltonian vector field at an equilibrium as the vector field of the quadratic part of the Hamiltonian. It also proves the three cases of the damped equation `ẍ + 2γ ẋ + ω₀² x = 0` and, for friction with a dissipative function `F`, the identity `X(H) = −2F` with the energy not increasing along the motion. For the forced equation it proves that every solution approaches the steady state when the damping is positive, the amplitude and phase of the steady state for a periodic force, and the exact resonance curve with its maximum at `Ω = ω₀` and its width `2γ`. Without friction it proves Duhamel's formula for an arbitrary smooth force, with existence and uniqueness for all initial data, the energy transferred in a finite time, and the unbounded growth at resonance. For several degrees of freedom it proves the simultaneous diagonalization of the two quadratic forms and the separation of the equations in normal co-ordinates, and for a periodic coefficient the monodromy relation and stability when the trace of the monodromy matrix is less than two. For a variable frequency it computes the derivative of the action variable `E/ω` along a solution exactly. The equations `M ẍ + K x = 0` are the Euler–Lagrange equations of the Lagrangian of small oscillations and Hamilton's equations of the quadratic Hamiltonian; quadratic Hamiltonians correspond to the matrices of `sp(2n, ℝ)` with linear Hamiltonian vector fields, and the normal co-ordinates are an invertible linear canonical transformation that brings the Hamiltonian to a sum of oscillators. For the canonical formalism it proves the chain rule for a substitution out of a free C∞-ring, the Legendre correspondence for natural Lagrangians and for every Lagrangian whose Legendre transformation has an inverse morphism, the canonical property of the transformation given by a free generating function `F(q, Q)`, Jacobi's theorem on complete integrals for a given curve, Stäckel's theorem that an action satisfying the separated equations solves the Hamilton–Jacobi equation, and Liouville's theorem in infinitesimal form. `Mechanics/Similarity` proves the mechanical similarity of the solutions for a homogeneous potential, the virial theorem for time averages, and for Kepler's problem the equation of the orbit and the third law for similar orbits. In the shared algebra layer, `SmoothAlgebra/Point` identifies the states of a system with the morphisms of its ring of functions to the dual numbers: pairs of a position and a velocity for a free ring, and the states tangent to the equations for a presented ring. The shared layer also proves that a parametric integral of a smooth function is smooth and Hadamard's lemma, so the quotient of a C∞-ring by an ordinary ideal is a C∞-ring, and the quotient of a Poisson C∞-ring by a Poisson ideal and the reduced ring `N(I)/I` are Poisson C∞-rings. On this the mechanics layer proves the reduction with respect to cyclic co-ordinates, the reduced mass as the reduction of two particles by translations, and the equations of motion of the Routhian. For a central field it proves that polar co-ordinates are canonical, obtains the radial Hamiltonian with the centrifugal energy by reduction, and writes the time and the angle as integrals over the radius, on an interval without a turning point and between two simple turning points; the period of Kepler's problem follows. General momentum maps, the reduction by the rotation group in space and cotangent modules remain stages of [issue #78](https://github.com/MGYamada/ProjectAinos/issues/78). [Mechanics guide](mechanics.md) · [Formalization notes](mechanics-notes.md)

The Kepler API documentation distinguishes the signed radius `r = ρ |q|²` from the ordinary distance. At real points satisfying `ρ² |q|² = 1`, `|r| = |q|`, with `r = |q|` on the positive branch `ρ > 0`. Both signs remain allowed by the definitions and the orbit identity. This corrects the distance terminology without changing declarations, proofs or ledger statuses ([M76](mechanics-notes.md#m76-kepler-distance-is-a-signed-radius)).

The proofs of the remaining rows are tracked in [issue #114](https://github.com/MGYamada/ProjectAinos/issues/114). The first step is the linear differential equation. The Volterra operator of a coefficient curve is quasi-nilpotent, `‖(V_A)ⁿ‖ ≤ ‖A‖ⁿ/n!`, so the integral equation operator is invertible for every continuous coefficient and the earlier hypothesis `‖A‖ < 1` is not needed. `SmoothGeometry/ODE/Propagator` defines the propagator `Φ(t, s)` of `y' = A(t) y` for all real times by a change of scale inside the coefficient, and proves the differential equation, uniqueness, the composition law, invertibility, and smooth dependence on a parameter and the two times; constant coefficients give the exponential. With it the equation `ẍ + p(t) x = 0` has a unique solution for given initial data and every smooth `p`, so every coefficient has exactly one fundamental system and a monodromy matrix. For a coefficient of period `T` every solution is bounded for `t ≥ 0` if and only if `|tr M| < 2` or `M = ±1`; in the hyperbolic case the bounded solutions are those on the stable eigenline, and in the parabolic case the others grow linearly. The width of the instability zone follows from an expansion of the propagator for a small coefficient, `‖Φ(t, s) y − y − ∫ A y − ∫ A ∫ A y‖ ≤ e^{g (t − s)} (g (t − s))³/6 · ‖y‖`, in which the trace of the term of second order is half the trace of the square of `∫ A`. For `ẍ + ω₀² (1 + h cos γt) x = 0` the co-ordinates that rotate with the frequency `γ/2` make the coefficient small and change the sign of the trace after a period, and the integral of the coefficient over a period is computed. The result is `|tr M + 2 − (4π²/γ⁴)((ω₀² − γ²/4)² − ω₀⁴ h²/4)| ≤ eʳ r³/3` with `r = (8π/γ²)(|ω₀² − γ²/4| + ω₀² |h|)`: an unbounded solution exists when `ω₀⁴ h²/4 − (ω₀² − γ²/4)²` exceeds the remainder, for example at `γ = 2ω₀` and `0 < |h| ≤ 1/400`, and all solutions are bounded when the opposite difference exceeds it. Row 27 is *proved* with this scope; the ledger has 33 rows proved ([M78](mechanics-notes.md), [M79](mechanics-notes.md)). [Parametric resonance](mechanics.md#parametric-resonance)

The second step treats given families of solutions. On a finite-dimensional space the determinant of the propagator is `exp ∫ tr A` (Liouville's formula), from Jacobi's formula for the derivative of the determinant at the identity. For a family `Φ(t, x)` of solutions of `ẋ = X(x)` that is twice continuously differentiable, the derivative in the initial point solves the variational equation `M′ = DX(Φ) M`, so `det D_x Φ(t, x) = exp ∫₀ᵗ tr DX(Φ(s, x)) ds`. Solutions of an equation with a continuously differentiable field are unique, so `Φ(t, ·)` is injective; if `tr DX = 0` it preserves the measure of every measurable set in its domain, and a family defined for all times and points is measure preserving. This is Liouville's theorem for a given flow, with the flow of a linear field of trace zero as an instance. For a family of paths `q(s, t)` with moving end times whose reference path solves the Euler–Lagrange equation, the derivative of the action is `p · dq − E · dt` taken between the two ends; the proof is Leibniz's rule with moving limits and an integration by parts. The action functions `m x²/2T` of the free particle and `(m ω x²/2) cot ωT` of the oscillator, away from the conjugate times, are instances. The flow of a nonlinear field and the families of solutions with given end points are not constructed, so rows 43 and 46 stay *informal* and the count is unchanged ([M80](mechanics-notes.md)). [The action as a function of its end points](mechanics.md#canonical-formalism)

The third step constructs the flow. For a smooth vector field `X` on a Banach space, the solution through `x` traversed up to the time `τ` is a curve `γ` on the unit interval with `γ(σ) = x + τ ∫₀^σ X(γ)`, in which the time is a factor. The map `((τ, x), γ) ↦ γ − x − τ ∫ X(γ)` is smooth on the space of continuous curves, because the superposition operator `γ ↦ X ∘ γ` is smooth for the supremum norm, and its derivative in `γ` is the equation operator of the linear equation with the coefficient `τ DX(γ)`, which is invertible for every coefficient by the first step. An implicit function theorem on a neighbourhood then gives `SmoothGeometry.NonlinearODE.flow`: its domain is open, it is smooth in the time and the point together, it solves the equation, a solution between two times is the flow, and `Φ(s + t, x) = Φ(t, Φ(s, x))`. No interval is subdivided. A solution that stays in a compact set exists for the whole time, and on a finite-dimensional space a field of linear growth has a flow defined for all times. A derivation of a free C∞-ring on finitely many generators is a vector field on `ℝⁿ` whose divergence, the trace of its derivative, is the value of `Σₐ ∂ₐ (D xₐ)`; its integral curves in the algebraic sense are the solutions of the differential equation. For the Hamiltonian field `(∂H/∂p, −∂H/∂q)` the divergence is zero, so the flow of every Hamiltonian of the free C∞-ring preserves the Lebesgue measure of the measurable sets in its domain, and a flow defined for all times is measure preserving: Liouville's theorem. The oscillator and the pendulums `Σ pᵢ²/2mᵢ − k Σ cos qᵢ` have flows defined for all times, and with friction the phase volume of the oscillator is multiplied by `exp (−Σ aᵢ/mᵢ · t)`. Row 46 is *proved* for a Hamiltonian that is smooth on all of `ℝ²ⁿ`; the ledger has 34 rows proved ([M81](mechanics-notes.md)). [Hamiltonian flows](mechanics.md#hamiltonian-flows-and-liouvilles-theorem)

The fourth step applies the end-point formula to the flow. The action `∫ (Σ pᵢ q̇ᵢ − H) dt` of a curve in the phase space has the Lagrangian `θ_z(ż) − H(z)` with `θ = Σ pᵢ dqᵢ`; its momentum is `θ`, its energy is `H`, and its Euler–Lagrange equations are Hamilton's equations. So for a curve of initial points and moving times the derivative of the action of the solutions is `θ` of the displacement of the end point minus `H` times the displacement of the time, at the two ends: `dS = p dq − H dt` on the families of solutions that the flow provides. The derivative of a Hamiltonian field paired with `ω = Σ dqᵢ ∧ dpᵢ` is the symmetric Hessian of the Hamiltonian, and with the variational equation the flow preserves `ω`: the map of the flow at every time is a canonical transformation. For a fixed initial position, if the derivative of the end position in the initial momentum is invertible, the implicit function theorem gives the initial momentum as a smooth function of the time and the end point, and the action of the solution is then a function `S(T, q)` with `dS = Σ pᵢ dqᵢ − H dT`; its derivatives along all lines come from the formula above and assemble to the Fréchet derivative because they depend continuously on the point. Hence `∂S/∂T + H(q, ∂S/∂q) = 0`. For a free particle the hypothesis holds at every time other than zero. Row 43 is *proved* in the Hamiltonian form, for a Hamiltonian that is smooth on all of `ℝ²ⁿ`; the ledger has 35 rows proved ([M82](mechanics-notes.md)). [The action along the flow](mechanics.md#the-action-along-the-flow-of-a-hamiltonian)

The fifth step is the motion in one dimension in a well, `H = p²/2m + U(x)` between two simple turning points `a < b` of the energy `E`. The second divided difference of `U` is a smooth function of three variables, and `E − U(x) = (x − a)(b − x) W(x)` with `W` positive on `[a, b]`; the turning points are smooth functions of the energy by the implicit function theorem. With `x = (a + b)/2 − (b − a)/2 · cos θ` and `p = √(2m) · (b − a)/2 · sin θ · √W` the level curve is a smooth closed curve that is tangent to the Hamiltonian field with a positive rate `λ = dt/dθ`, so the turning points are ordinary points of it. The motion is the curve run with the angle that solves `dθ/dt = 1/λ`; it exists for all times and has the period `T = ∫₀^{2π} λ dθ = √(2m) ∫ dx/√(E − U)`, and every solution with this energy between the turning points has the same period, by the uniqueness of solutions. The derivative of the identity `p²/2m + U = E` in the energy gives `d/dE ∮ p dx = T` (Proposition 68). Abel's inversion formula follows from Tonelli's theorem: for every measurable potential, `∫ (∫ dx/√(E − U)) dE/√(V − E)` is `π` times the measure of the set where `U < V`, and on nested wells the inner integral is the period. The action variable `I = (1/2π) ∮ p dx` has `dI/dE = T/2π`, the angle variable `φ = 2π t/T` moves uniformly along the motion, and `dx ∧ dp = dφ ∧ dI` in the chart of the energy and the angle. Rows 11, 12 and 50 are *proved* with the scopes written in the rows; the ledger has 38 rows proved ([M83](mechanics-notes.md)). [Motion in one dimension](mechanics.md#motion-in-one-dimension-wells)

The sixth step is the rigid body. A rigid motion is a curve `c(t)` of vectors and a curve `R(t)` of rotation matrices, and the body is a finite family of masses at `c + R rₐ`. With Newton's equations for the particles as hypotheses, the sum of the momenta is `μ ċ` for an origin at the centre of mass, and its derivative is the sum of the forces; the moment of the momenta about the origin of the body is `R (I Ω)` with `Ω` the vector of the skew-symmetric matrix `Rᵀ Ṙ`, because a rotation maps the cross product to the cross product, and its derivative is the moment of the forces when the origin is the centre of mass or is at rest. In the body frame this is `d(I Ω)/dt = I Ω × Ω + Rᵀ K`, and a vector fixed in space satisfies `Γ̇ = Γ × Ω`; in principal axes these are the Lie–Poisson equations of the free body and, for a fixed point in a uniform field, of the heavy top. The same equations come from Hamilton's principle on the curves of rotations. For a smooth family of orthogonal matrices `∂R/∂ε = R η̂`, and the symmetry of the second derivatives gives `∂Ω/∂ε = ∂η/∂t + Ω × η`; so the derivative of the action of `Ω · J Ω/2 − V(Rᵀγ)` is `[J Ω · η]` at the ends minus the integral of `(d(J Ω)/dt − J Ω × Ω − Γ × ∇V(Γ)) · η`. The Cayley transform is a rational map from vectors to rotations with the derivative `ξ ↦ ξ̂` at the identity, so every field `η` is the variation field of a family, and the action is stationary with fixed ends exactly when the equations hold. Conversely the rotation is the solution of the linear equation `Ṙ = R Ω̂` for a given `Ω(t)`, for all times, and for a solution of Euler's equations `R L` is constant. For the asymmetrical top the amplitude `am` is the solution of `φ′ = √(1 − k² sin² φ)`, a flow on the line of a positive bounded field; `sn = sin am`, `cn = cos am` and `dn = am′` have the derivatives `cn dn`, `−sn dn` and `−k² sn cn`, and `am` increases by `π` in the time `2K`. A curve `(A cn, B sn, C dn)(pt)` solves Euler's equations when three algebraic relations hold, and these determine `B`, `p` and `k` from a point `(A, 0, C)` with `M² > 2E I₁`; the amplitude is surjective, so every point of this regime is on such a curve, and by uniqueness every solution is one. The other regime exchanges two axes. Rows 34 and 37 are *proved* with the scopes written in the rows; the ledger has 40 rows proved ([M84](mechanics-notes.md)). [The equations of motion of a rigid body](mechanics.md#the-equations-of-motion-of-a-rigid-body)

The seventh step is the symmetry of the vibrations of a molecule. With a simultaneous diagonalization `Sᵀ M S = 1`, `Sᵀ K S = diag λ`, the spaces of the modes are the eigenspaces of `M⁻¹ K`; they are independent, the columns of `S` lie in them, and so the space of the co-ordinates is their internal direct sum, the space of the value `c` having as many dimensions as there are indices with `λ = c`. A group that acts by maps commuting with `M` and `K` preserves each of these spaces, and the trace of an element is the sum of its traces on them. For a real representation `σ` of a finite group the dimension of the space of the equivariant maps from `σ` to another representation is the scalar product of the characters, so the number of the modes of the symmetry type `σ`, summed over the frequencies, is `(1/|G|) Σ χ(g) χ_σ(g⁻¹)`. For a molecule the group acts on the displacements by the Kronecker product of the permutation of the atoms and the matrix on space, with the character `N_g · tr O_g`. The translations and the rotations `uₐ = t + ω × rₐ` are the image of an equivariant map from the vectors and the axial vectors, because an orthogonal matrix takes `x × y` to `det O · (O x × O y)`; their character is `(1 + det O_g) tr O_g`. Where they are exactly the modes of frequency zero, the vibrations of the type `σ` are counted with `(N_g − 1 − det O_g) tr O_g`, and there are `3N − 6` vibrations. This hypothesis is proved for three atoms that are not on a line, joined by three springs: the displacements annihilated by the matrix of the springs stretch no bond, and such a displacement is a translation and a rotation, with the rotation given by an explicit formula in the cross products. The equilateral molecule with the six permutations of its corners has the totally symmetric type once, the sign type never and the permutation representation twice, and the isosceles molecule with its four symmetries has two symmetric vibrations, one antisymmetric under the exchange of the atoms of the base, and none out of the plane. Row 24 is *proved* with the scope written in the row; the ledger has 41 rows proved ([M85](mechanics-notes.md)). [Symmetry of the normal modes](mechanics.md#symmetry-of-the-normal-modes)

The eighth step is the method of averaging, in two statements. If `ż = F(z) + r(t)` and `Ż = F(Z)` start at the same point, `F` is Lipschitz with the constant `K` and the integral of `r` from `0` to `t` has norm at most `δ` on the interval, then `u = z − Z − ∫ r` satisfies `‖u̇‖ ≤ K ‖u‖ + K δ` and vanishes at `0`, so `‖z − Z‖ ≤ δ e^{Kt}` by Gronwall's inequality; the perturbation is not small, only its integral is. And an integration by parts gives `|∫₀ᵗ φ(s) sin ωs ds| ≤ (2 sup |φ| + t sup |φ′|)/ω`. For the motion in a rapidly oscillating field, `m ẍ = −U′(x) + ω g(x) cos ωt`, the velocity is `w + (g(x)/m) sin ωt`, and the equations of `(x, w)` are those of the motion in the effective potential `U + g²/4m` plus the terms `(g/m) sin ωt`, `−(g′ w/m) sin ωt` and `(g g′/2m²) cos 2ωt`; their amplitudes have bounded derivatives along the motion when `U′`, `U″`, `g`, `g′`, `g″` are bounded, and the velocity is bounded independently of `ω`. Hence `|x(t) − X(t)| ≤ C/ω` on a given interval of time, with `C` independent of the frequency; both motions exist for all times, and for the pendulum with an oscillating support the upper position is a minimum of the effective potential exactly when `b² > 2 m a`. For the resonance of `ẍ + 2λ ẋ + ω₀² x = F cos γt − β x³`, the amplitudes of `x = a cos γt + b sin γt` satisfy exact equations, which are the field `(−λ a − (ε − κ r²) b, −λ b + (ε − κ r²) a + f)` with `ε = (γ² − ω₀²)/2γ`, `κ = 3β/8γ`, `f = F/2γ`, plus terms in `cos 2γt`, `sin 2γt`, `cos 4γt`, `sin 4γt` with polynomial amplitudes. The equilibria of the field are the solutions of `r² ((ε − κ r²)² + λ²) = f²`. On a disc the amplitudes and their derivatives along a motion are bounded by compactness, and the general statement for a finite sum of harmonics gives a constant `C` such that, for these slow parameters and every `γ`, the amplitudes of a motion and the solution of the averaged equations differ by at most `C/γ` on a given interval of time. Rows 29 and 30 are *proved* with the scopes written in the rows; the ledger has 43 rows proved ([M86](mechanics-notes.md)). [Motion in a rapidly oscillating field](mechanics.md#motion-in-a-rapidly-oscillating-field)

The ninth step is the anharmonic oscillator, in two parts that do not depend on each other. The formal part is the Birkhoff normal form in `ℝ[[q, p]]`, the ring `MvPowerSeries (Fin 2) ℝ` with the bracket `∂f/∂q ∂g/∂p − ∂f/∂p ∂g/∂q`. The series of order at least `n` form a filtration in which a sequence with successive differences of increasing order has a limit and a series of every order is zero. A linear map `D` that raises the order has the exponential `Σ Dᵏ/k!`. If `D` is a derivation of a bilinear map `B` that lowers the order by a fixed amount, the Leibniz rule for `Dⁿ/n!` writes the partial sum of `exp D` on `B(f, g)` as a triangular sum, which differs from `B` of the partial sums by terms of high order, so `exp D` preserves `B`. With `B` the product and `B` the bracket, the Lie transform `exp {W, ·}` of a series `W` of order at least three is an endomorphism of the algebra that preserves the bracket, by the Jacobi identity; it is bijective because it differs from the identity by a map that raises the order. The bracket with `I = (q² + p²)/2` is `q ∂/∂p − p ∂/∂q`. On the homogeneous series of degree `k` it is skew for the pairing `Σ a! b! f_{ab} g_{ab}`, since multiplication by `q` is adjoint to `∂/∂q`; hence its image and its kernel span the space, and a recursion on the coefficients shows that the kernel consists of the multiples of `I^{k/2}` for even `k` and is zero for odd `k`. So every homogeneous `G` is `{I, F} + c I^{k/2}`. Adding to `W` a term of order `k` changes `exp {W, ·} H` by the bracket of that term with `H` up to the order `k + 1`; choosing the term from the homological equation makes the component of degree `k` a multiple of `I^{k/2}` and leaves the lower components. The limit `W` of these partial generators gives `exp {W, ·} H = h(I)`. For `ν I + a q³ + b q⁴` the generators of degree three and four are explicit polynomials and give `h = ν x + (3b/2 − 15a²/4ν) x² + ⋯`; a canonical scaling carries `p²/2 + ν² q²/2 + α q³/3 + β q⁴/4` to this form, with the coefficient `3β/8ν² − 5α²/12ν⁴`. The part on solutions uses the wells of the fourth step. For the potential `ν² x²/2 + α x³/3 + β x⁴/4` the second divided difference is a polynomial. The centre of the oscillation of half-width `ρ` is `ρ² e(ρ²)` with `e` smooth, by the implicit function theorem applied to the equation that the potential has the same value at both ends; `e(0) = −α/3ν²`. The period is the integral over the angle of the level curve of `1/√(P − ρ B cos θ)`, with `P` and `B` functions of `ρ²` and `cos² θ`. The rates at `θ` and `θ + π` add to `√(2P + 2√(P² − R))/√(P² − R)` with `R = ρ² B² cos² θ`, which is a differentiable function of `ρ²` at zero. Differentiation under the integral gives the derivative `5πα²/6ν⁵ − 3πβ/4ν³` of the period in `ρ²` at zero, so the frequency `2π/T` is `ν + (3β/8ν − 5α²/12ν³) ρ² + o(ρ²)`, the value that the normal form gives at the action `ν ρ²/2`. This is Landau–Lifshitz §28 for one degree of freedom.

The tenth step is adiabatic invariance. For the oscillator `ẍ + ω(t)² x = 0`, the action `I = (ẋ² + ω² x²)/2ω` and the product `K = x ẋ` satisfy `İ = −(ω̇/2ω²) K̇` and `|K| ≤ I`, so the corrected action `I + (ω̇/2ω²) K` has the derivative `K d(ω̇/2ω²)/dt`. For `ω = Ω(εt)` this derivative is `ε² a′(εt) K` with `a = Ω′/2Ω²`. Since `|İ| ≤ ε b I` with `b` a bound of `|Ω′/Ω|`, Gronwall's inequality gives `I(t) ≤ I(0) e^{bT}` up to the time `T/ε`; the corrected action then changes by at most `ε T sup |a′| e^{bT} I(0)`, and it differs from `I` by at most `ε sup |a| I`. Hence `|I(t) − I(0)| ≤ C ε I(0)` for `0 ≤ t ≤ T/ε`, with `C` depending on `Ω` and `T` only. The general statement has the same form. Let `ż = X(z, λ)` with `λ = Λ(εt)`, let `I(z, λ)` be invariant under the field with a fixed parameter, and let `G(z, λ)` have the derivative `∂I/∂λ` along that field. Then `I − ε Λ′ G` has the derivative `−ε² (Λ″ G + Λ′² ∂G/∂λ)` along the motion, and `|I(t) − I(0)| ≤ ε (T (L₂ M₀ + L₁² M₁) + 2 L₁ M₀)` up to the time `T/ε` while the motion stays where the bounds hold. For `H = p²/2m + V(λ, x)` the function `I` is the action variable `A(H, λ)/2π`. The turning points of a family of wells are smooth functions of the energy and the parameter by the implicit function theorem, the factor of the well is smooth in the parameter, and so the period and the area are smooth, as integrals over the angle of the level curve. Differentiating the identity `p²/2m + V = E` on the level curves along a family, and integrating by parts in the angle, gives `dA = T dE − (∮ ∂V/∂λ dt) dλ`. So `∂I/∂λ = (T ∂V/∂λ − ∮ ∂V/∂λ dt)/2π` at a fixed point of the phase space, and the mean of this function over a period of the motion with a fixed parameter is zero. For a continuous function `φ` of period `T` and mean zero, `r ↦ T ∫₀¹ σ φ(Tσ + r) dσ` is `(1/T) ∫_r^{r+T} v φ(v) dv`, whose derivative at zero is `φ(0)`. Therefore `G(w) = T ∫₀¹ σ (∂I/∂λ)(Φ_{Tσ} w) dσ`, with `Φ` the flow with the parameter held fixed, has the required derivative along the flow; it is smooth near the level curves because the flow is smooth in the time and the point and the period is a smooth function of the point. The adiabatic theorem follows for a motion that stays in a compact set of points of the level curves. This is Landau–Lifshitz §49 for one degree of freedom.

The eleventh step is scattering. A motion in a central field is described in the plane of the orbit by the radius and the polar angle, with `ṙ² = F(r)` and `φ̇ = ℓ/r²`. If `F(r) = (r − r₀) W(r)` after the closest approach `r₀`, with `W` positive and bounded, then `r = r₀ + s²` turns the equation into `ṡ = ½ √W(r₀ + s²)`. This field is smooth, positive and bounded, so its solution through zero is defined for all times, is odd and increases to infinity; the radius is an even function of the time with `ṙ² = F(r)`, and differentiating this identity gives `r̈ = F′(r)/2`, with the value at the closest approach taken from the limit of the slope of `F`. The position `r (cos φ, sin φ)` then has an acceleration along the radius, `F′(r)/2 − ℓ²/r³`, which is `−U′(r)/m`. After the closest approach the radius is an injective differentiable function of the time, so the integral of a function of the radius over `(r₀, r(T)]` is the integral of `ṙ` times the function over `(0, T]`; for the density `(ℓ/ρ²)/√F(ρ)` this is the integral of `φ̇`, that is `φ(T) − φ(0)`. The singularity of the density at `r₀` is covered, because the formula is one of Lebesgue integrals. When the radius tends to infinity and the density is integrable at infinity, the angle tends to `φ₀ = ∫_{r₀}^∞ (ℓ/ρ²) dρ/√F(ρ)`. The velocity `(ṙ cos φ − (ℓ/r) sin φ, ṙ sin φ + (ℓ/r) cos φ)` tends to `v∞ (cos φ₀, sin φ₀)`, and by the symmetry in the time to `v∞ (−cos φ₀, sin φ₀)` before the scattering; the scalar product of the two is `v∞² cos (π − 2φ₀)`, so the angle between them is `arccos (cos (π − 2φ₀))`, which is `|π − 2φ₀|` when `|π − 2φ₀| ≤ π`; otherwise `π − 2φ₀` is the unwrapped angle. For the Coulomb field `F = v∞² (1 − 2a/r − ρ²/r²) = v∞² (r − r₀)(r + r₁)/r²` with `r₀ = a + √(a² + ρ²)` and `r₁ = √(a² + ρ²) − a`; the density has the primitive `arccos ((ρ²/r + a)/√(a² + ρ²))`, which vanishes at `r₀`, so `φ₀ = arccos (a/√(a² + ρ²))` and `χ = π − 2φ₀` has `cot (χ/2) = ρ/a`. The cross-section is the push-forward of the measure `2πρ dρ` by the deflection function. Where the deflection function has an injective differentiable inverse `b` on a set `A` of angles, the measure of `b(A)` is `∫_A 2π b |b′| dχ`, which is `∫_A (b |b′|/sin χ) 2π sin χ dχ`. With `b = a cot (χ/2)` the density is `(a/2)²/sin⁴ (χ/2)`. This is Landau–Lifshitz §§18–19.

The twelfth step is small-angle scattering. Write the relative potential as `ε g(ρ/r) = 2(U(r) − U(∞))/m v∞²` with `g` a smooth function on the line, so that in the variable `u = ρ/r` the square of the radial velocity is `v∞² h(u)`, `h(u) = 1 − u² − ε g(u)`. If `c` is a zero of `h`, then `h(u) = (c² − u²)(1 + ε Γ(c, u))` with `Γ(c, u) = (g(c) − g(u))/(c² − u²)`, the divided difference of `g` over `c + u`, which is smooth for `c + u ≠ 0`. If `c > 0` and `1 + ε Γ(c, u) > 0` for `0 ≤ u ≤ c`, then `h > 0` before `c`, so `ρ/c` is the closest approach, the factor of the eleventh step is `v∞² (c/r)(c + ρ/r)(1 + ε Γ(c, ρ/r))` and the motion exists. The change of variables `r = ρ/(c sin ψ)` between `r > ρ/c` and `0 < ψ < π/2`, again the formula for an injective differentiable map, turns the angle (18.4) into `φ₀ = ∫₀^{π/2} dψ/√(1 + ε Γ(c, c sin ψ))`: the factor `c² − u² = c² cos² ψ` cancels the Jacobian, and the integrand is continuous on the closed interval. For a potential `g(l, u)` with a parameter `l` the zero `c(ε, l)` near `c(0, l) = 1` is a smooth function by the implicit function theorem, since `∂h/∂u = −2` there; the integrand is then smooth on an open set that contains `{(0, l)} × [0, π/2]`, so `φ₀(ε, l)` is smooth at `(0, l)`. Its value at `ε = 0` is `π/2` and its derivative in `ε` is `−½ ∫₀^{π/2} Γ(1, sin ψ) dψ`, in which the derivative of `c` does not appear because the integrand is `1` at `ε = 0`. Since `Γ(1, sin ψ) sin ψ cos ψ = (g(1) − g(sin ψ)) tan ψ` has the derivative `Γ(1, sin ψ) − sin ψ g′(sin ψ)` and vanishes at both ends, the integral is `∫₀^{π/2} sin ψ g′(sin ψ) dψ`, and with `r = ρ/sin ψ` it is `−ρ ∫_ρ^∞ (d/dr) g(ρ/r) dr/√(r² − ρ²)`. Hence `χ = π − 2φ₀ = −(2ρ/m v∞²) ∫_ρ^∞ U′(r) dr/√(r² − ρ²) + R`, the formula (20.3). The remainder is bounded by the second derivative: the set where `φ₀` is twice continuously differentiable is open and contains `{0} × K` for a compact set `K` of parameters, hence `[−δ, δ] × K`, on which the second derivative in `ε` is bounded by some `M`, and `|R| ≤ M ε²`; a compact set is covered by finitely many sets on which a turning point is given. For `U(r) = ε r⁻ⁿ w(1/r)` with `w` smooth the normalized profile in `u` is `(ε/ρⁿ) · 2 (uⁿ w(u/ρ) − 0ⁿ w(0))/m v∞²`, smooth in `u`, `1/ρ` and `1/m v∞²` including `1/ρ = 0`, so that the strength is `ε/ρⁿ` and the remainder is at most `M (ε/ρⁿ)²` for all `ρ ≥ ρ₁` and `v∞ ≥ v₁`: for `n = 0` a small coupling, for `n ≥ 1` a large impact parameter. For the Coulomb field `g(u) = u`, `ε = 2a/ρ`, the coefficient is `∫₀^{π/2} sin ψ dψ = 1`, and the theorem gives `|χ − 2a/ρ| ≤ M (2a/ρ)²` for the angle `π − 2 arccos (a/√(a² + ρ²))` of the eleventh step.

The thirteenth step is Maupertuis' principle. Let `L = T(q, q̇) − U(q)` and fix an energy `E`. The Lagrangian of the abbreviated action is `ℓ = 2 √((E − U) T)`, defined and smooth where `(E − U) T > 0`. Its derivative in `(q, q̇)` is `((E − U) dT − T dU)/√((E − U) T)`, and at a point with `T + U = E` and `U < E` the square root is `E − U = T`, so the derivative is `dT − dU`, the derivative of `L`. Hence along a curve of the energy `E` the momenta `∂ℓ/∂q̇` and `∂L/∂q̇` are the same function of the time, the forces are the same, and the Euler–Lagrange expressions of `ℓ` and of `L` coincide. The theorem on stationary curves for a Lagrangian that is smooth on an open set of positions and velocities then gives the principle: a curve of the energy `E` in the region `U < E` makes `∫ ℓ dt` stationary for variations with fixed ends exactly when it satisfies the equations of motion, and on it `ℓ = 2T`, which is `p q̇` when `T` is homogeneous of degree two (Euler's relation). For the Jacobi metric, `ℓ` is positively homogeneous of degree one in the velocity. Differentiating `Λ(q, c w) = c Λ(q, w)` shows that `∂Λ/∂q` is homogeneous of degree one and `∂Λ/∂w` of degree zero, so for `q = γ ∘ σ` with `σ′ > 0` the momentum of `q` at `t` is that of `γ` at `σ(t)`, the force is multiplied by `σ′`, and the Euler–Lagrange expression of `q` at `t` is `σ′(t)` times that of `γ` at `σ(t)`. The energy of the metric is `ℓ²/2 = 2 (E − U) T`, whose derivative is `ℓ dℓ`; along a curve on which `ℓ` is a constant `ℓ₀` its Euler–Lagrange expression is `ℓ₀` times that of `ℓ`. For a curve of the energy `E` and `dσ/dt = 2 (E − U) = ℓ(q, q̇)`, homogeneity gives `ℓ(γ, γ′) = 1`, and the three facts combine: the Euler–Lagrange expression of `L` along `q` is `σ′` times that of `2 (E − U) T` along `γ`. The neighbourhood of `σ(t)` on which `ℓ(γ, γ′) = 1` is the image of a neighbourhood of `t`, because `σ` has a strict derivative different from zero. The parameter `σ = ∫ 2 (E − U(q)) dt` and, conversely, the time `τ = ∫ 2 T(γ, γ′) dx = ∫ dx/2 (E − U)` on a curve of unit velocity are primitives of continuously differentiable positive functions, twice continuously differentiable, and have twice continuously differentiable inverses on an open interval.

The fourteenth step is the separation of the variables on a box. A Hamiltonian of Stäckel's form is `H = Σᵢ Ψᵢ(q) (gᵢ(qᵢ) pᵢ²/2 + uᵢ(qᵢ))` with `Σᵢ Ψᵢ(q) φᵢⱼ(qᵢ) = δ_{j j₀}`. With `pᵢ² = Rᵢ(qᵢ, α) = 2 (Σⱼ φᵢⱼ αⱼ − uᵢ)/gᵢ` each bracket is `Σⱼ φᵢⱼ αⱼ`, and the sum over `i` with the weights `Ψᵢ` is `α_{j₀}`: this is the Hamilton–Jacobi equation for `S = −α_{j₀} t + Σᵢ εᵢ ∫_{cᵢ}^{qᵢ} √Rᵢ dx`, whose derivative in `qᵢ` is `εᵢ √Rᵢ` by the fundamental theorem of calculus. Replacing `αⱼ` by `a` changes `Rᵢ` by `2 φᵢⱼ (a − αⱼ)/gᵢ`, so on a box where the radicands are positive the integrand is continuously differentiable in `(a, x)` and the derivative of the integral in `a` is `Θᵢⱼ = ∫ φᵢⱼ/(gᵢ √Rᵢ) dx`. The matrix of the mixed derivatives is `diag(εᵢ/(gᵢ √Rᵢ)) φ`, so its determinant vanishes only with that of `φ`. For Jacobi's theorem let `Σᵢ εᵢ Θᵢⱼ(Qᵢ(t)) − δ_{j j₀} t` be constant. The derivative in `t` is `Σᵢ yᵢ φᵢⱼ = δ_{j j₀}` with `yᵢ = εᵢ Q̇ᵢ/(gᵢ √Rᵢ)`; the row `Ψ` satisfies the same equations, and `det φ ≠ 0` gives `y = Ψ`, that is `Q̇ᵢ = Ψᵢ gᵢ pᵢ = ∂H/∂pᵢ`. For the momenta, along the line of the co-ordinate `qᵢ` the function `H(q, P(q))` with `Pᵢ = εᵢ √Rᵢ(qᵢ)` is the constant `α_{j₀}`; since `H` is quadratic in `pᵢ`, `H(q, P) = H(q, p̄) + Ψᵢ gᵢ (Pᵢ² − p̄ᵢ²)/2`, and the derivative at the point where `Pᵢ = p̄ᵢ` is `∂H/∂qᵢ + Ψᵢ gᵢ p̄ᵢ Pᵢ′ = 0`. Hence `ṗᵢ = Pᵢ′ Q̇ᵢ = −∂H/∂qᵢ`. The three systems of §48 are instances with three co-ordinates. For `x = ρ cos φ`, `y = ρ sin φ` the square of the velocity is `ρ̇² + ρ² φ̇² + ż²`, and `ρ̇² + ż²` is `ṙ² + r² θ̇²` for `ρ = r sin θ`, `z = r cos θ`, `(ξ + η)(ξ̇²/ξ + η̇²/η)/4` for `ρ = √(ξ η)`, `z = (ξ − η)/2`, and `σ² (ξ² − η²)(ξ̇²/(ξ² − 1) + η̇²/(1 − η²))` for `ρ = σ √((ξ² − 1)(1 − η²))`, `z = σ ξ η`. The kinetic energy `Σᵢ q̇ᵢ²/(2 Ψᵢ gᵢ)` of a system has `H` as its Legendre transform, and the matrices are `[[1, −1/r², 0], [0, 1, −1/sin² θ], [0, 0, 1]]`, `[[ξ, 1, −1/ξ], [η, −1, −1/η], [0, 0, 1]]` and `[[ξ², 1, −1/σ²(ξ² − 1)], [−η², −1, −1/σ²(1 − η²)], [0, 0, 1]]`, with the determinants `1`, `−(ξ + η)` and `−(ξ² − η²)`.

The fifteenth step is the invariant tori of commuting flows. Two smooth fields commute if `DA·B = DB·A`. Along a solution of `A` the vector `v(t) = D_xΦ_A(t, x) B(x) − B(Φ_A(t, x))` satisfies `v′ = DA(Φ_A) v`, by the variational equation and the commutation, and `v(0) = 0`, so `v = 0`: the flow of `A` carries `B` into itself. Then `r ↦ Φ_A(r, Φ_B(r, x))` solves the equation of `A + B`, and the flow of `A + B` is the composition of the flows. For fields `Xᵢ` that commute in pairs, define `g^t` as the flow of `Σᵢ tᵢ Xᵢ` at the time `1`; on a set `M` that all these flows preserve and on which they are complete, `g^{t+s} = g^t g^s`, an action of `ℝ^ι`. Suppose that at every `x ∈ M` the map `t ↦ g^t x` is injective near zero and maps the neighbourhoods of zero onto neighbourhoods of `x` in `M`. Each orbit is then open in `M`, and so is the union of the other orbits; a connected `M` is one orbit. The periods `{t : g^t x = x}` are a subgroup, the same at all points since the action is commutative and transitive, and zero is isolated in it. If `M` is compact, finitely many of the neighbourhoods cover it, so `ℝ^ι = K + periods` with `K` compact; a linear functional that vanishes on the periods is then bounded, hence zero, and the periods span `ℝ^ι`. A discrete subgroup that spans is the set of integer combinations of a basis `b`, and in the angles `θ` with `t = Σ θᵢ bᵢ` the map `θ ↦ g^t x` is onto `M`, with the fibres `θ + ℤ^ι`; the flow of `Σ sᵢ Xᵢ` is `θ ↦ θ + r b⁻¹ s`. The hypothesis on `M` holds for a level set `F = c` of a smooth `F : E → ℝ^κ` with `DF·Xᵢ = 0`, `dim E = |ι| + |κ|`, at whose points `DF` is onto and the `Xᵢ` are independent. The joint flow is smooth in `(t, x)` because `(t, x) ↦ (t, g^t x)` is the flow of the field `(0, Σ tᵢ Xᵢ)`, and its derivative at `(0, x)` is `(τ, v) ↦ Σ τᵢ Xᵢ(x) + v`. With a right inverse `L` of `DF(x)`, the map `(t, s) ↦ g^t (x + L s)` has at zero the derivative `(τ, σ) ↦ Σ τᵢ Xᵢ(x) + L σ`, which is injective (apply `DF(x)`) and hence bijective by the count of dimensions; by the inverse function theorem it is a homeomorphism near zero. Since `F(g^t y) = F(y)` and `s ↦ F(x + L s)` is injective near zero, its points on the level set are those with `s = 0`. For elements `Fᵢ` of the phase space ring with `{Fᵢ, Fⱼ} = 0` the derivative of `G` along the Hamiltonian field of `H` is the value of `{G, H}`, so the fields are tangent to the level sets, and the component `a` of `DX_i·X_j` is the value of `{{x_a, F_i}, F_j}`; the Jacobi identity gives the commutation. Independent differentials give independent fields and a derivative `DF` that is onto. A compact connected level set with independent differentials is therefore a torus on which the motion of every Hamiltonian `Σ sᵢ Fᵢ` is conditionally periodic. For oscillators `Fᵢ = (qᵢ² + pᵢ²)/2` the level set with positive energies is a product of circles.

The sixteenth step is the action–angle variables near an invariant torus. Let the level set `F = c` be compact. A bounded open neighbourhood `U` of it has a compact frontier, whose image under `F` is closed and does not contain `c`; over the complement `B` of this image a level set does not meet the frontier, so a solution that starts in `U` over `B` stays in `U`, and the flows are complete on `F⁻¹(B) ∩ U`. For integrals in involution take the transversal `L a = Σₖ aₖ ∇Fₖ(x₀)`: the symplectic form vanishes on it, because `ω(∇Fⱼ, ∇Fₖ)` is the value of `{Fⱼ, Fₖ}`, and `DF(x₀) L` is the Gram matrix of the gradients, which is invertible. The joint flow preserves the symplectic form and carries each field into itself, and `ω(X_H, w) = dH(w)`; hence in the co-ordinates `(s, t) ↦ g^t (x₀ + L s)` the form is `Σᵢ dtᵢ ∧ dGᵢ`, where `G(s) = F(x₀ + L s)`. If `g^b x₀ = x₀`, the chart of the fifteenth step at `x₀` gives `g^b (x₀ + L s) = g^{τ(s)} (x₀ + L s′)` with a smooth `τ`, and `s′ = s` because `F` is constant along the flows and `G` is injective; so `e(s) = b − τ(s)` is a period of `x₀ + L s`. The derivative of `g^{e(s)} (x₀ + L s) = x₀ + L s`, inserted into the form, gives `Σᵢ ((De a)ᵢ DGᵢ a′ − (De a′)ᵢ DGᵢ a) = 0`. Take a basis `b₁, …, bₙ` of the periods of `x₀` with its families `eₖ(s)`, and the angles `φ` with `t = Σₖ (φₖ/2π) eₖ(s)`. By the symmetry the form is `Σₖ dφₖ ∧ Aₖ` with `Aₖ = (1/2π) Σᵢ eₖ(s)ᵢ dGᵢ`. For a family of curves `γ(ε, r)` the derivative of `∫ θ(γ)(∂ᵣγ) dr` is the boundary term `θ(γ)(∂_εγ)` plus `∫ (θ(∂_εγ)(∂ᵣγ) − θ(∂ᵣγ)(∂_εγ)) dr`, by the symmetry of the second derivative and an integration by parts; for `θ = p dq` the integrand is `ω(∂ᵣγ, ∂_εγ)`. For the cycle `r ↦ Ψ(s, φ + 2π r 1ₖ)` the boundary terms cancel and the integrand is `2π Aₖ(s) a`, so `(1/2π) ∮ p dq` has the derivative `Aₖ(s) a` in a direction `(a, α)`: it does not depend on the angles, and `Aₖ` is the differential of the action `Iₖ(s)`. A function whose derivatives along the lines are given by continuous linear maps that depend continuously on the point is differentiable, by the mean value inequality. At `s = 0` the map `A` is invertible, since `b` is a basis and `DG(0)` is invertible, and the inverse function theorem makes the actions co-ordinates: `Ψ(J, φ)` is canonical, the integrals are functions `H(J)`, and the flow of `Fᵢ` moves the angles with the velocities `∂Hᵢ/∂Jₖ`, because `⟨T ν, DG a⟩ = ⟨ν, A a⟩` for the times `T ν = Σₖ (νₖ/2π) eₖ`. A curve `r ↦ Ψ(J, φ + r ν′)` with `ν′ = Σᵢ wᵢ ν_i` solves the equation of a Hamiltonian whose field is `Σᵢ wᵢ(F) X_{Fᵢ}`, so it is its flow. A canonical map has an injective derivative, so `Ψ` is a local homeomorphism with an open image. Reduce the angles to the cube `[0, 2π]^ι`: a sequence of pairs of distinct points near the torus with the same image has a subsequence that converges to two points of the torus with the same image; these differ by a period, and after the shift by it both sequences converge to one point, at which `Ψ` is injective. Hence `Ψ` is injective up to the periods on a neighbourhood of the torus.

The seventeenth step is the accuracy of the adiabatic invariant. For the oscillator `ẍ + ω² x = 0` with the phase `θ`, `θ̇ = ω`, put `B = (ω x + i ẋ) e^{iθ} ω^{−1/2}`. Then `|B|² = 2I` and `Ḃ = (ω̇/2ω) e^{2iθ} B̄`. If the frequency is a function of the slow phase, `ω = exp q(s)` with `s = ε θ`, this is `dB/ds = g(s) e^{2is/ε} B̄` with `g = q′/2`: a linear system `u′ = g e^{2is/ε} w`, `w′ = g e^{−2is/ε} u` for `(u, w) = (B, B̄)`, whose coefficient `A(s)` is holomorphic where `g` is. Let `Φ_η(s₁, s₀)` be the propagator of `A(s + iη)` along the line of the height `η`. Since `∂A/∂η = i ∂A/∂s`, the function `∂Φ_η/∂η − i (A(s₁ + iη) Φ_η − Φ_η A(s₀ + iη))` solves the equation in `s₁` and vanishes at `s₁ = s₀`, so it is zero: the propagator depends on the height only through the coefficient at the two ends. The equation of `∂Φ/∂η` is the symmetry of the second derivative of the solution in the parameter and the time. On the line of the height `σ` the coefficients are `g e^{2is/ε} e^{−2σ/ε}` and `g e^{−2is/ε} e^{2σ/ε}`; for the unknowns `(e^{2σ/ε} u, w)` they are `g e^{±2is/ε}`, bounded by `m(s) ≥ |g(s + iσ)|`. By Gronwall's inequality with the integral of the coefficient the propagator of this system is at most `e^{G}`, `G ≥ ∫ m`, and the entry of `Φ_σ` from `w` to `u` is at most `e^{G} e^{−2σ/ε}`. Hence the entry `β` of the propagator on the real line satisfies `|β| ≤ e^{G} e^{−2σ/ε} + C (m(s₁) + m(s₀))`, with `C` depending on `ε`, and the second term tends to zero as `s₀ → −∞`, `s₁ → +∞`. On the real line the two coefficients are conjugate, so the propagator is complex linear, commutes with `(u, w) ↦ (w̄, ū)` and preserves `|u|² − |w|²`. Its matrix is therefore `(α, β; β̄, ᾱ)` with `|α|² − |β|² = 1`, and for `B₁ = α B₀ + β B̄₀` the triangle inequality gives `| |B₁|² − |B₀|² | ≤ |B₀|² |β| (4|β| + 2)`. The limits of `I` exist: `|İ| ≤ 2 Ẇ I` for `W = ∫₀^{εθ} m`, which is bounded and monotone, so `I e^{2W}` is monotone and bounded. Passing to the limits in the inequality for two times gives `|I(+∞) − I(−∞)| ≤ e^{G} (4 e^{G} + 2) e^{−2σ/ε} I(−∞)`.

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

## Quantum Field Theory Prototype

`QuantumFieldTheory/SmearedField` defines a Hermitian scalar smeared field on a common dense invariant domain, proves closability of its operators, and proves positivity of finite sums of vacuum words. It is an initial part of Gate A of [issue #46](https://github.com/MGYamada/ProjectAinos/issues/46).

`QuantumFieldTheory/LocalityExamples` adds causality-sensitive regressions for the locality predicate ([issue #72](https://github.com/MGYamada/ProjectAinos/issues/72)). Bump tests whose closed supports are closed coordinate balls give explicit witnesses in the time-first `(-+++)` convention: unit bumps displaced along a spatial axis are spacelike separated, and unit bumps displaced along the time axis have only timelike differences. `SpacelikeSeparated` is proved symmetric and invariant under conjugation of either test. The two-point field `φ(f) = f(p) A + f(q) B` with symmetric noncommuting `A` and `B` is local exactly when `p − q` is not spacelike, and the proof of locality uses the separation hypothesis. Its Pauli instance is local for timelike insertion points while having the explicit commutator `2 e₁` on timelike separated tests, and fails locality for spacelike insertion points. These are regression models for the locality predicate: no vacuum, covariance, spectrum condition or multipoint distribution is assumed, and they are not Wightman fields. [QFT prototype guide](quantum-field-theory-prototype.md)
