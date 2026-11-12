# General relativity: intrinsic clocks and particle variation

This is the implemented physics layer for stage E in
[§5.1 / issue #52](https://github.com/MGYamada/ProjectAInos/issues/52).
The shared connection, curvature and motion APIs are described in the
[smooth-geometry guide](smooth-geometry.md). Definitions here use the actual
tangent bundle, time first, signature `(-+++)`, and `c = 1`. The dimension
parameter is the number of spatial coordinates. No global frame or norm on
native tangent fibres is added.

## Intrinsic proper time and actions

For a smooth `LorentzMetric .timeNegative d M`,
[ProperTime](../ProjectAInos/GeneralRelativity/ProperTime.lean) defines
`Timelike g v` by `g(v,v) < 0`, `properSpeed g v = sqrt(-g(v,v))`, and
`properTime g γ a b` as the directed interval integral of the velocity's
proper speed. The functional is total; its physical interpretation for
massive clocks uses timelike curves. Reversing integration limits changes
its sign, and it is nonnegative for `a ≤ b`.

Local C¹ regularity near every point of the closed integration interval
gives continuity and integrability. `properTime_add` permits subdivision
without assuming a single chart contains the curve. `properTime_chart`
computes each segment in any smooth maximal-atlas chart whose source contains
that segment, using the metric and velocity obtained from native tangent
maps. `properTime_map` proves preservation under a map differentiable along
the curve that preserves its velocity's metric square; source and target
dimensions may differ.

`properTime_reparametrize` assumes local C¹ regularity of the curve and
parameter map, and nonnegative parameter derivative on the interval.
It permits zero derivative. This is an integral substitution theorem; it
does not construct an inverse or a proper-time parameter. For an affine
geodesic, metric-norm conservation evaluates the integral as interval
length times the initial proper-speed rate.

Under a timelike hypothesis, `fourVelocity_unit` gives metric square `-1`.
For a locally C² timelike curve, `hasDerivAt_speedAlong` proves

\[
\frac{ds}{dt}=-\frac{g(\nabla_{\dot\gamma}\dot\gamma,\dot\gamma)}{s},
\qquad s=\sqrt{-g(\dot\gamma,\dot\gamma)}.
\]

[ParticleAction](../ProjectAInos/GeneralRelativity/ParticleAction.lean)
defines `quadraticAction = ∫ ½g(γ̇,γ̇)` and `freeAction = -m * properTime`.
It proves integrability, interval subdivision, chart expressions for the
quadratic action, parameter invariance of the free action, and evaluation
along affine geodesics. Null reference curves have zero quadratic action
and proper time. No restriction to null variations is imposed, and zero
action alone is not a stationarity criterion.

## Actual first variation and affine geodesics in model coordinates

[QuadraticLagrangian](../ProjectAInos/GeneralRelativity/QuadraticLagrangian.lean)
treats `L(t,q,v) = ½B(q)(v,v)` on a finite-dimensional normed coordinate
space. It differentiates the position-dependent coefficients and both
velocity slots, deriving force, momentum and the Euler–Lagrange covector.
For a C² metric coefficient field on an **open** position domain and a C²
reference curve staying there on `[a,b]`, the existing
`Mechanics.OpenDomain` theorem proves the derivative of the actual action.
Small variations remain admissible by compactness. The open-domain theorem
also proves fixed-endpoint stationarity iff the Euler–Lagrange covector
vanishes on `(a,b)`, for `a < b`.

[QuadraticGeodesic](../ProjectAInos/GeneralRelativity/QuadraticGeodesic.lean)
then takes a native Lorentz metric on the model manifold `MinkowskiModel d`.
The metric can be curved and nonconstant. `modelMetric` gives its smooth
coordinate bilinear form. The intrinsic action equals the mechanical
action, and Koszul's formula proves

\[
\operatorname{EL}(w)=-g(\nabla_{\dot\gamma}\dot\gamma,w).
\]

The sign agrees with the Mechanics convention `force − d(momentum)/dt`.
`quadraticAction_hasDerivAt` proves the actual first variation, including
the endpoint term for an arbitrary C² variation:

\[
\delta S=[g(\dot\gamma,\eta)]_a^b
-\int_a^b g(\nabla_{\dot\gamma}\dot\gamma,\eta)\,dt.
\]

`quadraticAction_stationary_iff_geodesic` assumes a C² reference curve
and `a < b`. Stationarity quantifies over all smooth fixed-endpoint
coordinate variations, with no causal constraint. It is equivalent to
the native affine geodesic equation on `(a,b)`, using nondegeneracy of the
Lorentz metric. No geodesic equation or desired variation formula is
assumed as part of a data structure.

The coordinate theorem remains available for the model manifold. The native
`QuadraticStationary` theorem below proves the equivalence for arbitrary
Lorentz manifolds and actual fixed-endpoint families crossing chart boundaries.

## Massive stationarity and constructed proper-time parameters

[FreeLagrangian](../ProjectAInos/GeneralRelativity/FreeLagrangian.lean)
works on the open jet domain `q ∈ U` and `B(q)(v,v) < 0`. It proves
smoothness there, differentiates the actual action using
`Mechanics.OpenDomain`, and derives the full Euler–Lagrange covector.
Differentiating the factor `m/s` in the momentum retains the proper-speed
derivative. No global smoothness across the null cone is asserted.

[FreeGeodesic](../ProjectAInos/GeneralRelativity/FreeGeodesic.lean) proves,
for a native smooth metric on the model manifold and locally C² timelike
curves,

\[
\operatorname{EL}_{\rm free}(w)=-\frac{m}{s}
 g\left(\nabla_{\dot\gamma}\dot\gamma-\frac{s'}s\dot\gamma,w\right).
\]

For `m > 0`, `a < b`, a C² reference curve and timelikeness throughout
`[a,b]`, stationarity of the actual free action is equivalent to this
non-affine acceleration equation on `(a,b)`. Equivalently, it is tangential
acceleration, with its coefficient derived by metric compatibility.
`freeAction_stationary_iff_localGeodesic` proves both directions of
stationarity iff each interior point has a regular C² local parameter
change making the curve an affine geodesic. Its conclusion uses actual
open partial homeomorphisms, positive inverse derivative and the native
geodesic predicate on the whole parameter target. At unit proper-speed
rate, stationarity is equivalent to the affine equation in the given
parameter.

The parameter is constructed in
[ProperTimeParameter](../ProjectAInos/GeneralRelativity/ProperTimeParameter.lean),
which works on **arbitrary Lorentz manifolds**. For a C² timelike curve on
an open parameter interval, the fundamental theorem of calculus gives
`d(properTime g γ t₀)/dt = speedAlong g γ t`; the clock is C² with positive
derivative. The inverse function theorem constructs a local C² inverse
with derivative `1/s`, and the reparametrized curve has unit rate.
Tangential native acceleration is equivalent to the required speed factor;
the full second-derivative parameter law proves that the constructed
inverse removes it. The converse parameter law is also proved.

[FiniteProperTime](../ProjectAInos/GeneralRelativity/FiniteProperTime.lean)
extends this construction to one inverse covering an entire finite timelike
segment. Its hypotheses are C² regularity at every point of `[a,b]`, including
the endpoints, and timelikeness there. These give a slightly larger open
interval. [Variational.Parameter](../ProjectAInos/Variational/Parameter.lean)
constructs an open partial homeomorphism on that interval from positivity of
the clock derivative; inverse C² regularity follows from the inverse function
theorem. The forward and inverse images of the closed intervals are proved,
as are `r(0)=a`, `r(T)=b`, inverse derivative `1/s` and unit rate at both
endpoints. Here `T = properTime g γ a b`, positive when `a < b`.
Tangential acceleration throughout `(a,b)` yields affine motion throughout
`(0,T)`. The model-manifold stationarity theorem consequently supplies this
single finite-segment parameter. No geodesic completeness is asserted.

## Native manifold-family first variations

[CurveFamily](../ProjectAInos/SmoothGeometry/Lorentzian/CurveFamily.lean)
defines the velocities of a genuine two-parameter family `Γ : ℝ × ℝ → M`
by `mfderiv`, in actual tangent fibres. C² joint regularity implies C¹
bundle regularity of these velocities. Zero torsion and symmetry of second
coordinate derivatives prove `∇ε ∂t Γ = ∇t ∂ε Γ`. The statement imposes no
immersion, nonzero parameter velocity or global chart assumption, and supports
both Lorentz conventions.

[VariationDensity](../ProjectAInos/GeneralRelativity/VariationDensity.lean)
uses this interchange law and metric compatibility to differentiate the actual
scalar densities for signature `(-+++)`. Writing `T = ∂t Γ` and `V = ∂ε Γ`,
their derivatives in the first parameter are `g(∇t V,T)` for `½g(T,T)` and
`(m/s) g(∇t V,T)` for `-m s`. The latter requires timelikeness only at the
point of differentiation.

[VariationAction](../ProjectAInos/GeneralRelativity/VariationAction.lean)
now differentiates the actual finite action integrals. Joint C² regularity is
required only at points `(ε₀,t)` of the closed reference segment, with
timelikeness there for the massive action. `Variational.IntervalParameter`
localizes the scalar integrand near this compact set to a globally C¹
representative. Compactness bounds its parameter derivative on a common
parameter neighborhood, justifying differentiation under the integral.
Domination and global regularity are derived, not supplied by the caller.
This construction uses scalar functions on the parameter plane and requires
no chart containing the full spacetime curve.

[VariationBoundary](../ProjectAInos/GeneralRelativity/VariationBoundary.lean)
uses metric compatibility to prove the intrinsic endpoint formulas

\[
\delta S_2=[g(V,T)]_a^b-\int_a^b g(V,\nabla_tT)\,dt,
\qquad
\delta S_m=[(m/s)g(V,T)]_a^b
-\int_a^b (m/s)g\bigl(V,\nabla_tT-(s'/s)T\bigr)\,dt.
\]

`quadraticAction_family_deriv_add` and `freeAction_family_deriv_add` prove
that actual derivatives add over subdivisions. These native formulas use the
same endpoint pairing at a junction, so internal boundary terms cancel even
when adjacent segments use different coordinate charts.

[VariationStationary](../ProjectAInos/GeneralRelativity/VariationStationary.lean)
takes actual fixed endpoints for nearby variation parameters and derives zero
endpoint variation fields. It proves that every affine geodesic is stationary
under these manifold families for the quadratic action, with no causal
restriction on variations. Timelike tangential acceleration likewise implies
massive stationarity; metric compatibility determines the speed factor.

[ManifoldCurve](../ProjectAInos/Variational/ManifoldCurve.lean) defines
`ManifoldCurveVariation`: an actual two-parameter family through the reference
curve, jointly C² near each point of the finite reference segment, fixing both
endpoints for nearby parameters. `chartCurveVariation` constructs one from a
C² coordinate perturbation whose topological support lies in an interior time
patch mapped into a smooth chart. Outside the patch it is the reference curve;
the support condition proves smooth gluing.

`LocalizedVariation` proves that the actual native variation field is exactly
the prescribed chart field. `VariationTesting` applies the fundamental lemma
to compact scalar tests in a small chart near each time. Metric nondegeneracy
forces the residual to vanish. Realizability of tests is proved, not supplied
as a premise. `AccelerationRegularity` derives continuous native acceleration
from C² curve regularity.

[ManifoldStationary](../ProjectAInos/GeneralRelativity/ManifoldStationary.lean)
quantifies `QuadraticStationary` and `FreeStationary` over all such families.
For `a < b` and local C² regularity along `[a,b]`:

- `quadraticStationary_iff_geodesic` proves equivalence to affine motion on `(a,b)`.
- `freeStationary_iff_acceleration`, for positive mass and a timelike reference
  segment, proves `∇tT = (s'/s)T`; `freeStationary_iff_tangential` is equivalent.
- [ManifoldMotion](../ProjectAInos/GeneralRelativity/ManifoldMotion.lean) proves
  equivalence to actual regular local affine reparametrization. Unit proper
  speed gives the affine equation, and `freeStationary_finite_properTime`
  constructs one inverse of the actual clock integral over the full segment.
- The affine equation extends to finite endpoints by continuity.
  `QuadraticStationary.null_initial` preserves both nonvanishing and zero
  metric norm on the closed segment. The family space has no null constraint.

These results require no global chart, global frame, orientation, time
orientation, completeness, or global Hausdorff hypothesis.

## Proved examples and validation

[SpecialRelativity](../ProjectAInos/GeneralRelativity/SpecialRelativity.lean)
proves exact equality with the existing SR proper-speed and proper-time
functionals on Minkowski space, and with the four-dimensional free action
and its Mechanics formulation. These are functional equalities, not only
evaluations on inertial lines.

The [clock examples](../ProjectAInos/GeneralRelativity/ClockExamples.lean)
and particle examples below include the following Lean proofs:

| Metric and curve | Result |
| --- | --- |
| Nonlinear flat metric, `γ(s)=(s,-s²)` | Proper-speed rate `1`, proper time `b-a`, free action `-m(b-a)`. |
| `exp(2x²)(-dt²+dx²)`, clock at fixed spatial `x` | Timelike, rate `exp(x²)`, proper time `(b-a) exp(x²)`. |
| Same curved clock | Quadratic action `-(b-a) exp(2x²)/2`. |
| Nonlinear flat metric, `γ(s)=(exp(s),-exp(2s))` | Timelike, native acceleration equals velocity, rate `exp(s)`, proper time `exp(b)-exp(a)`. |

[ParticleExamples](../ProjectAInos/GeneralRelativity/ParticleExamples.lean)
proves that the exponential clock makes the massive action stationary for
positive mass on every nontrivial finite interval, while its quadratic
action is not stationary in that parameter. The constructed finite-segment
inverse is explicitly `r(τ) = log(τ + exp(a))`, maps both endpoints correctly,
has unit rate and gives affine motion on the full proper-time interior.

[VariationExamples](../ProjectAInos/GeneralRelativity/VariationExamples.lean)
constructs the family with inertial coordinates `T=t+εt(1-t)`, `X=ε²t(1-t)`
and evaluates it in the nonlinear shear chart. It is smooth and fixes both
endpoints for every parameter. The native manifold theorems prove zero
derivatives of both actual actions on `[0,1]`; this family is nonlinear in
both time and the variation parameter.

The same module constructs a smooth compact chart test supported in
`[1/4,3/4]`, fixing the endpoints `0,1` and realizing any prescribed chart
tangent vector at `1/2`. It also proves massive stationarity and failure of
quadratic stationarity for the exponential clock under all native families.

A clock at a fixed spatial coordinate is not claimed to be a geodesic.
Typed contracts in
[GeneralRelativityAPI](../checks/GeneralRelativityAPI.lean) use default
elaborator options and fix regularity, domain, signature and endpoint
hypotheses. The required Lean job includes this check. The transitive axiom
audit covers the new namespace and rejects an absent GR import. Only
`propext`, `Classical.choice` and `Quot.sound` are allowed.

The independent Lorentz SymPy entry point checks the flat, shear and curved
Euler–Lagrange/acceleration identities, nonvanishing endpoint variations,
clock rates and integrals, and unconstrained directions at a null velocity.
It also differentiates the square-root density independently in all three
metrics and checks the exponential clock's non-affine term and its explicit
proper-time inverse, including both finite-segment endpoints. Genuine
two-parameter families test the mixed covariant derivative law and both density
derivatives independently in flat, shear and curved conformal metrics.
They also verify the endpoint/residual identities, subdivision with a nonzero
junction pairing, and stationarity of the nonlinear fixed-endpoint family.
Localized C² polynomial cutoffs independently check zero-extension gluing,
chart test velocities and stationarity. A supported spatial test detects the
nonzero quadratic and massive first variations of the accelerated conformal
clock at `x=1`. It runs in the existing non-required Experiments workflow. These exact
calculations test conventions; Lean establishes the formal claims.

## Scope after stage E

The stage E principal proof endpoints are implemented and awaiting review.
Stage F now has native form bundles, pullback, exterior differentiation,
wedge calculus, positive chart-covariant density and a glued oriented volume
form. The [geometry guide](smooth-geometry.md) records these proofs and their
flat, nonlinear-chart and curved examples. Lorentz Hodge and the curved
Maxwell comparison (F), together with the controlled time-dependent Newtonian
motion/trajectory limit (G), remain. Einstein dynamics belongs to §5.2 and
the Maxwell field action to §4.2 / #44.
