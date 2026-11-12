# General relativity: intrinsic clocks and quadratic variation

This is the first physics-layer increment of stage E in
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

The intrinsic clock/action constructions work on arbitrary smooth
manifolds. The above geodesic **variational equivalence currently requires
the model manifold**. The open-domain calculus supplies local tools but
does not yet constitute a theorem for general manifold variations or
first-variation gluing across chart boundaries.

## Proved examples and validation

[SpecialRelativity](../ProjectAInos/GeneralRelativity/SpecialRelativity.lean)
proves exact equality with the existing SR proper-speed and proper-time
functionals on Minkowski space, and with the four-dimensional free action
and its Mechanics formulation. These are functional equalities, not only
evaluations on inertial lines.

[ClockExamples](../ProjectAInos/GeneralRelativity/ClockExamples.lean)
contains the following Lean proofs:

| Metric and curve | Result |
| --- | --- |
| Nonlinear flat metric, `γ(s)=(s,-s²)` | Proper-speed rate `1`, proper time `b-a`, free action `-m(b-a)`. |
| `exp(2x²)(-dt²+dx²)`, clock at fixed spatial `x` | Timelike, rate `exp(x²)`, proper time `(b-a) exp(x²)`. |
| Same curved clock | Quadratic action `-(b-a) exp(2x²)/2`. |

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
It runs in the existing non-required Experiments workflow. These exact
calculations test conventions; Lean establishes the formal claims.

## Remaining stage E obligations

- Construct manifold curve variations and prove first-variation covariance,
  chart-crossing gluing and boundary cancellation.
- Prove stationarity of the massive square-root action iff the timelike
  curve is a geodesic up to regular reparametrization, with `m > 0`.
- Construct a proper-time parameter and prove its affine-geodesic consequence.
- Connect null initial-data preservation to the full manifold variational
  result, without restricting variations to null curves.

This increment does not complete stage E or #52. Curved exterior
calculus/Hodge/Maxwell (F) and the controlled time-dependent Newtonian
motion/trajectory limit (G) remain. Einstein dynamics belongs to §5.2 and
the Maxwell field action to §4.2 / #44.
