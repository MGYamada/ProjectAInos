# General relativity: intrinsic clocks and particle variation

This is the implemented physics layer for particle variation and the
time-dependent Newtonian motion limit in
[§5.1 / issue #52](https://github.com/MGYamada/ProjectAinos/issues/52).
The shared connection, curvature and motion APIs are described in the
[smooth-geometry guide](smooth-geometry.md). Definitions here use the actual
tangent bundle, time first, signature `(-+++)`, and `c = 1`. The dimension
parameter is the number of spatial coordinates. No global frame or norm on
native tangent fibres is added.
The [C∞ general relativity research plan](cinfty-general-relativity.md)
extends this proof map to the Einstein, gravitational-radiation and cosmology
targets of §§81–119. The §5.1 delivery is merged; Einstein dynamics remains
a separate research stage.

## Intrinsic proper time and actions

For a smooth `LorentzMetric .timeNegative d M`,
[ProperTime](../ProjectAinos/GeneralRelativity/ProperTime.lean) defines
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

[ParticleAction](../ProjectAinos/GeneralRelativity/ParticleAction.lean)
defines `quadraticAction = ∫ ½g(γ̇,γ̇)` and `freeAction = -m * properTime`.
It proves integrability, interval subdivision, chart expressions for the
quadratic action, parameter invariance of the free action, and evaluation
along affine geodesics. Null reference curves have zero quadratic action
and proper time. No restriction to null variations is imposed, and zero
action alone is not a stationarity criterion.

## Actual first variation and affine geodesics in model coordinates

[QuadraticLagrangian](../ProjectAinos/GeneralRelativity/QuadraticLagrangian.lean)
treats `L(t,q,v) = ½B(q)(v,v)` on a finite-dimensional normed coordinate
space. It differentiates the position-dependent coefficients and both
velocity slots, deriving force, momentum and the Euler–Lagrange covector.
For a C² metric coefficient field on an **open** position domain and a C²
reference curve staying there on `[a,b]`, the existing
`Mechanics.OpenDomain` theorem proves the derivative of the actual action.
Small variations remain admissible by compactness. The open-domain theorem
also proves fixed-endpoint stationarity iff the Euler–Lagrange covector
vanishes on `(a,b)`, for `a < b`.

[QuadraticGeodesic](../ProjectAinos/GeneralRelativity/QuadraticGeodesic.lean)
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

[FreeLagrangian](../ProjectAinos/GeneralRelativity/FreeLagrangian.lean)
works on the open jet domain `q ∈ U` and `B(q)(v,v) < 0`. It proves
smoothness there, differentiates the actual action using
`Mechanics.OpenDomain`, and derives the full Euler–Lagrange covector.
Differentiating the factor `m/s` in the momentum retains the proper-speed
derivative. No global smoothness across the null cone is asserted.

[FreeGeodesic](../ProjectAinos/GeneralRelativity/FreeGeodesic.lean) proves,
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
[ProperTimeParameter](../ProjectAinos/GeneralRelativity/ProperTimeParameter.lean),
which works on **arbitrary Lorentz manifolds**. For a C² timelike curve on
an open parameter interval, the fundamental theorem of calculus gives
`d(properTime g γ t₀)/dt = speedAlong g γ t`; the clock is C² with positive
derivative. The inverse function theorem constructs a local C² inverse
with derivative `1/s`, and the reparametrized curve has unit rate.
Tangential native acceleration is equivalent to the required speed factor;
the full second-derivative parameter law proves that the constructed
inverse removes it. The converse parameter law is also proved.

[FiniteProperTime](../ProjectAinos/GeneralRelativity/FiniteProperTime.lean)
extends this construction to one inverse covering an entire finite timelike
segment. Its hypotheses are C² regularity at every point of `[a,b]`, including
the endpoints, and timelikeness there. These give a slightly larger open
interval. [Variational.Parameter](../ProjectAinos/Variational/Parameter.lean)
constructs an open partial homeomorphism on that interval from positivity of
the clock derivative; inverse C² regularity follows from the inverse function
theorem. The forward and inverse images of the closed intervals are proved,
as are `r(0)=a`, `r(T)=b`, inverse derivative `1/s` and unit rate at both
endpoints. Here `T = properTime g γ a b`, positive when `a < b`.
Tangential acceleration throughout `(a,b)` yields affine motion throughout
`(0,T)`. The model-manifold stationarity theorem consequently supplies this
single finite-segment parameter. No geodesic completeness is asserted.

## Native manifold-family first variations

[CurveFamily](../ProjectAinos/SmoothGeometry/Lorentzian/CurveFamily.lean)
defines the velocities of a genuine two-parameter family `Γ : ℝ × ℝ → M`
by `mfderiv`, in actual tangent fibres. C² joint regularity implies C¹
bundle regularity of these velocities. Zero torsion and symmetry of second
coordinate derivatives prove `∇ε ∂t Γ = ∇t ∂ε Γ`. The statement imposes no
immersion, nonzero parameter velocity or global chart assumption, and supports
both Lorentz conventions.

[VariationDensity](../ProjectAinos/GeneralRelativity/VariationDensity.lean)
uses this interchange law and metric compatibility to differentiate the actual
scalar densities for signature `(-+++)`. Writing `T = ∂t Γ` and `V = ∂ε Γ`,
their derivatives in the first parameter are `g(∇t V,T)` for `½g(T,T)` and
`(m/s) g(∇t V,T)` for `-m s`. The latter requires timelikeness only at the
point of differentiation.

[VariationAction](../ProjectAinos/GeneralRelativity/VariationAction.lean)
now differentiates the actual finite action integrals. Joint C² regularity is
required only at points `(ε₀,t)` of the closed reference segment, with
timelikeness there for the massive action. `Variational.IntervalParameter`
localizes the scalar integrand near this compact set to a globally C¹
representative. Compactness bounds its parameter derivative on a common
parameter neighborhood, justifying differentiation under the integral.
Domination and global regularity are derived, not supplied by the caller.
This construction uses scalar functions on the parameter plane and requires
no chart containing the full spacetime curve.

[VariationBoundary](../ProjectAinos/GeneralRelativity/VariationBoundary.lean)
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

[VariationStationary](../ProjectAinos/GeneralRelativity/VariationStationary.lean)
takes actual fixed endpoints for nearby variation parameters and derives zero
endpoint variation fields. It proves that every affine geodesic is stationary
under these manifold families for the quadratic action, with no causal
restriction on variations. Timelike tangential acceleration likewise implies
massive stationarity; metric compatibility determines the speed factor.

[ManifoldCurve](../ProjectAinos/Variational/ManifoldCurve.lean) defines
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

[ManifoldStationary](../ProjectAinos/GeneralRelativity/ManifoldStationary.lean)
quantifies `QuadraticStationary` and `FreeStationary` over all such families.
For `a < b` and local C² regularity along `[a,b]`:

- `quadraticStationary_iff_geodesic` proves equivalence to affine motion on `(a,b)`.
- `freeStationary_iff_acceleration`, for positive mass and a timelike reference
  segment, proves `∇tT = (s'/s)T`; `freeStationary_iff_tangential` is equivalent.
- [ManifoldMotion](../ProjectAinos/GeneralRelativity/ManifoldMotion.lean) proves
  equivalence to actual regular local affine reparametrization. Unit proper
  speed gives the affine equation, and `freeStationary_finite_properTime`
  constructs one inverse of the actual clock integral over the full segment.
- The affine equation extends to finite endpoints by continuity.
  `QuadraticStationary.null_initial` preserves both nonvanishing and zero
  metric norm on the closed segment. The family space has no null constraint.

These results require no global chart, global frame, orientation, time
orientation, completeness, or global Hausdorff hypothesis.

## Proved examples and validation

[SpecialRelativity](../ProjectAinos/GeneralRelativity/SpecialRelativity.lean)
proves exact equality with the existing SR proper-speed and proper-time
functionals on Minkowski space, and with the four-dimensional free action
and its Mechanics formulation. These are functional equalities, not only
evaluations on inertial lines.

The [clock examples](../ProjectAinos/GeneralRelativity/ClockExamples.lean)
and particle examples below include the following Lean proofs:

| Metric and curve | Result |
| --- | --- |
| Nonlinear flat metric, `γ(s)=(s,-s²)` | Proper-speed rate `1`, proper time `b-a`, free action `-m(b-a)`. |
| `exp(2x²)(-dt²+dx²)`, clock at fixed spatial `x` | Timelike, rate `exp(x²)`, proper time `(b-a) exp(x²)`. |
| Same curved clock | Quadratic action `-(b-a) exp(2x²)/2`. |
| Nonlinear flat metric, `γ(s)=(exp(s),-exp(2s))` | Timelike, native acceleration equals velocity, rate `exp(s)`, proper time `exp(b)-exp(a)`. |

[ParticleExamples](../ProjectAinos/GeneralRelativity/ParticleExamples.lean)
proves that the exponential clock makes the massive action stationary for
positive mass on every nontrivial finite interval, while its quadratic
action is not stationary in that parameter. The constructed finite-segment
inverse is explicitly `r(τ) = log(τ + exp(a))`, maps both endpoints correctly,
has unit rate and gives affine motion on the full proper-time interior.

[VariationExamples](../ProjectAinos/GeneralRelativity/VariationExamples.lean)
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

The stage E principal proof endpoints are implemented and merged into `main`.
Stage F now has native form bundles, pullback, exterior differentiation,
wedge calculus, positive chart-covariant density and a glued oriented volume
form. Native Hodge now has its wedge identity, uniqueness, sign laws,
metric/volume-preserving naturality, exact flat comparison and nonlinear shear
transport. Its local formula proves smooth-section regularity, and the
general square identity requires no flatness or global frame. The curved
conformal plane verifies the native and smooth operators. Intrinsic divergence
and its density formula are also proved in every smooth chart. Fixed-background
Maxwell forms now have invertible current identification, sourced current
closedness, orientation invariance and a nonzero-current example. Volume
contraction and `dJ = (div j) vol` identify that closedness with vanishing
covariant vector divergence. The
[geometry guide](smooth-geometry.md) and [electrodynamics guide](electrodynamics.md)
record these proofs. Two-form covariant differentiation now has proved
tensoriality, smoothness and its two Christoffel corrections. The homogeneous
Maxwell equation is equivalent to the cyclic covariant component equation in
every smooth chart. Intrinsic two-form divergence, its smoothness, both raised
indices and the density formula are proved. The source defined by `dH` is now
proved equal to this divergence on every oriented physical background. Both
Maxwell equations are equivalent to the covariant component equations in every
smooth chart. Stage F’s principal endpoints are implemented and merged into `main`;
stage G proves the controlled time-dependent Newtonian motion and trajectory limit.
Einstein dynamics belongs to §5.2 and is not proved here. The flat vacuum
Maxwell field action is proved in §4.2 / #44 and recorded in the
[electrodynamics guide](electrodynamics.md#vacuum-field-action-42); a sourced
or curved field action is not.

## Newtonian coordinate families and trajectory limits

`NewtonianMetricFamily U` fixes a common open domain in physical coordinates
`(t,x) : Fin 4 → ℝ`. Its potential and three correction families satisfy

```text
g_tt = -c² - 2 Φ + c⁻² A_c
g_ti = c⁻² B_c,i
g_ij = δ_ij + c⁻² H_c,ij
```

All coefficients may depend on time, `H_c` is symmetric, and each positive-`c`
member is smooth on `U`. One constant bounds values and the first two ordinary
spacetime derivatives for `c ≥ 1`. No differentiability in `c` is required.
`CoordinateC2Bound` records the actual operator norms of those derivatives on
the coordinate model; it does not assign norms to native tangent fibres.
The domain can be an open buffer around the compact trajectory tube.

`coefficient` and `form` construct the full symmetric coefficient matrix and
smooth bilinear form. `form_timeVelocity` expands the exact norm of `(1,v)`.
With coefficient bound `K` and `‖v‖ ≤ V`, the proved upper bound is

```text
g((1,v),(1,v)) ≤ -c² + 3 K + 6 K V + (3 + 9 K) V².
```

Consequently one sufficiently large-`c` tail makes this norm negative
simultaneously at every point in `U` and every velocity in the prescribed
range. `form_spatial_pos` proves positive definiteness on the spatial
hyperplane when `c² > 9 K`. Completing the square along the negative time line gives a positive form on
its orthogonal complement. The resulting pointwise inertial frame proves
Lorentz signature for `c ≥ 1` and `c² > 9 K`. The smooth coefficient form
therefore defines `lorentzMetric` on the actual tangent bundle of `U`.
`physicalChart` identifies the whole domain with its given open subset of
physical coordinates. The native metric, its inverse and its Levi-Civita
coefficients recover the ordinary matrix formulas in this chart.
`timelike_timeVelocity` applies the velocity estimate to the native metric.

For the stronger threshold `c² > 24 K`, multiplying the time row by
`-c⁻²` gives a matrix within `12 K c⁻²` of the identity in the induced
sup norm. The column equations give `|gⁱᵗ|, |gᵗʲ| ≤ 2 c⁻²` and
`|gⁱʲ - δⁱʲ| ≤ 24 K c⁻²` for spatial `i,j` in the last bound.
These estimates hold uniformly throughout the common open domain.

For an existing native Lorentz metric in any smooth chart,
`coordinateTimeAcceleration` is extracted from its actual connection as
`-Γⁱ(w,w) + vⁱ Γᵗ(w,w)`, `w=(1,v)`. `tangential_iff_coordinateTime` proves
that this ODE is equivalent to native acceleration being proportional to
velocity when the chart's time coordinate equals the parameter locally.
The family-level `acceleration` agrees with this native equation on `U`
and is smooth in the position and velocity variables there.
`coordinateTime_of_affine_reparam` derives it from a regular reparametrization
of an affine geodesic. Smoothness is proved locally from the connection;
no uniform Lipschitz bound is claimed by that local theorem.

`NewtonianExamples.family` uses `Φ=t x¹`, `A=t²`, `B_i=t xⁱ` and
`H_ij=t δ_ij` on the coordinate ball of radius two. Compactness of the closed
ball supplies actual finite C² bounds. Lean checks the mixed/spatial sample
coefficients and a nonzero time derivative of the potential. Exact SymPy
checks the same norm and sample coefficients, the leading inverse blocks, the sample acceleration limit,
and non-affine corrections in separate conformal and static calibrations.
The rational sample limit is not a uniform bound or a trajectory theorem.

The derivative of the time-time coefficient contributes the leading
spatial gradient. `christoffel_spatial_error` and
`christoffel_time_abs_le` bound the remaining terms, including time
derivatives and the mixed and spatial corrections. For `c ≥ 1`, `c² > 24K`
and `‖v‖ ≤ V`, `native_acceleration_error` bounds
`‖a_c + ∇ₓΦ‖` by `accelerationErrorConstant V / c²` uniformly on `U`.

On coordinate segments contained in `U`, the potential's second derivative
gives a Lipschitz constant `max 1 K` for the Newtonian phase field at fixed
time. `phase_error_gronwall` compares the position and velocity of two
solutions already defined on `[a,b]`. For initial error at most `δ`, the
bound at time `t` is `gronwallBound δ (max 1 K) (C/c²) (t-a)`. It uses
the velocity bound and requires the segment between the two positions at
each time to stay in `U`.

The second derivative bound also controls differences of the relativistic
field. `relativisticPhaseField_sub_le` uses the matrix inverse difference
identity, the uniform inverse bounds and bounded velocities to give a
Lipschitz constant independent of large `c`. It applies to pairs whose
connecting coordinate segment stays in `U`.

`exists_trajectory_tube` gives a common radius from compactness of the
reference trajectory on the closed interval. `exists_relativistic_on_Icc`
solves an auxiliary equation for the deviation, evaluating the field with
each component of the deviation clipped to the tube radius. The auxiliary
field is bounded and Lipschitz in the deviation on the whole interval.
Picard–Lindelöf gives a solution, and the Gronwall bound keeps the deviation
within the radius when the endpoint error budget fits. On this solution,
clipping acts as the identity and the original relativistic equation holds.

`exists_uniform_newtonian_limit` constructs trajectories on the reference
interval for sufficiently large `c` and proves uniform position and
velocity convergence as the initial phase points approach the Newtonian
ones. `exists_newtonian_limit_with_rate` gives a uniform `C/c²` error
from an initial bound `D/c²`. The Gronwall decomposition includes the
zero-Lipschitz case, whose forcing factor is the elapsed time.

For the polynomial family, `polynomial_trajectory_limit` uses the
reference trajectory `x¹=-t³/6`, `v¹=-t²/2` on `[0,1]` with the
other spatial coordinates zero. Lean verifies the reference equation and
domain membership and proves convergence at order `c⁻²` for equal zero
initial data. Exact SymPy checks the trajectory and both nonzero corrections
along it. The stage G implementation is merged into `main`.

## Observers, Killing fields and rotation (§§82, 84, 88, 89)

**Metrics from coefficients.** `Minkowski.exists_lorentzFrame` completes the
square along `e₀`: a symmetric bilinear form on `MinkowskiModel d` that is
negative on the time axis and positive definite on `{(0, v)}` is the
Minkowski form of `.timeNegative` in some frame. `exists_lorentzFrame_convention`
is the statement for either convention, with the hypotheses on `−σ.timeSign · B`.
A `CoordinateMetric σ d U` is a family of forms on the model, smooth on the
open set `U`, with the signature of `σ` at every point of `U`. `toLorentzMetric`
makes it a Lorentz metric on the manifold `U`, whose chart is the inclusion
`physicalChart`; the components, the inverse and the Christoffel symbols in this
chart are the matrix formulas of the coefficients, and `ofCriterion` builds an
instance from the criterion.

**Observers (§§82, 84).** In the convention `(−+++)` an observer at an event is
a timelike vector `u`. `Minkowski.spatialForm B u v w = B(v, w) − B(u, v) B(u, w)/B(u, u)`
is the metric of the parts orthogonal to `u` (`spatialForm_eq`), and the
observer measures with it: if a light signal leaves the worldline `τ ↦ τ u` at
`τ₁`, reaches the event `v` and returns at `τ₂`, then half the proper time of
the round trip is `√(γ_u(v, v))` and the event of the worldline at the middle
parameter is simultaneous with `v` (`radar`, `radar_distance`; `exists_radar`
gives the two signals). These are statements in one tangent space, about
neighbouring events. With a Lorentz frame the spatial form is positive
semidefinite and positive on every vector that is not a multiple of `u`
(`LorentzMetric.spatialForm_nonneg`, `LorentzMetric.spatialForm_pos`). For the
observer at rest, `u = e₀`, `spatialForm_timeAxis` gives `γᵢⱼ dxⁱ dxʲ` with
`γᵢⱼ = gᵢⱼ − g₀ᵢ g₀ⱼ/g₀₀`, independent of `dx⁰`, `CoordinateMetric.spatialMetric_pos`
its positivity where `g₀₀ < 0`, and `orthogonal_timeAxis_iff` the simultaneity
`dx⁰ = −g₀ᵢ dxⁱ/g₀₀`. In the co-ordinates of `U`, `properTime_coordinate` is
`τ = ∫ √(−g_{μν} ẋ^μ ẋ^ν) dt` for a smooth curve, and `properTime_atRest` the
clock `∫ √(−g₀₀) dt` of a curve that is at rest on `[a, b]`.

**Killing fields and the red shift (§88).** `LorentzMetric.IsKillingField g K` is
the Killing equation `g(∇_v K, w) + g(v, ∇_w K) = 0` at every event. Along a
geodesic given on any convex set of parameters, `IsKillingField.pairing_eq`
keeps `g(K, γ̇)` constant: it differentiates the pairing with
`hasDerivAt_pairing_along` and uses the geodesic equation and the Killing
equation. The observer that moves along a timelike Killing field has the unit
velocity `u = K/N`, `N = √(−g(K, K))` (`form_stationaryVelocity`), and measures
the frequency `ω = −g(u, γ̇)` of a ray `γ` (`observedFrequency`);
`killingNorm_mul_observedFrequency_eq` is the red shift `N(γ(a)) ω(a) = N(γ(b)) ω(b)`,
for any geodesic, null or not. For a coordinate metric,
`CoordinateMetric.isKillingField_of_invariant` makes `∂_k` a Killing field when
the form does not change under the translations along `x^k`; it rests on
`killing_chartField_of`, which reads `L_{∂_k} g = ∂_k g_{ij}` from metric
compatibility and the vanishing torsion. `SchwarzschildExterior` is the exterior
field `−(1 − 2M/r) dt² + dr²/(1 − 2M/r) + r² dθ² + r² sin²θ dφ²` on
`r > 2M`, `0 < θ < π`: `∂_t` and `∂_φ` are Killing fields, and along every
geodesic segment of this domain, radial rays included, `√(1 − 2M/r) ω` is
constant.

**The geodesic Hamiltonian (§88, stage G-H).** In a chart whose domain is all
of `ℝⁿ`, the coefficients `gm` of the metric and `gi` of its inverse are
elements of the free C∞-ring with `Σ_λ gm μ λ * gi λ ν = δ`.
`GeodesicHamiltonian.hamiltonian gi` is `½ g^{μν}(x) p_μ p_ν`. Its brackets give
`ẋ^μ = g^{μν} p_ν` and `ṗ_l = −½ ∂_l g^{μν} p_μ p_ν = ½ ∂_l g_{αβ} ẋ^α ẋ^β`
(`canonical_q_hamiltonian`, `canonical_p_hamiltonian_eq`), and `isTrajectory_iff`
shows that a curve is a trajectory exactly when `p_μ = g_{μν} ẋ^ν` and
`g_{μν} ẍ^ν + Γ_{μαβ} ẋ^α ẋ^β = 0`. For a vector field `ξ`,
`canonical_vectorMomentum_hamiltonian` is `{ξ^μ p_μ, H} = −½ (L_ξ g⁻¹)^{μν} p_μ p_ν`,
and `of_lieInverse` is `L_ξ g⁻¹ = −g⁻¹ (L_ξ g) g⁻¹`; so the momentum is an
integral exactly when `L_ξ g = 0` (`isIntegral_vectorMomentum_iff_killing`), the
momentum of a co-ordinate on which the metric does not depend is an integral
(`isIntegral_p_of_metric_independent`), and `g(ξ, ẋ)` is then constant
(`pairing_eq_of_killing`); `killingNorm_mul_frequency_eq` is `N ω = const`. A
trajectory is defined for all values of the affine parameter; `isTrajectory_rest`
and `isTrajectory_line` show that the curve at rest with zero momenta, and for
constant coefficients every straight line with constant momenta, are
trajectories.
`GeodesicHamiltonian.SchwarzschildEquatorial` is the equatorial plane of the
exterior field with `r = 2M + eˢ`: the metric `diag(−eˢ/r, eˢ r, r²)` and its
inverse are smooth on all of `ℝ³`, the energy `−p_t` and `p_φ` are integrals,
and `√(1 − 2M/r) ω` is constant along every trajectory. Every radial geodesic
along which `r` changes, and every ray that enters `r < 3M`, reaches `r = 2M` at
a finite parameter and is not a trajectory; the red shift along such rays is the one of
`SchwarzschildExterior`.

**Rotation (§89).** `RotatingFrame.form Ω` is
`−(1 − Ω²ρ²) dt² + 2Ω (x dy − y dx) dt + dx² + dy² + dz²`; `form_eq_pullback` and
`hasDerivAt_toInertial` show that it is the pullback of the Minkowski form by
the map to the inertial co-ordinates. `metric Ω` is the Lorentz metric on the
domain `Ω²ρ² < 1`. A clock at rest runs at `√(1 − Ω²ρ²)` (`properTime_static`);
the spatial form gives radial displacements their Euclidean length and the
tangent of the circle of radius `ρ` per unit angle the squared length
`ρ²/(1 − Ω²ρ²)` (`spatialForm_radial`, `spatialForm_tangential`), so the circle
has the length `2πρ/√(1 − Ω²ρ²)` (`circumference_circle`); the metric does not
depend on `t`, so this length does not depend on the slice. Synchronizing each
clock on the circle with its neighbour, going round in the sense of increasing
`φ`, gives the co-ordinate time `2πΩρ²/(1 − Ω²ρ²)` over one turn
(`synchronization_circle`; for `Ω > 0` this is the sense of the rotation); a clock on the
circle reads `√(1 − Ω²ρ²)` times this gap, and the Sagnac delay of two signals
sent round in opposite senses is twice it. `∂_t` is a Killing field
(`isKillingField_time`), and along every geodesic segment inside the light
cylinder the observers at rest measure frequencies with `√(1 − Ω²ρ²) ω = const`.

| Result | Declarations | Source |
| --- | --- | --- |
| Lorentz frames of a bilinear form | `Minkowski.exists_lorentzFrame`, `exists_lorentzFrame_convention` | [LorentzFrame](../ProjectAinos/SmoothGeometry/Lorentzian/LorentzFrame.lean) |
| Metrics from coefficients | `CoordinateMetric.toLorentzMetric`, `toLorentzMetric_chartMetric`, `toLorentzMetric_christoffel`, `ofCriterion`, `minkowski`, `spatialMetric_pos`; `LorentzMetric.spatialForm_pos` | [CoordinateMetric](../ProjectAinos/SmoothGeometry/Lorentzian/CoordinateMetric.lean) |
| The spatial form and radar | `Minkowski.spatialForm_eq`, `spatialForm_pos`, `radar`, `radar_distance`, `exists_radar`, `spatialForm_timeAxis`, `orthogonal_timeAxis_iff` | [SpatialForm](../ProjectAinos/SmoothGeometry/Lorentzian/SpatialForm.lean) |
| Clocks in co-ordinates | `properTime_coordinate`, `properTime_atRest` | [ObserverMeasurement](../ProjectAinos/GeneralRelativity/ObserverMeasurement.lean) |
| Killing fields and the red shift | `LorentzMetric.IsKillingField`, `IsKillingField.pairing_eq`, `killingNorm_mul_observedFrequency_eq`, `killing_chartField_of`, `CoordinateMetric.isKillingField_of_invariant` | [Killing](../ProjectAinos/SmoothGeometry/Lorentzian/Killing.lean) |
| The exterior Schwarzschild field | `SchwarzschildExterior.metric`, `isKillingField_time`, `isKillingField_angle`, `killingNorm_time`, `killingNorm_mul_observedFrequency_eq` | [SchwarzschildExterior](../ProjectAinos/GeneralRelativity/SchwarzschildExterior.lean) |
| The geodesic Hamiltonian | `GeodesicHamiltonian.isTrajectory_iff`, `canonical_vectorMomentum_hamiltonian`, `of_lieInverse`, `isIntegral_vectorMomentum_iff_killing`, `isIntegral_p_of_metric_independent`, `isTrajectory_rest`, `pairing_eq_of_killing`, `killingNorm_mul_frequency_eq` | [GeodesicHamiltonian](../ProjectAinos/GeneralRelativity/GeodesicHamiltonian.lean) |
| The Schwarzschild plane in `r = 2M + eˢ` | `GeodesicHamiltonian.SchwarzschildEquatorial.isTrajectory_iff`, `isIntegral_p_time`, `isIntegral_p_angle`, `killingNorm_eq`, `killingNorm_mul_frequency_eq` | [SchwarzschildEquatorial](../ProjectAinos/GeneralRelativity/SchwarzschildEquatorial.lean) |
| Rotating co-ordinates | `RotatingFrame.metric`, `form_eq_pullback`, `properTime_static`, `circumference_circle`, `synchronization_circle`, `killingNorm_mul_observedFrequency_eq` | [RotatingFrame](../ProjectAinos/GeneralRelativity/RotatingFrame.lean) |

The typed examples are in `checks/CoordinateMetricAPI.lean`,
`checks/GeodesicHamiltonianAPI.lean` and `checks/ObserverAPI.lean`. The
decisions are recorded in [GR03–GR07](general-relativity-notes.md).

## The derivative of the curvature, the Bianchi identities and the Einstein tensor (§§85, 92)

**Covariant differentiation (§85).** The text differentiates vectors, covectors
and tensors of every rank. The library has `leviCivita` on vector fields,
`Tensor.bilinearCovariantDerivative` on covariant two-tensors and
`twoFormDerivative`; this wave adds tangent-valued trilinear tensors. Covectors,
contravariant and mixed tensors and the general shapes have no derivative yet:
the pinned Mathlib induces no connection on dual or hom bundles, and the ledger
row is closed with this remainder. `Tensor.ContMDiffTensorialAt.mkHom₃`
turns an operation that is linear over scalar germs in each of three slots into a
continuous trilinear map on the tangent spaces, and
`Tensor.trilinearCovariantDerivative connection R hR x v w z u` is
`(∇_u R)(v, w)z` for any connection on the tangent bundle and any smooth field
`R` of trilinear maps: on locally `C¹` fields it is
`∇_u(R(X, Y)Z) − R(∇_u X, Y)Z − R(X, ∇_u Y)Z − R(X, Y)∇_u Z`
(`trilinearCovariantDerivative_apply`). The direction comes last, as for the
other tensors. `LorentzMetric.curvatureDerivative g x v w z u` is its value on
the curvature. Components are written in the library's order
`R^l_{ijk} = (R(∂_i, ∂_j)∂_k)^l`, with the antisymmetric pair first; Landau–Lifshitz
write the transported vector first, so this is their `R^l_{kij}`. The
chart formula `chartCurvatureDerivative_eq` is
`∇_m R^l_{ijk} = ∂_m R^l_{ijk} + Γ^l_{ma} R^a_{ijk} − Γ^a_{mi} R^l_{ajk} − Γ^a_{mj} R^l_{iak} − Γ^a_{mk} R^l_{ija}`;
`leviCivita_chart_components` and `bilinearCovariantDerivative_chart` are the
formulas for a vector field and for a covariant two-tensor.
`bilinearDivergenceCovector g B x b` is the divergence `∇^a B_{ab}` of a smooth
covariant two-tensor on its first index.

**The second Bianchi identity (§92).** `curvature_second_bianchi` is
`(∇_u R)(v, w)z + (∇_v R)(w, u)z + (∇_w R)(u, v)z = 0` for any tangent vectors
of a smooth Lorentz metric, in either convention and every dimension, and
`chartCurvatureDerivative_bianchi` is
`∇_m R^l_{ijk} + ∇_i R^l_{jmk} + ∇_j R^l_{mik} = 0`. The proof takes the
co-ordinate fields of a chart as a frame: they commute, so on them
`R(B, C) = [∇_B, ∇_C]`, and the cyclic sum of the triple covariant derivatives
cancels in pairs; the remaining terms `R(∇_A B, C)` cancel by the symmetry of
`∇_A B` in `A` and `B` and the antisymmetry of `R`.

**The contracted identity and the Einstein tensor (§92).**
`ricci_contracted_bianchi` is `∇^a Ric_{ab} = ½ ∂_b R`. It is proved at the
centre of an inertial chart (`exists_inertialChart`), where the Christoffel
symbols vanish, so the co-ordinate fields are parallel
(`IsInertialChartAt.leviCivita_chartField`) and the inverse metric
`g^{ij} = dx^i(♯dx^j)` (`chartInverse`) has zero derivative
(`IsInertialChartAt.mvfderiv_chartInverse`). There the covariant derivatives of
the Ricci and Riemann components are their partial derivatives, `Ric_{jk} = R^i_{ijk}`
(`ricci_chartField`), `R^i_{jmk} g^{mk} = g^{il} Ric_{lj}` (`chartCurvature_contract`,
from the pair symmetry), and the second Bianchi identity contracted twice is an
identity between arrays of numbers. `einstein g x = Ric − (R/2) g` is symmetric
and smooth and does not depend on the convention (`einstein_opposite`); its trace
is `(1 − n/2) R` in dimension `n = d + 1` (`contract_einstein`), so it vanishes
only where the Ricci tensor does, except in dimension two
(`ricci_eq_zero_of_einstein_eq_zero`), and `einstein_divergence_eq_zero` is
`∇^a G_{ab} = 0`. These are identities of every smooth metric: the Einstein
equations are not a premise.

**A four-dimensional regression.** In dimension two the cyclic sum and the
Einstein tensor vanish for every metric (GR01).
`ExponentialConformalExample.metric` is `e^{2z}(−dt² + dx² + dy² + dz²)` on
`ℝ⁴`, a `CoordinateMetric` on the whole space. For a coordinate metric,
`toLorentzMetric_leviCivita_eq` reads `∇_{∂_v} ∂_w` off the Koszul formula with
the co-ordinate fields, and `toLorentzMetric_curvature_of_connection` and
`toLorentzMetric_curvatureDerivative_of_connection` compute the curvature and
its derivative when the connection is a map `Γ` that does not depend on the
point. Here `Γ(v, w) = v₃ w + w₃ v − η(v, w) e₃`, and the example has
`Ric = diag(2, −2, −2, 0)`, `R = −6 e^{−2z}`, `G = diag(−1, 1, 1, 3) ≠ 0`,
`∇_{∂_z} R = −2 R ≠ 0`, and, through the contracted identity,
`∇^a Ric_{az} = 6 e^{−2z}`, half of `∂_z R = 12 e^{−2z}`: on this metric both
sides of the identity are nonzero.

| Result | Declarations | Source |
| --- | --- | --- |
| Tensoriality in three slots | `Tensor.ContMDiffTensorialAt.pointwise₃`, `mkHom₃`, `mkHom₃_apply` | [TrilinearTensoriality](../ProjectAinos/SmoothGeometry/Tensor/TrilinearTensoriality.lean) |
| Derivative of trilinear tensors | `Tensor.trilinearBundle`, `IsSmoothTrilinear`, `trilinearCovariantDerivative`, `trilinearCovariantDerivative_apply` | [TrilinearDerivative](../ProjectAinos/SmoothGeometry/Tensor/TrilinearDerivative.lean) |
| Derivative of the curvature, second Bianchi | `LorentzMetric.curvatureDerivative`, `curvatureDerivative_apply`, `leviCivita_chart_components`, `bilinearCovariantDerivative_chart`, `chartCurvatureDerivative_eq`, `covariantField_chartField_comm`, `curvature_second_bianchi`, `chartCurvatureDerivative_bianchi` | [CurvatureDerivative](../ProjectAinos/SmoothGeometry/Lorentzian/CurvatureDerivative.lean) |
| Chart contractions, inertial centre | `chartInverse`, `contract_chart`, `ricci_chartField`, `scalarCurvature_chart`, `chartCurvature_contract`, `IsInertialChartAt.mvfderiv_chartInverse`, `IsInertialChartAt.bilinearCovariantDerivative_chartField`, `IsInertialChartAt.chartCurvatureDerivative_eq` | [InertialDerivatives](../ProjectAinos/SmoothGeometry/Lorentzian/InertialDerivatives.lean) |
| Contracted Bianchi, Einstein tensor | `bilinearDivergenceCovector`, `ricciBilinear`, `ricci_contracted_bianchi`, `einstein`, `einstein_symmetric`, `einstein_smooth`, `contract_einstein`, `ricci_eq_zero_of_einstein_eq_zero`, `bilinearCovariantDerivative_einstein`, `einstein_divergence_eq_zero` | [Einstein](../ProjectAinos/SmoothGeometry/Lorentzian/Einstein.lean) |
| Connection of a coordinate metric | `CoordinateMetric.toLorentzMetric_pairing_derivative`, `toLorentzMetric_leviCivita_eq`, `toLorentzMetric_curvature_of_connection`, `toLorentzMetric_curvatureDerivative_of_connection` | [CoordinateConnection](../ProjectAinos/SmoothGeometry/Lorentzian/CoordinateConnection.lean) |
| Four-dimensional regression | `ExponentialConformalExample.metric_leviCivita`, `metric_curvature`, `metric_ricci_chartField`, `metric_scalarCurvature`, `metric_einstein_chartField`, `metric_einstein_ne_zero`, `metric_curvatureDerivative_dz`, `metric_curvatureDerivative_ne_zero`, `metric_scalarCurvature_derivative`, `metric_ricci_divergence` | [ExponentialConformalExample](../ProjectAinos/SmoothGeometry/Lorentzian/ExponentialConformalExample.lean) |

The typed examples are in `checks/BianchiAPI.lean`. The decisions are recorded
in [GR01, GR08 and GR09](general-relativity-notes.md) and in
[G03](smooth-geometry-notes.md).

## The first variation of the Einstein–Hilbert action (§93)

**Admissible variations.** A metric is a `CoordinateMetric σ d U`: smooth
symmetric coefficients `g_{ik}` on an open set `U` of the model space with the
Lorentz signature at each point. A variation is a smooth field `h` of symmetric
bilinear forms with compact support in `U`. `g.IsAdmissible h ε` says that
`g + εh` has the Lorentz signature on `U`, and then `g.addVariation h hh ε hε`
is the varied coordinate metric. `eventually_isAdmissible` gives one interval
of `ε` for all points: `Minkowski.exists_lorentzFrame_of_near` keeps the
signature of a form whose quadratic form is close to that of a Lorentz form in
the norm of a frame, and the tube lemma makes the bound uniform on the compact
support. Off the support nothing changes.

**The coefficient formulas.** `christoffelOf`, `ricciOf`, `scalarOf` and
`densityOf` are the textbook formulas in a matrix-valued function `C` of the
point: `Γ^k_{ij} = ½ g^{kl}(∂_i g_{jl} + ∂_j g_{li} − ∂_l g_{ij})`,
`R_{jk} = ∂_i Γ^i_{jk} − ∂_j Γ^i_{ik} + Γ^i_{ia} Γ^a_{jk} − Γ^i_{ja} Γ^a_{ik}`,
`R = g^{ac} R_{ac}` and `√|det g|`. For a coordinate metric they are the native
Christoffel symbols, Ricci tensor, scalar curvature and chart density
(`toLorentzMetric_chartChristoffel`, `toLorentzMetric_ricci_chartField`,
`toLorentzMetric_scalarCurvature`, `toLorentzMetric_chartDensity`), and
`einsteinOf` is the native Einstein tensor on the co-ordinate fields
(`toLorentzMetric_einstein_chartField`). The same formulas applied to the slices
of a family `C(ε, x)` (`familyChristoffel`, `familyRicci`, `familyScalar`,
`familyDensity`) are jointly smooth in `(ε, x)` where `det C ≠ 0`, and their
derivatives in `ε` are computed under the swap of the mixed partials.

**The pointwise first variation.** For the family `g + εh`,
`δg^{ik} = −g^{im} h_{mn} g^{nk}` (`hasDerivAt_inverseVariation`) and
`δ√|g| = ½ g^{ab} h_{ab} √|g|` (`hasDerivAt_variationFamily_density`).
`palatini_algebra` is the Palatini identity as an identity between arrays of
numbers: with metric compatibility `∂_e g^{bc} = −Γ^b_{ed} g^{dc} − Γ^c_{ed} g^{bd}`
(`fderiv_coefficient_inv`, and natively `mvfderiv_chartInverse_chartField`) and
`∂_k √|g| = √|g| Γ^c_{ck}` (`fderiv_densityOf`), it turns `g^{bc} δR_{bc} √|g|`
into the divergence `∂_a(√|g| V^a)` of
`V^a = g^{bc} δΓ^a_{bc} − g^{ab} δΓ^c_{cb}` (`variationVector`).
`hasDerivAt_scalarDensity` is then
`δ((R − 2Λ)√|g|) = −(R^{mn} − (R/2 − Λ) g^{mn}) h_{mn} √|g| + ∂_a(√|g| V^a)`
at each point of `U`.

**The integrated first variation.** `scalarDensity g h Λ (ε, x)` is
`(R_ε − 2Λ) √|g_ε|` at `x`; it does not change off the support of `h`
(`scalarDensity_of_notMem`), and for an admissible `ε` it is the native density
of `g + εh` (`scalarDensity_eq_toLorentzMetric`). The derivative is taken under
the integral (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`) on a closed
interval of admissible `ε`, where the derivative in `ε` is bounded on the
compact set `[−δ, δ] × supp h`. The divergence term has compact support, so its
integral vanishes (`integral_fderiv_density_mul_variationVector`), and
`hasDerivAt_integral_scalarDensity` is
`d/dε ∫ ((R_ε − 2Λ)√|g_ε| − (R − 2Λ)√|g|) dx = −∫ (R^{mn} − (R/2 − Λ) g^{mn}) h_{mn} √|g| dx`
at `ε = 0`; `eulerLagrangeDensity_eq` writes the integrand as
`(G_{ik} + Λ g_{ik}) δg^{ik} √|g|`.

**The physical action.** `GeneralRelativity/EinsteinHilbertAction.lean` states
Landau–Lifshitz's action in four dimensions and the convention `(−+++)`, with
`S = (1/2κ) ∫ (R − 2Λ) √|g| d⁴x`. An action over a region that is not compact
need not converge, so `relativeAction g h κ Λ ε` is
`(1/2κ) ∫ ((R_ε − 2Λ)√|g_ε| − (R − 2Λ)√|g|) d⁴x`.
`eventually_relativeAction_integrand` says that for every `ε` near `0` its
integrand is the difference of the native Lagrangians `lagrangian`, and
`hasDerivAt_relativeAction` is
`ΔS'(0) = (1/2κ) ∫ (G_{ik} + Λ g_{ik}) δg^{ik} √|g| d⁴x`, the variation of
Landau–Lifshitz with a cosmological term; `integrand_eq_native` reads `G_{ik}`, `g_{ik}`
and `√|g|` as the native tensors and density on the co-ordinate fields.

**Regressions.** For the Minkowski metric and `h = f η`,
`ΔS'(0) = −(2Λ/κ) ∫ f` (`hasDerivAt_relativeAction_flat`); it is not zero for a
bump function when `Λ ≠ 0`. For the curved metric `e^{2z} η` of §92 and
`h = f η`, `ΔS'(0) = −(1/2κ) ∫ f (6 + 4Λ e^{2z})`
(`hasDerivAt_relativeAction_conformal`): the `6` is `η^{ik} G_{ik}` with
`G = diag(−1, 1, 1, 3)`, so the Einstein tensor alone gives a nonzero derivative
when `Λ = 0` (`exists_deriv_relativeAction_conformal_ne_zero`).

**Scope.** The variation is supported in an open set of the model space, which
is the domain of the co-ordinates. A variation supported in a chart of a general
Lorentz manifold needs the extension by zero and the comparison of charts, and
is not stated. The divergence vector is written with `δΓ`; its tensorial form
`∇_b h^{ab} − ∇^a tr h` is not stated.

| Result | Declarations | Source |
| --- | --- | --- |
| Stability of the signature | `Minkowski.abs_apply_self_le`, `Minkowski.exists_lorentzFrame_of_near` | [SignatureStability](../ProjectAinos/SmoothGeometry/Lorentzian/SignatureStability.lean) |
| Admissible variations | `CoordinateMetric.IsAdmissible`, `isAdmissible_zero`, `eventually_isAdmissible`, `addVariation`, `addVariation_form` | [CoordinateVariation](../ProjectAinos/SmoothGeometry/Lorentzian/CoordinateVariation.lean) |
| Coefficient formulas | `christoffelOf`, `ricciOf`, `scalarOf`, `densityOf`, `toLorentzMetric_chartChristoffel`, `toLorentzMetric_chartCurvature`, `toLorentzMetric_ricci_chartField`, `toLorentzMetric_scalarCurvature`, `toLorentzMetric_chartDensity` | [CoordinateCurvature](../ProjectAinos/SmoothGeometry/Lorentzian/CoordinateCurvature.lean) |
| Families of coefficients | `familyChristoffel`, `familyRicci`, `familyScalar`, `familyDensity`, `contDiffAt_familyScalar`, `hasDerivAt_familyChristoffel`, `hasDerivAt_familyRicci`, `hasDerivAt_familyScalar` | [CoordinateFamily](../ProjectAinos/SmoothGeometry/Lorentzian/CoordinateFamily.lean) |
| Palatini identity | `palatini_algebra` | [PalatiniAlgebra](../ProjectAinos/SmoothGeometry/Lorentzian/PalatiniAlgebra.lean) |
| Inverse metric and density | `variationFamily`, `hasDerivAt_variationFamily_inv`, `hasDerivAt_variationFamily_density`, `fderiv_coefficient_inv`, `fderiv_densityOf`, `LorentzMetric.mvfderiv_chartInverse_chartField` | [CoordinateFirstVariation](../ProjectAinos/SmoothGeometry/Lorentzian/CoordinateFirstVariation.lean), [InertialDerivatives](../ProjectAinos/SmoothGeometry/Lorentzian/InertialDerivatives.lean) |
| Pointwise first variation | `variationVector`, `ricciUp`, `hasDerivAt_scalarDensity` | [ScalarCurvatureVariation](../ProjectAinos/SmoothGeometry/Lorentzian/ScalarCurvatureVariation.lean) |
| Integrated first variation | `scalarDensity`, `scalarDensity_of_notMem`, `integral_fderiv_density_mul_variationVector`, `eulerLagrangeDensity`, `hasDerivAt_integral_scalarDensity`, `scalarDensity_eq_toLorentzMetric`, `einsteinOf`, `toLorentzMetric_einstein_chartField`, `inverseVariation`, `hasDerivAt_inverseVariation`, `eulerLagrangeDensity_eq` | [CoordinateEinsteinHilbert](../ProjectAinos/SmoothGeometry/Lorentzian/CoordinateEinsteinHilbert.lean) |
| The action and its regressions | `EinsteinHilbert.lagrangian`, `relativeAction`, `relativeAction_integrand`, `eventually_relativeAction_integrand`, `hasDerivAt_relativeAction`, `integrand_eq_native`, `hasDerivAt_relativeAction_flat`, `exists_deriv_relativeAction_flat_ne_zero`, `conformal_einsteinOf`, `hasDerivAt_relativeAction_conformal`, `exists_deriv_relativeAction_conformal_ne_zero` | [EinsteinHilbertAction](../ProjectAinos/GeneralRelativity/EinsteinHilbertAction.lean) |

The typed examples are in `checks/EinsteinHilbertAPI.lean`. The decisions are
recorded in [GR01, GR02, GR10 and GR11](general-relativity-notes.md) and in
[G04](smooth-geometry-notes.md).
