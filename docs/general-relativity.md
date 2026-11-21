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

## Matter and the Einstein equations (§§94, 95)

**Hilbert tensors (§94).** A matter density that depends on the metric only
through `g^{ab}` and `√|g|` at the point has a first variation
`δℒ = −½ T_{ik} δg^{ik} √|g|`, which defines its Hilbert tensor.
`CoordinateMetric.scalarFieldDensity` is `−½ (g^{ab} ∂_aφ ∂_bφ + m² φ²) √|g|`,
with `scalarStress`
`T_{ik} = ∂_iφ ∂_kφ − ½ g_{ik} (g^{ab} ∂_aφ ∂_bφ + m² φ²)`; in Minkowski space
`T₀₀ = ½ (φ̇² + |∇φ|² + m² φ²)` (`scalarStress_minkowski_zero_zero`).
`maxwellDensity` is `−¼ F_{ab} F^{ab} √|g|` for a fixed antisymmetric field
`F_{ab}`, with `maxwellStress` `T_{ik} = F_{ib} F_k{}^b − ¼ g_{ik} F²`, symmetric
and, in four dimensions, trace-free; in Minkowski space it is the tensor
`stressForm` of §33 (`Electrodynamics.maxwellStress_minkowski`). The field is held
fixed while the metric varies. `hasDerivAt_integral_scalarFieldDensity` and
`hasDerivAt_integral_maxwellDensity` differentiate the relative actions under the
integral with `Variational.hasDerivAt_integral_sub`, the general form of the
argument of §93.

**Matter actions.** `EinsteinEquations.MatterAction g` bundles a relative action
for each variation with its Hilbert tensor, smooth and symmetric on `U`, and the
theorem `δS_m = −½ ∫ T_{ik} δg^{ik} √|g| d⁴x`. The tensor is a theorem of the
action, not a datum beside it. The instances are `vacuum`, `scalarField` and
`maxwellField`.

**The Einstein equations (§95).** `totalAction g M κ Λ h` is
`ΔS_g + ΔS_m` for the variation `g + εh`, and `hasDerivAt_totalAction` gives its
derivative `(1/2κ) ∫ (G_{ik} + Λ g_{ik} − κ T_{ik}) δg^{ik} √|g| d⁴x`.
`isStationary_iff` is the theorem of the section: for `κ ≠ 0`, the total action is
stationary under every smooth symmetric variation with compact support in `U` if
and only if `G_{ik} + Λ g_{ik} = κ T_{ik}` on `U` (`CoordinateMetric.IsEinstein`).
The converse uses the variations `φ (dx^p ⊗ dx^q + dx^q ⊗ dx^p)` with a bump
function `φ` (`testVariation`), which read off `E^{pq}` of the tensor `E` of the
equations, the fundamental lemma of the calculus of variations, `√|g| > 0`, and
the lowering of indices (`integral_inverseVariation_eq_zero_iff`). This is an
equivalence for given fields; no metric is constructed from a source.

**Native form, trace and conservation.** `LorentzMetric.SatisfiesEinstein κ Λ T`
is `G + Λ g = κ T` for a smooth covariant two-tensor `T` on any Lorentz manifold.
`satisfiesEinstein_bilinearOf_iff` identifies it with the co-ordinate equations for
the tensor `bilinearOf T` with the coefficients `T_{ik}`, so a stationary metric
satisfies the native equations (`isStationary_iff_satisfiesEinstein`). For
`κ ≠ 0` the source is conserved, `∇^a T_{ab} = 0`
(`SatisfiesEinstein.divergence_eq_zero`, `divergence_stress_eq_zero`), from the
contracted Bianchi identity and `∇g = 0`. The trace is
`(1 − n/2) R + n Λ = κ T^a{}_a` (`SatisfiesEinstein.contract`), and away from
dimension two `Ric = κ (T − T^a{}_a g/(n − 2)) + 2Λ g/(n − 2)`
(`SatisfiesEinstein.ricci_eq`); in four dimensions
`Ric = κ (T − ½ T^a{}_a g) + Λ g` (`ricci_eq_four`, `ricci_eq_of_isStationary`).

**Regressions.** Minkowski space is a vacuum solution with `Λ = 0`
(`minkowski_isStationary_vacuum`); with a constant scalar field `c` it is a
solution with `Λ = −κ m² c²/2`, the potential energy of the field acting as a
cosmological constant (`minkowski_isStationary_constantScalar`); the curved
metric `e^{2z} η` is not a vacuum solution (`conformal_not_isStationary_vacuum`).

**Conservation from the field equation of the matter (§94).** On a fixed metric,
`CoordinateMetric.fieldAction g m φ ψ ε` is the relative action
`S[φ + εψ] − S[φ]` of the scalar field. For a smooth `ψ` with compact support in
`U`, `hasDerivAt_fieldAction` gives `∫ ψ (□φ − m² φ) √|g| dx`, through the wave
operator in divergence form `∂_b(√|g| g^{ab} ∂_aφ) = √|g| □φ`
(`sum_fderiv_density_inv_mul`), with `□φ = g^{ab} ∇_a ∇_b φ` (`boxOf`,
`hessianOf`); so the action is stationary in `φ` exactly when `□φ = m² φ`
(`isFieldStationary_iff`, `EinsteinEquations.isFieldStationary_iff_kleinGordon`).
`divergenceOf_scalarStress` computes `∇^a T_{ab} = (□φ − m² φ) ∂_bφ` from metric
compatibility `∂_c g_{ab} = Γ^l_{ca} g_{lb} + Γ^l_{cb} g_{al}` (`fderiv_coefficient`)
and the symmetry of the Hessian; `bilinearDivergence_bilinearOf` identifies the
co-ordinate divergence with the native one, so a solution of the Klein–Gordon
equation has a conserved stress on the fixed background
(`divergence_scalarStress_eq_zero`), without the Einstein equations. In Minkowski
space `φ = e^{m x}` is a solution (`kleinGordon_exp`).

**Scope.** As in §93, the metric is given by coefficients on an open set of the
model space. The conservation from the field equation of the matter is proved for
the scalar field; for the fixed electromagnetic field it needs the Maxwell
equations on the curved background, and the derivation from the invariance under
diffeomorphisms for a general matter action is not stated.

| Result | Declarations | Source |
| --- | --- | --- |
| Relative integrals | `Variational.hasDerivAt_integral_sub`, `Variational.integrable_deriv_sub` | [RelativeIntegral](../ProjectAinos/Variational/RelativeIntegral.lean) |
| Hilbert tensors | `CoordinateMetric.hasDerivAt_integral_of_pointwise`, `sum_coefficient_mul_inverseVariation`, `scalarFieldDensity`, `scalarStress`, `hasDerivAt_scalarFieldDensity`, `hasDerivAt_integral_scalarFieldDensity`, `maxwellDensity`, `maxwellProduct`, `maxwellInvariant`, `maxwellStress`, `maxwellStress_symm`, `sum_inv_mul_maxwellStress`, `hasDerivAt_maxwellDensity`, `hasDerivAt_integral_maxwellDensity` | [CoordinateMatter](../ProjectAinos/SmoothGeometry/Lorentzian/CoordinateMatter.lean) |
| Native Einstein equations | `LorentzMetric.SatisfiesEinstein`, `SatisfiesEinstein.bilinearCovariantDerivative_eq`, `SatisfiesEinstein.divergence_eq_zero`, `SatisfiesEinstein.contract`, `SatisfiesEinstein.ricci_eq`, `SatisfiesEinstein.ricci_eq_four` | [EinsteinEquation](../ProjectAinos/SmoothGeometry/Lorentzian/EinsteinEquation.lean) |
| Test variations and native tensors | `contDiffAt_ricciOf`, `contDiffAt_einsteinOf`, `einsteinOf_symm`, `testVariation`, `raised`, `sum_mul_inverseVariation_test`, `eq_zero_of_raised_eq_zero`, `integral_inverseVariation_eq_zero_iff`, `coefficientForm`, `bilinearOf`, `bilinearOf_chartField`, `IsEinstein`, `satisfiesEinstein_bilinearOf_iff` | [CoordinateEinsteinEquation](../ProjectAinos/SmoothGeometry/Lorentzian/CoordinateEinsteinEquation.lean) |
| Matter and the equations | `EinsteinEquations.MatterAction`, `vacuum`, `scalarField`, `maxwellField`, `totalAction`, `fieldEquation`, `IsStationary`, `hasDerivAt_totalAction`, `isStationary_iff`, `isStationary_iff_satisfiesEinstein`, `divergence_stress_eq_zero`, `ricci_eq_of_isStationary`, `minkowski_isStationary_vacuum`, `minkowski_isStationary_constantScalar`, `conformal_not_isStationary_vacuum`, `scalarStress_minkowski_zero_zero` | [EinsteinEquations](../ProjectAinos/GeneralRelativity/EinsteinEquations.lean) |
| The tensor of §33 | `Electrodynamics.componentMatrix`, `maxwellStress_minkowski` | [HilbertStress](../ProjectAinos/Electrodynamics/HilbertStress.lean) |
| Conservation on a fixed metric | `CoordinateMetric.fderiv_coefficient`, `hessianOf`, `hessianOf_symm`, `boxOf`, `divergenceOf`, `bilinearDivergence_bilinearOf`, `scalarInvariant`, `fderiv_scalarInvariant`, `covariantDerivative_scalarStress`, `divergenceOf_scalarStress` | [CoordinateConservation](../ProjectAinos/SmoothGeometry/Lorentzian/CoordinateConservation.lean) |
| Field equation of the scalar field | `CoordinateMetric.fieldDensity`, `fieldAction`, `sum_fderiv_density_inv_mul`, `hasDerivAt_fieldAction`, `isFieldStationary_iff`, `bilinearDivergence_scalarStress`, `bilinearDivergence_scalarStress_eq_zero` | [CoordinateScalarField](../ProjectAinos/SmoothGeometry/Lorentzian/CoordinateScalarField.lean) |
| Klein–Gordon and conservation | `EinsteinEquations.KleinGordon`, `isFieldStationary_iff_kleinGordon`, `divergence_scalarStress`, `divergence_scalarStress_eq_zero`, `kleinGordon_exp` | [ScalarFieldEquation](../ProjectAinos/GeneralRelativity/ScalarFieldEquation.lean) |

The typed examples are in `checks/EinsteinEquationsAPI.lean` and
`checks/MatterConservationAPI.lean`. The decisions are recorded in
[GR12, GR13 and GR14](general-relativity-notes.md) and in
[ED14 and ED15](electrodynamics-notes.md).

## The field and a charge on a fixed background (§90)

**The action of the field.** For a metric given by coefficients on an open set `U`
of the model space, `CoordinateMetric.potentialAction g j A η ε` is the relative
action `S[A + εη] − S[A]` of a field of covectors `A` smooth on `U`, with the density
`(−¼ F_{ab} F^{ab} − A_b j^b) √|g|` (`potentialDensity`), the field
`F_{ab} = ∂_a A_b − ∂_b A_a` (`potentialField`) and a prescribed current `j`
continuous on `U`. The metric is held fixed. For a smooth `η` with compact support in
`U` the action is exactly quadratic in `ε` (`potentialDensity_sub`), and
`hasDerivAt_potentialAction` gives `∫ η_b (∂_a(√|g| F^{ab}) − √|g| j^b) dx` by
integration by parts; so the action is stationary under every such `η` exactly when
`∂_a(√|g| F^{ab}) = √|g| j^b` on `U` (`isPotentialStationary_iff`). For a native
two-form `F` with the components `F_{ab}` and a native vector field `J` with the
components `j^b` this is `∇_a F^{ab} = J^b` (`twoFormDivergence_eq_iff`), and in
electrodynamics the sourced equation `dH = J` of `Curved.Maxwell`
(`Curved.potentialStationary_iff_sourced`); with `dF = 0` it is the whole system
(`Curved.maxwell_iff_potentialStationary`). With the coupling `+A_b k^b` of a matter
current `k` the source is `−k` (`Curved.potentialStationary_matter_iff`). At the
Minkowski metric the density and the relative action are those of the flat
functional `SourcedAction.lagrangian` with the current form `ι_j vol`
(`Electrodynamics.potentialDensity_minkowski`, `potentialAction_minkowski`).

**The action of a charge.** For a Lorentz metric `g` on `U` and a field of covectors
`A` that is `C¹` on `U`, `chargedAction g m e A γ a b` is `−m ∫ dτ + e ∫ A(γ̇) dt`
(`lineIntegral`), varied by the actual fixed-endpoint families of curves in `U`
(`ChargedStationary`). The first variation of the line integral is
`∫ F(J, γ̇) dt` with the variation field `J` and `F(u, w) = ∂_u A(w) − ∂_w A(u)`
(`fieldCovector`, `lineIntegral_family_hasDerivAt`): the term `d/dt A(J)` integrates to
zero at the fixed end points, and the symmetry of the second derivative of the family
exchanges the two parameters. With the free variation of
`freeAction_variation_hasDerivAt` this gives `chargedAction_variation_hasDerivAt`, and
`chargedStationary_iff` is the theorem of the section: for a timelike `C²` curve the
action is stationary if and only if `(m/s)(∇_t γ̇ − (ṡ/s) γ̇) = e F(·, γ̇)^♯` on the open
interval, that is `m ∇_t U = e F(·, γ̇)^♯` with `U = γ̇/s`, and `m ∇_τ U = −e (ι_U F)^♯`
in proper time. No sign of `m` is assumed. A gauge change `A ↦ A + dχ` with a `C²`
function leaves `F` unchanged (`fieldCovector_gauge`), changes the action by the
end-point term `e (χ(γ(b)) − χ(γ(a)))` (`lineIntegral_gauge`) and does not change the
stationary curves (`chargedStationary_gauge_iff`). For the Minkowski coordinate metric
and the covector field of a flat potential, the stationarity is that of the flat action
of `Electrodynamics.stationary_iff_lorentzForce` (`chargedStationary_minkowski_iff`):
the native velocity is the derivative of the coordinates, the Christoffel symbols vanish
and the native raising is that of the model.

**Scope.** The background is an open set of the model space with its identity chart.
A potential given only on a chart of a general Lorentz manifold, the joint variation of
the field and of point charges, whose current is a distribution, and the exchange of
stress between the field and the matter on a curved background are not stated.

| Result | Declarations | Source |
| --- | --- | --- |
| Tangent fields in co-ordinates | `CoordinateMetric.trivializationAt_snd`, `contMDiffAt_tangent_iff`, `contDiffAt_val`, `contMDiffAt_iff_contDiffAt_val`, `curveVelocity_val`, `familyVelocity_val`, `minkowski_sharp` | [CoordinateTangent](../ProjectAinos/SmoothGeometry/Lorentzian/CoordinateTangent.lean) |
| Action of the field | `CoordinateMetric.potentialField`, `fieldPairing`, `raisedField`, `potentialDensity`, `potentialAction`, `potentialEuler`, `potentialDensity_sub`, `hasDerivAt_potentialAction`, `isPotentialStationary_iff`, `twoFormDivergence_component`, `twoFormDivergence_eq_iff` | [CoordinatePotential](../ProjectAinos/SmoothGeometry/Lorentzian/CoordinatePotential.lean) |
| Maxwell equations from the action | `Electrodynamics.Curved.potentialStationary_iff_sourced`, `maxwell_iff_potentialStationary`, `potentialDensity_matter`, `potentialStationary_matter_iff`, `Electrodynamics.potentialDensity_minkowski`, `potentialAction_minkowski` | [CurvedAction](../ProjectAinos/Electrodynamics/CurvedAction.lean) |
| Action of a charge | `lineIntegral`, `fieldCovector`, `chargedAction`, `ChargedStationary`, `chargedResidual`, `lineIntegral_family_hasDerivAt`, `lineIntegral_variation_hasDerivAt`, `chargedAction_variation_hasDerivAt`, `chargedStationary_iff`, `fieldCovector_gauge`, `lineIntegral_gauge`, `chargedStationary_gauge_iff` | [ChargedMotion](../ProjectAinos/GeneralRelativity/ChargedMotion.lean) |
| The flat case | `fieldCovector_potentialCovector`, `chargedStationary_minkowski_iff` | [FlatChargedMotion](../ProjectAinos/GeneralRelativity/FlatChargedMotion.lean) |

The typed examples are in `checks/CurvedChargeAPI.lean`. The decisions are recorded in
[GR15](general-relativity-notes.md) and [ED16](electrodynamics-notes.md).

## Orthonormal frames and the tetrad equations (§98)

**Frames.** `LorentzMetric.OrthonormalFrame g W` is a family of vector fields `E_a`
smooth on an open set `W` with `g(E_a, E_b) = η_{ab}` there, `η_{aa} = lorentzSign σ a`.
At a point of `W` every vector is `Σ_a η_{aa} g(v, E_a) E_a` (`sum_coord_smul`): the
frame coordinates `coord` and the combination `combine` are inverse, so `E_a` is a
basis (`coordEquiv`), the metric is `Σ_a η_{aa} g(u, E_a) g(w, E_a)` (`form_eq_sum`)
and a bilinear form is determined by its frame components (`bilinear_ext`). Two
orthonormal frames differ by a Lorentz matrix (`transition_orthonormal`). The coordinate
fields of the Minkowski coordinate metric are a frame (`CoordinateMetric.minkowskiFrame`).

**Rotation coefficients.** `rotation a b c` is `γ_{abc} = g(∇_{E_c} E_a, E_b)`, the
index order of Landau–Lifshitz, and `commutator a b c` is
`λ_{abc} = g(E_a, [E_b, E_c])`, which is their
`(e_{(a)i,k} − e_{(a)k,i}) e^i_{(b)} e^k_{(c)}`. Metric compatibility makes `γ`
antisymmetric in `a, b` (`rotation_antisymm`), the vanishing torsion gives
`λ_{abc} = γ_{abc} − γ_{acb}` (`commutator_eq`), and together
`γ_{abc} = ½ (λ_{abc} + λ_{bca} − λ_{cab})` (`rotation_eq`).

**Curvature.** `curvatureComponent a b c k` is `R_{abck} = g(R(E_c, E_k) E_b, E_a)` with
the convention `R(X, Y) = [∇_X, ∇_Y] − ∇_{[X,Y]}`, and `curvatureComponent_eq` is the
second structure equation of Cartan in components:
`R_{abck} = E_c(γ_{bak}) − E_k(γ_{bac}) −
Σ_f η_{ff} (γ_{bfk} γ_{afc} − γ_{bfc} γ_{afk} + λ_{fck} γ_{baf})`. Each `∇∇` term is
differentiated by metric compatibility, and `∇_{[E_c, E_k]}` is expanded in the frame,
so no Leibniz rule for the frame fields is needed. `ricci_field`, `ricci_field_eq` and
`scalarCurvature_eq` give `Ric(E_b, E_k) = Σ_i η_{ii} R_{ikib}` in the rotation
coefficients and `R = Σ_i η_{ii} Ric(E_i, E_i)`, and `einstein_field` the frame
components of `G`.

**The tetrad equations.** `einstein_eq_iff`: at a point of the frame,
`G + Λ g = κ T` if and only if `G_{ab} + Λ η_{ab} = κ T_{ab}` for all frame indices;
`satisfiesEinstein_iff_frames` states this for the Einstein equations on a manifold
covered by the open sets of frames. The existence of a smooth orthonormal frame near every
point is not stated, and the Ricci tensor is written with `γ` rather than with `λ` alone.

| Result | Declarations | Source |
| --- | --- | --- |
| Frames and expansion | `LorentzMetric.OrthonormalFrame`, `OrthonormalFrame.coord`, `combine`, `coord_combine`, `sum_coord_smul`, `coordEquiv`, `coordEquiv_symm_single`, `form_eq_sum`, `bilinear_ext`, `coord_field`, `transition_orthonormal`, `CoordinateMetric.minkowskiFrame` | [Tetrad](../ProjectAinos/SmoothGeometry/Lorentzian/Tetrad.lean) |
| Rotation coefficients | `OrthonormalFrame.rotation`, `commutator`, `rotation_antisymm`, `commutator_eq`, `rotation_eq` | [Tetrad](../ProjectAinos/SmoothGeometry/Lorentzian/Tetrad.lean) |
| Curvature and the equations | `OrthonormalFrame.curvatureComponent`, `curvatureComponent_eq`, `ricci_eq_sum_frame`, `ricci_field`, `ricci_field_eq`, `scalarCurvature_eq`, `einstein_field`, `einstein_eq_iff`, `LorentzMetric.satisfiesEinstein_iff_frames` | [Tetrad](../ProjectAinos/SmoothGeometry/Lorentzian/Tetrad.lean) |

The typed examples are in `checks/TetradAPI.lean`. The decisions are recorded in
[GR16](general-relativity-notes.md).

## The synchronous reference system (§97)

**Normal geodesics.** `LorentzMetric.familyVelocity_pairing_eq`: for a two-parameter
family whose curves `t ↦ Γ(s, t)` are geodesics with the same metric norm `c` of their
velocity, the pairing `g(γ̇, ∂_s Γ)` is constant in `t`. Its derivative is
`g(γ̇, D_t ∂_sΓ) = g(γ̇, D_s γ̇) = ½ ∂_s g(γ̇, γ̇) = 0` by the interchange of the covariant
derivatives of a family (`covariantAlong_family_interchange`). So a variation field
orthogonal to the velocity at `t = 0` stays orthogonal (`familyVelocity_orthogonal`, the
lemma of Gauss): geodesics normal to a slice with unit velocity have synchronous
co-ordinates. The family is data; its construction from a slice needs the geodesic flow
of a metric smooth only on an open set and the inverse function theorem.

**Synchronous co-ordinates.** `CoordinateMetric.IsSynchronous g` is `g_{00} = −1` and
`g_{0α} = 0` on `U`, so `ds² = −dt² + γ_{αβ} dx^α dx^β`. The inverse has the same time row
(`inv_zero`), `Γ^k_{00} = 0`, `Γ^0_{0j} = 0`, `Γ^α_{0β} = ½ κ^α_β` and
`Γ^0_{αβ} = ½ ∂_t γ_{αβ}`, with `κ^α_β = γ^{αδ} ∂_t γ_{βδ}` (`extrinsicRate`) and
`κ_{αβ} = ∂_t γ_{αβ}` (`metricRate`). The time lines are geodesics in the proper time,
orthogonal to the slices (`isGeodesicOn_timeLine`). The Ricci tensor is (97.11)–(97.13):
`ricci_zero_zero`, `R_{00} = −½ ∂_t κ^α_α − ¼ κ^α_β κ^β_α`; `ricci_zero_succ`,
`R_{0α} = ½ (κ^β_{α;β} − κ^β_{β;α})` with the covariant derivative of the slices, where
`∂_t Γ^β_{βα} = ½ ∂_α κ^β_β` comes from `Γ^c_{ck} = ∂_k log √|g|` (`fderiv_log_densityOf`)
and the symmetry of second derivatives; `ricci_succ_succ`,
`R_{αβ} = P_{αβ} + ½ ∂_t κ_{αβ} + ¼ (κ^γ_γ κ_{αβ} − κ_{αγ} κ^γ_β − κ^γ_α κ_{γβ})` with the
Ricci tensor `P_{αβ}` of the slices (`sliceRicci`). The components are read natively by
`toLorentzMetric_ricci_chartField`; with them the Einstein equations in this system are
the constraints `R_{00}`, `R_{0α}` and the evolution `R_{αβ}`.

**Regression.** `DeSitterSlicing.metric` is `−dt² + e^{2t}(dx² + dy² + dz²)` on `ℝ⁴`:
it is synchronous with `κ^α_β = 2 δ^α_β`, and the three formulas give `Ric = 3 g`
(`DeSitterSlicing.ricci_eq`), the vacuum equations with `Λ = 3`.

**Scope.** The focusing of the time lines, by which a synchronous system meets a caustic
in a finite time, is planned with the equation of Raychaudhuri (F25).

| Result | Declarations | Source |
| --- | --- | --- |
| Normal geodesics | `LorentzMetric.familyVelocity_pairing_eq`, `familyVelocity_orthogonal` | [NormalGeodesics](../ProjectAinos/SmoothGeometry/Lorentzian/NormalGeodesics.lean) |
| Synchronous co-ordinates | `CoordinateMetric.IsSynchronous`, `extrinsicRate`, `metricRate`, `sliceRicci`, `fderiv_log_densityOf`, `IsSynchronous.coefficient_zero`, `inv_zero`, `christoffel_zero_zero`, `christoffel_zero_zero_succ`, `christoffel_succ_zero_succ`, `christoffel_zero_succ_succ`, `ricci_zero_zero`, `ricci_zero_succ`, `ricci_succ_succ`, `isGeodesicOn_timeLine` | [Synchronous](../ProjectAinos/SmoothGeometry/Lorentzian/Synchronous.lean) |
| De Sitter space | `DeSitterSlicing.metric`, `isSynchronous`, `extrinsicRate_eq`, `metricRate_eq`, `christoffel_spatial`, `ricci_eq` | [DeSitterSlicing](../ProjectAinos/GeneralRelativity/DeSitterSlicing.lean) |

The typed examples are in `checks/SynchronousAPI.lean`. The decisions are recorded in
[GR17](general-relativity-notes.md).

## The energy-momentum pseudotensor (§96)

**The superpotential.** For a metric given by coefficients on an open set `U`,
`CoordinateMetric.superpotentialDensity` is `λ^{iklm} = |g| (g^{ik} g^{lm} − g^{il} g^{km})`
with `|g| = (√|det g|)²`, and `superpotential` is `h^{ikl} = ∂_m λ^{iklm}`. It is antisymmetric
in `k, l` (`superpotential_antisymm`), so `∂_k ∂_l h^{ikl} = 0` on `U` by the symmetry of
second derivatives (`divergence_divergence_superpotential`).

**The identity (96.5).** At a point where the first derivatives of the coefficients vanish,
the Christoffel symbols and the first derivatives of `g^{ik}` and `√|g|` vanish, and every
second derivative is linear in `S_{ab,cd} = ∂_c ∂_d g_{ab}` (`secondDerivative`):
`∂_m Γ^k_{ij} = ½ g^{kl}(S_{jl,mi} + S_{li,mj} − S_{ij,ml})`
(`fderiv_christoffel_of_critical`), `∂_l ∂_m g^{bc} = −g^{ba} g^{ce} S_{ae,lm}`
(`fderiv_fderiv_coefficient_inv`), `∂_l ∂_m √|g| = ½ √|g| g^{ce} S_{ce,lm}`
(`fderiv_fderiv_densityOf`) and the Ricci tensor (`ricciOf_of_critical`). The product rule
at such a point keeps only `(∂∂u) v + u (∂∂v)` (`fderiv_fderiv_mul_of_critical`). The identity
`∂_l h^{ikl} = 2 |g| G^{ik}` (`divergence_superpotential_eq`) then reduces to an identity of
arrays (`pseudotensor_algebra`), whose four-fold sums match after reindexing with the
symmetries of `S` and `g`.

**The pseudotensor.** `pseudotensor` is `t^{ik}` defined by
`2 |g| (G^{ik} + t^{ik}) = ∂_l h^{ikl}`, with the raised Einstein tensor `raisedEinstein`. It
vanishes at a point where the first derivatives vanish (`pseudotensor_eq_zero`) and is
symmetric (`pseudotensor_symm`); with the Einstein equations `G^{ik} = κ T^{ik}` on `U` the total
`|g| (κ T^{ik} + t^{ik})` has zero ordinary divergence (`divergence_total_eq_zero`). The
pseudotensor depends on the co-ordinates; it is not a tensor.

**The expression (96.9).** At every point of `U`, `h^{ikl} = |g| H^{ikl}` with `H` (`pseudoH`)
linear in the Christoffel symbols (`superpotential_eq`, by `superpotential_algebra`), so
`t^{ik} = Γ^c_{cl} H^{ikl} + ½ ∂_l H^{ikl} − G^{ik}` needs only the first derivatives of `Γ`
(`divergence_superpotential_christoffel`, with `fderiv_pseudoH`). They are
`∂_m Γ^k_{ij} = ½ g^{kl}(Ŝ_{jl,mi} + Ŝ_{li,mj} − Ŝ_{ij,ml}) − Γ^k_{me} Γ^e_{ij}`
(`fderiv_christoffelOf`) for the array
`Ŝ_{ab,ce} = ∂_c ∂_e g_{ab} − g_{pq}(Γ^p_{cb} Γ^q_{ea} + Γ^p_{ca} Γ^q_{eb})`
(`reducedSecondDerivative`), which is symmetric in each pair like the second derivatives, and
the Ricci tensor is the `Ŝ`-part of its formula (`ricciOf_eq`). The part of `t^{ik}` linear in
`Ŝ` cancels the Einstein tensor (`pseudotensor_second_algebra`), and the part quadratic in the
Christoffel symbols is half the braces of Landau and Lifshitz (`pseudotensor_quadratic`), so
`t^{ik} = ½ {…}` with `pseudoBraces` (`pseudotensor_eq`); the factor `c⁴/16πk` is absorbed in
`t`. The identities of arrays are sums of contractions; after the sums are expanded, each is
rewritten to a representative of its contraction class (`sum4_reindex`, `sum2_reindex`). The
exact experiment `verify_pseudotensor_expression` in
[`verify_lorentz_geometry.py`](../experiments/ainos_experiments/verify_lorentz_geometry.py)
checks the normalization for a nonconstant metric in four dimensions.

**Scope.** The energy and momentum (96.16) as integrals over a spacelike hypersurface, their
conservation and their four-vector character are not stated: they need the decay of the
metric and of the matter at spatial infinity and co-ordinates that are Galilean there.

| Result | Declarations | Source |
| --- | --- | --- |
| Identities of arrays | `pseudotensor_algebra`, `inverse_second_algebra`, `density_second_algebra`, `ricci_algebra` | [PseudotensorAlgebra](../ProjectAinos/SmoothGeometry/Lorentzian/PseudotensorAlgebra.lean) |
| Superpotential and pseudotensor | `fderiv_fderiv_mul_of_critical`, `fderiv_mul_of_critical`, `fderiv_fderiv_sub`, `CoordinateMetric.superpotentialDensity`, `superpotential`, `raisedEinstein`, `pseudotensor`, `superpotential_antisymm`, `divergence_divergence_superpotential`, `secondDerivative`, `fderiv_christoffel_of_critical`, `fderiv_fderiv_coefficient_inv`, `fderiv_fderiv_densityOf`, `ricciOf_of_critical`, `divergence_superpotential_eq`, `pseudotensor_eq_zero`, `divergence_superpotential_symm`, `pseudotensor_symm`, `divergence_total_eq_zero` | [Pseudotensor](../ProjectAinos/SmoothGeometry/Lorentzian/Pseudotensor.lean) |
| Algebra of (96.9) | `pseudoH`, `pseudoHDeriv`, `pseudoBraces`, `christoffelDerivative`, `ricciDerivative`, `reducedSecond`, `sum2_reindex`, `sum4_reindex`, `pseudoHDeriv_add`, `reducedSecond_symm_left`, `reducedSecond_symm_right`, `christoffelDerivative_reducedSecond`, `superpotential_algebra`, `pseudotensor_second_algebra`, `pseudotensor_quadratic` | [PseudotensorQuadratic](../ProjectAinos/SmoothGeometry/Lorentzian/PseudotensorQuadratic.lean) |
| The expression (96.9) | `fderiv_pseudoH`, `CoordinateMetric.reducedSecondDerivative`, `sum_coefficient_mul_christoffelOf`, `fderiv_christoffelOf`, `ricciOf_eq`, `superpotential_eq`, `divergence_superpotential_christoffel`, `raisedEinstein_eq`, `pseudotensor_eq` | [PseudotensorChristoffel](../ProjectAinos/SmoothGeometry/Lorentzian/PseudotensorChristoffel.lean) |

The typed examples are in `checks/PseudotensorAPI.lean` and
`checks/PseudotensorChristoffelAPI.lean`. The decisions are recorded in GR18 and GR19 of the
[notes](general-relativity-notes.md).

## The centrally symmetric field (§§100, 101)

**Co-ordinate tools.** Five shared files carry the computations. `CoordinateMetric.ofDiagonal`
builds a metric from diagonal coefficients. `christoffelOf_diagonal` gives its Christoffel
symbols with no differentiability hypothesis, because the off-diagonal entries are the constant
zero. `christoffelOf_eq_of_lowered` certifies a table of Christoffel symbols by the lowering
identity `g_{lq} Γ^q_{ij} = ½(∂_i g_{jl} + ∂_j g_{li} − ∂_l g_{ij})`, without computing an
inverse, and `ricciOf_eq_ricciOfChristoffel` then computes the Ricci tensor from the table.
`CoordinateMetric.isGeodesicOn_iff` is the geodesic equation of a coordinate metric in its
co-ordinates, `isKillingField_iff_lieOf` the Killing equation in components, and
`ofFrameCriterion` the Lorentz criterion for a form in a pointwise frame, which a time
co-ordinate that becomes null needs.

**The ansatz (100.1).** `SphericalAnsatz.Data` is a pair of smooth positive functions
`A, B` of `(t, r)` on open sets `I × J` with `J ⊆ (0, ∞)`, and `SphericalAnsatz.metric` is
`−A dt² + B dr² + r² dθ² + r² sin²θ dφ²` on `I × J × (0, π) × ℝ`. Its Christoffel symbols
(`christoffelOf_eq`), Ricci tensor (`ricciOf_eq`) and Einstein tensor (`einsteinOf_eq`) are
computed at every point in the partial derivatives `partialT`, `partialR`:
`G₀₀ = A/r² (1 − 1/B + r ∂_rB/B²)`, `G₀₁ = ∂_tB/(rB)`, `G₁₁ = ∂_rA/(rA) − (B − 1)/r²`,
`G₃₃ = sin²θ G₂₂` (100.3)–(100.5), with `G₀₀/A + G₁₁/B = ∂_r(AB)/(rAB²)`
(`einstein_zero_zero_div_add_one_one_div`).

**The Schwarzschild field.** The exterior metric of `SchwarzschildExterior` is the ansatz with
`A = 1 − 2M/r`, `B = (1 − 2M/r)⁻¹` (`coefficient_eq_ansatz`). Its Ricci tensor vanishes on the
domain `r > 2M`, `0 < θ < π` (`ricciOf_eq_zero`), so it satisfies the vacuum Einstein
equations for every coupling (`isEinstein_zero`, `satisfiesEinstein_zero`), and the native
Ricci tensor vanishes on all tangent vectors (`ricci_eq_zero`).

**Birkhoff's theorem.** `SphericalAnsatz.birkhoff`: if `I` and `J` are preconnected and the
Ricci tensor of the ansatz vanishes, there are a constant `M` with `2M < r` on `J` and a
smooth positive `f` with `B = r/(r − 2M)` and `A = f(t)(1 − 2M/r)`. The proof uses only
`G₀₁ = 0` (so `∂_tB = 0`), `G₀₀ = 0` (so `∂_r(r/B) = 1`) and `G₀₀/A + G₁₁/B = 0` (so
`∂_r(AB) = 0`). Conversely the Ricci tensor of these coefficients vanishes for every `M` and
`f` (`ricciOf_schwarzschildData`), and a change of the time co-ordinate with `T' = √f` turns
the metric into the exterior Schwarzschild form (`form_schwarzschildData`,
`birkhoff_timeChange`). The mass is unique (`mass_schwarzschildData`). `M` may be negative:
then the exterior has no horizon.

**Across the horizon.** `EddingtonFinkelstein.metric` is
`−(1 − 2M/r) dv² + 2 dv dr + r² dΩ²` on `r > 0`, a Lorentz metric by `ofFrameCriterion`, since
`v` is a null co-ordinate where `r = 2M`. Its Christoffel symbols are certified
(`christoffelOf_eq`) and its Ricci tensor vanishes on the whole domain (`ricciOf_eq_zero`,
`ricci_eq_zero`). The ingoing radial line `(v₀, r₀ − λ, θ₀, φ₀)` is a null geodesic
(`isGeodesicOn_ingoing`, `form_ingoingRay_velocity`) that crosses `r = 2M`
(`exists_ingoingRay_lt`). Inside `r = 2M` every causal vector with `dv > 0` has `dr < 0`
(`radial_lt_zero_of_causal`). The substitution `v = t + r + 2M log(r/2M − 1)` pulls the form
back to the exterior form (`hasFDerivAt_toEddington`, `form_toEddington`).

**Rotations and the plane of the motion.** The generators of the rotations,
`K₀ = −sin φ ∂_θ − cot θ cos φ ∂_φ`, `K₁ = cos φ ∂_θ − cot θ sin φ ∂_φ`, `K₂ = ∂_φ`
(`rotationField`), are Killing fields of the exterior metric
(`isKillingField_rotationField`, by `lieOf_rotationField`). Along a geodesic, the components
`J_a = g(K_a, γ̇)` are constant (`angularMomentum_eq`),
`J₀² + J₁² + J₂² = r⁴(θ̇² + sin²θ φ̇²)` (`sum_angularMomentum_sq`), and the radial direction
stays orthogonal to the constant vector `J` (`planar_motion`): the motion is in a plane
through the centre.

**The integrals of the motion.** Along a geodesic given on an open convex set of
parameters, the energy `E = −g(∂_t, γ̇) = (1 − 2M/r) ṫ` (`energy_eq`, `energy_eq_coord`), the
square of the angular momentum (`angularMomentumSq_eq`) and the normalization `κ = −g(γ̇, γ̇)`
(`normalization_eq`) are constant, and the radial equation is
`ṙ² = E² − (1 − 2M/r)(κ + L²/r²)` (`radial_sq_eq`, with `effectivePotential`). The angle
swept in the plane of the motion (`sweptAngle`) has the rate `L/r²`
(`hasDerivAt_sweptAngle_eq_div`), and the co-ordinate time the rate `E/(1 − 2M/r)`
(`timeRate_eq`).

**Circular orbits.** For bodies (`κ = 1`, `M > 0`) the effective potential is critical at `R`
if and only if `L²(R − 3M) = MR²` (`deriv_effectivePotential_eq_zero_iff`), which forces
`R > 3M`. At a critical point the second derivative is `2M(R − 6M)/(R³(R − 3M))`, so the
circular orbit is stable if and only if `R > 6M` (`deriv_deriv_effectivePotential_pos_iff`).
For light the only critical radius is `R = 3M`, a maximum
(`deriv_effectivePotential_light_eq_zero_iff`, `isMaxOn_effectivePotential_light`). The
circular orbits `s ↦ (αs, R, π/2, Ωs)` with `α = (1 − 3M/R)^{−1/2}`, `Ω = α√(M/R³)` and the
photon circle at `3M` are geodesics (`isGeodesicOn_circular`, `isGeodesicOn_photonCircle`),
with `E² = (1 − 2M/R)²/(1 − 3M/R)` (`circularEnergy_sq`).

**The perihelion advance.** For a bound orbit of a body given between a perihelion and an
aphelion, `u = 1/r` satisfies `u̇² = L²u⁴(u₁ − u)(u − u₂)(1 − 2M(u₁ + u₂ + u))`, from the two
roots `u₁ = 1/r_min`, `u₂ = 1/r_max` of the cubic (`cubic_eq_factor_of_roots`,
`radial_sq_eq_factor`). The simple-apsides condition `2M(2u₁ + u₂) < 1` is derived, by a
Grönwall argument that excludes a double root at the perihelion (`simple_apsides_lt`). The
angle swept between the apsides is the exact integral
`∫₀^π dθ/√(1 − 2M(u₁ + u₂ + u(θ)))` (`angle_between_apsides`, with
`Perihelion.apsidalAngle`), the return from the aphelion sweeps the same angle
(`return_half`), and the advance between successive perihelia satisfies
`0 ≤ δφ − 3πM(u₁ + u₂) ≤ 4πM²(2u₁ + u₂)²` for `2M(2u₁ + u₂) ≤ 1/4`
(`perihelion_advance_between_perihelia`). With `r_min = a(1 − e)`, `r_max = a(1 + e)` the
leading term is `6πM/(a(1 − e²))` (101.7) (`perihelion_advance_bounds_semiMajor`).

**The deflection of light.** For a ray given from its closest approach to infinity, with
the impact parameter `ρ = L/E` (`impactParameter`), the radial equation is the small-angle
radicand of the potential `−u³` with strength `2M/ρ` (`radial_sq_eq_light`), and twice the
angle swept to infinity tends to `π − χ` with the deflection angle `χ` of the scattering
library (`tendsto_two_mul_sweptAngle_atTop`, L&L (18.1)). The closest approach is the root
of `IsClosest` (`closest_eq`, `exists_isClosest_light`), and for `2M/ρ` small
`|χ + 4M/ρ| ≤ C(M/ρ)²` (`deflection_bound`, `deflection_bound_sweptAngle`): the ray is turned
towards the centre by `4M/ρ` (101.9), with a quadratic remainder. The constants `δ` and `C`
come from the implicit function theorem and are not explicit. `exists_ray_zero_mass` is a
ray with `M = 0` that satisfies every hypothesis.

**The chart geodesics of the geodesic Hamiltonian.** The comparison deferred in GR04 is
proved. For a coordinate metric on all of the model space whose coefficients are the values
of a matrix of the free C∞-ring, a curve of `TimeFunction`s is an `IsCoordinateGeodesic`
exactly when it is a native geodesic for all values of the parameter
(`GeodesicHamiltonian.isCoordinateGeodesic_iff_isGeodesicOn`). For the equatorial plane of
the exterior field the trajectories of `H = ½ g^{μν} p_μ p_ν` are the native geodesics of
`SchwarzschildEquatorial.equatorialMetric` with `p_μ = g_{μν} ẋ^ν`
(`isCoordinateGeodesic_iff`, `isTrajectory_iff_isGeodesicOn`, `momentum_apply`); the
circular orbits of Kepler's law in co-ordinate time are an instance (`isTrajectory_kepler`).

**Scope.** Units `G = c = 1`, time first, signature `(−+++)`. The orbits and rays are given
geodesics on a convex set of parameters, as AGENTS.md prescribes for a field smooth only on
an open set; the existence of a non-circular bound orbit and of a ray from infinity with
`M > 0` is not constructed. The deflection angle is defined from the outgoing half of the ray,
as in the scattering library; the symmetry of the incoming half is not stated. Birkhoff's
theorem is stated within the ansatz (100.1): the reduction of a metric with an isometric
action of `SO(3)` to that ansatz, and charts that cover the axis or the whole sphere, are not
stated. The rotating field of §104 is the next stage.

| Result | Declarations | Source |
| --- | --- | --- |
| Diagonal metrics | `CoordinateMetric.diagonalForm`, `ofDiagonal`, `coefficient_ofDiagonal`, `christoffelOf_diagonal`, `christoffelOf_ofDiagonal`, `minkowski_eq_ofDiagonal` | [DiagonalMetric](../ProjectAinos/SmoothGeometry/Lorentzian/DiagonalMetric.lean) |
| Certified Christoffel tables | `CoordinateMetric.ricciOfChristoffel`, `ricciOf_eq_ricciOfChristoffel`, `christoffelOf_eq_of_lowered`, `curvatureOf`, `toLorentzMetric_chartCurvature_eq_curvatureOf`, `fderiv_single_eq_deriv_update` | [ChristoffelCertificate](../ProjectAinos/SmoothGeometry/Lorentzian/ChristoffelCertificate.lean) |
| Geodesics and Killing fields in co-ordinates | `CoordinateMetric.isGeodesicOn_iff`, `form_curveVelocity`, `pairing_curveVelocity`, `vectorFieldOf`, `lieOf`, `isKillingField_iff_lieOf`, `isKillingField_of_lieOf` | [CoordinateGeodesic](../ProjectAinos/SmoothGeometry/Lorentzian/CoordinateGeodesic.lean), [CoordinateKilling](../ProjectAinos/SmoothGeometry/Lorentzian/CoordinateKilling.lean) |
| The frame criterion | `CoordinateMetric.ofFrameCriterion`, `ofFrameCriterion_refl`, `nullMetric` | [CoordinateFrameCriterion](../ProjectAinos/SmoothGeometry/Lorentzian/CoordinateFrameCriterion.lean) |
| The ansatz (100.1) | `SphericalAnsatz.Data`, `metric`, `christoffelOf_eq`, `ricciOf_eq`, `einsteinOf_eq`, `einstein_zero_zero`, `einstein_zero_one`, `einstein_one_one`, `einstein_two_two`, `einstein_zero_zero_div_add_one_one_div` | [SphericalAnsatz](../ProjectAinos/GeneralRelativity/SphericalAnsatz.lean) |
| The Schwarzschild field | `SchwarzschildExterior.coefficient_eq_ansatz`, `ricciOf_eq_zero`, `isEinstein_zero`, `satisfiesEinstein_zero`, `ricci_eq_zero` | [SchwarzschildVacuum](../ProjectAinos/GeneralRelativity/SchwarzschildVacuum.lean) |
| Birkhoff's theorem | `SphericalAnsatz.birkhoff`, `birkhoff_timeChange`, `ricciOf_schwarzschildData`, `form_schwarzschildData`, `mass_schwarzschildData` | [Birkhoff](../ProjectAinos/GeneralRelativity/Birkhoff.lean) |
| Eddington–Finkelstein | `EddingtonFinkelstein.metric`, `ricciOf_eq_zero`, `ricci_eq_zero`, `isGeodesicOn_ingoing`, `exists_ingoingRay_lt`, `radial_lt_zero_of_causal`, `form_toEddington` | [EddingtonFinkelstein](../ProjectAinos/GeneralRelativity/EddingtonFinkelstein.lean) |
| Rotations | `SchwarzschildExterior.rotationField`, `isKillingField_rotationField`, `angularMomentum_eq`, `sum_angularMomentum_sq`, `planar_motion` | [SchwarzschildRotations](../ProjectAinos/GeneralRelativity/SchwarzschildRotations.lean) |
| Integrals of the motion | `SchwarzschildExterior.energy_eq`, `angularMomentumSq_eq`, `normalization_eq`, `radial_sq_eq`, `sweptAngle`, `hasDerivAt_sweptAngle_eq_div`, `timeRate_eq` | [SchwarzschildOrbit](../ProjectAinos/GeneralRelativity/SchwarzschildOrbit.lean) |
| Circular orbits | `SchwarzschildExterior.effectivePotential`, `deriv_effectivePotential_eq_zero_iff`, `deriv_deriv_effectivePotential_pos_iff`, `deriv_effectivePotential_light_eq_zero_iff`, `isGeodesicOn_circular`, `isGeodesicOn_photonCircle`, `circularEnergy_sq` | [SchwarzschildCircular](../ProjectAinos/GeneralRelativity/SchwarzschildCircular.lean) |
| The perihelion advance | `Perihelion.apsidalAngle`, `apsidalAngle_bounds`, `SchwarzschildExterior.simple_apsides_lt`, `angle_between_apsides`, `return_half`, `perihelion_advance_between_perihelia`, `perihelion_advance_bounds_semiMajor` | [PerihelionIntegral](../ProjectAinos/GeneralRelativity/PerihelionIntegral.lean), [Perihelion](../ProjectAinos/GeneralRelativity/Perihelion.lean) |
| The deflection of light | `LightDeflection.exists_abs_deflectionAngle_schwarzschild_add_le`, `SchwarzschildExterior.radial_sq_eq_light`, `tendsto_two_mul_sweptAngle_atTop`, `closest_eq`, `deflection_bound`, `deflection_bound_sweptAngle`, `exists_ray_zero_mass` | [DeflectionIntegral](../ProjectAinos/GeneralRelativity/DeflectionIntegral.lean), [LightDeflection](../ProjectAinos/GeneralRelativity/LightDeflection.lean) |
| Chart geodesics | `GeodesicHamiltonian.isCoordinateGeodesic_iff_isGeodesicOn`, `SchwarzschildEquatorial.equatorialMetric`, `isCoordinateGeodesic_iff`, `isTrajectory_iff_isGeodesicOn`, `isTrajectory_kepler` | [EquatorialComparison](../ProjectAinos/GeneralRelativity/EquatorialComparison.lean) |

The typed examples are in `checks/CoordinateToolsAPI.lean`, `checks/SchwarzschildAPI.lean` and
`checks/SchwarzschildOrbitAPI.lean`. The exact experiment `verify_spherical_vacuum` in
[`verify_lorentz_geometry.py`](../experiments/ainos_experiments/verify_lorentz_geometry.py)
checks the formulas of the ansatz, Birkhoff's identities and the orbits. The decisions are
recorded in GR20 and GR21 of the [notes](general-relativity-notes.md) and in G05 of the
[smooth-geometry notes](smooth-geometry-notes.md).

## The rotating field (§104)

**The metric.** `Kerr.metric` is the Kerr metric (104.1) in Boyer–Lindquist co-ordinates with
`χ = cos θ`, so that every coefficient is a rational function of `r` and `χ`:
`g_tt = −(1 − 2Mr/Σ)`, `g_tφ = −2Mar(1 − χ²)/Σ`, `g_rr = Σ/Δ`, `g_χχ = Σ/(1 − χ²)`,
`g_φφ = (r² + a² + 2Ma²r(1 − χ²)/Σ)(1 − χ²)`, with `Σ = r² + a²χ²` and `Δ = r² − 2Mr + a²`,
on the exterior `r > r₊ = M + √(M² − a²)`, `−1 < χ < 1`, for `M > 0` and `a² ≤ M²`. It is a
Lorentz metric by `ofFrameCriterion`, since `∂_t` is spacelike in the ergoregion; the frame
shears `e₀` to `e₀ − (g_tφ/g_φφ) e₃`, where `g_tt g_φφ − g_tφ² = −Δ(1 − χ²)`.

**The vacuum equations.** The twenty independent Christoffel symbols are certified by the
lowering identity (`christoffelOf_eq`). The Ricci tensor then vanishes on the domain
(`ricciOf_eq_zero`), natively on all tangent vectors (`ricci_eq_zero`), and the metric satisfies
the vacuum Einstein equations (`isEinstein_zero`, `satisfiesEinstein_zero`). The certificate is
generated by the scripts in [`experiments/kerr_certificate`](../experiments/kerr_certificate),
which reproduce the file byte for byte, and Lean checks every generated lemma.

**Bounded claims.**
- `∂_t` and `∂_φ` are Killing fields (`isKillingField_time`, `isKillingField_angle`).
- The ergoregion, where `∂_t` is spacelike, is `r² − 2Mr + a²χ² < 0` (`ergoregion_iff`). For
  `a ≠ 0` it is nonempty between `r₊` and `2M` on the equator (`ergoregion_nonempty`).
- A stationary observer `∂_t + Ω∂_φ` is timelike exactly for `Ω₋ < Ω < Ω₊`
  (`form_rotating_neg_iff`). In the ergoregion with `a > 0`, `Ω₋ > 0`: every observer rotates
  with the black hole (`omegaMinus_pos`). At the horizon both bounds tend to
  `Ω_H = a/(r₊² + a²)` (`tendsto_omegaPlus`, `tendsto_omegaMinus`), and `g^{rr} = Δ/Σ → 0`
  (`inverse_rr`, `tendsto_inverse_rr`).
- At `a = 0` the change `θ = arccos χ` pulls the exterior Schwarzschild form back to the form of
  the metric (`hasFDerivAt_toAngle`, `form_zero_toAngle`).

**Scope.** The event horizon as a global causal boundary, the end state of collapse and the
uniqueness of the Kerr field are outside the target of §104. The region `r ≤ r₊`, the axis
`χ = ±1` and a chart across the horizon are not stated.

| Result | Declarations | Source |
| --- | --- | --- |
| The Kerr field | `Kerr.metric`, `christoffelOf_eq`, `ricciOf_eq_zero`, `ricci_eq_zero`, `satisfiesEinstein_zero`, `isKillingField_time`, `isKillingField_angle`, `ergoregion_iff`, `ergoregion_nonempty`, `form_rotating_neg_iff`, `omegaMinus_pos`, `tendsto_omegaPlus`, `tendsto_omegaMinus`, `inverse_rr`, `tendsto_inverse_rr`, `form_zero_toAngle` | [Kerr](../ProjectAinos/GeneralRelativity/Kerr.lean) |

The typed examples are in `checks/KerrAPI.lean`. The exact experiment `verify_kerr_vacuum` checks
the vacuum equations with SymPy. The decisions are recorded in GR22 of the
[notes](general-relativity-notes.md).

## Isotropic cosmology (§§111–114)

**Spaces of constant curvature.** `SpaceForm.coefficient k` is `ψ_k⁻² δ` with
`ψ_k = 1 + k|x|²/4` on `ψ_k > 0`. Its curvature is `k(δ^l_i h_jm − δ^l_j h_im)`
(`curvatureOf_eq`), so `Ric = 2k h` (`ricciOf_eq`, (111.1)–(111.2)). For `k = 1` the inverse
stereographic map is a homeomorphism of ℝ³ onto `S³` minus a point (`sphere_embedding`,
`sphereHomeomorph`). For `k = −1` the ball `|x| < 2` is homeomorphic to the upper sheet of the
hyperboloid (`hyperboloid_embedding`, `hyperboloidHomeomorph`). Both pull the ambient metric
back to `coefficient k` (`sphere_firstFundamentalForm`, `hyperboloid_firstFundamentalForm`).
The closed space of radius `a` has the volume `2π²a³`
(`integral_inv_conformalFactor_pow_three_of_pos`).

**The Friedmann equations.** `FLRW.metric` is `−N(t)² dt² + a(t)² ψ_k⁻² dx²`, with a lapse `N`;
for `N = 1` it is synchronous. With the comoving perfect fluid `perfectFluidStress`, the
divergence `∇^a T_ab` is `−(ρ̇ + 3H(ρ + p))` in its time component and zero otherwise
(`divergenceOf_perfectFluidStress`). The Einstein equations hold if and only if both Friedmann
equations hold (`isEinstein_iff_friedmann`, `satisfiesEinstein_iff_friedmann`). The continuity
equation follows from the two by an exact identity, without dividing by `H`
(`continuity_of_friedmann`). Conversely, where `ȧ ≠ 0`, the first equation and continuity give
the second (`second_of_first_of_continuity`); a static counterexample shows that this needs
`ȧ ≠ 0` (`not_secondFriedmann_static`). `k` has the sign of `ρ − 3H²/κ` (`curvature_sign`).

**Exact models.** In conformal time (`N = a`) the closed dust `a = a₀(1 − cos η)` (112.8), the
closed radiation `a = a₀ sin η`, the open dust `a = a₀(cosh η − 1)` (113.3), the open radiation
`a = a₀ sinh η` and the flat models `a = a₀η²`, `a = a₀η` are exact solutions
(`isEinstein_closedDust`, …, `isEinstein_flatRadiation`), with their cosmic times, for
example `t = a₀(η − sin η)` (`hasDerivAt_closedDustTime`), as the proper time of the comoving
observers (`properTime_closedDust`). The closed dust reaches its maximal radius `a_m = 2a₀` at
the age `πa_m/2` (`closedDustTime_pi_sub_zero`, `tendsto_closedDust_age`). An open or flat
universe that expands at one time expands at all times (`open_expands_forever`).

**The red shift.** The comoving observers move along geodesics (`comoving_isGeodesicOn`) and
measure the frequency `ω = N ṫ` of a ray (`observedFrequency_eq`). Along a null geodesic `a ω`
is constant (`scale_mul_frequency_eq`), so `1 + z = a(t_obs)/a(t_em)` (`redshift_eq`, (114.2)).
In de Sitter space the radial ray `λ ↦ (log λ, x₀ − 1/λ, 0, 0)` is an explicit instance
(`isGeodesicOn_deSitterRay`, `redshift_deSitterRay`).

**Scope.** The local classification of homogeneous isotropic three-metrics is not stated. The
models are explicit solutions; the existence and uniqueness of solutions of the Friedmann
equation through `a = 0` is not stated. The observers of the conformal models are given curves.
Homogeneous spaces and the Kasner solution (§§116, 117) follow below.

| Result | Declarations | Source |
| --- | --- | --- |
| Spaces of constant curvature | `SpaceForm.conformalFactor`, `coefficient`, `christoffelOf_eq`, `curvatureOf_eq`, `ricciOf_eq`, `sphere_embedding`, `sphereHomeomorph`, `hyperboloid_embedding`, `hyperboloidHomeomorph`, `sphere_firstFundamentalForm`, `hyperboloid_firstFundamentalForm`, `integral_inv_conformalFactor_pow_three` | [SpaceForm](../ProjectAinos/SmoothGeometry/Lorentzian/SpaceForm.lean) |
| The Friedmann equations | `FLRW.Data`, `metric`, `isSynchronous`, `einsteinOf_eq`, `perfectFluidStress`, `divergenceOf_perfectFluidStress`, `isEinstein_iff_friedmann`, `satisfiesEinstein_iff_friedmann`, `continuity_of_friedmann`, `second_of_first_of_continuity`, `curvature_sign`, `ricciOf_deSitter`, `isEinstein_milne` | [FLRW](../ProjectAinos/GeneralRelativity/FLRW.lean) |
| Exact models | `CosmologicalModels.isEinstein_closedDust`, `isEinstein_closedRadiation`, `isEinstein_openDust`, `isEinstein_openRadiation`, `isEinstein_flatDust`, `isEinstein_flatRadiation`, `properTime_closedDust`, `tendsto_closedDust_age`, `open_expands_forever` | [CosmologicalModels](../ProjectAinos/GeneralRelativity/CosmologicalModels.lean) |
| The red shift | `CosmologicalRedshift.comoving_isGeodesicOn`, `observedFrequency_eq`, `scale_mul_frequency_eq`, `redshift_eq`, `isGeodesicOn_deSitterRay`, `redshift_deSitterRay` | [CosmologicalRedshift](../ProjectAinos/GeneralRelativity/CosmologicalRedshift.lean) |

The typed examples are in `checks/CosmologyAPI.lean`. The decisions are recorded in GR23 of the
[notes](general-relativity-notes.md) and in G06 of the [smooth-geometry notes](smooth-geometry-notes.md).

## Homogeneous cosmological models (§§116, 117)

**Structure constants.** `StructureConstants.ofBianchi n a` is the Bianchi decomposition
`C^c_{ab} = Σ_d ε_{abd} n_{dc} + δ^c_b a_a − δ^c_a a_b` (L&L (116.8)). Every set of constants
antisymmetric in the lower indices has exactly one such form with `n` symmetric
(`existsUnique_bianchi`, with the inverse maps `bianchiN`, `bianchiA`). The Jacobi identity of
`[X_a, X_b] = Σ C^c_{ab} X_c` is `n a = 0` (`jacobi_ofBianchi_iff`, `jacobi_iff`), and class A is
`a = 0`, the vanishing of the traces `Σ_c C^c_{bc}` (`bianchiA_eq_zero_iff`). The canonical types
`bianchiI`, …, `bianchiIX` of L&L's table satisfy the identity (`jacobi_bianchiI`, …), and
`not_jacobi_ofBianchi_one` shows that it is a genuine condition.

**The homogeneous metric.** `HomogeneousSpace.InvariantFrame` is the data of a given invariant
frame: vector fields `X_a` and dual one-forms `ω^a` with components smooth on a nonempty open set
of ℝ³, and constant structure constants. `HomogeneousSpace.Data` adds a triad `e(t)` with a smooth
inverse `f(t)`; the metric is `−dt² + Σ_k (θ^k)²` with `θ^k = Σ_a e_{ka} ω^a`, that is
`γ_{ab} = (eᵀe)_{ab}` in the invariant frame (`Data.metric`). The fields `∂_t` and
`E_i = Σ_a f_{ai} X_a` are an orthonormal frame (`form_frameField`, `Data.frame`, built with
`CoordinateMetric.orthonormalFrameOf`). Their commutators are `[E₀, E_j] = Σ ḟ_{aj} X_a` and
`[E_i, E_j] = Σ_c (Σ_{ab} f_{ai} f_{bj} C^c_{ab}) X_c` (`bracket_zero_succ`, `bracket_succ_succ`),
so the commutator coefficients `λ_{abc}` are functions of the time alone (`Data.lam`,
`commutator_frame`).

**The reduction of the field equations.** The frame components of the Ricci tensor at a point are
`frameRicci` at its time (`ricci_frame`): Cartan's structure equations in the coefficients
`λ_{abc}`, the rotation coefficients `γ_{abc} = ½(λ_{abc} + λ_{bca} − λ_{cab})` and their time
derivatives. Hence the vacuum equations on the whole domain are equivalent to ordinary
differential equations on the interval of times (`ricci_eq_zero_iff`), and so are the equations
`G + Λg = κT` with a comoving perfect fluid (`einstein_iff`). This is the statement of the
dictionary that the reduction preserves the full field equations; no action is reduced.

**Diagonal models of class A.** For `C^c_{ab} = ε_{abc} n_c` (`ofBianchi_diagonal`) and
`e = diag(a₁, a₂, a₃)` (`Data.diagonal`), `λ_{k0j} = −(ȧ_k/a_k) δ_{kj}` and
`λ_{kij} = ε_{ijk} n_k a_k/(a_i a_j)` (`lam_diagonal`). The Ricci tensor is diagonal in the
frame, with `R₀₀ = −Σ ä_i/a_i` and
`R_{ii} = ä_i/a_i + (ȧ_i/a_i)(ȧ_j/a_j + ȧ_k/a_k) + ((n_i a_i²)² − (n_j a_j² − n_k a_k²)²)/(2(a₁a₂a₃)²)`
(`frameRicci_zero_zero`, `frameRicci_one_one`, `frameRicci_two_two`, `frameRicci_three_three`,
`frameRicci_ne`), and the vacuum equations are these four (`ricci_eq_zero_iff_diagonal`). For type
IX they are the equations that L&L use in §118 (`ricci_eq_zero_iff_bianchiIX`).

**Invariant frames.** `BianchiFrames.lean` gives the frames of type I (the co-ordinate fields),
type II (`X₂ = ∂₂ + x₁∂₀`), type V (`X₁ = e^{x₀}∂₁`, `X₂ = e^{x₀}∂₂`) and type IX (the
left-invariant frame of `SU(2)` in Euler angles on `0 < x₀ < π`), each with its canonical
structure constants (`InvariantFrame.bianchiI`, …, `InvariantFrame.bianchiIX`). The Kasner metric
is a vacuum solution of type I through the frame reduction (`kasnerModel`,
`ricci_kasnerModel_eq_zero`), independently of the co-ordinate computation below.

**The Kasner solution.** `Kasner.Data` is the diagonal metric `−dt² + Σ a_α(t)² dx_α²` with its
Christoffel, Ricci and Einstein tables (`christoffelOf_eq`, `ricciOf_eq`, `einsteinOf_eq`). With a
comoving perfect fluid the Einstein equations are one constraint and three evolution equations
(`isEinstein_iff`). The metric `a_α = t^{p_α}` on `t > 0` is Ricci flat if and only if
`Σp = Σp² = 1` or `p = 0`, the latter being Minkowski space (`ricciOf_kasner_eq_zero_iff`,
(117.3)); its volume element is `t` (`volume_kasner`). Ordered exponents lie in
`−1/3 ≤ p₁ ≤ 0 ≤ p₂ ≤ 2/3 ≤ p₃ ≤ 1` (`kasner_ranges`) and are `(0, 0, 1)` or
`p(u) = (−u, 1 + u, u(1 + u))/(1 + u + u²)` with `u ≥ 1` (`eq_kasnerExponents`, (117.5)–(117.6));
`u ↦ 1/u` exchanges the last two (`kasnerExponents_inv`). Apart from the permutations of
`(1, 0, 0)`, `R^α_{0α0} = p_α(p_α − 1)/t²` is nonzero at every point
(`chartCurvature_kasner_ne_zero`).

**Dust.** The declared matter model is dust: `a_α = t^{p_α}(t + t₀)^{2/3 − p_α}` with `t₀ ≥ 0` is an
exact solution with `ρ = 4/(3κ t(t + t₀))` (`isEinstein_dustKasner`). It approaches the Kasner
metric as `t → 0⁺` for `t₀ > 0` (`tendsto_dustKasner_nhdsGT`) and the isotropic dust model
`a = t^{2/3}` as `t → ∞` (`tendsto_dustKasner_atTop`); `t₀ = 0` is that model.

**Scope.** The invariant frame and the triad are data (decision 5 on #135): the group of motions,
Lie's third theorem, the classification of the structure constants up to a change of frame and
the construction of an invariant frame for a given homogeneous space are not stated. The approach
of a general solution with matter to the Kasner regime is not stated; one exact transition between
Kasner epochs is the planned part of §118.

| Result | Declarations | Source |
| --- | --- | --- |
| Frames from components | `CoordinateMetric.lieBracketOf`, `mlieBracket_vectorFieldOf`, `contMDiffAt_vectorFieldOf`, `mvfderiv_vectorFieldOf`, `orthonormalFrameOf`, `commutator_orthonormalFrameOf`, `rotationOf`, `ricciOfFrame`, `ricci_orthonormalFrameOf`, `ricci_eq_zero_iff_frame` | [CoordinateFrame](../ProjectAinos/SmoothGeometry/Lorentzian/CoordinateFrame.lean) |
| Structure constants | `StructureConstants.levi`, `IsAntisymm`, `Jacobi`, `ofBianchi`, `bianchiN`, `bianchiA`, `existsUnique_bianchi`, `jacobi_ofBianchi_iff`, `jacobi_iff`, `bianchiA_eq_zero_iff`, `bianchiI`, …, `bianchiIX`, `jacobi_bianchiIX` | [StructureConstants](../ProjectAinos/GeneralRelativity/StructureConstants.lean) |
| The homogeneous metric and its reduction | `HomogeneousSpace.InvariantFrame`, `Data`, `Data.metric`, `form_frameField`, `frame`, `bracket_zero_succ`, `bracket_succ_succ`, `lam`, `commutator_frame`, `frameRicci`, `ricci_frame`, `ricci_eq_zero_iff`, `fluid`, `einstein_iff` | [HomogeneousSpace](../ProjectAinos/GeneralRelativity/HomogeneousSpace.lean) |
| Diagonal models of class A | `ofBianchi_diagonal`, `Data.diagonal`, `lam_diagonal`, `frameRicci_zero_zero`, `frameRicci_one_one`, `frameRicci_two_two`, `frameRicci_three_three`, `frameRicci_ne`, `ricci_eq_zero_iff_diagonal` | [BianchiClassA](../ProjectAinos/GeneralRelativity/BianchiClassA.lean) |
| Invariant frames | `InvariantFrame.bianchiI`, `bianchiII`, `bianchiV`, `bianchiIX`, `bracket_fieldIX`, `coframe_fieldIX` | [BianchiFrames](../ProjectAinos/GeneralRelativity/BianchiFrames.lean) |
| Types I and IX | `bianchiIX_eq_diagonal`, `ricci_eq_zero_iff_bianchiIX`, `kasnerModel`, `ricci_kasnerModel_eq_zero` | [BianchiExamples](../ProjectAinos/GeneralRelativity/BianchiExamples.lean) |
| The Kasner solution | `Kasner.Data`, `metric`, `ricciOf_eq`, `einsteinOf_eq`, `isEinstein_iff`, `kasner`, `ricciOf_kasner_eq_zero_iff`, `isEinstein_kasner`, `volume_kasner`, `kasnerExponents`, `kasner_ranges`, `eq_kasnerExponents`, `kasnerExponents_inv`, `chartCurvature_kasner_ne_zero`, `dustKasner`, `isEinstein_dustKasner`, `tendsto_dustKasner_nhdsGT`, `tendsto_dustKasner_atTop` | [Kasner](../ProjectAinos/GeneralRelativity/Kasner.lean) |

The typed examples are in `checks/HomogeneousSpaceAPI.lean` and `checks/KasnerAPI.lean`. The exact
experiment `verify_homogeneous_cosmology` checks the frame formula against the co-ordinate Ricci
tensor for the frames of types II and V, the class-A closed forms for a general `n`, the Kasner
conditions and the dust solution. The decisions are recorded in GR24 and GR25 of the
[notes](general-relativity-notes.md) and in G07 of the
[smooth-geometry notes](smooth-geometry-notes.md).

## The Newtonian limit and gravitational waves (§§99, 107, 109)

**Static fields.** `CoordinateMetric.staticCoefficient N γ` is `−N² dt² + γ_{αβ} dx^α dx^β` with
`N` and `γ` functions of the spatial point alone. Its Christoffel symbols are
`Γ⁰_{0α} = ∂_αN/N`, `Γ^α_{00} = N γ^{αβ}∂_βN` and the spatial `Γ̃^α_{βγ}`
(`christoffelOf_staticCoefficient_*`), and `R₀₀ = N Δ_γ N` with
`Δ_γ N = γ^{αβ}(∂_α∂_βN − Γ̃^μ_{αβ}∂_μN)` (`ricciOf_staticCoefficient_zero_zero`). The
trace-reversed form `R_{ik} = κ(T_{ik} − ½ g_{ik} g^{ab}T_{ab})` follows from `IsEinstein`
(`IsEinstein.ricciOf_eq`).

**Newton's law (§99).** `NewtonianFieldLimit.StaticWeakFieldFamily` is a family with
`N_ε = 1 + εΦ_ε`, `γ_ε = δ + εq_ε`, an energy density `ερ_ε` and a spatial trace `τ_ε` with
`|τ_ε| ≤ ε²P`, uniform bounds `K` on the fields and their derivatives, and the 00 component of
the trace-reversed field equations. The field equation is then exactly
`ΔΦ_ε − 4πGρ_ε = ε R_ε` with an explicit remainder (`flatLaplacian_sub_eq`), so
`|ΔΦ_ε − 4πGρ_ε| ≤ C ε` for `ε ≤ ε₁` with explicit `ε₁` and `C`
(`abs_flatLaplacian_sub_le`), and the limit satisfies the Poisson equation `ΔΦ = 4πGρ`
(`flatLaplacian_eq_of_tendsto`). The hypothesis follows from the Einstein equations
(`fieldEquation_of_isEinstein`). The sourced family `halfSquare` satisfies it exactly. Unlike
§81, where the metric was assumed, here the metric solves the field equations.

**The linearized field equations (§107).** `CoordinateMetric.linearizedRicci σ h` is
`½ Σ_i η^{ii}(∂_i∂_j h_{ik} + ∂_i∂_k h_{ij} − ∂_i∂_i h_{jk} − ∂_j∂_k h_{ii})`, the derivative at
`ε = 0` of the Ricci tensor of `η + εh` (`hasDerivAt_ricciOf_linear`, with the Einstein tensor
in `hasDerivAt_einsteinOf_linear`). For bounded `h` and small `ε`, `η + εh` is an actual Lorentz
metric (`isAdmissible_linear`, `linearMetric`), and the linearization is the derivative of its
native Ricci and Einstein tensors (`hasDerivAt_ricci_linearMetricFamily`). It is invariant under
`h ↦ h + L_ξη` (`linearizedRicci_add_lie`), and in harmonic gauge `∂^a h̄_{ab} = 0` it is
`−½□h`, with the Einstein tensor `−½□h̄` (`linearizedRicci_of_isHarmonicGauge`,
`linearizedEinstein_of_isHarmonicGauge`).

**Weak waves.** A plane wave `e cos(k·x)` with null `k` satisfies `□h = 0`; it is in harmonic
gauge exactly when `k^a ē_{ab} = 0` (`isHarmonicGauge_planeWave_iff`), and is then a linearized
vacuum solution (`linearizedRicci_planeWave`). For every nonzero null `k`, the harmonic amplitudes
form a space of dimension 6 (`finrank_polarizationSpace`). It contains the amplitudes
`k ⊗ ζ + ζ ⊗ k` of the residual gauge transformations, which form a space of dimension 4
(`gaugeSpace_le_polarizationSpace`, `finrank_gaugeSpace`). The quotient has dimension 2
(`finrank_polarizationQuotient`): the two polarizations, with the plus and cross amplitudes as a
basis for an axial `k` (`polarizationBasis`).

**Strong waves (§109).** `ExactPlaneWave.metric` is the diagonal Rosen form
`−dt² + a(u)² dx² + b(u)² dy² + dz²`, `u = t − z`, on the slab where `a, b > 0`. Its Ricci tensor
is exactly `−(a''/a + b''/b) ℓ_iℓ_k` with the null covector `ℓ = du` (`ricciOf_eq_null`), so
the vacuum equation is `a''/a + b''/b = 0` (`ricciOf_eq_zero_iff`), and with `a = Le^β`,
`b = Le^{−β}` it is `L'' + β'²L = 0` (`ricciOf_toData_eq_zero_iff`). The wave `L = cos u`,
`β = u` on `|u| < π/2` is an exact vacuum solution (`ricciOf_strong`) with `R¹₀₁₀ = −2 tan u`,
nonzero wherever `u ≠ 0` (`chartCurvature_strong_ne_zero`); `L` vanishes at `u = ±π/2`, where the
co-ordinates focus. For `a = e^{εf}`, `b = e^{−εf}` the exact Ricci tensor is `−2ε²f'²ℓℓ`
(`ricciOf_weak`): its first-order part vanishes (`hasDerivAt_ricciOf_weak`), but it is not Ricci
flat for `ε ≠ 0` (`not_ricciFlat_weak`).

**Scope.** §99 is stated for static fields (decision 4 on #135); slowly varying fields and their
compatibility with the equations of motion are §106 (F24). In §107 gauge fixing, which needs a
solution of `□χ = f`, and the energy flux (107.11) are not stated. In §109 the transverse metric is
diagonal (one polarization), and the global structure of the focusing surface is not stated.

| Result | Declarations | Source |
| --- | --- | --- |
| Static fields | `CoordinateMetric.staticCoefficient`, `christoffelOf_staticCoefficient_zero_zero_succ`, `christoffelOf_staticCoefficient_succ_zero_zero`, `spatialLaplacian`, `ricciOf_staticCoefficient_zero_zero`, `staticMetric`, `IsEinstein.ricciOf_eq` | [Static](../ProjectAinos/SmoothGeometry/Lorentzian/Static.lean) |
| Newton's law | `NewtonianFieldLimit.StaticWeakFieldFamily`, `remainder`, `flatLaplacian_sub_eq`, `abs_flatLaplacian_sub_le`, `flatLaplacian_eq_of_tendsto`, `fieldEquation_of_isEinstein`, `trivialFamily`, `halfSquare`, `halfSquare_poisson` | [NewtonianFieldLimit](../ProjectAinos/GeneralRelativity/NewtonianFieldLimit.lean) |
| The linearized field equations | `CoordinateMetric.linearizedChristoffel`, `linearizedRicci`, `linearizedEinstein`, `hasDerivAt_ricciOf_linear`, `hasDerivAt_einsteinOf_linear`, `isAdmissible_linear`, `linearMetricFamily`, `hasDerivAt_ricci_linearMetricFamily`, `linearizedRicci_add_lie`, `IsHarmonicGauge`, `linearizedRicci_of_isHarmonicGauge`, `linearizedEinstein_of_isHarmonicGauge` | [Linearized](../ProjectAinos/SmoothGeometry/Lorentzian/Linearized.lean) |
| Weak waves | `WeakWaves.planeWave`, `isHarmonicGauge_planeWave_iff`, `linearizedRicci_planeWave`, `gaugeMap`, `polarizationSpace`, `gaugeSpace`, `finrank_polarizationSpace`, `finrank_gaugeSpace`, `finrank_polarizationQuotient`, `polarizationBasis` | [WeakWaves](../ProjectAinos/GeneralRelativity/WeakWaves.lean) |
| Strong waves | `ExactPlaneWave.metric`, `christoffelOf_eq`, `ricciOf_eq_null`, `ricciOf_eq_zero_iff`, `ricciOf_toData_eq_zero_iff`, `strong`, `ricciOf_strong`, `chartCurvature_strong_ne_zero`, `weak`, `ricciOf_weak`, `hasDerivAt_ricciOf_weak`, `not_ricciFlat_weak` | [ExactPlaneWave](../ProjectAinos/GeneralRelativity/ExactPlaneWave.lean) |

The typed examples are in `checks/NewtonianFieldLimitAPI.lean` and
`checks/LinearizedGravityAPI.lean`. The exact experiment `verify_weak_fields_and_waves` checks the
Rosen-wave Ricci tensor and its two examples, the linearized Ricci tensor against the exact
derivative for a polynomial perturbation, gauge invariance, the plane-wave vacuum and the static
`R₀₀`. The decisions are recorded in GR26–GR28 of the [notes](general-relativity-notes.md) and
in G08 of the [smooth-geometry notes](smooth-geometry-notes.md).

## Charges at infinity, gravitational radiation and focusing (§§105, 108, 110, 119)

**Charges at infinity (§105, with §96).** For co-ordinates Galilean at spatial infinity the
pseudotensor is `O(1/r⁴)` (`IsAsymptoticallyGalileanAt.abs_pseudotensor_le`), the superpotential
flux through spheres changes by the integral of the conserved total over shells
(`surfaceCharge_sub_surfaceCharge_eq`), and the charges are the limits of the surface integrals with
their volume form (`tendsto_surfaceCharge`, `charge_eq_integral`); `P⁰ = M` for the isotropic far
metric (`charge_zero_eq_mass`), and the charges are conserved when the flux vanishes
(`charge_const_of_flux`). The four-vector character is the remainder.

**Waves on a curved background (§108).** The derivative of the Ricci tensor along `g + εh` is the
Palatini form (`familyRicciDeriv_eq`), gauge invariant on Ricci-flat backgrounds
(`familyRicciDeriv_lie_eq_zero`); a short wave has the exact expansion `familyRicciDeriv_shortWave`,
whose symbol in the gauge vanishes iff the phase is null (`shortWaveSymbol_eq_zero_iff`), and the
rays are null geodesics (`isGeodesicOn_ray`).

**The radiation of gravitational waves (§110).** The retarded perturbation `h̄ = 2κRT` of a
localized conserved stress is harmonic and solves the linearized equations
(`linearizedEinstein_retardedPerturbation`); its far zone is the quadrupole amplitude
(`farZone_quadrupole`), and the flux of the quadratic pseudotensor through large spheres tends to
the radiated power (`tendsto_pseudotensorFlux`), which for slow sources is `(G/45) Σ D⃛²`
(`gravitationalPower_slow`); the circular binary radiates `(32/5)Gμ²a⁴Ω⁶` (`binary_power_smooth`).

**Focusing (§119).** For a synchronous congruence `∂ₜθ = −θ²/d − σ² − R₀₀` (`IsSynchronous.raychaudhuri`),
the strong energy condition with Einstein's equations and `Λ ≤ 0` gives `R₀₀ ≥ 0`
(`SatisfiesEinstein.ricci_timelike_nonneg`), and the synchronous system breaks down within `3/|θ|`
(`IsSynchronous.exists_notMem_of_focusing`). Geodesic incompleteness is the remainder.

| Result | Declarations | Source |
| --- | --- | --- |
| Charges at infinity | `CoordinateMetric.surfaceCharge`, `Sphere.flux_sub_flux`, `surfaceCharge_sub_surfaceCharge_eq`, `IsAsymptoticallyGalilean`, `abs_pseudotensor_le`, `tendsto_surfaceCharge`, `charge_eq_integral`, `charge_zero_eq_mass`, `charge_const_of_flux` | [PseudotensorFlux](../ProjectAinos/SmoothGeometry/Lorentzian/PseudotensorFlux.lean), [AsymptoticCharge](../ProjectAinos/GeneralRelativity/AsymptoticCharge.lean) |
| Waves on a curved background | `CoordinateMetric.curvedChristoffel`, `palatini`, `familyChristoffelDeriv_eq`, `familyRicciDeriv_eq`, `familyRicciDeriv_lie_eq_zero`, `ShortWave.familyRicciDeriv_shortWave`, `shortWaveSymbol_eq_zero_iff`, `isGeodesicOn_ray` | [CurvedLinearization](../ProjectAinos/SmoothGeometry/Lorentzian/CurvedLinearization.lean), [ShortWave](../ProjectAinos/GeneralRelativity/ShortWave.lean) |
| Gravitational radiation | `LinearizedRadiation.retardedPerturbation`, `linearizedEinstein_retardedPerturbation`, `farZone_quadrupole`, `tendsto_pseudotensorFlux`, `gravitationalPower_slow`, `binary_power_smooth`, `Wave.integral_ttSquare` | [TransverseTraceless](../ProjectAinos/SmoothGeometry/Wave/TransverseTraceless.lean), [LinearizedRadiation](../ProjectAinos/GeneralRelativity/LinearizedRadiation.lean) |
| Focusing | `Focusing.trace_sq_ge`, `IsSynchronous.raychaudhuri`, `RiccatiComparison.lt_div_abs`, `StrongEnergyCondition`, `SatisfiesEinstein.ricci_timelike_nonneg`, `IsSynchronous.exists_notMem_of_focusing`, `deSitter_not_focusing` | [RiccatiComparison](../ProjectAinos/SmoothGeometry/ODE/RiccatiComparison.lean), [Focusing](../ProjectAinos/SmoothGeometry/Lorentzian/Focusing.lean), [EnergyCondition](../ProjectAinos/GeneralRelativity/EnergyCondition.lean) |

The typed examples are in `checks/AsymptoticChargeAPI.lean`, `checks/CurvedWavesAPI.lean`,
`checks/GravitationalRadiationAPI.lean` and `checks/FocusingAPI.lean`. The decisions are recorded
in GR30–GR33 of the [notes](general-relativity-notes.md) and in G16 of the
[smooth-geometry notes](smooth-geometry-notes.md).
