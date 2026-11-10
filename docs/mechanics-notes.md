# Mechanics Formalization Notes

These notes record mathematical distinctions and modeling decisions made explicit by the Lean development, following the [thermodynamics notes](thermodynamics-notes.md). Each entry states its effect on the interface and its proof status. These are clarifications of the formal model, not claims of new physical results.

The [research plan](cinfty-mechanics.md) preserves the long-term programme. The [mechanics guide](mechanics.md) states the implemented endpoint and its hypotheses. Add future observations here with proof links; keep unresolved claims explicit.

## M01. Fixed endpoints are weaker than interior compact support

**Observation.** A fixed-endpoint variation satisfies `η(a)=η(b)=0`, but may have nonzero derivatives at both ends and may be nonzero arbitrarily close to them. For `a < b`, the scalar variation `η(t)=(t−a)(b−t)` has `η'(a)=b−a ≠ 0`.

**Interface decision.** `FixedEndpointVariation` requires smoothness and the two value equations, with no support condition. The previous common theorem for compactly supported interior variations alone would not cover this full class. The new common action-derivative theorem uses compactness of the base interval. Integration by parts retains the momentum pairing until the endpoint values cancel it.

**Proof status.** `polynomial_fixedEndpointVariation` and `polynomial_variation_left_derivative` check this example. `firstVariation_fixedEndpoints` covers the full variation class. Compactly supported interior tests are used only to infer the differential equation in the forward implication; the converse covers every fixed-endpoint variation. [Examples](../ProjectAInos/Mechanics/Examples.lean) · [First variation](../ProjectAInos/Mechanics/FirstVariation.lean) · [Euler–Lagrange](../ProjectAInos/Mechanics/EulerLagrange.lean)

## M02. The action derivative needs analytic justification

**Observation.** The identity for the pointwise derivative of `L(t,qε,qε')` does not, by itself, justify differentiating its integral. On a finite interval, joint C² regularity bounds that derivative on a compact product of parameter and time intervals. The resulting constant bound is integrable for restricted Lebesgue measure.

**Interface decision.** `hasDerivAt_action_restrict_compact` proves this analytic step in the common layer. The mechanics endpoint consequently has no assumed first-variation formula, no assumed fundamental lemma, and no independent domination or integrability premise. The theorem still explicitly assumes C² regularity of the ambient Lagrangian and path.

**Proof status.** The common domination argument and the actual `HasDerivAt` statement are proved. Reducing the hypotheses to functions defined only on a closed interval, or to weaker Sobolev regularity, remains future work. [Common regularity](../ProjectAInos/Variational/Regularity.lean) · [Mechanical action derivative](../ProjectAInos/Mechanics/FirstVariation.lean)

## M03. Momentum and the residual are covectors

**Observation.** Both `∂L/∂q` and `∂L/∂v` naturally act on configuration vectors. Writing them as vectors would introduce an inner product and a dual-space identification that the variational argument does not require. In one-dimensional time, the common derivative `Dq : ℝ →L[ℝ] Q` becomes velocity by evaluation at `1`.

**Interface decision.** `force`, `momentum`, and `eulerLagrange` take values in `Q →L[ℝ] ℝ`. `positionVelocity` is an explicit continuous linear map connecting the shared first jet to the mechanical pair. The proof works for any real normed `Q`, and thus for every finite number of generalized coordinates, without a metric on `Q`.

**Proof status.** The jet identification, fibre derivative decomposition and covector-valued endpoint formula are proved. Coordinate transformations and cotangent bundles on a nonlinear configuration manifold are not yet implemented. [Basic interfaces](../ProjectAInos/Mechanics/Basic.lean) · [Covector integration by parts](../ProjectAInos/Variational/IntegrationByParts.lean)

## M04. A nondegenerate interval is necessary to detect an equation

**Observation.** When `a = b`, the action is identically zero for all paths. Stationarity then supplies no differential information. Also, the measure-theoretic fundamental lemma initially gives an almost-everywhere equation; it becomes pointwise because the residual is continuous and Lebesgue measure is positive on nonempty open intervals.

**Interface decision.** The equation-detecting equivalence requires `a < b` and states the equation on `(a,b)`. The first-variation identity itself retains oriented interval integrals. Changing between `[a,b]`, `(a,b]`, and `(a,b)` in scalar integrals uses the fact that endpoints have zero measure; it does not silently change the admissible endpoint values of a path.

**Proof status.** `stationary_self` proves the zero-length case, while `stationary_iff_eulerLagrange` contains the fundamental-lemma and continuity steps. No theorem about natural boundary conditions or free endpoints is asserted. [Euler–Lagrange](../ProjectAInos/Mechanics/EulerLagrange.lean) · [Examples](../ProjectAInos/Mechanics/Examples.lean)

## M05. Stationarity, regularity of the Lagrangian, and minimality differ

**Observation.** Deriving Euler–Lagrange from first-order stationarity requires neither a positive velocity Hessian nor an invertible one. Invertibility is needed for later steps such as solving the equations for accelerations or constructing a Legendre equivalence. First-order stationarity alone makes no assertion of local or global minimality.

**Interface decision.** `Stationary` is defined by the actual parameter derivative, independently of the field equation. The equivalence assumes joint C² regularity but no Hessian condition. For the natural Lagrangian, Newton's equation is retained as `m q'' = −V'(q)`; this statement makes sense even at zero mass. Existence, uniqueness and minimality of trajectories are separate targets.

**Proof status.** The first-order equivalence and `stationary_natural_iff` are proved. No second-variation test, Legendre theorem or existence theorem is claimed. [Definitions](../ProjectAInos/Mechanics/Basic.lean) · [Natural Lagrangian](../ProjectAInos/Mechanics/Examples.lean)

## M06. The concrete smooth model does not settle arbitrary coefficient rings

**Observation.** A real smooth operation supplies an actual C∞ observable, and evaluation at `(t,q,v)` preserves all smooth substitutions. This connects the common algebraic API to the analytic action. It does not establish a fundamental lemma with coefficients in an arbitrary quotient C∞-ring, the unresolved issue noted in the original manuscript.

**Interface decision.** `ofSmoothOperation` uses the existing `SmoothRingHom` evaluation, derives joint C∞ regularity, and then invokes the real analytic theorem. The algebraic theory is not duplicated inside Mechanics. The analytic jet remains the pair of a field and its Fréchet derivative; it is not presented as a constructed abstract jet ring.

**Proof status.** `ofSmoothOperation_op` and `stationary_ofSmoothOperation_iff` prove the concrete bridge. Abstract quotients, dual numbers, universal smooth differentials, jet rings, and the coefficient-valued fundamental lemma remain research targets. [Smooth Lagrangians](../ProjectAInos/Mechanics/SmoothLagrangian.lean) · [Original critical-subfunctor discussion](cinfty-mechanics.md#rem:fundamental)

## M07. A boundary term shifts momentum and preserves the equations

For $F(t,q)$, the action shift is $F(b,q(b))-F(a,q(a))$. Every path with the same endpoints receives the same shift, so the action differences between such paths are preserved. Along a fixed-endpoint variation, the shift is constant even when the endpoint velocities vary. The action identity and stationarity equivalence use C¹ regularity of $F$ and the path and continuity of $L$.

The velocity derivative of the added density is $\partial_q F$, so the momentum covector shifts by that amount. Along the path, the derivative of this shift cancels the extra position derivative by symmetry of $d^2F$. This proves pointwise equality of the Euler–Lagrange residuals with C² $F$, $L$, and $q$. At that regularity, the added density is guaranteed to be C¹, which is why the proof computes the cancellation directly. The momentum shift also identifies the correction to track when a symmetry changes a Lagrangian by a total derivative in the planned Noether development. [Lean proofs](../ProjectAInos/Mechanics/TotalTimeDerivative.lean) · [Noether target](cinfty-mechanics.md#prop:noether-jet)
