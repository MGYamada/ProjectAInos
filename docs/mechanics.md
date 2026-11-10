# Fixed-Endpoint Variational Mechanics

The first Mechanics stage derives the Euler–Lagrange equation from the actual action derivative on a finite real time interval. It reuses the [shared variational calculus](variational.md) and the [shared C∞-ring](smooth-algebra.md). The [research plan](cinfty-mechanics.md) retains the longer algebraic programme; [formalization notes](mechanics-notes.md) record the distinctions exposed by this stage.

## Mathematical statement

Let `Q` be a real normed space, for example `Fin n → ℝ`, and let

$$
L:\mathbb R\times(Q\times Q)\longrightarrow\mathbb R,
\qquad q:\mathbb R\longrightarrow Q
$$

be C². The action and the variation are

$$
S_{a,b}[q]=\int_a^b L(t,q(t),\dot q(t))\,dt,
\qquad q_\varepsilon=q+\varepsilon\eta.
$$

`FixedEndpointVariation a b η` means that η is C∞ and `η a = η b = 0`. These conditions preserve the endpoints of `q` for every real ε; they do not constrain `η' a` or `η' b`. `Stationary` requires `HasDerivAt (fun ε => S[qε]) 0 0` for every such η. The field equation is not built into this definition.

The position and velocity derivatives are continuous linear functionals on `Q`:

$$
A(t)=\partial_q L(t,q(t),\dot q(t)),\qquad
p(t)=\partial_v L(t,q(t),\dot q(t)),\qquad
E_L[q](t)=A(t)-\dot p(t).
$$

For any C² variation the full first-variation formula is

$$
\left.\frac{d}{d\varepsilon}S_{a,b}[q+\varepsilon\eta]\right|_0
=\int_a^b\bigl(A(t)(\eta(t))+p(t)(\dot\eta(t))\bigr)\,dt
=p(b)(\eta(b))-p(a)(\eta(a))+\int_a^b E_L[q](t)(\eta(t))\,dt.
$$

When `a < b`, Lean proves

$$
\operatorname{Stationary}_{a,b}(L,q)
\quad\Longleftrightarrow\quad
\forall t\in(a,b),\quad \frac{d}{dt}\partial_v L(t,q(t),\dot q(t))
=\partial_q L(t,q(t),\dot q(t)).
$$

This is a covector equality, so it gives every coordinate Euler–Lagrange equation in a finite-dimensional configuration space. No inner product, Hessian invertibility, existence of a minimizing path, or separate integrability assumption is required. The current theorem uses globally defined C² functions; its equation is asserted on the open interval. Local extensions and one-sided endpoint regularity are future refinements.

## Proof and interfaces

1. `positionVelocity` maps a common first jet `(q,Dq)` to `(q,Dq(1))`. Thus `toVariational L` and the ordinary density `L(t,q,q')` agree, and the mechanical action equals the common action with Lebesgue measure restricted to `[a,b]`.
2. On the compact product `[-1,1] × [a,b]`, the variation derivative is continuous and uniformly bounded. The common `hasDerivAt_action_restrict_compact` proves differentiation under the integral. All perturbed densities are integrable by C² regularity and compactness.
3. The common `interval_firstVariation_pairing` integrates the product rule for `p(t)(η(t))`. Fixed endpoints cancel its boundary term.
4. To recover the pointwise equation, test with `η(t)=g(t)v`, where `g` is any smooth scalar test function supported inside `(a,b)` and `v ∈ Q`. The fundamental lemma gives almost-everywhere vanishing of each residual pairing. Continuity upgrades it to pointwise vanishing. Conversely, the pointwise equation makes the first variation zero for every fixed-endpoint variation.

## C∞ observables

`ofSmoothOperation` interprets `f : SmoothOperation (n+n+1)` in coordinates ordered as `(t,q₁,…,qₙ,v₁,…,vₙ)`. It uses `SmoothOperation.eval`, a `SmoothRingHom`, so `ofSmoothOperation_op` preserves arbitrary smooth substitution. Joint C∞ regularity follows from the bundled operation. `stationary_ofSmoothOperation_iff` applies the mechanical theorem without an extra regularity premise on `f`, including when `n = 0`.

This realizes real-valued observables and their variational calculus. It does not assert a fundamental lemma for paths with values in an arbitrary abstract C∞-ring or identify the analytic first jet with a quotient of an abstract jet ring.

## Total time derivatives

For a boundary function $F(t,x)$ of time and position, define the first-order density

$$
D_t F(t,x,v)=dF_{(t,x)}(1,v)=\partial_tF(t,x)+\partial_qF(t,x)(v).
$$

When $F$ and $q$ are C¹ and $L$ is continuous, the chain rule and the fundamental theorem of calculus give

$$
S_{a,b}[L+D_t F,q]=S_{a,b}[L,q]+F(b,q(b))-F(a,q(a)).
$$

The identity uses the oriented integral for any endpoints $a,b$. Along a fixed-endpoint perturbation, the endpoint difference is constant in the variation parameter, so the two stationarity predicates are equivalent under the same regularity assumptions.

For C² $F$, $L$, and $q$, the Euler–Lagrange residuals agree pointwise. The velocity differential of $D_t F$ is $\partial_q F$, and symmetry of $d^2F$ makes its position differential equal to $\frac{d}{dt}\partial_qF(t,q(t))$ along the path. The two terms cancel in the residual. [Lean proof](../ProjectAInos/Mechanics/TotalTimeDerivative.lean)

## Proof map

| Module | Main declarations |
| --- | --- |
| [Basic](../ProjectAInos/Mechanics/Basic.lean) | `Lagrangian`, `action`, `force`, `momentum`, `eulerLagrange`, `FixedEndpointVariation`, `Stationary`, `toVariational`, `action_eq_variational` |
| [FirstVariation](../ProjectAInos/Mechanics/FirstVariation.lean) | `hasDerivAt_action_firstVariation`, `firstVariation_eq_boundary_add_integral`, `firstVariation_fixedEndpoints`, `hasDerivAt_action_eulerLagrange` |
| [EulerLagrange](../ProjectAInos/Mechanics/EulerLagrange.lean) | `stationary_iff_eulerLagrange`, `stationary_iff_momentum_equation` |
| [SmoothLagrangian](../ProjectAInos/Mechanics/SmoothLagrangian.lean) | `ofSmoothOperation`, `ofSmoothOperation_op`, `stationary_ofSmoothOperation_iff` |
| [TotalTimeDerivative](../ProjectAInos/Mechanics/TotalTimeDerivative.lean) | `action_add_totalTimeDerivative`, `stationary_add_totalTimeDerivative_iff`, `eulerLagrange_totalTimeDerivative`, `eulerLagrange_add_totalTimeDerivative` |
| [Examples](../ProjectAInos/Mechanics/Examples.lean) | Newton equation, stationary uniform free motion, rejection of accelerated free motion, endpoint-vanishing polynomial variation and its endpoint derivative, zero-length interval and zero-coordinate system |

For `L = m v²/2 − V(q)`, `stationary_natural_iff` proves `m q'' = −V'(q)` on `(a,b)`. This algebraic equation remains valid at `m = 0`; dividing by the mass would require a separate nonzero premise.

## Verification

The library uses Lean / Mathlib v4.35.0 and the existing required Lean build checks:

```sh
lake build --wfail ProjectAInos
lake exe mk_all --check --lib ProjectAInos
lake env lean -DwarningAsError=true checks/AxiomAudit.lean
git diff --check
```

The audit checks transitive dependencies of every `ProjectAInos` declaration, including generated and private declarations. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed.
