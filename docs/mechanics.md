# Fixed-Endpoint Variational Mechanics

The first Mechanics stage derives the Euler–Lagrange equation from the actual action derivative on a finite real time interval. The second stage, [jet rings and conservation laws](#jet-rings-and-conservation-laws), is algebraic and uses no path. It reuses the [shared variational calculus](variational.md) and the [shared C∞-ring](smooth-algebra.md). The [research plan](cinfty-mechanics.md) retains the longer algebraic programme; [formalization notes](mechanics-notes.md) record the distinctions exposed by this stage.

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

## Jet rings and conservation laws

A `JetRing ι J` is a C∞-ring `J` with commuting vector fields `dt` and `d i k`, elements `q i k` dual to them, and finite order for every element. The index type `ι` is any finite type, so particles in space use `κ × Fin 3`. The total derivative

$$
DF=\partial_tF+\sum_{k\ge0}\sum_i q_i^{(k+1)}\,\partial_i^{(k)}F
$$

is a finite sum and a vector field (`JetRing.totalDeriv`). Lean proves `D q i k = q i (k+1)`, that `D` raises the order by at most one, and the commutators `[∂ₜ, D] = 0`, `[∂ᵢ⁽⁰⁾, D] = 0`, `[∂ᵢ⁽ᵏ⁺¹⁾, D] = ∂ᵢ⁽ᵏ⁾`.

The Euler operator `JetRing.euler i` is `Σₖ (−D)ᵏ ∂ᵢ⁽ᵏ⁾`. `euler_totalDeriv` proves `Eᵢ(DF) = 0` for every `F` of any order, by a telescoping sum. The Euler–Lagrange ideal of `L` is generated by all `Dᵏ Eᵢ(L)`; it is stable under `D`, and `Conserved L F` means that `DF` lies in it.

For a Lagrangian of order at most one, with momenta `pᵢ = ∂L/∂vᵢ` and energy `Σ vᵢ pᵢ − L`:

- `totalDeriv_energy`: `D(E_L) = −Σᵢ vᵢ Eᵢ(L) − ∂ₜL`;
- `prolong_eq_euler_add_totalDeriv`: `pr ξ(L) = Σᵢ ξᵢ Eᵢ(L) + D(Σᵢ ξᵢ pᵢ)`, for every variation `ξ`;
- `conserved_noetherCharge`: if `pr ξ(L) = DF`, then `Σᵢ ξᵢ pᵢ − F` is conserved.

For the natural Lagrangian `Σᵢ ½ mᵢ vᵢ² − U` with a potential of order zero, `euler_naturalLagrangian` gives Newton's equations `Eᵢ(L) = −∂ᵢU − mᵢ aᵢ`. The conservation laws of Landau–Lifshitz §§6–9 follow: energy for `∂ₜU = 0`, momentum and the centre-of-mass integral for a potential invariant along a direction, the charge of a linear symmetry with `mᵢ Aᵢⱼ + mⱼ Aⱼᵢ = 0`, and angular momentum about an axis for a rotation-invariant potential. The boost law needs a time coordinate `τ` with `∂ₜτ = 1`, which is an explicit hypothesis.

`StandardJet ι` is the free C∞-ring on the time coordinate and the jet coordinates. `StandardJet.jetRing` makes it a jet ring, so the structure is not vacuous. Its vector fields come from the universal property of the free ring and the dual numbers, without analysis. The examples have nonzero values: `Eᵢ(q q̈) = 2 q̈`, `Eᵢ(q̇²) = −2 q̈`, Newton's equation of the isotropic oscillator, and the centre-of-mass integral of free particles.

These statements are identities in a ring. They do not yet say that a quantity is constant along a solution of the Euler–Lagrange equations in the real analytic model above; that needs the prolongation of a path and is a later stage of [issue #78](https://github.com/MGYamada/ProjectAInos/issues/78).

## Poisson models

Hamiltonian mechanics uses the Poisson structures of the
[C∞-ring guide](smooth-algebra.md#poisson-structures). A system is a Poisson
structure together with one element `H`, and the equation of motion of an
observable `f` is `{f, H}`. The canonical phase space `PhaseSpace ι`, with
Hamilton's equations, is in the shared algebra layer.

`RigidBody.PhaseSpace` is the free C∞-ring on the components `L 0`, `L 1`, `L 2`
of the angular momentum in the body frame. `RigidBody.poisson` has
`{Lᵢ, Lⱼ} = −εᵢⱼₖ Lₖ`; the Jacobi identity is checked on generators. In vector
form `{f, g} = −L · (∇f × ∇g)` (`poisson_bracket`), and for every Hamiltonian
`{Lₐ, H} = (L × ∇H)ₐ` (`poisson_L_bracket`). For the kinetic energy
`H = Σᵢ Lᵢ² / 2Iᵢ` the gradient is the angular velocity `Ωᵢ = Lᵢ / Iᵢ`, and
`euler_equations` gives Euler's equations `{Lₐ, H} = (L × Ω)ₐ`, with the
components

$$
\{L_0,H\}=\Bigl(\frac1{I_2}-\frac1{I_1}\Bigr)L_1L_2\quad\text{and cyclic permutations.}
$$

`|L|²` is a Casimir (`poisson_casimir_left`): its bracket with every element
vanishes, so it is an integral of every Hamiltonian. `L_ne_zero` evaluates at a
point to show that the generators, and hence the bracket, are not zero. The
identities use the real inverse `(I i)⁻¹` and hold for every `I`; a physical
body has `I i > 0`. The quotient by `|L|² − r²`, the ring of functions on the
sphere, is not constructed.

## Proof map

| Module | Main declarations |
| --- | --- |
| [Basic](../ProjectAInos/Mechanics/Basic.lean) | `Lagrangian`, `action`, `force`, `momentum`, `eulerLagrange`, `FixedEndpointVariation`, `Stationary`, `toVariational`, `action_eq_variational` |
| [FirstVariation](../ProjectAInos/Mechanics/FirstVariation.lean) | `hasDerivAt_action_firstVariation`, `firstVariation_eq_boundary_add_integral`, `firstVariation_fixedEndpoints`, `hasDerivAt_action_eulerLagrange` |
| [EulerLagrange](../ProjectAInos/Mechanics/EulerLagrange.lean) | `stationary_iff_eulerLagrange`, `stationary_iff_momentum_equation` |
| [SmoothLagrangian](../ProjectAInos/Mechanics/SmoothLagrangian.lean) | `ofSmoothOperation`, `ofSmoothOperation_op`, `stationary_ofSmoothOperation_iff` |
| [TotalTimeDerivative](../ProjectAInos/Mechanics/TotalTimeDerivative.lean) | `action_add_totalTimeDerivative`, `stationary_add_totalTimeDerivative_iff`, `eulerLagrange_totalTimeDerivative`, `eulerLagrange_add_totalTimeDerivative` |
| [Jet/Basic](../ProjectAInos/Mechanics/Jet/Basic.lean) | `JetRing`, `OrderLE`, `totalDeriv`, `totalDeriv_q`, `dt_totalDeriv`, `d_zero_totalDeriv`, `d_succ_totalDeriv` |
| [Jet/Euler](../ProjectAInos/Mechanics/Jet/Euler.lean) | `euler`, `euler_totalDeriv`, `euler_add_totalDeriv`, `eulerLagrangeIdeal`, `Conserved`, `totalDeriv_mem_eulerLagrangeIdeal` |
| [Jet/Noether](../ProjectAInos/Mechanics/Jet/Noether.lean) | `momentum`, `energy`, `prolong`, `totalDeriv_energy`, `prolong_eq_euler_add_totalDeriv`, `conserved_noetherCharge`, `conserved_energy` |
| [Jet/Conservation](../ProjectAInos/Mechanics/Jet/Conservation.lean) | `naturalLagrangian`, `euler_naturalLagrangian`, `conserved_momentum`, `conserved_boost`, `conserved_linear`, `conserved_angularMomentum` |
| [Jet/Standard](../ProjectAInos/Mechanics/Jet/Standard.lean) | `StandardJet`, `jetRing`, `totalDeriv_eq_derivation`, `euler_q_mul_acceleration`, `euler_oscillator`, `conserved_energy_oscillator`, `conserved_boost_free` |
| [Poisson/RigidBody](../ProjectAInos/Mechanics/Poisson/RigidBody.lean) | `PhaseSpace`, `L`, `poisson`, `poisson_L_L`, `L_ne_zero`, `poisson_bracket`, `poisson_L_bracket`, `kineticEnergy`, `gradient_kineticEnergy`, `euler_equations`, `euler_equation_zero`, `casimir`, `poisson_casimir_left`, `isIntegral_casimir` |
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
