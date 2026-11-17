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

`Jet/Metric` treats the general natural Lagrangian of Landau–Lifshitz §5,
`metricLagrangian a U = ½ Σᵢₖ aᵢₖ vᵢ vₖ − U`, where the kinetic coefficients
`aᵢₖ` and the potential have order zero. For a symmetric `a`:

- `momentum_metricLagrangian`: `pᵢ = Σₖ aᵢₖ vₖ`;
- `euler_metricLagrangian_eq`: Lagrange's equations
  `Eᵢ(L) = −Σₖ aᵢₖ q̈ₖ − Σⱼₖ (∂ⱼaᵢₖ − ½ ∂ᵢaⱼₖ) vⱼ vₖ − Σₖ ∂ₜaᵢₖ vₖ − ∂ᵢU`;
- `energy_metricLagrangian`: the energy is `½ Σᵢₖ aᵢₖ vᵢ vₖ + U`, conserved when
  `a` and `U` do not depend explicitly on time
  (`conserved_energy_metricLagrangian`);
- `energy_metricLagrangian_eq_inverse`: if `b` is inverse to `a`, the energy is
  `½ Σᵢⱼ bᵢⱼ pᵢ pⱼ + U`.

`metricLagrangian_diagonal` recovers the constant-mass Lagrangian, and
`conserved_momentum_of_cyclic` proves, for any first-order Lagrangian, that the
momentum conjugate to a co-ordinate on which the Lagrangian does not depend is
conserved. `Jet/Polar` is a model with a kinetic form that depends on the
position: plane polar co-ordinates, `a = diag(1, r²)`. Its equations are
`E_r = −r̈ + r φ̇² − ∂U/∂r`, with the centrifugal term, and
`E_φ = −(r² φ̈ + 2 r ṙ φ̇) − ∂U/∂φ`; the angular momentum `r² φ̇` is conserved
when `U` does not depend on `φ`.

`StandardJet ι` is the free C∞-ring on the time coordinate and the jet coordinates. `StandardJet.jetRing` makes it a jet ring, so the structure is not vacuous. Its vector fields come from the universal property of the free ring and the dual numbers, without analysis. The examples have nonzero values: `Eᵢ(q q̈) = 2 q̈`, `Eᵢ(q̇²) = −2 q̈`, Newton's equation of the isotropic oscillator, and the centre-of-mass integral of free particles.

These statements are identities in a ring. The prolongation of a path turns them into statements about trajectories. `TimeFunction` is the C∞-ring of smooth functions of time and `timeDerivative` is `d/dt`; `TimeFunction.timeDerivative_apply` proves that it is Mathlib's `deriv` of the function of a real variable. Both live in their own module and are shared with the Hamiltonian trajectories below. For a smooth path `γ : ι → TimeFunction`, `StandardJet.prolongation γ` is the morphism from the standard jet ring that sends the time coordinate to `t` and `qᵢ⁽ᵏ⁾` to the `k`-th derivative of `γᵢ`. `prolongation_totalDeriv` proves that it turns the total derivative into `d/dt`. `IsSolution L γ` means that the prolongation annihilates every `Eᵢ(L)`; it then annihilates the Euler–Lagrange ideal, and `prolongation_eq_of_conserved` proves that a conserved element takes the same value at all times along a solution.

For a natural Lagrangian, `isSolution_naturalLagrangian_iff` identifies the solutions with the smooth solutions of Newton's equations `mᵢ γ̈ᵢ = −∂ᵢU` along the path, and `energy_eq_of_isSolution` proves that `Σᵢ ½ mᵢ γ̇ᵢ² + U(γ)` is constant in time when `∂ₜU = 0`. The isotropic oscillator has `mᵢ γ̈ᵢ = −k γᵢ`, and uniform motion is a solution of the free equations, so solutions exist. Paths are smooth and defined for all times.

`Jet/Analytic` identifies this notion of solution with the variational one at the top of this guide. A smooth function `f` of time, position and velocity gives the jet-ring element `firstOrder f` and the analytic Lagrangian `ofSmoothOperation f`. For a smooth path `γ` with real path `realPath γ`:

- `prolongation_firstOrder_apply`: the prolongation of `firstOrder f` at time `t` is the Lagrangian on the path;
- `prolongation_euler_firstOrder_apply`: the prolongation of `Eᵢ(firstOrder f)` at time `t` is the Euler–Lagrange residual of the path in the direction of the `i`-th coordinate;
- `isSolution_firstOrder_iff_stationary`: `γ` is a solution exactly when the action is stationary under fixed-endpoint variations on every interval `[a, b]` with `a < b`.

Hence `prolongation_eq_of_stationary`: a conserved element of the jet ring takes the same value at all times along a smooth stationary path. `energy_eq_of_stationary` is the case of the energy `Σᵢ q̇ᵢ ∂L/∂q̇ᵢ − L` for a Lagrangian with `∂f/∂t = 0`, stated with real derivatives and no jet ring in the conclusion. The statement quantifies over all intervals because a solution in the jet ring is a condition at all times; paths that are only `C²` or defined on one interval are not covered.

## The Lagrangian of a free particle

`Jet/FreeParticle` proves Theorem 66 of the manuscript (Landau–Lifshitz §4)
in the standard jet ring. `DependsOnVelocities L` says that `∂L/∂t = 0` and
`∂L/∂qᵢ⁽ᵏ⁾ = 0` for `k ≠ 1`. The infinitesimal boost with the velocity `u` is
`boost u L`, the prolongation of the variation `δqᵢ = t uᵢ`; on a function of
the velocities it is `Σ uᵢ ∂L/∂vᵢ` (`boost_eq`). `IsBoostQuasiInvariant L`
says that for every `u` the boost of `L` is the total derivative of a function
of the time and the positions.

- `isBoostQuasiInvariant_iff`: a function of the velocities is quasi-invariant
  under boosts exactly when it is `velocityPolynomial m b c`
  `= ½ Σ mᵢⱼ vᵢ vⱼ + Σ bᵢ vᵢ + c` for a symmetric matrix `m`.
- `velocityPolynomial_eq_add_totalDeriv`: the terms of degree at most one are
  `D(Σ bᵢ qᵢ + c t)`.
- `IsIsotropic L` says `L(A v) = L(v)` for every matrix `A` with `Aᵀ A = 1`,
  where `velocityValue L w` is the value of `L` at the velocities `w`.
  `eq_smul_one_of_isIsotropic`: an isotropic polynomial has `m = μ · 1` and
  `b = 0`. `exists_eq_of_isIsotropic`: a function of the velocities that is
  quasi-invariant under boosts and isotropic is
  `naturalLagrangian (fun _ => μ) 0 + c`, that is, `½ μ |v|² + c`.
- `freeLagrangian_boost`: `½ μ |v + u|² − ½ μ |v|² = D(μ u · q + ½ μ |u|² t)`
  (Landau–Lifshitz (4.2)).

The proof of the first statement applies `∂/∂vⱼ` to `Σ uᵢ ∂L/∂vᵢ = D F_u`.
The left side then depends only on the velocities and the right side only on
the time and the positions, so all the partial derivatives of both vanish.
`Constants` proves that such an element of a free C∞-ring is a constant
(`eq_algebraMap_of_partialDerivation_eq_zero`): along the segment between two
points it is a function of time with zero derivative. This is the only
analytic step. A function with constant second derivatives is then a
polynomial of degree at most two by the same lemma applied twice.

Isotropy uses three orthogonal matrices: `−1` removes the linear term, the
change of sign of one co-ordinate removes the off-diagonal entries, and the
exchange of two co-ordinates makes the diagonal entries equal. The action of
the orthogonal group on the jet ring is not defined; the hypothesis is on the
values of `L`.

## The Galilei algebra on the jet ring

`Jet/Galilei` treats Galileo's relativity principle (Landau–Lifshitz §3) at
the level of vector fields on the standard jet ring.

- `JetRing.prolongField ξ` is the prolongation `pr ξ = Σₖ Σᵢ (Dᵏ ξᵢ) ∂ᵢ⁽ᵏ⁾` of
  a variation as a vector field, in every jet ring; its values are the
  `prolong ξ F` of Noether's theorem (`JetRing.prolong_op` is its chain rule).
  On the standard jet ring `evolutionary ξ` is the vector field with `t ↦ 0`
  and `qᵢ⁽ᵏ⁾ ↦ Dᵏ ξᵢ`; it commutes with the total derivative
  (`evolutionary_totalDeriv`) and equals the prolongation
  (`evolutionary_eq_prolongField`, `evolutionary_apply`).
- `galileiField A a u` is the field of `δqₗ = Σₘ Aₗₘ qₘ + aₗ + t uₗ`: a linear
  map, a translation and a boost. `galileiField_q`:
  `X qₗ⁽ⁿ⁾ = Σₘ Aₗₘ qₘ⁽ⁿ⁾ + Dⁿ(aₗ + t uₗ)`, where `affineShift a u n` is
  `a + t u`, `u`, `0` for `n = 0`, `1`, `≥ 2`. `boost_eq_galileiField`: the
  boost of the previous section is `galileiField 0 0 u`.
- `commutator_galileiField`:
  `[X_{A,a,u}, X_{A',a',u'}] = X_{A'A − AA', A'a − Aa', A'u − Au'}`.
  `commutator_dt_galileiField`: `[∂/∂t, X_{A,a,u}] = X_{0,u,0}`, so the
  commutator of the time translation with a boost is a translation. With `A`
  antisymmetric these are the relations of the Galilei algebra; boosts and
  translations commute on the jet ring, and the mass appears as a central
  term only for the Poisson bracket (`Galilei.canonical_K_p`).
- `d_galileiField`: `[∂ₗ⁽ᵏ⁾, X_{A,a,u}] = Σᵢ Aᵢₗ ∂ᵢ⁽ᵏ⁾`. `JetRing.euler_apply`
  turns such a relation, for a vector field commuting with `D`, into
  `Eₗ(X F) = X(Eₗ F) + Σᵢ cₗᵢ Eᵢ(F)`; `euler_galileiField` is the case of the
  Galilei fields.
- `galileiField_mem_eulerLagrangeIdeal`: if `X L = D F`, then `X` maps the
  Euler–Lagrange ideal of `L` into itself. `JetRing.dt_mem_eulerLagrangeIdeal`
  is the same statement for `∂/∂t`.
- `galileiField_naturalLagrangian`: for `L = Σ ½ mᵢ vᵢ² − U` with
  `mᵢ Aᵢⱼ + mⱼ Aⱼᵢ = 0` and `X U = 0`, `X L = D(Σ mᵢ uᵢ qᵢ)`.
- `IsInertial L` says that the Euler–Lagrange ideal of `L` is invariant under
  `∂/∂t` and under `galileiField A a u` for every antisymmetric `A`.
  `isInertial_naturalLagrangian`: the free system `Σ ½ μ vᵢ²` is inertial.

The finite transformations of the Galilei group are not defined, and no
statement asserts that an inertial frame exists: that is the physical premise.

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

`Poisson/RigidBodyMotion` treats trajectories of Euler's equations
(`isTrajectory_kineticEnergy_iff`). A rotation about a principal axis,
`L = ℓ eₐ`, is an equilibrium (`isTrajectory_principalRotation`). For a
symmetric top, `I₀ = I₁`, the curve
`(a cos νt, a sin νt, ℓ)` with `ν = (1/I₀ − 1/I₂) ℓ` is a trajectory
(`isTrajectory_symmetricTop`). The element `stabilityForm I a = 2 Iₐ E − |L|²`
is an integral, and along every trajectory `Σᵢ (Iₐ/Iᵢ − 1) Lᵢ(t)²` keeps its
value (`sum_mul_sq_eq`). When `Iₐ` is the greatest moment every term is
non-negative, so each `(Iₐ/Iⱼ − 1) Lⱼ(t)²` is at most the initial value of the
sum (`mul_sq_le_of_greatest`); `mul_sq_le_of_least` is the statement for the
least moment. These are bounds for the non-linear motion. For the middle axis
only the linearized statement is proved: at `L = (0, ℓ, 0)` the linearized
equations couple the components `0` and `2` with the coefficients
`(1/I₂ − 1/I₁) ℓ` and `(1/I₁ − 1/I₀) ℓ` (`linearization_zero_two`,
`linearization_two_zero`), whose product is positive for the middle moment
(`linearization_mul_pos_of_middle`) and negative for an extreme one.

`Poisson/AsymmetricTop` solves Euler's equations by Jacobi's elliptic functions
(Landau–Lifshitz §37). `eulerField I` is the vector field of the bracket on
the space of `L`: `L̇₀ = a₀ L₁ L₂`, `L̇₁ = a₁ L₂ L₀`, `L̇₂ = a₂ L₀ L₁` with
`a₀ = 1/I₂ − 1/I₁`, `a₁ = 1/I₀ − 1/I₂`, `a₂ = 1/I₁ − 1/I₀`. For `a₀ < 0 < a₁`
and `a₂ ≤ 0`, that is `I₀ ≤ I₁ < I₂`, and for `a₂ A² > a₀ C²`, that is
`M² > 2E I₁`, `ellipticMotion I A C` is the curve
`(A cn, (a₁ A/q) sn, C dn)(C q t)` with `q = √(−a₀ a₁)` and the modulus
`k² = a₂ A²/(a₀ C²)`.

- `hasDerivAt_ellipticMotion`, `flow_eulerField_ellipticMotion`: it is the
  solution through `(A, 0, C)`, for all times.
- `ellipticMotion_add_period`: it has the period `2 · 2K/(C q)`.
- `eq_ellipticMotion_of_hasDerivAt`: every solution with `a₂ L₀² > a₀ L₂²` is
  such a motion up to a shift of the time; `exists_ellipticMotion_eq` states
  that every point of the regime is on one.
- `hasDerivAt_ellipticMotion'`, `eq_ellipticMotion'_of_hasDerivAt`: the
  regime `M² < 2E I₁`, with the axes `0` and `2` exchanged.
- `isTrajectory_ellipticTrajectory`: the motion is a trajectory of the
  Lie–Poisson bracket.

For `a₂ = 0`, the symmetric top, the modulus is zero and the functions are
circular. The separatrix `M² = 2E I₁` and the Eulerian angles of the motion
are not treated.

`|L|²` is a Casimir (`poisson_casimir_left`): its bracket with every element
vanishes, so it is an integral of every Hamiltonian. `L_ne_zero` evaluates at a
point to show that the generators, and hence the bracket, are not zero. The
identities use the real inverse `(I i)⁻¹` and hold for every `I`; a physical
body has `I i > 0`. The quotient by `|L|² − r²`, the ring of functions on the
sphere, is not constructed.

`AngularMomentum` works on the canonical phase space of one particle in space.
With `M = q × p` it proves `{Mₐ, q_b} = εₐ_bc q_c`, `{Mₐ, p_b} = εₐ_bc p_c` and
`{Mₐ, M_b} = εₐ_bc M_c`. The scalars `|q|²`, `|p|²` and `q · p` Poisson-commute
with `M`, so `isIntegral_M` gives conservation of angular momentum for every
Hamiltonian `Φ_f(|q|², |p|², q · p)` with `f` a smooth function of three
variables. `momentumMap` is the morphism from the rigid-body ring with
`L ↦ −M`, and `isPoissonHom_momentumMap` proves that it is a Poisson morphism.
The sign relates the body-frame convention `{Lᵢ, Lⱼ} = −εᵢⱼₖ Lₖ` to the
space-frame relations of `q × p`.

`HeavyTop.PhaseSpace` is the free C∞-ring on the angular momentum `L` and the
vertical unit vector `Γ` in the body frame, with `{Lᵢ, Lⱼ} = −εᵢⱼₖ Lₖ`,
`{Lᵢ, Γⱼ} = −εᵢⱼₖ Γₖ` and `{Γᵢ, Γⱼ} = 0`. For every Hamiltonian
`{L, H} = L × ∇_L H + Γ × ∇_Γ H` and `{Γ, H} = Γ × ∇_L H`. For
`H = Σᵢ Lᵢ² / 2Iᵢ + k Γ · χ` these are `L × Ω + k Γ × χ` and `Γ × Ω`. `|Γ|²` and
`L · Γ` are Casimirs.

`Galilei` adds the boost generator `K = m q − t p` and the free Hamiltonian
`H₀ = |p|² / 2m` of one particle. It proves `{Kₐ, p_b} = m δₐ_b`,
`{Kₐ, K_b} = 0`, `{Mₐ, K_b} = εₐ_bc K_c`, `{Mₐ, H₀} = 0`, `{pₐ, H₀} = 0` and,
for `m ≠ 0`, `{Kₐ, H₀} = pₐ`. The time `t` is a real parameter, and
`K_sub_K` records `K_t − K_s = −(t − s) p`; together with `{K, H₀} = p` this
is conservation of the centre-of-mass integral. A single statement
`∂ₜK + {K, H₀} = 0` needs time-dependent Hamiltonian systems, which are not
formalized.

`PhaseSpace.dilation` is `Σᵢ qᵢ pᵢ`. For every Hamiltonian
`{Σ qᵢ pᵢ, H} = Σᵢ pᵢ ∂H/∂pᵢ − Σᵢ qᵢ ∂H/∂qᵢ` (`canonical_dilation_bracket`).
`virial` gives `{Σ qᵢ pᵢ, T + U} = 2T − kU` for the kinetic energy
`T = Σᵢ pᵢ² / 2mᵢ` and a potential `U` of the positions with
`Σᵢ qᵢ ∂U/∂qᵢ = k U`. `virial_oscillator` is the case `k = 2`.

`RotatingFrame` treats one particle in a frame rotating with constant angular
velocity `Ω`. The Hamiltonian is `hamiltonian m U Ω = |p|² / 2m + U − Ω · M`,
for a potential `U` that does not depend on the momenta. Its equations of
motion are `{q, H} = p / m − Ω × q` and `{p, H} = −∇U − Ω × p`. With the
velocity `v = p / m − Ω × q`, `canonical_velocity_hamiltonian` proves

$$
\{v,H\}=-\frac1m\nabla U-2\,\Omega\times v-\Omega\times(\Omega\times q),
$$

the Coriolis and centrifugal accelerations with the signs of Landau–Lifshitz
§39. The identity needs no hypothesis on the mass. For `m ≠ 0`,
`hamiltonian_eq_velocity` rewrites the energy as
`m |v|² / 2 − m |Ω × q|² / 2 + U`, with the centrifugal potential.

`Kepler` treats Landau–Lifshitz §15. The Hamiltonian `|p|² / 2m − α / r`
contains `1 / r`, which is not an element of the free ring on `q` and `p`. A
*Kepler frame* in a Poisson C∞-ring is a triple `q`, `p`, `ρ` with the canonical
brackets and the brackets of a formal inverse radius, `{ρ, qⱼ} = 0` and
`{ρ, pⱼ} = −ρ³ qⱼ` (`Kepler.IsFrame`). The relation `ρ² |q|² = 1` is not
assumed. It is the element `constraint = ρ² |q|² − 1`, and each statement says
how it enters. With `H = |p|² / 2m − α ρ`, `M = q × p`,
`A = p × M − m α ρ q` and `r = ρ |q|²`:

| Identity | Lean | Dependence on the constraint |
| --- | --- | --- |
| `{Aₐ, H} = α ρ pₐ · constraint` | `IsFrame.rungeLenz_hamiltonian` | multiple, `m ≠ 0` |
| `{Mₐ, A_b} = εₐ_bc A_c` | `IsFrame.angularMomentum_rungeLenz` | exact |
| `{Aₐ, A_b} = −(2 m H + m α ρ · constraint) εₐ_bc M_c` | `IsFrame.rungeLenz_rungeLenz` | multiple, `m ≠ 0` |
| `A · M = 0` | `rungeLenz_dotProduct_angularMomentum` | exact |
| `A · A = m² α² + 2 m H (M · M) + m² α² · constraint` | `rungeLenz_dotProduct_self` | multiple, `m ≠ 0` |
| `A · q = M · M − m α r` | `rungeLenz_dotProduct_q` | exact |

Also `{Mₐ, H} = 0` exactly, and `ρ r = 1`, `r² = |q|²` up to the constraint.
At real points where the constraint vanishes, both `ρ = ±1/|q|` are allowed.
Thus `Kepler.distance` is a signed radius: the ordinary distance is `|r|`,
and `r = |q|` requires the positive branch `ρ > 0`.

`KeplerModel` shows that Kepler frames exist: the free C∞-ring on `q`, `p` and
`ρ` with these generator brackets is a Poisson structure (`KeplerModel.poisson`;
the only nontrivial case of the Jacobi identity is `ρ, pⱼ, pₖ`), and the ideal
generated by the constraint is a Poisson ideal
(`isPoissonIdeal_constraintIdeal`), so identities modulo the constraint are
compatible with the bracket.

`KeplerMotion` turns this into statements about solutions. A *Kepler motion* is
a triple of smooth functions of time with `R² |Q|² = 1`, `Q̇ = P / m` and
`Ṗ = −α R³ Q`: Newton's equations for the inverse-square force with `R` the
inverse signed radius. Both signs of `R` are allowed; for fixed `α`, switching
the sign reverses the force. `IsKeplerMotion.timeDerivative_R` derives the evolution of `R`
from the constraint, `isTrajectory` shows that the motion is a trajectory of the
Kepler Hamiltonian, and `rungeLenz_eq`, `angularMomentum_eq` and
`hamiltonian_eq` prove that the Runge–Lenz vector, the angular momentum and the
energy, computed from `Q`, `P` and `R`, take the same value at all times. The
orbit identity then holds at every time with `r = R |Q|²` the signed radius:
`R r = 1` and `r² = |Q|²` (`R_mul_distance`, `distance_mul_distance`).
Pointwise, `r = |Q|` when `R > 0`, whereas `r = -|Q|` when `R < 0`.
`isKeplerMotion_circular` is the
uniform circular motion of unit radius, so Kepler motions exist. Kepler's third
law and the description of the orbit as a conic in polar co-ordinates are not
formalized.

`Poisson/Trajectory` connects these models to curves. For a Poisson structure
on a free C∞-ring and a family `c` of smooth functions of time indexed by the
generators, `FreeSmoothRing.lift c` evaluates an observable along the curve.
`IsTrajectory π H c` says that each generator satisfies
`d/dt x(c) = {x, H}(c)`. `IsTrajectory.timeDerivative_lift` extends this to
every observable, `d/dt f(c) = {f, H}(c)`, and
`IsTrajectory.lift_eq_of_isIntegral` proves that an integral of the motion
takes the same value at all times. `isTrajectory_canonical_iff` identifies the
trajectories of the canonical bracket with the solutions of Hamilton's
equations along the curve. The corollaries are constancy of the Hamiltonian,
of `|L|²` for the rigid body, of the angular momentum in a central field, and
of `|Γ|²` and `L · Γ` for the heavy top. Existence of trajectories is not
proved.

## Two bodies and collisions

`Mechanics/TwoBody` covers Landau–Lifshitz §§13, 16 and 17 as algebra of real
vectors in `Fin 3 → ℝ`.

`reducedMass m₁ m₂` is `m₁ m₂ / (m₁ + m₂)` and `centreOfMassVelocity` is
`(m₁ v₁ + m₂ v₂) / (m₁ + m₂)`. `kineticEnergy_eq` splits the kinetic energy into
the centre of mass and the relative motion, and `total_mass_mul_kinetic` is the
division-free identity
`(m₁ + m₂)(m₁ v₁² + m₂ v₂²) = (m₁ v₁ + m₂ v₂)² + m₁ m₂ (v₁ − v₂)²`, valid for all
masses. In the centre-of-mass frame the momenta are `± μ (v₁ − v₂)`.

*Disintegration.* With opposite momenta `p₁ + p₂ = 0` and the energy balance
`E = E₁ + E₂ + p₁²/2m₁ + p₂²/2m₂`, `disintegration_momentum_sq` gives
`p² = 2 μ ε` for the disintegration energy `ε = E − E₁ − E₂`, the fragments
carry the fractions `m₂/M` and `m₁/M` of `ε`, and `ε ≥ 0` for positive masses.

*Elastic collisions.* `IsElastic` says that momentum and kinetic energy are
conserved. Then the centre of mass keeps its velocity and the relative velocity
keeps its length (`IsElastic.relative_speed`). `isElastic_iff` is the
characterization: the velocities after the collision are
`outgoingOne = V + (m₂/M) w` and `outgoingTwo = V − (m₁/M) w` for some vector `w`
with the length of the initial relative velocity, and every such `w` occurs. For
a target at rest, with unit vectors `n` and `n₀` for the incident direction and
the direction of `w`:

- `outgoingOne_rest_dotProduct_self`: `v₁'² = v² (m₁² + m₂² + 2 m₁ m₂ n·n₀) / M²`;
- `outgoingTwo_rest_dotProduct_self`: `v₂'² = 2 m₁² v² (1 − n·n₀) / M²`;
- `outgoingOne_headOn`, `outgoingTwo_headOn`: the head-on velocities
  `(m₁ − m₂) v / M` and `2 m₁ v / M`;
- `energy_transfer_le`: the transferred energy is at most `4 m₁ m₂ / M²` times
  the incident energy;
- `outgoing_rest_dotProduct_eq_zero`: equal masses separate at a right angle.

`Poisson/TwoBody` works on the canonical phase space of two particles. The
centre of mass `R`, the relative position `r`, the total momentum `P` and the
relative momentum `p = (m₂ p₁ − m₁ p₂) / M` satisfy `{Rᵢ, Pⱼ} = {rᵢ, pⱼ} = δᵢⱼ`
with the mixed brackets zero, and `kineticEnergy_eq_centre` rewrites the kinetic
energy as `P²/2M + p²/2μ`.

`Poisson/ReducedMass` proves the reduction of Landau–Lifshitz §13
(Example 62(a) of the plan). `centreCoordinates m₁ m₂` is the morphism from the
phase space with the co-ordinates `(r, R; p, P)` that writes them as functions
of the particles, and `particleCoordinates m₁ m₂` is its inverse.

- `isPoissonHom_centreCoordinates`, `centreCoordinates_particleCoordinates`,
  `particleCoordinates_centreCoordinates`: the change of variables is an
  isomorphism of Poisson C∞-rings.
- `particleCoordinates_hamiltonian`: for an interaction that depends on the
  relative position the Hamiltonian is `|P|²/2M + |p|²/2μ + U(r)`, so the
  centre of mass is a cyclic co-ordinate.
- `reducedMassHom_bijective`, `isPoissonHom_reducedMassHom`: the reduced ring
  `N(I)/I` of the ideal `I = (P₁, P₂, P₃)` of total momentum zero is the phase
  space of one particle.
- `reducedMassHom_relativeHamiltonian`: the class of the Hamiltonian is
  `|p|²/2μ + U(q)` with the reduced mass `μ`.
- `isIntegral_totalMomentum`, `isTrajectory_relative`: the total momentum is an
  integral, and along a trajectory with total momentum zero the relative
  position and the relative momentum form a trajectory of `|p|²/2μ + U(q)`.

The proofs apply [the reduction with respect to cyclic
co-ordinates](#reduction-and-the-routhian) in these co-ordinates. The
interaction `U` is an element of the free ring, a smooth function on all of
`ℝ³`.

## Rigid-body kinematics

`Mechanics/Rigid` covers Landau–Lifshitz §§31–32 and the first formula of §33.
It is linear algebra over the reals with Mathlib's cross product `⨯₃` and
matrices; no C∞-ring is involved.

`hat Ω` is the skew-symmetric matrix with `hat Ω *ᵥ r = Ω × r`, and `vee` is
its inverse on skew-symmetric matrices. `hatEquiv` is the linear equivalence
between `ℝ³` and Mathlib's `so (Fin 3) ℝ`, and `hatEquiv_cross` proves that it
sends the cross product to the commutator: `so(3) ≅ ℝ³` as Lie algebras.

The velocity field of a rigid motion is `velocityField V Ω r = V + Ω × r`.
`velocityField_change_of_origin` proves that describing the same field from an
origin displaced by `a` changes `V` to `V + Ω × a` and leaves `Ω` unchanged,
and `velocityField_injective` proves that the field determines `V` and `Ω`. The
form of the field is a theorem about motions: for `x(s) = c(s) + R(s) r₀` with
`R(s)` orthogonal and entrywise differentiable, `transpose_deriv_mul_transpose`
proves that `Ṙ Rᵀ` is skew-symmetric, and `hasDerivAt_rigidMotion` proves that
the velocity of the body point is `ċ + Ω × (x − c)` with `Ω = vee (Ṙ Rᵀ)`.

`inertia m r` is the inertia tensor `Σₐ mₐ (|rₐ|² δᵢₖ − rₐᵢ rₐₖ)` of finitely
many point masses. It is symmetric (`transpose_inertia`).
`inertia_mulVec` is `M = I Ω` with `M = Σₐ mₐ rₐ × (Ω × rₐ)`, and
`dotProduct_inertia_mulVec` is `Ω · I Ω = Σₐ mₐ |Ω × rₐ|²`, twice the kinetic
energy, which is non-negative for non-negative masses. `inertia_add_apply` is
the parallel-axis theorem for a system with centre of mass at the origin.

`principalMoments` and `principalAxes` are the eigenvalues and an orthonormal
basis of eigenvectors of the inertia tensor, from Mathlib's spectral theorem
for Hermitian matrices. For non-negative masses the principal moments are
non-negative, and `principalMoments_two_le` and its two companions prove the
triangle inequality `I₂ ≤ I₀ + I₁`. The basis-free statement behind it is
`two_mul_dotProduct_inertia_mulVec_le_trace`: for a unit vector `n`,
`2 n · I n ≤ tr I`.

`Rigid/EulerAngles` covers Landau–Lifshitz §35. The rotation with Eulerian
angles is `eulerMatrix = R_z(φ) R_x(θ) R_z(ψ)`. The algebraic statements are
over a commutative ring: the cosines and sines are elements `cₖ`, `sₖ` with
`cₖ² + sₖ² = 1`, the rates of the angles are elements `wₖ`, and
`eulerMatrixDeriv` is the derivative of the rotation given by the product rule.

- `eulerMatrix_mul_transpose`, `det_eulerMatrix`: the rotation is orthogonal
  with determinant one.
- `transpose_mul_eulerMatrixDeriv`: `Rᵀ Ṙ = hat Ω` with the angular velocity in
  the body frame
  `Ω = (φ̇ sin θ sin ψ + θ̇ cos ψ, φ̇ sin θ cos ψ − θ̇ sin ψ, φ̇ cos θ + ψ̇)`.
- `eulerMatrixDeriv_mul_transpose`: `Ṙ Rᵀ = hat ω` with the angular velocity in
  the space frame; `eulerMatrix_mulVec_bodyAngularVelocity`: `ω = R Ω`.
- `symmetricTop_energy`: twice the kinetic energy of a symmetric top is
  `I₁ (θ̇² + φ̇² sin² θ) + I₃ (φ̇ cos θ + ψ̇)²`.
- `det_eulerJacobian`: the linear map from the rates of the angles to `Ω` has
  determinant `−sin θ`, so the angles are non-degenerate co-ordinates where
  `sin θ` is invertible.

For real angles, `eulerRotation φ θ ψ` is an element of Mathlib's
`specialOrthogonalGroup (Fin 3) ℝ`. For differentiable functions `φ`, `θ`, `ψ`
of time, `hasDerivAt_eulerRotation` proves that the entrywise derivative of the
rotation is `eulerMatrixDeriv` with the rates `φ'`, `θ'`, `ψ'`, so the formulas
above are the angular velocities of the actual motion
(`angularVelocity_eulerRotation`, `vee_transpose_mul_eulerMatrixDeriv`).

`Rigid/RegularPrecession` treats the free symmetric top of Landau–Lifshitz §33
in Eulerian angles. `symmetricTopMomentum I1 I3 Ω` is the angular momentum
`(I₁ Ω₁, I₁ Ω₂, I₃ Ω₃)` in the body frame, and the rotation applied to it is
the angular momentum in the space frame. The fixed axis `Z` has the components
`(sin θ sin ψ, sin θ cos ψ, cos θ)` in the body frame
(`transpose_eulerMatrix_mulVec`).

- `eulerMatrix_mulVec_symmetricTopMomentum_iff`: for real angles with
  `sin θ ≠ 0` and `I₁ ≠ 0`, the angular momentum in the space frame is
  `(0, 0, M)` exactly when `θ̇ = 0`, `I₁ φ̇ = M` and
  `I₃ (φ̇ cos θ + ψ̇) = M cos θ`. So `ψ̇ = M cos θ (1/I₃ − 1/I₁)`
  (`regularPrecession_psi_rate`).
- `eulerRotation_mulVec_symmetricTopMomentum`: the motion with the angles
  `φ₀ + (M/I₁) t`, `θ₀`, `ψ₀ + M cos θ₀ (1/I₃ − 1/I₁) t` has the angular
  momentum `(0, 0, M)` at every time.

The statement that a free motion keeps its angular momentum in the space frame
is the equation of motion `Ṁ = 0`. It is derived from Newton's equations and
from Hamilton's principle in the next section.

## The equations of motion of a rigid body

`Rigid/Dynamics` derives the equations of Landau–Lifshitz §34 from Newton's
equations for finitely many point masses `mₐ` at the body positions `rₐ`.
`IsRigidMotion c c' R R'` states that the origin of the body `c` has the
velocity `c'`, that the matrix `R` has the entrywise derivative `R'`, and that
`R(s)ᵀ R(s) = 1` and `det R(s) = 1` at every time. The particles are at
`qₐ = c + R rₐ` (`IsRigidMotion.hasDerivAt_position`). The angular velocity in
the body frame is `angularVelocityBody R R' = vee (Rᵀ R')`, and `Ṙ = R Ω̂`
(`IsRigidMotion.rotation_deriv`). A rotation maps the cross product to the
cross product (`mulVec_cross`); this is where `det R = 1` is used.

Newton's equations are the hypothesis
`HasDerivAt (fun u => mₐ • (c' u + R' u *ᵥ rₐ)) Fₐ t` for each particle, with
`Fₐ` the total force on it.

- `IsRigidMotion.hasDerivAt_momentum`: if `Σ mₐ rₐ = 0`, the momentum is
  `μ ċ` and its derivative is `Σ Fₐ`.
- `IsRigidMotion.sum_smul_cross_velocity`: the angular momentum about the
  origin of the body is `R (I Ω)` with `I = inertia m r`.
- `IsRigidMotion.hasDerivAt_angularMomentum`: its derivative is the moment
  `Σ (R rₐ) × Fₐ` of the forces, when the origin is the centre of mass or is
  at rest.
- `IsRigidMotion.hasDerivAt_bodyAngularMomentum`: in the body frame,
  `d(I Ω)/dt = (I Ω) × Ω + Rᵀ K`. `IsRigidMotion.hasDerivAt_bodyVector`:
  `Γ = Rᵀ e` satisfies `Γ̇ = Γ × Ω`.
- `sum_internal_force`, `sum_cross_internal_force`: forces `f_ab = −f_ba`
  along the lines joining the particles cancel in the total force and in the
  total moment.
- `transpose_mulVec_sum_cross_weight`: the moment of the uniform field
  `−g e` is `Γ × (g Σ mₐ rₐ)` in the body frame.
- `IsRigidMotion.sum_mul_velocity_sq`: `Σ mₐ |vₐ|² = μ |ċ|² + Ω · I Ω`.

`Rigid/Reconstruction`: for a continuous angular velocity `Ω(t)` in the body
frame, `rotation Ω R₀` is the solution of `Ṙ = R Ω̂` with `R(0) = R₀`, for all
times, by the propagator of the equation `u̇ = u × Ω` of its rows. It is the
only solution (`eq_rotation_of_hasDerivAt`), it is a rotation if `R₀` is one
(`rotation_transpose_mul`, `det_rotation`), so it is a rigid motion with the
angular velocity `Ω` (`isRigidMotion_rotation`,
`angularVelocityBody_rotation`), and `d(R L)/dt = R (L̇ − L × Ω)`
(`hasDerivAt_rotation_mulVec`).

`Rigid/Variation` and `Rigid/RotationAction` are the Lagrangian form.
`IsRotationFamily R` is a smooth family `R(ε, t)` of orthogonal matrices. Its
variation field is `η = vee (Rᵀ ∂R/∂ε)` (`familyVariation`), and
`∂R/∂ε = R η̂` (`IsRotationFamily.familyDeriv_parameter`): every variation of
a rotation is an infinitesimal rotation in the body frame.

- `IsRotationFamily.hasDerivAt_curveVelocity_family`:
  `∂Ω/∂ε = ∂η/∂t + Ω × η`, from the symmetry of the second derivatives.
- `hasDerivAt_rotationAction`: for the action `rotationAction J V γ` of the
  Lagrangian `Ω · J Ω / 2 − V(Rᵀ γ)`, with `J` symmetric and `V` smooth,
  `dS/dε = [J Ω · η] − ∫ (d(J Ω)/dt − J Ω × Ω − Γ × ∇V(Γ)) · η dt`.
- `cayley ξ` is the Cayley transform of `hat ξ / 2`, an orthogonal matrix
  that is rational in `ξ`, with `cayley 0 = 1` and the derivative `hat ξ` at
  `0`. The family `R₀(t) · cayley (ε η(t))` has the variation field `η`
  (`isRotationFamily_mul_cayley`, `familyVariation_mul_cayley`).
- `stationary_rotationAction_iff`: a smooth curve of rotations is stationary
  among the families with fixed ends if and only if
  `d(J Ω)/dt = J Ω × Ω + Γ × ∇V(Γ)` between the ends
  (`eulerPoissonResidual_eq_zero_iff`).

`Poisson/RigidBodyEquations` identifies these equations with the Lie–Poisson
equations in principal axes, `inertia m r = diagonal I` with `Iᵢ ≠ 0`.
`HeavyTop.field I k χ` is the vector field of the heavy top on the space of
`(L, Γ)`, with the values `(L × Ω + Γ × kχ, Γ × Ω)` (`HeavyTop.field_inl`,
`HeavyTop.field_inr`).

- `IsRigidMotion.hasDerivAt_eulerField`: with no moment of the forces, the
  angular momentum in the body frame is an integral curve of
  `RigidBody.eulerField`.
- `IsRigidMotion.hasDerivAt_heavyTopField`: for a body with a fixed point
  under the field `−g e` and forces without moment about the fixed point,
  `(I Ω, Rᵀ e)` is an integral curve of `HeavyTop.field I g (Σ mₐ rₐ)`.
- `hasDerivAt_heavyTopField_of_stationary`: the same conclusion for a curve
  of rotations that is stationary for the action with `V(Γ) = Γ · kχ`.
- `rotation_mulVec_eulerSolution`: for a solution `L(t)` of Euler's equations
  the rotation with `Ωᵢ = Lᵢ/Iᵢ` exists for all times and `R L` is constant.
  `stationary_rotationAction_rotation`: this rotation is stationary for the
  action of the free body when `Ω` is smooth.

The motion is given as curves of vectors and matrices. The space
`ℝ³ ⋊ SO(3)` as a manifold, the bracket of `T*SO(3)` and its reduction to the
Lie–Poisson bracket, a potential that depends on the rotation otherwise than
through one vector `Rᵀ γ`, and continuous distributions of mass are not
treated.

## Small oscillations

`Mechanics/Oscillations` covers Landau–Lifshitz §21, and §§25, 26, 22, 23 and
27 in the sections that follow.

`Oscillations/Harmonic` treats the equation `ẍ + ω² x = 0` for a smooth
function of time. `IsHarmonic ω x` is the equation `ẍ = −ω² x` in the ring
`TimeFunction`, and `TimeFunction.cosMul ω`, `TimeFunction.sinMul ω` are the
functions `cos ωt`, `sin ωt`.

- `IsHarmonic.eq_cos_add_sin`: for `ω ≠ 0`,
  `x = x(0) cos ωt + (ẋ(0)/ω) sin ωt`. The combinations
  `x cos ωt − (ẋ/ω) sin ωt` and `x sin ωt + (ẋ/ω) cos ωt` have zero derivative,
  so they are constants. `isHarmonic_iff` states the result as an equivalence,
  and `IsHarmonic.eq_of_initial` as uniqueness for given `x(0)` and `ẋ(0)`.
- `amplitude_mul_cos_add`, `IsHarmonic.apply_eq_amplitude_mul_cos`:
  `x(t) = a cos (ωt + α)` with `a = √(x(0)² + (ẋ(0)/ω)²)`. The phase `α` is the
  argument of the complex number `x(0) − i ẋ(0)/ω`.
- `IsHarmonic.apply_add_period`: the period is `2π/ω` for every amplitude.
- `IsHarmonic.energy_eq`, `IsHarmonic.energy_eq_amplitude`:
  `½ m (ẋ² + ω² x²)` is constant and equals `½ m ω² a²`.

`Oscillations/Oscillator` connects the equation to the Lagrangian and the
Hamiltonian of the oscillator. The hypotheses are `mᵢ ≠ 0` and `k = mᵢ ωᵢ²`.

- `StandardJet.isSolution_oscillator_iff_isHarmonic`: a path solves the
  Euler–Lagrange equations of `Σᵢ ½ mᵢ q̇ᵢ² − ½ k qᵢ²` exactly when each
  component is a free oscillation of frequency `ωᵢ`.
- `Oscillator.isTrajectory_iff_isHarmonic`: a curve is a trajectory of
  `Σᵢ pᵢ²/2mᵢ + ½ k qᵢ²` exactly when each `qᵢ` is a free oscillation and
  `pᵢ = mᵢ q̇ᵢ`.
- `Oscillator.flowMatrix m ω t` is the matrix of the flow on a pair `(q, p)`.
  It is a one-parameter group (`flowMatrix_zero`, `flowMatrix_add`) of
  determinant one (`det_flowMatrix`) with period `2π/ω`
  (`flowMatrix_add_period`). Every trajectory is the flow of its initial point
  (`apply_eq_flowMatrix_mulVec`), and every point lies on a trajectory
  (`isTrajectory_flowCurve`).

`Oscillations/Linearization` treats an equilibrium of a Hamiltonian on a free
C∞-ring. A point `x₀` is an equilibrium when the constant curve at `x₀` is a
trajectory.

- `isTrajectory_const_iff`: `x₀` is an equilibrium exactly when the brackets
  `{x_a, H}` vanish at `x₀`. For the canonical bracket this is a critical point
  of `H` (`isTrajectory_canonical_const_iff`).
- `linearization π H x₀` is the matrix `∂_c {x_a, H}(x₀)`. `hessian H x₀` is
  the matrix of second partial derivatives at `x₀`, and `quadraticPart H x₀` is
  `½ Σ H_ab(x₀) ξ_a ξ_b` with the displacements `ξ_a = x_a − x₀ a`.
- `canonical_bracket_quadraticPart`: for the canonical bracket,
  `{x_a, quadraticPart H x₀} = Σ_c A_ac ξ_c` with `A` the linearization of `H`
  at `x₀`. So `H` and its quadratic part have the same linearization
  (`linearization_quadraticPart`), and the trajectories of the quadratic part
  are the solutions of `d/dt ξ_a = Σ_c A_ac ξ_c`
  (`isTrajectory_quadraticPart_iff`).
- One degree of freedom: `naturalHamiltonian b U` is `½ b(q) p² + U(q)`. The
  point `(q₀, 0)` is an equilibrium exactly when `U'(q₀) = 0`
  (`isTrajectory_restPoint_iff`). Along a solution of the linearized equations
  the displacement `q − q₀` is a free oscillation with `ω² = b(q₀) U''(q₀)`
  (`isHarmonic_of_isTrajectory_quadraticPart`). At a non-degenerate minimum with
  a positive mass, `ω = √(b(q₀) U''(q₀))`
  (`isHarmonic_sqrt_of_isTrajectory_quadraticPart`).
- `isHarmonic_pendulum`: for the pendulum `p²/(2 m l²) − m g l cos q`,
  `ω² = g/l`.

The linearization is the derivative of the Hamiltonian vector field at the
equilibrium. No theorem here compares the solutions of the non-linear
equations with those of the linearized equations. The Hamiltonian
`½ b(q) p² + U(q)` corresponds to the Lagrangian `½ a(q) q̇² − U(q)` of
Landau–Lifshitz with `b = 1/a`; the Legendre transformation between them is
not formalized.

## Damped oscillations

`Oscillations/Damped` treats the equation `ẍ + 2γ ẋ + ω₀² x = 0` of
Landau–Lifshitz §25. The damping coefficient is written `γ`, because `λ` is a
reserved word of Lean. `IsDamped γ ω₀ x` is the equation
`ẍ = −2γ ẋ − ω₀² x` in the ring `TimeFunction`; `TimeFunction.expMul a` is the
function `e^{at}` and `TimeFunction.time` is `t`.

- `isDamped_iff_expMul_mul`: `x` is a solution exactly when `y = e^{γt} x`
  satisfies `ÿ = −(ω₀² − γ²) y`.
- Weak damping, `ω₀² − γ² = ω²` with `ω ≠ 0`: `y` is a free oscillation
  (`isDamped_iff_isHarmonic`), so
  `x = e^{−γt} (x(0) cos ωt + ((ẋ(0) + γ x(0))/ω) sin ωt)`
  (`IsDamped.apply_eq_underdamped`). In amplitude and phase,
  `x = a e^{−γt} cos (ωt + α)` (`IsDamped.apply_eq_amplitude_mul_exp_mul_cos`),
  and `|x(t)| ≤ a e^{−γt}` (`IsDamped.abs_apply_le`).
- Critical damping, `ω₀² = γ²`:
  `x = (x(0) + (ẋ(0) + γ x(0)) t) e^{−γt}` (`IsDamped.apply_eq_critical`).
- Strong damping, `γ² − ω₀² = β²` with `β ≠ 0`:
  `x = c₁ e^{−(γ−β)t} + c₂ e^{−(γ+β)t}` with the constants given by `x(0)` and
  `ẋ(0)` (`IsDamped.apply_eq_overdamped`).
- `IsDamped.eq_of_initial`: for all real `γ` and `ω₀`, a solution is determined
  by `x(0)` and `ẋ(0)`. The proof is the trichotomy of `ω₀²` and `γ²`.
- Existence: `isDamped_expMul` for `e^{rt}` with `r² + 2γ r + ω₀² = 0`,
  `isDamped_time_mul_expMul` for `t e^{−γt}` at critical damping,
  `IsHarmonic.isDamped_expMul_neg_mul` for weak damping, and sums and constant
  multiples (`IsDamped.add`, `IsDamped.const_mul`).
- `IsDamped.timeDerivative_energy`: `d/dt (ẋ² + ω₀² x²) = −4γ ẋ²`. For `γ ≥ 0`
  the energy does not increase (`IsDamped.energy_antitone`).

`Oscillations/Dissipation` treats friction on the canonical phase space.
`IsIntegralCurve X c` says that the curve `c` evolves by the vector field `X`;
a trajectory of a Hamiltonian is an integral curve of its Hamiltonian vector
field (`isIntegralCurve_hamiltonian_iff`), and `d/dt f(c) = X(f)(c)` along an
integral curve (`IsIntegralCurve.timeDerivative_lift`).

For a real matrix `α` and a Hamiltonian `H`, with the velocities
`vᵢ = ∂H/∂pᵢ`:

- `frictionalForce α H i` is `fᵢ = Σₖ αᵢₖ vₖ`, `dissipativeFunction α H` is
  `F = ½ Σ αᵢₖ vᵢ vₖ`, and `dissipativeField α H` is the vector field
  `X = X_H − Σᵢ fᵢ ∂/∂pᵢ`.
- `dissipativeField_q`, `dissipativeField_p`: `X(qᵢ) = ∂H/∂pᵢ` and
  `X(pᵢ) = −∂H/∂qᵢ − fᵢ`.
- `dissipativeField_self`: `X(H) = −2F`. The identity does not use the symmetry
  of `α`.
- `lift_dissipativeFunction_nonneg`: if `v · α v ≥ 0` for every real vector
  `v`, then `F` is non-negative at every point.
- `IsIntegralCurve.energy_antitone`: under the same hypothesis the energy does
  not increase along an integral curve of `X`.
- `Oscillator.isIntegralCurve_dissipativeField_iff_isDamped`: for the oscillator
  with the diagonal matrix `αᵢᵢ = 2 mᵢ γᵢ`, the integral curves are the curves
  with `IsDamped γᵢ ω₀ᵢ` for every position and `pᵢ = mᵢ q̇ᵢ`.

The vector field `X` is not Hamiltonian. That it does not preserve the bracket
and that the phase volume contracts are not proved. No theorem asserts that an
integral curve exists for a general Hamiltonian.

## Forced oscillations under friction

`Oscillations/Forced` treats the equation `ẍ + 2γ ẋ + ω₀² x = g` of
Landau–Lifshitz §26. `IsForced γ ω₀ g x` is the equation
`ẍ = g − 2γ ẋ − ω₀² x` in the ring `TimeFunction`, with `g` the force divided
by the mass. The frequency of the force is written `Ω`; Landau–Lifshitz write
`γ` for it and `λ` for the damping coefficient.

- `IsForced.add`, `IsForced.const_mul`: superposition. `IsForced.sub`: two
  solutions for the same force differ by a solution of the damped equation.
  `IsForced.eq_of_initial`: a solution is determined by `x(0)` and `ẋ(0)`.
- `IsDamped.tendsto_zero`: for `γ > 0` and `ω₀ ≠ 0` every solution of the
  damped equation tends to zero as `t → ∞`, in each of the three cases. So two
  solutions for the same force approach each other (`IsForced.tendsto_sub`).
- `IsForced.timeDerivative_energy`:
  `d/dt (ẋ² + ω₀² x²) = 2 ẋ g − 4γ ẋ²`.

For the force `F cos Ωt`, with `D = (ω₀² − Ω²)² + 4γ² Ω²`
(`responseDenominator`):

- `steadyState γ ω₀ F Ω` is
  `(F (ω₀² − Ω²)/D) cos Ωt + (2 F γ Ω/D) sin Ωt`, and it is a solution when
  `D ≠ 0` (`isForced_steadyState`). It is linear in `F`
  (`steadyState_const_mul`).
- `steadyState_apply`: the steady state is `b cos (Ωt + δ)` with
  `b = |F| / √D` (`steadyAmplitude`). The phase satisfies
  `b cos δ = F (ω₀² − Ω²)/D` and `b sin δ = −2 F γ Ω/D`, so `sin δ ≤ 0` for
  positive `F` and non-negative `γ`, `Ω` (`sin_steadyPhase_nonpos`).
- `IsForced.apply_eq_transient_add_steadyState`: for weak damping,
  `x = a e^{−γt} cos (ωt + α) + b cos (Ωt + δ)`.
  `IsForced.tendsto_sub_steadyState`: for `γ > 0` and `ω₀ ≠ 0` every solution
  approaches the steady state.
- `steadyAmplitude_le`, `steadyAmplitude_eq_max`: with `ω² = ω₀² − γ²`, the
  amplitude is at most `|F|/(2γω)`, and it has this value at
  `Ω² = ω₀² − 2γ²`.
- `absorption m γ ω₀ F Ω` is `m γ b² Ω²`. It is the mean over a period of
  twice the dissipative function `m γ ẋ²` in the steady state
  (`mean_dissipation_steadyState`, an interval integral), because
  `2 m γ ẋ² = I (1 − cos 2(Ωt + δ))` (`two_mul_dissipation_steadyState`).
- `absorption_le`, `absorption_resonance`: the absorption is at most
  `m F²/4γ`, and it has this value at `Ω = ω₀`.
- `absorption_eq_half_max_iff`: for positive `γ` and `Ω`, the absorption is
  `m F²/8γ` exactly at `Ω = √(ω₀² + γ²) + γ` and `Ω = √(ω₀² + γ²) − γ`. These
  two frequencies differ by `2γ`.

The resonance curve here is the exact function
`m γ F² Ω² / ((ω₀² − Ω²)² + 4γ² Ω²)`. The approximation of Landau–Lifshitz near
resonance for small damping, a Lorentzian in `Ω − ω₀`, is an asymptotic
statement and is not proved. A force with a phase, `F cos (Ωt + β)`, is not
treated; a general force is treated without friction in the next section.

## Forced oscillations without friction

`Oscillations/Duhamel` treats the equation `ẍ + ω² x = g` of Landau–Lifshitz
§22, which is `IsForced 0 ω g x` (`isForced_zero_damping_iff`). The force `g`
per unit mass is any smooth function of time.

`Mechanics/TimePrimitive` provides the calculus: the increment of a smooth
function of time is the integral of its derivative
(`TimeFunction.apply_sub_apply_eq_integral`), and `TimeFunction.primitive f`
is the smooth function `t ↦ ∫₀ᵗ f` with derivative `f`.

- `complexAmplitudeRe ω x` and `complexAmplitudeIm ω x` are
  `ẋ cos ωt + ω x sin ωt` and `ω x cos ωt − ẋ sin ωt`, the real and the
  imaginary part of `(ẋ + iωx) e^{−iωt}`. For a solution their derivatives are
  `g cos ωt` and `−g sin ωt`, so
  `Re = ẋ(0) + ∫₀ᵗ g cos ωs ds` and `Im = ω x(0) − ∫₀ᵗ g sin ωs ds`
  (`IsForced.complexAmplitudeRe_eq`, `IsForced.complexAmplitudeIm_eq`). These
  hold for every `ω`.
- `IsForced.apply_eq_integral`: Duhamel's formula, for `ω ≠ 0`,
  `x(t) = x(0) cos ωt + (ẋ(0)/ω) sin ωt + (1/ω) ∫₀ᵗ g(s) sin ω(t − s) ds`.
  `IsForced.timeDerivative_apply_eq_integral` gives the velocity.
- `IsForced.energy_apply`: `ẋ² + ω² x² = Re² + Im²` at every time.
  `IsForced.energy_transfer`: for the force `F` on a particle of mass `m` at
  rest at time zero, the energy at time `T` is
  `((∫₀ᵀ F cos ωt)² + (∫₀ᵀ F sin ωt)²) / 2m`.
- `duhamel ω g` is the function `(1/ω) ∫₀ᵗ g(s) sin ω(t − s) ds`
  (`duhamel_apply`). It is a solution (`isForced_duhamel`) at rest at time
  zero, so for every smooth force and all initial data a solution exists
  (`exists_isForced`); it is unique by `IsForced.eq_of_initial`.
- `isForced_cos_of_sq_ne`: for `Ω² ≠ ω²` the forced oscillation is
  `F/(ω² − Ω²) cos Ωt`, which is the steady state of the previous section with
  `γ = 0` (`steadyState_zero_damping`). `IsForced.apply_eq_of_sq_ne` is the
  general solution.
- `isForced_resonance`: for `Ω = ω` the forced oscillation is
  `(F/2ω) t sin ωt`. It is the motion from rest
  (`IsForced.eq_resonance_of_rest`), and no solution is bounded
  (`IsForced.exists_abs_gt_of_resonance`).

The energy transfer of Landau–Lifshitz (22.12) is the limit of the formula
above for a force acting during all time, with improper integrals; it is not
proved. Beats near resonance are not treated.

## Normal modes

`Oscillations/NormalModes` treats the equations
`Σₖ (mᵢₖ ẍₖ + kᵢₖ xₖ) = 0` of Landau–Lifshitz §23 for real matrices `M` and
`K` on a finite index type.

- `exists_simultaneous_diagonalization`: for a positive definite `M` and a
  symmetric `K` there are a matrix `S` and numbers `λₐ` with `Sᵀ M S = 1` and
  `Sᵀ K S = diag λ`. The proof uses Mathlib's spectral theorem twice: once to
  bring `M` to the unit form, once for the symmetric matrix `Bᵀ K B`.
- The remaining statements take `S` and `λ` with these two properties as
  hypotheses. `mul_eq_mul_mul_diagonal`: `K S = M S diag λ`, so the columns of
  `S` are the normal modes. `det_sub_smul_eq_zero_iff`: the roots of
  `det (K − c M) = 0` are the `λₐ`. `lam_pos`: they are positive when `K` is
  positive definite.
- `IsSmallOscillation M K x` is the system of equations for a family
  `x : n → TimeFunction`. `normalCoordinates S M x` is `Θ = Sᵀ M x`, and
  `x = S Θ` (`map_mulVec_normalCoordinates`).
- `isSmallOscillation_iff`: `x` is a solution exactly when
  `Θ̈ₐ = −λₐ Θₐ` for every `a`. With `ωₐ² = λₐ`, each `Θₐ` is a free
  oscillation (`IsSmallOscillation.isHarmonic_normalCoordinates`), every
  superposition `S Θ` of free oscillations is a solution
  (`isSmallOscillation_map_mulVec`), and `IsSmallOscillation.apply_eq` writes
  each co-ordinate as the sum of the normal oscillations.

The equations are derived from the Lagrangian and from the Hamiltonian in the
next section.

## Quadratic Hamiltonians and the normal form

`Poisson/Quadratic`, `Oscillations/NormalForm` and
`Oscillations/QuadraticLagrangian` prove Proposition 70 of the manuscript and
connect `M ẍ + K x = 0` with the Lagrangian and the Hamiltonian
(Landau–Lifshitz §23).

- `eulerField` is the vector field `Σₐ xₐ ∂ₐ` of a free C∞-ring, and
  `IsEulerHomogeneous k f` is `Σₐ xₐ ∂ₐ f = k f`. Generators have the degree
  one and constants the degree zero, the degrees add under products, and a
  partial derivative lowers the degree by one.
  `IsEulerHomogeneous.canonical_bracket`: for the canonical bracket, the
  bracket of elements of degrees `j` and `k` has the degree `j + k − 2`.
- `quadraticForm S` is `½ Σ S_ab x_a x_b`, and `PhaseSpace.canonicalForm ι`
  is the matrix `J` of the canonical bracket. For symmetric `S` and `T`,
  `{Q_S, Q_T} = Q_{SJT − TJS}` (`PhaseSpace.canonical_bracket_quadraticForm`),
  and `Q_S` determines `S` (`quadraticForm_injective`).
- `PhaseSpace.canonicalForm_mul_mem_sp_iff`: `J S` is in Mathlib's
  `LieAlgebra.Symplectic.sp` exactly when `S` is symmetric. With
  `PhaseSpace.spHamiltonian A = Q_{−JA}`, for `A` and `B` in `sp(2n, ℝ)`,
  `{xₐ, H_A} = Σ_c Aₐ_c x_c` (`canonical_bracket_generator_spHamiltonian`),
  `{H_A, H_B} = H_{[A, B]}` (`canonical_bracket_spHamiltonian`), and
  `A ↦ H_A` is injective (`spHamiltonian_injective`). Every quadratic form is
  `H_{JS}` (`quadraticForm_eq_spHamiltonian`).
- `NormalModes.linearTransformation A B` is the morphism `q ↦ A q`,
  `p ↦ B p` of phase space. It is a Poisson morphism when `A Bᵀ = 1`
  (`isPoissonHom_linearTransformation`), and these morphisms compose by the
  product of the matrices (`linearTransformation_comp`).
- `NormalModes.quadraticHamiltonian W K` is `½ pᵀ W p + ½ qᵀ K q`. With
  `Sᵀ M S = 1` and `Sᵀ K S = diag λ` for a symmetric `M`, the inverse of `M`
  is `S Sᵀ`, and `quadraticHamiltonian_eq_normalForm` is
  `H = Σₐ ½ (Pₐ² + λₐ Qₐ²)` for `Q = Sᵀ M q` and `P = Sᵀ p`. The
  transformation is canonical (`isPoissonHom_normalTransformation`) with the
  inverse `q ↦ S q`, `p ↦ M S p` (`linearTransformation_comp_inverse`,
  `linearTransformation_inverse_comp`).
- `NormalModes.isTrajectory_quadraticForm_iff`: a trajectory of `Q_S`
  satisfies `ẋ = J S x`.
  `NormalModes.isTrajectory_quadraticHamiltonian_iff_isSmallOscillation`: for
  `M W = 1`, the trajectories of `½ pᵀ W p + ½ qᵀ K q` are the solutions of
  `M ẍ + K x = 0` with `p = M ẋ`.
- `JetRing.quadraticLagrangian M K` is `½ Σ (mᵢₖ vᵢ vₖ − kᵢₖ qᵢ qₖ)`
  (Landau–Lifshitz (23.3)). For symmetric `M` and `K` its Euler–Lagrange
  expressions are `−Σₖ kᵢₖ qₖ − Σₖ mᵢₖ q̈ₖ`
  (`JetRing.euler_quadraticLagrangian`), its solutions are the small
  oscillations (`StandardJet.isSolution_quadraticLagrangian_iff`), and
  `NormalModes.isTrajectory_quadraticHamiltonian_iff_isSolution` is the
  Legendre correspondence with the Hamiltonian.

The correspondence with `sp(2n, ℝ)` is stated by these identities and is not
bundled as an isomorphism of Lie algebras. The matrices `M` and `K` are
constants.

## Symmetry of the normal modes

`Oscillations/Symmetry` gives the part of Landau–Lifshitz §24 that is linear
algebra. `modeSpace M K c` is the space of the vectors with `K v = c M v`.

- `mulVec_mem_modeSpace`: a matrix `P` that commutes with `M` and `K`
  preserves `modeSpace M K c`. For a group of such matrices, each of these
  spaces carries a representation of the group.
- `isSmallOscillation_symmetry`: such a matrix takes small oscillations to
  small oscillations.
- `card_ne_zero_eq_rank`: with `Sᵀ M S = 1` and `Sᵀ K S = diag λ`, the number
  of non-zero `λₐ` is the rank of `K`. The modes with zero frequency are the
  kernel of `K`; for a molecule they contain the translations and the
  rotations.

`Oscillations/SymmetryTypes` is the decomposition and the counting. With
`Sᵀ M S = 1` and `Sᵀ K S = diag λ`, `modeSpace M K c` is the eigenspace of
`S Sᵀ K = M⁻¹ K` for the value `c` (`modeSpace_eq_eigenspace`).

- `isInternal_modeSpace`: the space of the co-ordinates is the direct sum of
  the spaces `modeSpace M K c` over the values `c` of `λ`.
  `finrank_modeSpace`: the dimension of the space of the value `c` is the
  number of the indices with `λ = c`.
- `IsSymmetryRep ρ M K`: a representation `ρ` of a group on the co-ordinates
  by maps that commute with `M` and `K`. `modeSubrep` and `modeRep` are the
  subrepresentation and the representation on the modes of one value.
- `character_eq_sum_modeRep`: the character of `ρ` is the sum of the
  characters on the spaces of the modes.
- `sum_finrank_intertwiningMap_modeRep`: for a representation `σ` of the same
  finite group, the dimensions of the spaces of the equivariant maps from `σ`
  to the modes of each value add up to `(1/|G|) Σ_g χ_ρ(g) χ_σ(g⁻¹)`.

A symmetry type is a real representation `σ`. The dimension of the space of
the equivariant maps from `σ` is the number of times `σ` occurs when the
equivariant endomorphisms of `σ` are the scalars.

`Oscillations/Molecule`: the atoms are indexed by `ι` and a displacement is a
function on `ι × Fin 3`; `atom u a` is the displacement of the atom `a`. A
group acts on space by the matrices `O g` and permutes the atoms by `π g`.

- `displacementRep O π`: `(g u)ₐ = O_g u_{π_g⁻¹ a}` (`atom_displacementRep`).
  Its matrix is the Kronecker product of a permutation matrix and `O g`.
- `character_displacementRep`: the character is `N_g · tr O_g`, with `N_g`
  the number of the atoms that `g` leaves in place.
- `rigidMap r`: the displacement `uₐ = t + ω × rₐ`. For orthogonal `O g` and a
  symmetric configuration, `O_g rₐ = r_{π_g a}`, it is equivariant from
  `rigidRep O`, the vectors and the axial vectors
  (`displacementRep_rigidMap`), whose character is `(1 + det O_g) tr O_g`
  (`character_rigidRep`).
- `sum_finrank_vibration`: if `rigidMap r` is injective and its range is the
  space of the modes of frequency zero, the modes of non-zero frequency
  contain the type `σ` as many times as
  `(1/|G|) Σ_g (N_g − 1 − det O_g) tr O_g χ_σ(g⁻¹)`.
- `card_vibration_add_six`: there are then `3N − 6` modes of non-zero
  frequency; `card_vibration_add_finrank_range` is the count without the
  injectivity, as for a molecule on a line.

`Oscillations/SpringMolecule` is a model of the potential energy: a spring of
the stiffness `κ a b` along each bond, so that
`u · K u = Σ κ_ab ((uₐ − u_b) · (rₐ − r_b))²` (`springMatrix`,
`dotProduct_springMatrix_mulVec`), with the mass matrix `massMatrix m`.

- `springMatrix_mulVec_eq_zero_iff`: for positive stiffnesses the modes of
  frequency zero are the displacements that stretch no bond; the rigid
  displacements are among them (`rigidMap_mem_modeSpace_zero`).
- `isSymmetryRep_spring`: a group of orthogonal symmetries of the
  configuration that preserves the masses and the stiffnesses is a
  representation by symmetries.

`Oscillations/Triatomic`: three atoms that are not on a line.

- `rigidMap_injective`, `exists_rigidMap_eq`,
  `range_rigidMap_eq_modeSpace_zero`: the six rigid displacements are
  independent, and with a spring on each bond they are the modes of frequency
  zero. `card_vibration_triatomic`: there are three vibrations.
- `sum_finrank_vibration_triatomic`: the number of the vibrations of each
  symmetry type, for every group of symmetries of the molecule.
- `Equilateral`: three equal atoms and the six permutations of the corners,
  acting by permutation matrices. The trivial type occurs once
  (`sum_finrank_trivial`), the sign type never (`sum_finrank_sign`) and the
  permutation representation twice (`sum_finrank_permutation`); the
  permutation representation is the sum of the trivial type and of the
  two-dimensional type, so the vibrations are one totally symmetric vibration
  and one pair of the two-dimensional type.
- `Isosceles`: an isosceles molecule and its four symmetries, the reflection
  that exchanges the atoms of the base and the reflection in the plane of the
  molecule. Two vibrations are symmetric under both
  (`sum_finrank_symmetric`), one is antisymmetric under the first
  (`sum_finrank_antisymmetric`), and none is antisymmetric under the second
  (`sum_finrank_plane`).

The representations are real. Complex characters, the list of the irreducible
representations of the point groups, the symmetry types of a molecule on a
line, and the statement that the modes of one frequency form one irreducible
representation in the absence of accidental degeneracy are not treated.

## Parametric resonance

`Oscillations/Parametric` treats `ẍ + p(t) x = 0` (Landau–Lifshitz §27).
`IsHill p x` is the equation in the ring `TimeFunction`, and
`TimeFunction.shift T f` is the translate `t ↦ f(t + T)`; the coefficient has
period `T` when `TimeFunction.shift T p = p`.

- `IsHill.wronskian_eq`: the Wronskian `x ẏ − ẋ y` of two solutions is
  constant.
- `FundamentalSystem p` is the data of the two solutions with the initial
  values `(1, 0)` and `(0, 1)`. Its Wronskian is one, and every solution is
  `x(0) x₁ + ẋ(0) x₂` (`FundamentalSystem.eq_combination`); so a solution is
  determined by its initial data. `FundamentalSystem.harmonic` is the system
  `cos ωt`, `sin ωt / ω` of the oscillator.
- `FundamentalSystem.matrix t` is the matrix `Φ(t)`, with `Φ(0) = 1`,
  `det Φ(t) = 1` (`det_matrix`) and `state x t = Φ(t) (state x 0)`
  (`state_eq`). For a coefficient of period `T`,
  `Φ(s + nT) = Φ(s) Φ(T)ⁿ` (`matrix_add_nat_mul_period`).
- `mul_self_eq`, `sin_smul_pow_succ`, `exists_abs_pow_apply_le`: for a real
  `2 × 2` matrix of determinant one, `A² = (tr A) A − 1`; with
  `tr A = 2 cos θ`, `sin θ · Aᵏ⁺¹ = sin (k+1)θ · A − sin kθ · 1`; so the powers
  are bounded when `|tr A| < 2`.
- `FundamentalSystem.exists_abs_apply_le_of_abs_trace_lt`,
  `FundamentalSystem.exists_abs_apply_le_of_eq`: if `|tr Φ(T)| < 2`, or
  `Φ(T) = ±1`, every solution is bounded for `t ≥ 0`.

`Oscillations/ParametricExistence` constructs the solutions. The first-order
system `(x, v)' = (v, −p(t) x)` has the continuous coefficient
`hillCoefficient p`, and `hillState p x₀ v₀ t` is its propagator from time
zero applied to `(x₀, v₀)`. The propagator of a smooth coefficient is smooth
in the time, so the two components are functions of time in `TimeFunction`.

- `isHill_hillSolution`, `hillSolution_zero`,
  `timeDerivative_hillSolution_zero`: `hillSolution p x₀ v₀` solves the
  equation for all time with the initial data `(x₀, v₀)`.
- `IsHill.eq_of_initial`, `existsUnique_isHill`: the solution with given
  initial data is unique.
- `FundamentalSystem.ofCoefficient p`, `FundamentalSystem.nonempty`: every
  smooth coefficient has a fundamental system, and the type has at most one
  element. For a constant frequency it is `FundamentalSystem.harmonic`
  (`FundamentalSystem.ofCoefficient_harmonic`).
- `monodromy p T` is the matrix of that system at the time `T`, with
  `det_monodromy` and `FundamentalSystem.matrix_eq_monodromy`.

`Oscillations/ParametricTrace` decides stability by the trace of the monodromy
matrix `M` of a coefficient of period `T > 0`.

- `IsHill.shift_eq_of_mulVec_eq`: if the state at time zero is an eigenvector
  of `M` with eigenvalue `ν`, then `x(t + T) = ν x(t)`. Such a solution is
  bounded for `t ≥ 0` when `|ν| ≤ 1` (`exists_abs_apply_le_of_shift_eq`) and
  unbounded when `|ν| > 1` and `x ≠ 0` (`not_exists_abs_apply_le_of_shift_eq`).
- `exists_mulVec_eq_smul_of_two_lt_abs_trace`: a real `2 × 2` matrix of
  determinant one with `|tr A| > 2` has a real eigenvalue `μ` with `|μ| > 1`.
- `exists_isHill_not_bounded_of_two_lt_abs_trace`: if `|tr M| > 2` there is an
  unbounded solution. Not every solution is unbounded:
  `IsHill.exists_abs_apply_le_iff_of_two_lt_abs_trace` states that a solution
  is bounded exactly when its state at time zero is an eigenvector whose
  eigenvalue has absolute value less than one.
- `mulVec_mulVec_sub_of_trace_eq`,
  `IsHill.exists_abs_apply_le_iff_of_trace_eq`: if `tr M = 2σ` with `σ = ±1`,
  then `(M − σ)² = 0`; a solution is bounded exactly when its state at time
  zero is an eigenvector, and the other solutions grow linearly,
  `x(t + nT) = σⁿ (x(t) + n σ y(t))` with a solution `y ≠ 0`.
- `forall_isHill_bounded_iff`: every solution is bounded for `t ≥ 0` if and
  only if `|tr M| < 2` or `M = 1` or `M = −1`.

`Oscillations/ParametricZone` gives the width of the instability zone for the
coefficient `modulated ω₀ h γ`, that is `ω₀² (1 + h cos γt)`, with the period
`T = 2π/γ` (`shift_modulated`).

- `rotation γ t` is the change of co-ordinates
  `(a, b) ↦ (a cos (γt/2) + b sin (γt/2), (γ/2)(−a sin (γt/2) + b cos (γt/2)))`,
  and `rotatingCoefficient p γ` is the coefficient of the system for `(a, b)`,
  `(2/γ)(p(t) − γ²/4)` times a matrix of products of `cos (γt/2)` and
  `sin (γt/2)`. `propagator_hillCoefficient_rotation` states that the two
  propagators are conjugate by `rotation`, for every coefficient `p`.
- `trace_monodromy_eq_neg`: after the period `2π/γ` the rotation is `−1` times
  the rotation at time zero, so `tr M` is minus the trace of the propagator in
  the rotating co-ordinates.
- `norm_rotatingCoefficient_modulated_le`: the coefficient in the rotating
  co-ordinates has norm at most `zoneBound ω₀ h γ`, which is
  `(4/γ)(|ω₀² − γ²/4| + ω₀² |h|)`.
- `integralCoefficient_rotating_left`, `integralCoefficient_rotating_right`:
  the integral of that coefficient over a period. Its diagonal vanishes and
  its two other entries are `(2π (ω₀² − γ²/4) ∓ π ω₀² h)/γ²`.
- `abs_trace_monodromy_modulated_sub_le`: with `r = zoneBound ω₀ h γ · 2π/γ`,
  `|tr M + 2 − (4π²/γ⁴)((ω₀² − γ²/4)² − ω₀⁴ h²/4)| ≤ eʳ r³/3`.
- `exists_isHill_not_bounded_modulated`: if `ω₀⁴ h²/4 − (ω₀² − γ²/4)²`, times
  `4π²/γ⁴`, exceeds the remainder, there is an unbounded solution.
  `exists_abs_apply_le_modulated`: if `(ω₀² − γ²/4)² − ω₀⁴ h²/4`, times
  `4π²/γ⁴`, exceeds the remainder and `r ≤ 1`, every solution is bounded.
- `exists_isHill_not_bounded_modulated_resonance`: at `γ = 2ω₀` and for
  `0 < |h| ≤ 1/400` there is an unbounded solution.
  `exists_abs_apply_le_modulated_of_le`: for
  `ω₀² |h| ≤ |ω₀² − γ²/4| ≤ γ²/4000` and `γ² ≠ 4ω₀²` every solution is bounded.

`Oscillations/ParametricExamples` proves the hypotheses of these theorems for
constant coefficients, which have every period (`shift_algebraMap`). For
`ẍ + ω² x = 0` the trace over the period `π/(2|ω|)` is zero, and the criterion
gives the boundedness of all solutions (`exists_abs_apply_le_harmonic`). For
`ẍ = 0` the monodromy matrix is `!![1, T; 0, 1]` (`monodromy_free`), the
parabolic case: a solution is bounded exactly when its velocity at time zero
vanishes (`IsHill.exists_abs_apply_le_free_iff`). For `ẍ = κ² x` the trace is
`2 cosh κT` (`trace_monodromy_hyperbolic`), the hyperbolic case, with an
unbounded solution (`exists_isHill_hyperbolic_not_bounded`).

For `γ = 2ω₀ + ε` the variable is `ω₀² − γ²/4 = −ε (ω₀ + ε/4)`, so to first
order the zone is `|ε| < |h| ω₀/2`, which is (27.11). The zones near
`γ = 2ω₀/n` for `n ≥ 2` and the rate of growth (27.12) are not treated.

## Motion in a rapidly oscillating field

`Oscillations/RapidForce` treats Landau–Lifshitz §30 for one degree of
freedom: `m ẍ = −U′(x) + ω g(x) cos ωt`. The amplitude of the force is
proportional to the frequency, so that its effect has a limit for large `ω`.
`RapidBounds U g A B` states that `U` and `g` are smooth with
`|U′|, |U″| ≤ A` and `|g|, |g′|, |g″| ≤ B`.

- `slowVelocity`: the smooth part `w = v − (g(x)/m) sin ωt` of the velocity.
  `IsRapidMotion.hasDerivAt_pair`: `(x, w)` follows the field `slowField` of
  the motion in the effective potential `U + g²/4m` (`effectivePotential`,
  `hasDerivAt_effectivePotential`) up to the terms `oscillation₁`,
  `oscillation₂`, which oscillate with the frequencies `ω` and `2ω`.
- `exists_forall_abs_sub_le`: there is a constant `C`, depending on `m`, `A`,
  `B`, a bound `V` of the velocity and `L`, such that for every `ω > 0` a
  motion and the motion in the effective potential from the same position
  with the same velocity satisfy `|x(t) − X(t)| ≤ C/ω` on `[0, L]`.
- `IsRapidMotion.abs_velocity_le`: the velocity is bounded on `[0, L]`
  independently of `ω`; `exists_forall_abs_sub_le_of_initial` is the theorem
  with a bound of the initial velocity only.
- `RapidForceExistence`: both motions exist for all times
  (`exists_isRapidMotion`, `exists_isSlowMotion`), as flows of fields of linear
  growth, and `exists_forall_exists_abs_sub_le` combines the statements.
- `Pendulum`: for `U = −a cos x` and `g = b sin x`, a pendulum whose point of
  support oscillates vertically, the bounds hold, the upper position is an
  equilibrium of the effective potential, and the derivative of its force
  there is `−a + b²/2m`, which is positive exactly when `b² > 2 m a`.

Several degrees of freedom, potentials with unbounded derivatives and the
corrections of higher order are not treated.

## Resonance in non-linear oscillations

`Oscillations/NonlinearResonance` treats Landau–Lifshitz §29 for a cubic term:
`ẍ + 2λ ẋ + ω₀² x = F cos γt − β x³` (`IsMotionOn`, on a set of times).
`amplitude γ x v` is the pair `(a, b)` with `x = a cos γt + b sin γt` and
`ẋ = γ (−a sin γt + b cos γt)`. The slow parameters are
`detuning = (γ² − ω₀²)/2γ`, `nonlinearity = 3β/8γ` and `forcing = F/2γ`.

- `IsMotionOn.hasDerivAt_amplitude`: the amplitudes follow
  `averagedField λ ε κ f`, the field
  `(−λ a − (ε − κ r²) b, −λ b + (ε − κ r²) a + f)`, up to four terms in
  `cos 2γt`, `sin 2γt`, `cos 4γt`, `sin 4γt` with polynomial amplitudes
  (`cosAmplitude`, `sinAmplitude`). This is an identity, with no
  approximation.
- `amplitude_equation`: at an equilibrium of the averaged field,
  `r² ((ε − κ r²)² + λ²) = f²`, the equation (29.4).
  `exists_averagedField_eq_zero`: conversely every solution `r²` of it is the
  squared amplitude of an equilibrium.
- `exists_forall_norm_amplitude_sub_le`: for fixed `λ`, `ε`, `κ`, `f`, `ρ`,
  `L` there is `C` such that for every `γ > 0` the amplitudes of a motion and
  the solution of the averaged equations with the same initial value differ
  by at most `C/γ` on `[0, L]`, as long as both stay in the disc of the
  radius `ρ`.
- `exists_forall_abs_sub_steady_le`: a motion that starts with the amplitudes
  of an equilibrium stays within `2C/γ` of `a₀ cos γt + b₀ sin γt`.

The quadratic term of the text, the existence of an exactly periodic motion,
the stability of the branches of the amplitude equation and the resonances at
other frequencies are not treated.

## Anharmonic oscillations

Landau–Lifshitz §28 is treated in two independent parts: the normal form of
the formal Hamiltonian, and the frequency of the solutions.

The formal part is in `SmoothAlgebra/FormalSeries`, described in the
[C∞-ring guide](smooth-algebra.md#formal-power-series-in-q-and-p):
`exists_birkhoff_normal_form` is the Birkhoff normal form in one degree of
freedom. `Oscillations/AnharmonicNormalForm` applies it to the oscillator.

- `hamiltonian ν a b` is `ν I + a q³ + b q⁴` with `I = (q² + p²)/2`.
  `generator₃` and `generator₄` are explicit polynomials of degree three and
  four: `lieExp_generator₃` and `lieExp_generator₄` state that their Lie
  transforms carry the Hamiltonian to `ν I + c₂ I²` up to terms of the order
  five, with `c₂ = secondCoefficient ν a b = 3b/2 − 15a²/(4ν)`.
- `exists_normal_form`: a Poisson automorphism carries `hamiltonian ν a b` to
  `h(I)` with `h = ν x + c₂ x² + ⋯`. The degrees from five on are normalized
  by `FormalSeries.exists_normal_form_of_resonant`, which does not change the
  lower degrees.
- `physicalHamiltonian ν α β` is `p²/2 + ν² q²/2 + α q³/3 + β q⁴/4`, the
  Hamiltonian of `ẍ + ν² x = −α x² − β x³`. `scale_physicalHamiltonian`: the
  canonical scaling `q ↦ q/√ν`, `p ↦ √ν p` carries it to
  `hamiltonian ν (α/3ν^{3/2}) (β/4ν²)`. `exists_normal_form_physical`: its
  normal form is `h = ν x + (3β/8ν² − 5α²/12ν⁴) x² + ⋯`.
- `two_mul_coefficient_mul_action`: at the action `I = ν ρ²/2` of an
  oscillation of amplitude `ρ`, the correction `2 c₂ I` of the formal
  frequency `h′(I)` is `(3β/8ν − 5α²/12ν³) ρ²`.

The part on solutions is `OneDimension/Anharmonic`, for the potential
`potential ν α β x = ν² x²/2 + α x³/3 + β x⁴/4` with `ν > 0`. It uses the
wells of [Motion in one dimension](#motion-in-one-dimension-wells) and not the
normal form.

- `wellFactor_potential`: the second divided difference of the potential is
  the polynomial `factor ν α β a b x`.
- `exists_slope`, `potential_centre`: by the implicit function theorem there
  is a smooth function `e` of `s = ρ²` near zero, with `e(0) = −α/3ν²`, such
  that the potential takes the same value at `ρ² e(ρ²) ± ρ`. `exists_isWell`:
  for small `ρ > 0` these two points are the turning points of a well.
- `periodFunction ν α β e s` is half the integral over the angle of
  `kernel`, the sum of the rates of the level curve at the angles `θ` and
  `θ + π`, written with `symRoot P R = √(2P + 2√(P² − R))/√(P² − R)`, which is
  `1/√(P − r) + 1/√(P + r)` for `R = r²` (`inv_sqrt_add_inv_sqrt`). The
  kernel is a function of `s = ρ²` that is continuously differentiable at
  `s = 0`. `orbitPeriod_eq_periodFunction`: the period of the well of the
  half-width `ρ` is `periodFunction (ρ²)`.
- `periodFunction_zero`, `hasDerivAt_periodFunction`: the period function is
  `2π/ν` at zero, with the derivative `5πα²/6ν⁵ − 3πβ/4ν³` there.
  `hasDerivAt_frequency`: the derivative of `2π/T` in `ρ²` at zero is
  `3β/8ν − 5α²/12ν³`.
- `exists_tendsto_frequency`: there are a centre `c(ρ)` and `ρ₀ > 0` such that
  `c(ρ) ± ρ` are the turning points of a well for `0 < ρ < ρ₀`,
  `c(ρ)/ρ² → −α/3ν²`, and
  `(2π/T(ρ) − ν)/ρ² → 3β/8ν − 5α²/12ν³` as `ρ → 0`, where `T(ρ)` is
  `orbitPeriod` of that well. By `IsWell.position_add_period` every motion
  with that energy between the turning points repeats after `T(ρ)`.

The expansion of the solution in harmonics, the uniqueness of the normal form
and a comparison of the truncated normal form with solutions are not treated.

## The action variable of an oscillator with a variable frequency

`Oscillations/Adiabatic` gives the exact part of Landau–Lifshitz §49. For
functions of time `ω` and `ωinv` with `ω ωinv = 1`, `Parametric.action ω ωinv x`
is `I = (ẋ² + ω² x²)/2ω`.

- `Parametric.timeDerivative_inv`: `d(1/ω)/dt = −ω̇/ω²`.
- `Parametric.timeDerivative_action`: along a solution of `ẍ + ω(t)² x = 0`,
  `İ = (ω̇/2ω²)(ω² x² − ẋ²)`.
- `Parametric.timeDerivative_action_of_const`: `I` is constant when `ω` is.

The derivative of `I` is proportional to `ω̇`, and its second factor
oscillates about zero. The adiabatic theorem, that the change of `I` stays
small over a long time when `ω` varies slowly, is the subject of the next
section.

## Adiabatic invariance

`Oscillations/AdiabaticOscillator` proves the adiabatic theorem of
Landau–Lifshitz §49 for the oscillator `ẍ + Ω(εt)² x = 0`. A motion is a pair
of functions `x`, `v` with `ẋ = v` and `v̇ = −Ω(εt)² x` on `[0, T/ε]`.

- `action ω x v` is `I = (v² + ω² x²)/2ω`, with `|x v| ≤ I`
  (`abs_mul_le_action`).
- `hasDerivAt_action`: along a motion `İ = ε a(εt) (ω² x² − v²)` with
  `a = Ω′/2Ω²` (`coefficient`). `hasDerivAt_correctedAction`: the corrected
  action `I + ε a(εt) x v` has the derivative `ε² a′(εt) x v`.
- `exists_forall_abs_action_sub_le`: if `Ω` is twice continuously
  differentiable and positive on `[0, T]`, there is a constant `C` such that
  for every `ε > 0` and every motion `|I(t) − I(0)| ≤ C ε I(0)` for
  `0 ≤ t ≤ T/ε`. `exists_forall_abs_action_sub_le_exp` is the case
  `Ω = exp`, and by `action_eq_of_const` the action is constant when the
  frequency is.

`OneDimension/WellFamily` treats a smooth family `V(s, x)` of potentials with a
parameter `s` in a space of finite dimension and a smooth level `ℰ(s)`.

- `contDiff_wellFactor_family`: the factor of the well is smooth in the
  parameter, the two points and the position together.
  `IsWell.exists_family_param`: the turning points of a well of one parameter
  extend to smooth functions `α`, `β` of the parameter on an open set, with
  wells between them.
- `contDiffOn_orbitRate_family`, `contDiffOn_orbitMomentum_family_param`: the
  rate and the momentum on the level curves are smooth in the parameter and
  the angle. Hence the period, the area and the integral over a period of a
  smooth function of the parameter and the position are smooth functions of
  the parameter (`contDiffOn_orbitPeriod_family`, `contDiffOn_orbitArea_family`,
  `contDiffOn_integral_orbitRate_mul`).
- `hasDerivAt_orbitArea_family`: for a real parameter `r`,
  `dA/dr = ∮ (ℰ′ − ∂V/∂r) dt`. `fderiv_orbitArea_family`: in general the
  derivative of the area in a direction `u` of the parameter is
  `∮ (dℰ(u) − ∂V/∂s (u)) dt`. For a potential that does not depend on the
  parameter and `ℰ(E) = E` this is `dA/dE = T`.

`OneDimension/AdiabaticInvariant` treats `H = p²/2m + V(λ, x)`; a point is
`w = ((x, p), λ)`.

- `IsWellFamily V J α β`: a smooth family of wells of the potentials
  `V(λ, ·)` over an open set `J` of pairs `(E, λ)`. `exists_isWellFamily`: a
  well of one potential extends to such a family.
- `period`, `area`, `parameterForce`: the period `T`, the area `A` and
  `∮ ∂V/∂λ dt` as smooth functions on `J`, with
  `dA = T dE − (∮ ∂V/∂λ dt) dλ` (`fderiv_area`).
- `invariant` is the action variable `I(w) = A(H(w), λ)/2π`.
  `fderiv_invariant_frozenField`: its derivative along the field
  `frozenField` of the motion with a fixed parameter is zero.
  `fderiv_invariant_parameter`: its derivative in the parameter is
  `invariantDeriv = (T ∂V/∂λ − ∮ ∂V/∂λ dt)/2π`.
- `exists_orbit`: through each point of `wellRegion`, the set of the points on
  the level curves of the family, there is a motion with the fixed parameter.
  It stays on the level curve, has the period `T`, and the integral of
  `∂V/∂λ` along a period is `parameterForce`.
- `corrector` is `T ∫₀¹ σ ∂I/∂λ (Φ_{Tσ} w) dσ`, with `Φ` the flow of
  `extendedField`, the field with the parameter held fixed. It is smooth at
  the points of `wellRegion` (`contDiffAt_corrector`), and its derivative along
  `frozenField` is `invariantDeriv` (`fderiv_corrector_frozenField`, from
  `hasDerivAt_weighted_shift` and the vanishing mean of `∂I/∂λ` over a
  period).
- `exists_forall_abs_invariant_sub_le`: for a compact subset `K` of
  `wellRegion` and `Λ` twice continuously differentiable there is `C` such
  that for every `ε > 0` a motion `ż = frozenField (z, Λ(εt))` that stays in
  `K` on `[0, T/ε]` has `|I(t) − I(0)| ≤ C ε` there.
- `isWellFamily_oscillator`, `invariant_oscillator`: for `V(k, x) = k x²/2`
  the oscillators of all positive stiffnesses and energies form a family, and
  `I = E √(m/k)`.

The estimate itself is `SlowParameter.abs_sub_le_of_corrector` of the
[geometry guide](smooth-geometry.md). The hypothesis that the motion stays in
`K` is not derived from the initial point. Several parameters, the
neighbourhoods of an equilibrium and of a separatrix, and several degrees of
freedom are not treated.

## A non-holonomic constraint

`KnifeEdge` treats the standard example of Landau–Lifshitz §38: a blade that
touches a plane at `(x, y)` and makes the angle `θ` with the `x`-axis, with
the constraint `ẋ sin θ − ẏ cos θ = 0`. `Configuration` is the free C∞-ring
on the three co-ordinates, and `cosθ`, `sinθ` are obtained by the operations
of the ring.

- `along` is `cos θ ∂ₓ + sin θ ∂_y`, `turn` is `∂_θ` and `across` is
  `−sin θ ∂ₓ + cos θ ∂_y`. `constraint_along`, `constraint_turn`,
  `constraint_across`: the first two fields satisfy the constraint, and the
  third has the value `−1`.
- `commutator_turn_along`: `[turn, along] = across`. The admissible fields
  are not closed under the commutator.
- `eq_algebraMap_of_along_eq_zero_of_turn_eq_zero`: a function annihilated by
  `along` and `turn` is a constant. No equation between the co-ordinates
  follows from the constraint.

A holonomic constraint is a ring presented by equations. It is the quotient of
the free ring by the ideal of the equations
([quotients by ideals](smooth-algebra.md#hadamards-lemma-and-quotients-by-ideals)),
and its states are those of
[the shared algebra](smooth-algebra.md#points-and-tangent-vectors).
The equations of motion with reactions are not treated.

## Rutherford's formula

`Rutherford` proves the identities of Landau–Lifshitz §19 between real
numbers. `eccentricity_sq_sub_one`: `2 E M²/m α² = (m v² ρ/α)²` for
`E = ½ m v²` and `M = m ρ v`. `cot_half_eq`: if `sin (χ/2) = 1/e`,
`0 < χ < π` and `e² − 1 = k²` with `k ≥ 0`, then `cot (χ/2) = k`.
`hasDerivAt_impactParameter` and `rutherford`: for `ρ(χ) = a cot (χ/2)`,
`ρ |dρ/dχ| / sin χ = (a/2)² / sin⁴ (χ/2)`. The angle of deflection as a limit
along the orbit and the cross-section as a measure are in the next section.

## Scattering

`Mechanics/Scattering` treats Landau–Lifshitz §§18–19 for a motion in a
central field, described in the plane of the orbit by the radius `r(t)` and
the polar angle `φ(t)`, with `ṙ² = F(r)` and `φ̇ = ℓ/r²`. Here `ℓ = M/m` and
`F(r) = (2/m)(E − U(r)) − ℓ²/r²`.

`Scattering/RadialMotion`: `IsFactor W r₀ C` states that `W` is smooth,
positive and at most `C` along `r = r₀ + s²`; then `F(r) = (r − r₀) W(r)` has
the simple turning point `r₀`.

- `parameter W r₀` is the solution of `ṡ = ½ √W(r₀ + s²)` with `s(0) = 0`,
  defined for all times, odd and strictly increasing; `radius W r₀ t` is
  `r₀ + s(t)²` and `radialVelocity` is `2 s ṡ`.
- `IsFactor.radialVelocity_sq`: `ṙ² = (r − r₀) W(r)`.
  `IsFactor.radialVelocity_pos`: `ṙ > 0` for `t > 0`. `IsFactor.radius_neg`:
  the radius is an even function of the time.
  `IsFactor.tendsto_radius_atTop`: `r → ∞`.
- `IsFactor.hasDerivAt_radialVelocity`: `r̈ = F′(r)/2`, for `F` differentiable
  on `[r₀, ∞)` with `F(r) = (r − r₀) W(r)` there.
- `exists_isFactor_dividedDifference`: a smooth `G` with `G(r₀) = 0`,
  `G′(r₀) > 0`, positive and bounded after `r₀`, has the factor
  `dividedDifference G (r, r₀)`.
- `angle W r₀ ℓ t = ∫₀ᵗ ℓ/r²`, an odd function of the time.

`Scattering/Deflection`: statements about a given motion after the closest
approach, with `r(0) > 0`, `ṙ > 0` and `ṙ² = F(r)` for `t > 0`.

- `angleDensity ℓ F ρ = (ℓ/ρ²)/√F(ρ)`.
  `integral_angleDensity_eq`: the density is integrable on `(r(0), r(T)]`, and
  its integral there is `φ(T) − φ(0)`.
- `tendsto_angle_atTop`: if `r → ∞` and the density is integrable on some
  `(R, ∞)`, it is integrable on `(r(0), ∞)` and
  `φ(t) → φ(0) + ∫_{r(0)}^∞ (ℓ/ρ²) dρ/√F(ρ)` (Landau–Lifshitz (18.4)).
  `integrableOn_angleDensity_Ioi`: the hypothesis holds if `F` is continuous
  and at least `c² > 0` on `[R, ∞)`.
- `deflectionAngle ℓ F r₀ = π − 2 ∫_{r₀}^∞ (ℓ/ρ²) dρ/√F(ρ)`.

`Scattering/Asymptote`: `position` and `velocity` are the motion in the plane.

- `IsFactor.tendsto_angle_atTop`, `IsFactor.tendsto_angle_atBot`: the angle of
  the motion `radius W r₀` tends to `± φ₀`.
- `IsFactor.hasDerivAt_position`, `IsFactor.hasDerivAt_velocity`: the velocity
  is the derivative of the position, and the acceleration is
  `(F′(r)/2 − ℓ²/r³) (cos φ, sin φ)`, which is `−(U′(r)/m) (cos φ, sin φ)`.
  `position_cross_velocity`: the moment of the velocity is `ℓ`.
- `IsFactor.tendsto_velocity_atTop`, `IsFactor.tendsto_velocity_atBot`: if
  `ṙ → v∞` and `φ → φ₀` as `t → ∞`, the velocity tends to
  `v∞ (cos φ₀, sin φ₀)` as `t → ∞` and to `v∞ (−cos φ₀, sin φ₀)` as
  `t → −∞`. `asymptote_inner`: the scalar product of these is
  `v∞² cos (π − 2φ₀)`. `arccos_cos_deflection`: the angle between the two
  velocities, `arccos (cos (π − 2φ₀))`, is `|π − 2φ₀|` when `|π − 2φ₀| ≤ π`.
  For a motion that turns further round the centre `χ = π − 2φ₀` is the
  unwrapped angle: with `φ₀ = 3π/2` the two velocities coincide.

`Scattering/Coulomb`: `U = α/r`, with `a = α/m v∞²` of either sign.

- `speedSq a ρ v∞ r = v∞² (1 − 2a/r − ρ²/r²)`, `closest a ρ = a + √(a² + ρ²)`,
  and `isFactor`: the motion exists for all times.
  `hasDerivAt_velocity`: its acceleration is `(v∞² a/r²) (cos φ, sin φ)`.
- `integral_angleDensity`: `φ₀ = arccos (a/√(a² + ρ²))`, from the primitive
  `arccos ((ρ²/r + a)/√(a² + ρ²))`.
  `tendsto_angle_atTop`, `tendsto_velocity_atTop`, `tendsto_velocity_atBot`.
- `deflection a ρ = π − 2 arccos (a/√(a² + ρ²))`, with
  `sin (χ/2) = a/√(a² + ρ²)`, `cos (χ/2) = ρ/√(a² + ρ²)` and
  `cot (χ/2) = ρ/a` (`cot_half_deflection`, Landau–Lifshitz (19.1)).

`Scattering/CrossSection`: `impactMeasure` is `2πρ dρ` on `ρ > 0`,
`solidAngle` is `2π sin χ dχ` on `0 < χ < π`, and `crossSection χ` is the
push-forward of `impactMeasure` by a deflection function `χ`.

- `crossSection_apply`: for a measurable `A ⊆ (0, π)` and a function `b` that
  is injective and differentiable on `A` with `χ⁻¹(A) ∩ (0, ∞) = b(A)`,
  `crossSection χ A = ∫_A (b |b′|/sin χ) dΩ` (Landau–Lifshitz (18.8)).
- `Coulomb.deflection_impact`, `Coulomb.impact_deflection`: `a cot (χ/2)` is
  the inverse of the deflection function of a repulsive Coulomb field.
- `Coulomb.crossSection_coulomb`: Rutherford's formula,
  `crossSection (deflection a) A = ∫_A (a/2)²/sin⁴ (χ/2) dΩ` for `a > 0`;
  `Coulomb.crossSection_coulomb_abs` is the statement for either sign, in the
  magnitude of the angle.

The deflection function of a general potential as a function of the impact
parameter, several branches, the laboratory system and small-angle scattering
are not treated.

## The phase volume of the oscillator

`Oscillations/PhaseVolume`: the flow matrix of the oscillator has determinant
one, so it preserves the Lebesgue measure of the phase plane
(`Oscillator.map_flowMatrix_volume`, `Oscillator.measurePreserving_flowMatrix`).
This is Liouville's theorem (Landau–Lifshitz §46) for a linear flow in the
plane. The theorem for the flow of every Hamiltonian of the free C∞-ring is in
[Hamiltonian flows](#hamiltonian-flows-and-liouvilles-theorem).

## Canonical formalism

`Mechanics/Legendre` treats the Legendre transformation of the natural
Lagrangian `L = Σᵢ ½ mᵢ q̇ᵢ² − U(q)` (Landau–Lifshitz §40). A potential is an
element `u` of the free C∞-ring on the positions; `positionsToJet u` reads it
in the jet ring and `positionsToPhase u` on the phase space.

- `legendre m` is the morphism from the phase space to the jet ring with
  `qᵢ ↦ qᵢ` and `pᵢ ↦ mᵢ q̇ᵢ`. It takes `pᵢ` to the momentum `∂L/∂q̇ᵢ`
  (`legendre_p_eq_momentum`) and, for non-zero masses, the Hamiltonian
  `Σᵢ pᵢ²/2mᵢ + U` to the energy of `L` (`legendre_hamiltonian`).
- `isSolution_natural_iff`, `isTrajectory_natural_iff`: Newton's equations
  `mᵢ γ̈ᵢ = −(∂ᵢu)(γ)` and Hamilton's equations along curves.
- `isTrajectory_natural_iff_isSolution`: a curve of the phase space is a
  trajectory of the Hamiltonian exactly when its positions solve the
  Euler–Lagrange equations of `L` and `pᵢ = mᵢ q̇ᵢ`.

`Mechanics/Hyperregular` proves Theorem 51 of the manuscript for a general
Lagrangian `L(q, v)`, an element of `VelocitySpace ι`, the free C∞-ring on the
positions `q i` and the velocities `v i`.

- `VelocitySpace.momentum L i` is `∂L/∂vᵢ`, `energy L` is `Σ vᵢ ∂L/∂vᵢ − L`,
  and `legendre L` is the morphism `FL` from the phase space with `qᵢ ↦ qᵢ`
  and `pᵢ ↦ ∂L/∂vᵢ`. `IsHyperregular L G` says that `G` is an inverse
  morphism of `FL`, and `hamiltonian L G` is `G (energy L)`.
- `IsHyperregular.inverseHessian_mul_hessian`: the matrix `∂²L/∂vᵢ∂vⱼ`
  (`hessian L`) is invertible over the ring, with the inverse
  `FL(∂(G vₖ)/∂pᵢ)`.
- `IsHyperregular.legendre_hamiltonian`: `FL(H) = E`.
  `legendre_partialDerivation_inr_hamiltonian`: `FL(∂H/∂pᵢ) = vᵢ`.
  `legendre_partialDerivation_inl_hamiltonian`: `FL(∂H/∂qᵢ) = −∂L/∂qᵢ`.
- `toJet` reads a function of the positions and the velocities in the jet
  ring, and `velocityCurve γ` is the curve `(γ, γ̇)`. `isSolution_toJet_iff`:
  a path solves the Euler–Lagrange equations of `L` exactly when
  `d/dt (∂L/∂vᵢ) = ∂L/∂qᵢ` along it.
- `IsHyperregular.isTrajectory_iff_isSolution`: a curve of the phase space is
  a trajectory of `H` exactly when its positions solve the Euler–Lagrange
  equations of `L` and `pᵢ = ∂L/∂vᵢ` along it.
- `lagrangeBracket L G` is the canonical bracket transported by `FL`
  (`IsHyperregular.legendre_bracket`). `lagrangeBracket_q_q`: `{qᵢ, qⱼ} = 0`.
  `lagrangeBracket_q_v`: `{qᵢ, vⱼ}` is the entry of the inverse of
  `∂²L/∂v∂v`. `lagrangeBracket_q_energy`: `{qᵢ, E} = vᵢ`.
- `isHyperregular_natural`, `hamiltonian_natural`: for non-zero masses the
  natural Lagrangian `natural m u` is hyperregular with the inverse
  `vᵢ ↦ pᵢ/mᵢ`, and its Hamiltonian is `Σ pᵢ²/2mᵢ + U`. `toJet_natural`
  identifies it with the natural Lagrangian of the jet ring.

Hyperregularity is a hypothesis: no criterion for the existence of the
inverse morphism is proved. The Lagrangian does not depend explicitly on
time, and the form `ω_L` is represented by the transported bracket.

`Poisson/GeneratingFunction` treats canonical transformations given by a
generating function `F(q, Q)` of the old and the new positions
(Landau–Lifshitz §45). `F` is an element of `PositionPair ι`, the free C∞-ring
on `oldPosition i` and `newPosition i`; `gradOld` and `gradNew` are the
gradients with respect to the two groups of variables.

- `oldMap F` is the morphism from the phase space with `qᵢ ↦ qᵢ` and
  `pᵢ ↦ ∂F/∂qᵢ`; `newMap F` is the one with `Qᵢ ↦ Qᵢ` and `Pᵢ ↦ −∂F/∂Qᵢ`.
  `IsFree F G` says that `G` is an inverse morphism of `oldMap F`, and
  `transformation F G = G ∘ newMap F` expresses a function of `(Q, P)` in the
  variables `(q, p)`.
- `IsFree.inverseMixed_mul_mixedHessian`: the mixed matrix `∂²F/∂qₖ∂Qₗ` is
  invertible over the ring; its inverse `B` is the matrix `∂Qⱼ/∂pₖ`.
- `IsFree.oldMap_bracket`: in the co-ordinates `(q, Q)` the canonical bracket
  is `{x, y} = ∂x/∂q · (∂y/∂Q · B) − (∂x/∂Q · B) · ∂y/∂q`.
- `IsFree.isPoissonHom_transformation`: the transformation is a Poisson
  morphism, that is, `{Qᵢ, Qⱼ} = 0`, `{Qᵢ, Pⱼ} = δᵢⱼ` and `{Pᵢ, Pⱼ} = 0` as
  functions of `(q, p)`. If `newMap F` also has an inverse `G'`, the
  transformation has the inverse `G' ∘ oldMap F`
  (`IsFree.transformation_comp_inverse`, `IsFree.inverse_comp_transformation`).
- `exchange` is `Σ qᵢ Qᵢ`. It is free with `G` the identity
  (`isFree_exchange`), and its transformation is `Qᵢ = pᵢ`, `Pᵢ = −qᵢ`
  (`transformation_exchange_q`, `transformation_exchange_p`).

The generating function does not depend on time, and only the first kind
`F(q, Q)` is treated. That the mixed matrix is invertible is a consequence of
the hypothesis; the converse, which needs the inverse function theorem, is not
proved.

`Poisson/CompleteIntegral` proves Jacobi's theorem (Landau–Lifshitz §47). The
functions of the co-ordinates `q`, of as many parameters `α` and of the time
form the free C∞-ring `ActionSpace ι`. For `S` in this ring,
`substitution S` is the morphism `qᵢ ↦ qᵢ`, `pᵢ ↦ ∂S/∂qᵢ` from the phase
space, and `IsHamiltonJacobi H S` is the equation
`∂S/∂t + H(q, ∂S/∂q) = 0`. `along Q α` evaluates along a curve `q(t)` with
fixed parameters.

- `isTrajectory_of_isHamiltonJacobi`: if `S` satisfies the Hamilton–Jacobi
  equation, every `∂S/∂αᵢ` has zero time derivative along the curve, and the
  matrix `∂²S/∂αᵢ∂qₖ` along the curve has no kernel, then `q(t)` with the
  momenta `pᵢ = ∂S/∂qᵢ` is a trajectory of `H`.
- `isHamiltonJacobi_freeAction`, `isTrajectory_freeAction`: for the free
  particle, `S = α q − α² t / 2m` satisfies the equation, and the theorem
  gives the uniform motion `q = β + (α/m) t`.

The curve is a hypothesis of the theorem: solving `∂S/∂αᵢ = βᵢ` for `q(t)` by
the implicit function theorem is not proved. The Hamiltonian has no explicit
dependence on time.

`Poisson/Separation` treats the separation of the variables (Landau–Lifshitz
§48). `positionsToAction ι u` reads a function `u` of the co-ordinates as a
function of `(q, α, t)`, and `parameter i` is `αᵢ`.

- `stackelHamiltonian m Ψ g u` is `Σᵢ Ψᵢ(q) (gᵢ(q) pᵢ²/2m + uᵢ(q))`.
  `isHamiltonJacobi_stackel`: if `Σᵢ Ψᵢ Φᵢⱼ = δⱼ,ⱼ₀` for a matrix `Φ` of
  functions of the co-ordinates, and the derivatives of `S` satisfy
  `gᵢ (∂S/∂qᵢ)²/2m + uᵢ = Σⱼ Φᵢⱼ cⱼ` and `∂S/∂t = −cⱼ₀` for separation
  constants `cⱼ`, then `S` satisfies the Hamilton–Jacobi equation. The
  separation constants are functions of the parameters and not the parameters
  themselves: for a positive mass the left side is bounded below, and a
  parameter takes every real value.
- `nestedHamiltonian m ρ σ a b c` is
  `p₀²/2m + a + ρ (p₁²/2m + b + σ (p₂²/2m + c))`.
  `isHamiltonJacobi_nested_of_separated`: the equations
  `(∂S/∂q₀)²/2m + a = E − ρ β`, `(∂S/∂q₁)²/2m + b = β − σ γ`,
  `(∂S/∂q₂)²/2m + c = γ` and `∂S/∂t = −E` give a solution. In spherical
  co-ordinates `ρ = 1/r²` and `σ = 1/sin²θ`.
- `liouvilleHamiltonian m λ g₀ g₁ κ₀ κ₁ u₀ u₁ u₂` is
  `λ (g₀ p₀²/2m + u₀ + g₁ p₁²/2m + u₁ + (κ₀ + κ₁)(p₂²/2m + u₂))`.
  `isHamiltonJacobi_liouville_of_separated`: with `λ (w₀ + w₁) = 1`, the
  equations `g₀ (∂S/∂q₀)²/2m + u₀ = w₀ E + β − κ₀ γ`,
  `g₁ (∂S/∂q₁)²/2m + u₁ = w₁ E − β − κ₁ γ`, `(∂S/∂q₂)²/2m + u₂ = γ` and
  `∂S/∂t = −E` give a solution. This is the form in parabolic and in
  elliptic co-ordinates.
- `linearAction E` is `Σ αᵢ qᵢ − E t`, and `quadraticEnergy w` is `Σ wᵢ αᵢ²`.
  `isHamiltonJacobi_nested_freeAction`: the free particle
  `(p₀² + p₁² + p₂²)/2m` is an instance of the nested form, with
  `E = Σ αᵢ²/2m`, `β = (α₁² + α₂²)/2m` and `γ = α₂²/2m`.
  `isHamiltonJacobi_liouville_freeAction` is an instance of the form of
  Liouville. So the hypotheses of both theorems can be satisfied.

`Poisson/ActionFunction` gives the relation `dS = p dq − H dt` of
Landau–Lifshitz §43 along curves: for a solution `S` of the Hamilton–Jacobi
equation and any curve `q(t)`,
`IsHamiltonJacobi.timeDerivative_along` is `dS/dt = Σ pᵢ q̇ᵢ − H(q, p)` with
`pᵢ = ∂S/∂qᵢ`.

`EndpointAction` gives the same relation for the action integral of a given
family of paths `q(s, t)` whose end times `a(s)`, `b(s)` move with the
parameter. `pathEnergy L q t` is `p · q̇ − L` along a path.
`hasDerivAt_action_movingEndpoints_on`: if the path of the parameter `s₀`
solves the Euler–Lagrange equation between its end times, the derivative of
`s ↦ ∫ L dt` at `s₀` is

`[p · d/ds q(s, b(s)) − E · b′] − [p · d/ds q(s, a(s)) − E · a′]`.

The family is smooth on an open set `U` that contains the reference segment
`{s₀} × [a(s₀), b(s₀)]`, and the Lagrangian on an open set `W` of the jet
space that contains the jet of the reference path. The other paths of the
family need not solve the equation. `hasDerivAt_action_movingEndpoints` is the
case `U = W = univ`, and `hasDerivAt_action_natural_movingEndpoints_on` the
case of one co-ordinate with a potential, with Newton's equation as the
hypothesis. The proof uses `Variational.hasDerivAt_intervalIntegral_moving_on`
(Leibniz's rule with moving limits), the symmetry of the second derivative of
the family, and an integration by parts along the reference path.

- `hasDerivAt_action_free_endpoint`: the paths `t ↦ (x + sξ) t / (T + sτ)` of
  a free particle from the origin to the point `x + sξ` at the time `T + sτ`,
  for `T ≠ 0`. The derivative of the action is `(m x / T) ξ − (m x² / 2T²) τ`,
  that is, `dS = p dx − E dT` for `S = m x² / 2T`.
- `hasDerivAt_action_oscillator_endpoint`: the paths
  `t ↦ (x + sξ) sin ωt / sin ω(T + sτ)` of the oscillator, for `sin ωT ≠ 0`.
  The derivative is `m ω x cot ωT · ξ − m ω² x² / (2 sin² ωT) · τ`. At the
  conjugate times `sin ωT = 0` the family does not exist.
- `hasDerivAt_action_oscillator_family`: the motions
  `(A + sα) cos ωt + (B + sβ) sin ωt` with the time of arrival `T + sτ`.

The families are given. For the flow of a Hamiltonian the families exist, and
the action is a function of the end point away from conjugate points; see
[the action along the flow](#the-action-along-the-flow-of-a-hamiltonian).

The coefficient functions of `Poisson/Separation` are elements of the free
C∞-ring, smooth on all of `ℝ³`. The coefficients `1/r²`, `1/sin²θ` and `1/(ξ + η)` of the classical
co-ordinate systems are smooth only on open subsets, so those systems are not
instances as stated. The quadratures that give `S` are not constructed, and
the completeness of the integral is not checked.

`Poisson/Liouville` defines the divergence `Σₐ ∂ₐ (X xₐ)` of a vector field on
a free C∞-ring with finitely many generators. `divergence_hamiltonian`: a
Hamiltonian vector field of the canonical bracket has zero divergence, the
infinitesimal form of Liouville's theorem (Landau–Lifshitz §46).
`divergence_dissipativeField`: with friction the divergence is
`−Σᵢ ∂fᵢ/∂pᵢ`, and for the oscillator with the friction coefficients `aᵢ` it
is the constant `−Σᵢ aᵢ/mᵢ` (`Oscillator.divergence_dissipativeField`).

### Hamiltonian flows and Liouville's theorem

`Poisson/HamiltonianField` connects these algebraic statements with the flow
of a vector field on `ℝ²ⁿ`, which the [geometry guide](smooth-geometry.md)
constructs.

- `realCurve c t` is the point `(cₐ(t))ₐ` of a family of smooth functions of
  time. `isIntegralCurve_iff_hasDerivAt` and `isTrajectory_iff_hasDerivAt`: the
  family is an integral curve of a derivation `D`, or a trajectory of a
  Hamiltonian, if and only if the real curve solves `ż = X(z)` for the field
  `X = FreeSmoothRing.realField D`.
- `traceCLM_fderiv_realField`: the trace of `DX(z)` is the value at `z` of the
  divergence `Σₐ ∂ₐ (D xₐ)`.
- `hamiltonianField H` is the field `(∂H/∂p, −∂H/∂q)` of the canonical bracket
  (`hamiltonianField_inl`, `hamiltonianField_inr`). It is smooth, and its
  divergence is zero (`traceCLM_fderiv_hamiltonianField`).
- `volume_image_hamiltonianFlow`: Liouville's theorem. For a measurable set
  `A` of the phase space whose points have the time `t` in the domain of the
  flow, the image of `A` under the flow of the time `t` has the Lebesgue
  measure of `A`. `measurePreserving_hamiltonianFlow`: a flow defined for all
  times and points is measure preserving.
- `IsTrajectory.flow_eq`: a trajectory is a line of the flow, so the flow is
  defined for all times at its points. `exists_isTrajectory`: if the flow is
  defined for all times and points, there is a trajectory through every point.

`Poisson/LiouvilleFlow` gives flows that are defined for all times.

- `Oscillator.flowDomain_hamiltonianField`,
  `Oscillator.measurePreserving_hamiltonianFlow`: the oscillator with any
  number of co-ordinates.
- `Pendulum.hamiltonian m k` is `Σ pᵢ²/2mᵢ − k Σ cos qᵢ`. Its field
  `(pᵢ/mᵢ, −k sin qᵢ)` is not linear and has linear growth, so the flow is
  defined for all times and points (`Pendulum.flowDomain_hamiltonianField`),
  it preserves the measure (`Pendulum.measurePreserving_hamiltonianFlow`), and
  there is a motion through every point (`Pendulum.exists_isTrajectory`).
- `Oscillator.volume_image_dissipativeFlow`: with the friction coefficients
  `aᵢ` the flow multiplies the Lebesgue measure of every measurable set by
  `exp (−Σᵢ aᵢ/mᵢ · t)`.

The Hamiltonian is an element of the free C∞-ring, smooth on all of `ℝ²ⁿ`,
and does not depend on the time.

### The action along the flow of a Hamiltonian

`Poisson/PhaseAction` treats the action `∫ (Σᵢ pᵢ q̇ᵢ − H) dt` of a curve in
the phase space. `liouvilleForm ι` is the form `θ = Σᵢ pᵢ dqᵢ`, as a bilinear
form of the point and the vector, and `phaseLagrangian H` is the Lagrangian
`θ_z(ż) − H(z)` on the phase space. Its momentum is `θ`
(`momentum_phaseLagrangian`), its energy is `H` (`pathEnergy_phaseLagrangian`),
and its Euler–Lagrange equations hold along a solution of Hamilton's
equations (`eulerLagrange_phaseLagrangian`).

- `hamiltonian_flow_eq`: the Hamiltonian is constant along its flow, also
  when the flow is not defined for all times. It is an instance of
  `SmoothGeometry.NonlinearODE.flow_invariant`.
- `hasDerivAt_action_hamiltonianFlow`: Proposition 49. For a curve of initial
  points `z₀(s)` and moving times `a(s)`, `b(s)`, the derivative of the action
  of the solutions `t ↦ Φ(t, z₀(s))` is
  `[θ(d/ds Φ(b, z₀)) − H b′] − [θ(d/ds Φ(a, z₀)) − H a′]`. The solutions are
  those of the flow, and the only hypothesis is that the times between `a(s₀)`
  and `b(s₀)` are in its domain at the point `z₀(s₀)`.

`Poisson/SymplecticFlow`: `symplecticForm ι` is `ω = Σᵢ dqᵢ ∧ dpᵢ`. The
derivative of a Hamiltonian field paired with `ω` is the Hessian of the
Hamiltonian (`symplecticForm_fderiv_hamiltonianField`), which is symmetric, so
`ω(DX u, v) + ω(u, DX v) = 0`. By the variational equation,
`symplecticForm_fderiv_flow`: `ω(D_zΦ u, D_zΦ v) = ω(u, v)` at every time and
point of the domain. The map of the flow at every time is a canonical
transformation.

`Poisson/LocalAction` constructs the action as a function of the co-ordinates
and the time (Landau–Lifshitz §43). Fix an initial position `q₀`.
`endPosition H q₀ (T, p)` and `endMomentum H q₀ (T, p)` are the position and
the momentum at the time `T` of the solution that starts at `q₀` with the
momentum `p`.

- `exists_initialMomentum`: if the derivative of `p ↦ endPosition H q₀ (T₀, p)`
  at `p₀` is invertible, there are an open set `W` of times and end points
  around `(T₀, q₁)`, with `q₁` the position reached, and a smooth function
  `P₀` on `W` such that the solution from `q₀` with the momentum `P₀(T, q)`
  reaches `q` at the time `T`.
- `exists_localAction`: the action `localAction H q₀ P₀` of that solution is
  differentiable on `W`, and its derivative at `(T, q)` is
  `(τ, ξ) ↦ Σᵢ pᵢ ξᵢ − H(q, p) τ` with `p` the momentum at the end point
  (`actionDifferential`).
- `localAction_hamiltonJacobi`: for a function with this derivative,
  `∂S/∂T + H(q, ∂S/∂q) = 0`.
- `exists_localAction_kineticEnergy`: for a free particle with non-zero masses
  the hypothesis holds at every time `T ≠ 0`
  (`isInvertible_fderiv_endPosition_kineticEnergy`); the flow is the uniform
  motion (`flow_kineticEnergy`).

The hypothesis says that the end point is not conjugate to `q₀` along the
solution. The action function is defined on an open set and is not an element
of a free C∞-ring, so it is not an instance of
`CompleteIntegral.IsHamiltonJacobi`. A Lagrangian that is not given through a
Hamiltonian is treated in `EndpointAction`, for given families.

## Reduction and the Routhian

`Poisson/CyclicReduction` treats Example 62(d) of the plan, the reduction with
respect to cyclic co-ordinates at fixed values of their momenta. The phase
space has the co-ordinates `q_i`, `p_i` for `i : ι` and `q_k`, `p_k` for
`k : κ`, and `momentumIdeal ι c` is the ideal `(p_k − c_k)`.

- `isCoisotropic_momentumIdeal`: the ideal is coisotropic.
- `mem_normalizer_iff`: `f` is in the normalizer exactly when the derivatives
  `∂f/∂q_k` are in the ideal.
- `inclusion ι κ` is the phase space of the remaining co-ordinates in the full
  phase space, a Poisson morphism with values in the normalizer.
  `restriction ι c` is a function at `q_k = 0`, `p_k = c_k`.
- `sub_inclusion_restriction_mem`: an element of the normalizer agrees modulo
  the ideal with its restriction.
- `reductionHom_bijective`, `isPoissonHom_reductionHom`,
  `reductionHom_restriction`: the reduced ring `N(I)/I` is the phase space of
  the remaining co-ordinates, and the class of `f` is its restriction.
- `mem_normalizer_of_cyclic`, `p_eq_algebraMap_of_cyclic`,
  `isTrajectory_restriction`: if the `q_k` are cyclic co-ordinates of `H`, then
  `H` is in the normalizer, the `p_k` are constant along a trajectory, and the
  remaining co-ordinates of a trajectory with `p_k = c_k` form a trajectory of
  the Hamiltonian at `p_k = c_k`.

The key step has two parts. By Hadamard's lemma, `f` agrees modulo the ideal
with `f` at `p_k = c_k` (`sub_fixMomenta_mem`). For `f` in the normalizer the
derivatives of that function in the `q_k` vanish, so it does not depend on the
`q_k`. The second part is `lift_eq_self_of_partialDerivation_eq_zero` of
`Constants`: a substitution fixes an element whose partial derivatives vanish
in the co-ordinates that the substitution changes. It is proved along a
segment, as the statement on constants.

`canonicalReductionHom_bijective` and its companions state the same reduction
for a Poisson C∞-ring `P` with an isomorphism `Φ` from the phase space, for
the ideal generated by the `Φ (p_k − c_k)`. The reduced mass uses this form.
`IsTrajectory.of_isPoissonHom` carries a trajectory back along a Poisson
morphism of free rings.

`Mechanics/Routhian` treats Landau–Lifshitz §41 for a Lagrangian `L(q, v)` in
`VelocitySpace (ι ⊕ κ)`. `RouthSpace ι κ` is the ring of functions of the
positions `q_a`, the velocities `v_i` and the momenta `p_k`.

- `partialLegendre L` is the morphism with `q_a ↦ q_a`, `v_i ↦ v_i` and
  `p_k ↦ ∂L/∂v_k`. `IsPartiallyHyperregular L G` says that `G` is an inverse
  morphism, and `routhian L G` is `G(Σ_k v_k ∂L/∂v_k − L)`.
- `IsPartiallyHyperregular.inversePartialHessian_mul_partialHessian`: the
  matrix `∂²L/∂v_k∂v_l` is invertible.
- `partialLegendre_partialDerivation_p_routhian`,
  `partialLegendre_partialDerivation_q_routhian`,
  `partialLegendre_partialDerivation_v_routhian`: `∂R/∂p_k = v_k`,
  `∂R/∂q_a = −∂L/∂q_a` and `∂R/∂v_i = −∂L/∂v_i`.
- `IsRouthTrajectory R c`: `q̇_i = v_i`, Lagrange's equations
  `d/dt (∂R/∂v_i) = ∂R/∂q_i`, and Hamilton's equations `q̇_k = ∂R/∂p_k`,
  `ṗ_k = −∂R/∂q_k`.
- `IsPartiallyHyperregular.isRouthTrajectory_routhCurve_iff`: a path satisfies
  the Euler–Lagrange equations of `L` exactly when its curve of positions,
  velocities `v_i` and momenta `p_k = ∂L/∂v_k` satisfies the equations of the
  Routhian. `eq_routhCurve`: every curve that satisfies them is of this form.
- `IsRouthTrajectory.p_eq_algebraMap`,
  `IsRouthTrajectory.isSolution_reducedRouthian`: if the Routhian does not
  depend on the `q_k`, the `p_k` are constant, and the `q_i` satisfy the
  Euler–Lagrange equations of `reducedRouthian R c`, the Routhian at
  `p_k = c_k`.
- `isPartiallyHyperregular_natural`: a natural Lagrangian is hyperregular in
  the velocities of the co-ordinates with non-zero masses.

As for the Legendre transformation, the inverse morphism is a hypothesis, and
the Lagrangian does not depend explicitly on time. The Euler–Lagrange
equations of `R` and of `−R` are the same; Landau–Lifshitz use `−R` as the
Lagrangian of the remaining co-ordinates.

## Motion in a central field

`Mechanics/Elementary` defines the cosine and the sine of an element of a
C∞-ring, `ringCos a` and `ringSin a`, by the smooth operations of one
variable, as `SmoothRing.exp a` is defined. `exp_mul_exp_neg`:
`exp a · exp (−a) = 1`. `apply_exp`, `apply_ringCos`, `apply_ringSin`: a vector
field differentiates them by the chain rule.

`Poisson/CentralField` treats Landau–Lifshitz §14 for a particle in the plane.
The polar co-ordinates are taken with the logarithm `s` of the radius, so that
all functions are elements of a free C∞-ring: `Polar` is the phase space of
`(s, φ)` with the momenta `p_s = r p_r` and `p_φ`, and `r = exp s`,
`1/r = exp (−s)`.

- `polarCoordinates` is the morphism from the phase space of the plane with
  `x ↦ r cos φ`, `y ↦ r sin φ`, `p_x ↦ (p_s cos φ − p_φ sin φ)/r`,
  `p_y ↦ (p_s sin φ + p_φ cos φ)/r`. `isPoissonHom_polarCoordinates`: it is a
  Poisson morphism, so the polar co-ordinates are canonical.
- `polarCoordinates_p_sq`: `|p|² = (p_s² + p_φ²)/r²`, which is
  `p_r² + p_φ²/r²`. `polarCoordinates_angularMomentum`: `x p_y − y p_x = p_φ`.
- `polarHamiltonian m V` is `(p_s² + p_φ²)/2mr² + V(s)`.
  `polarCoordinates_hamiltonian`: it is the Hamiltonian `|p|²/2m + U(|q|²)`
  of the plane for `V = logPotential U`.
  `partialDerivation_polarHamiltonian`: the angle is cyclic.
- `reductionHom_radialHamiltonian`: in the reduced ring at `p_φ = ℓ` the class
  of the Hamiltonian is `radialHamiltonian m V ℓ`. `radialHamiltonian_eq`:
  it is `p_r²/2m + ℓ²/2mr² + V` with `radialMomentum = p_s / r`, and
  `canonical_radius_radialMomentum`: `{r, p_r} = 1`. The centrifugal energy
  comes from the reduction.
- `isTrajectory_radial`, `timeDerivative_angle`, `pφ_eq_algebraMap`: along a
  trajectory `p_φ` is constant, the radial part is a trajectory of the radial
  Hamiltonian, and `φ̇ = p_φ/mr²`. `isTrajectory_plane`: a trajectory in polar
  co-ordinates gives a trajectory in the plane.
- `sum_q_mul_M_eq_zero`: along a trajectory of a central Hamiltonian in space
  the position is orthogonal to the angular momentum at the time `0`. The orbit
  lies in a plane.

In polar co-ordinates the potential energy `V` is a smooth function of
`s = log r`, an arbitrary smooth function of the radius `r > 0`; Coulomb's
potential is included. The comparison with the plane needs a potential energy
that is a smooth function of `|q|²`. The polar co-ordinates cover the plane
without the origin, and `polarCoordinates` is not an isomorphism: a trajectory
in the plane is not lifted to polar co-ordinates here.

`Mechanics/Quadrature` is real analysis. If `r` has a continuous positive
derivative `r'` on an interval and `r'(t)² = F(r(t))`, then
`∫ w(r(t)) dt = ∫ w(u)/√F(u) du` (`integral_comp_eq_integral_div_sqrt`).
`sub_eq_sqrt_mul_integral_of_energy` is Landau–Lifshitz (11.3):
`t₁ − t₀ = √(m/2) ∫ dx/√(E − U(x))` when `m ẋ²/2 + U(x) = E` and `ẋ > 0`.

`Poisson/OrbitIntegral` applies it to the radial motion. `radiusAt y t` and
`radialVelocityAt m y t` are the radius and `p_r/m` at the time `t`.

- `hasDerivAt_radiusAt`: the radial velocity is the derivative of the radius.
- `radialVelocityAt_sq`: `ṙ² = (2/m)(E − V) − ℓ²/m²r²` (14.5), with
  `radialSpeedSq m V ℓ E` for the right side as a function of the radius.
- `sub_eq_integral_radius`: `t₁ − t₀ = ∫ dr/√((2/m)(E − V) − ℓ²/m²r²)` (14.6).
- `angle_sub_eq_integral_radius`:
  `φ(t₁) − φ(t₀) = ∫ (ℓ/mr²) dr/√((2/m)(E − V) − ℓ²/m²r²)` (14.7).

The two integrals are over an interval of time where the radial velocity is
positive, so the interval contains no turning point.

`Mechanics/TurningPoint` treats the integrals up to the turning points. For
simple turning points `u₁ < u₂`, `ẋ² = (x − u₁)(u₂ − x) G(x)` with `G > 0`,
the function `1/√((u − u₁)(u₂ − u) G(u))` is unbounded at both ends and
integrable, and `turningParam u₁ u₂ θ = (u₁ + u₂)/2 + (u₂ − u₁)/2 · cos θ`
removes the singularity.

- `integral_div_sqrt_turning`:
  `∫ w(u) du/√((u − u₁)(u₂ − u) G(u)) = ∫₀^π w(u(θ)) dθ/√G(u(θ))`, for all
  functions `w` and `G`. `integrableOn_div_sqrt_turning`: the integrand is
  integrable when `w` and `G` are continuous and `G > 0`.
- `integral_comp_eq_integral_div_sqrt_turning`: if `x` increases from `u₁`
  to `u₂` on `[t₁, t₂]`, with the velocity allowed to vanish at both ends,
  then `∫ w(x(t)) dt = ∫ w(u) du/√((u − u₁)(u₂ − u) G(u))`.
  `integral_comp_eq_integral_div_sqrt_turning_of_neg` is the same for a
  decreasing motion.
- `sub_eq_sqrt_mul_integral_of_energy_turning` is Landau–Lifshitz (11.5):
  `t₂ − t₁ = √(m/2) ∫ dx/√(E − U(x))` between two turning points, when
  `E − U = (x − x₁)(x₂ − x) W` with `W > 0`.
- `sqrt_mul_integral_oscillator`: for the oscillator the formula gives `π/ω`.
  `sub_eq_sqrt_mul_integral_oscillator`: the motion `−a cos ωt` satisfies the
  hypotheses.

The integrals are Lebesgue integrals; no limit at a turning point is taken.
The change of variables uses Mathlib's formula for an injective
differentiable map, which needs no integrability hypothesis.

`Poisson/Apsides` applies this to the radial motion. An apsis is a time at
which the radial velocity vanishes.

- `sub_eq_integral_turningParam_radius`,
  `angle_sub_eq_integral_turningParam_radius`: between two apsides at which
  `ṙ²` has simple zeros, the time and the angle (14.10) are regular integrals
  in `θ`.
- `keplerPotential α` is `−α/r` as a function of `s = log r`.
  `kepler_radialSpeedSq_eq`: the two apsides `r₁ < r₂` determine the energy
  and the angular momentum, and `ṙ² = (r − r₁)(r₂ − r) · 2α/(m (r₁ + r₂) r²)`.
- `kepler_sub_eq`, `kepler_sub_eq_of_neg`: the time from one apsis to the
  next is `π a √(m a/α)`, with `a = (r₁ + r₂)/2`.
- `kepler_period`: if the radius increases from an apsis at `t₁` to an apsis
  at `t₂` and decreases to an apsis at `t₃`, then `r(t₃) = r(t₁)` and
  `t₃ − t₁ = 2π a √(m a/α)`. This is Landau–Lifshitz (15.8),
  `T = 2π a^{3/2} √(m/α)`.

In Kepler's problem `θ` is the eccentric anomaly, up to the direction in
which it is counted. The statements are for a given trajectory with its
apsides. The integrals to infinity of the scattering problem, the condition
for a closed orbit and the periodicity of the motion as a whole are not
proved.

## Motion in one dimension: wells

`Mechanics/OneDimension` treats `H = p²/2m + U(x)` with `U` smooth on `ℝ` and
`m > 0` in the plane `ℝ × ℝ` of `(x, p)` (Landau–Lifshitz §§11, 12, 50).

`OneDimension/Well`: `IsWell U E a b` states that `a < b` are simple turning
points of the energy `E`: `U(a) = U(b) = E`, `U′(a) < 0 < U′(b)` and `U < E`
between them.

- `IsWell.sub_eq`: `E − U(x) = (x − a)(b − x) W(x)` with
  `W = wellFactor U a b`, the second divided difference of `U`
  (`SmoothAlgebra.dividedDifference₂`). It is smooth in `(a, b, x)` together
  (`contDiff_wellFactor`) and positive on `[a, b]` (`IsWell.wellFactor_pos`).
- `IsWell.exists_family`: the turning points are smooth functions `α(E)`,
  `β(E)` on an open set of energies, and the energies of that set have wells
  between them. `isWell_oscillator` is the oscillator.

`OneDimension/Orbit`: the level curve is the image of
`x(θ) = (a + b)/2 − (b − a)/2 · cos θ`,
`p(θ) = √(2m) · (b − a)/2 · sin θ · √W(x(θ))` (`orbitPosition`,
`orbitMomentum`). Both are smooth and `2π`-periodic,
`p²/2m + U(x) = E` on the curve (`IsWell.orbit_energy`), and the curve is
tangent to the Hamiltonian field: `x′(θ) = λ p/m` and `p′(θ) = −λ U′(x)` with
`λ = orbitRate = √(m/2)/√W > 0` (`hasDerivAt_orbitPosition`,
`IsWell.orbitRate_mul_orbitMomentum`, `IsWell.hasDerivAt_orbitMomentum`). No
point of the curve is singular. `orbitPeriod` is `∫₀^{2π} λ dθ`, and
`IsWell.orbitPeriod_eq` is `T = √(2m) ∫ₐᵇ dx/√(E − U(x))`.

`OneDimension/Motion`: `field m U` is the field `(p/m, −U′(x))`.
`wellMotion m U a b` is the level curve run with the angle that solves
`dθ/dt = 1/λ(θ)`, which exists for all times.

- `IsWell.hasDerivAt_wellMotion`, `wellMotion_zero`: it solves Hamilton's
  equations at every time and starts at `(a, 0)`; it is the line of the flow
  through that point (`IsWell.flow_field_eq`).
- `IsWell.wellMotion_add_period`: it has the period `orbitPeriod`.
- `IsWell.exists_wellMotion_eq`: every point with the energy `E` and the
  position in `[a, b]` is reached by it.
- `IsWell.add_period_of_hasDerivAt`, `IsWell.position_add_period`: every
  solution with the energy `E` that starts between the turning points has the
  period `orbitPeriod`.

`OneDimension/Area`: `orbitArea` is `∮ p dx` as an integral over the angle,
equal to `2 ∫ₐᵇ √(2m (E − U)) dx` (`IsWell.orbitArea_eq`).
`hasDerivAt_orbitArea` is Proposition 68: along a smooth family of wells
`d/dE ∮ p dx = T(E)`. The derivative of `p x_θ` in the energy is `λ` plus the
derivative in `θ` of `p ∂x/∂E`, by the derivative in the energy of
`p²/2m + U(x) = E` (`orbitMomentum_mul_deriv_energy`); the second term
integrates to zero over the closed curve.

`OneDimension/Abel`: `lintegral_levelTime_mul` is the exchange of integrals
`∫ (∫_Ω dx/√(E − U(x))) dE/√(V − E) = π · |{x ∈ Ω : U(x) < V}|`, for every
measurable `U` and every set `Ω`, by Tonelli's theorem; the integrands are
non-negative and vanish where the square root has a negative argument.
`abel_inversion` is (12.1) for wells nested from the bottom `E₀` to `V`:
`x₂(V) − x₁(V) = (1/π√(2m)) ∫ T(E) dE/√(V − E)`.

`OneDimension/ActionAngle`: `orbitAction` is `I = (1/2π) ∮ p dx`, with
`dI/dE = T/2π` (`hasDerivAt_orbitAction`) and strict monotonicity on an
interval of the family (`strictMonoOn_orbitAction`). `orbitPhase` is the angle
variable `φ = 2π t/T` of a point of the level curve; it increases by `2π`
around the curve, and along the motion `φ = (2π/T) t`
(`IsWell.orbitPhase_add_two_pi`, `IsWell.orbitPhase_orbitAngle`).
`orbit_area_form`: in the chart `(E, θ)` the area form `dx ∧ dp` is `dφ ∧ dI`.

`OneDimension/Oscillator`: for `U = k x²/2` the factor is the constant `k/2`,
the period is `2π√(m/k)`, the action variable is `E √(m/k)`, and the wells
satisfy the hypotheses of Abel's formula (`orbitPeriod_oscillator`,
`orbitAction_oscillator`, `abel_inversion_oscillator`).

The turning points are simple. An unbounded motion, a turning point with
`U′ = 0`, the generating function of the action–angle variables and the map
`(φ, I) ↦ (x, p)` are not treated.

## Mechanical similarity

`Mechanics/Similarity` covers Landau–Lifshitz §10. `TimeFunction.scale β` is
the morphism `f ↦ f(βt)` of the ring of functions of time, with
`d/dt f(βt) = β f'(βt)` (`TimeFunction.timeDerivative_scale`). `dilate α` is
the morphism `xᵢ ↦ α xᵢ` of the free ring on the positions, and
`IsHomogeneous k u` says that `dilate α u = α^k u` for every `α > 0`.

- `IsHomogeneous.dilate_partialDerivation`: the partial derivatives of a
  function homogeneous of degree `k` are homogeneous of degree `k − 1`. The
  proof applies `∂ⱼ` to the defining identity and uses the chain rule for a
  substitution.
- `StandardJet.IsSolution.similar`: for the Lagrangian
  `Σᵢ ½ mᵢ q̇ᵢ² − U(q)` with `U` homogeneous of degree `k`, if `γ(t)` is a
  solution, so is `α γ(βt)` with `β = α^{(k − 2)/2}`.
- `similar_apply_add_period`: if `γ` has the period `T`, the similar path has
  the period `T/β = α^{1 − k/2} T`.

`Poisson/VirialAverage` proves the virial theorem for time averages.
`TimeFunction.tendsto_average_timeDerivative`: for a bounded function `G` of
time, `(1/τ) ∫₀^τ Ġ dt → 0` as `τ → ∞`. `IsTrajectory.tendsto_average_virial`:
along a trajectory of `Σᵢ pᵢ²/2mᵢ + U` on which `Σᵢ qᵢ pᵢ` is bounded, with `U`
satisfying Euler's relation of degree `k`, the time average of `2T − kU`
tends to zero.

`Poisson/KeplerOrbit` applies the same ideas to Kepler motions.
`IsKeplerMotion.conic`: at every time,
`A · q(t) = |M|² − m α r(t)` with the constant vectors `A = A(0)` and
`M = M(0)`. Here `r(t) = R(t) |Q(t)|²` is the signed radius; the ordinary
distance is `|r(t)|`, and equals `r(t)` on the branch `R(t) > 0`.
`IsKeplerMotion.similar`: if `(Q, P, R)` is a Kepler motion and
`β² λ³ = 1`, then `(λ Q(βt), λ β P(βt), R(βt)/λ)` is a Kepler motion.
`similar_period`: the similar orbit has the period `T/β`, and
`(T/β)² = λ³ T²`, so the squares of the periods are as the cubes of the
linear dimensions.

The scaling is a statement about solutions; the corresponding automorphism of
the jet ring is not constructed. Euler's relation `Σ qᵢ ∂U/∂qᵢ = kU`, the
hypothesis of the virial identity, is not derived from the scaling property
`u(αx) = α^k u(x)`. The period of an elliptic orbit as a function of its
semi-major axis is not computed.

## Proof map

| Module | Main declarations |
| --- | --- |
| [Basic](../ProjectAInos/Mechanics/Basic.lean) | `Lagrangian`, `action`, `force`, `momentum`, `eulerLagrange`, `FixedEndpointVariation`, `Stationary`, `toVariational`, `action_eq_variational` |
| [FirstVariation](../ProjectAInos/Mechanics/FirstVariation.lean) | `hasDerivAt_action_firstVariation`, `firstVariation_eq_boundary_add_integral`, `firstVariation_fixedEndpoints`, `hasDerivAt_action_eulerLagrange` |
| [EulerLagrange](../ProjectAInos/Mechanics/EulerLagrange.lean) | `stationary_iff_eulerLagrange`, `stationary_iff_momentum_equation` |
| [EndpointAction](../ProjectAInos/Mechanics/EndpointAction.lean) | `pathEnergy`, `hasDerivAt_density_family`, `deriv_family_endpoint`, `contDiffAt_momentum`, `hasDerivAt_action_movingEndpoints_on`, `hasDerivAt_action_movingEndpoints`, `pathEnergy_natural`, `hasDerivAt_action_natural_movingEndpoints_on`, `hasDerivAt_action_free_endpoint`, `hasDerivAt_action_oscillator_endpoint`, `hasDerivAt_action_oscillator_family` |
| [SmoothLagrangian](../ProjectAInos/Mechanics/SmoothLagrangian.lean) | `ofSmoothOperation`, `ofSmoothOperation_op`, `stationary_ofSmoothOperation_iff` |
| [TotalTimeDerivative](../ProjectAInos/Mechanics/TotalTimeDerivative.lean) | `action_add_totalTimeDerivative`, `stationary_add_totalTimeDerivative_iff`, `eulerLagrange_totalTimeDerivative`, `eulerLagrange_add_totalTimeDerivative` |
| [Jet/Basic](../ProjectAInos/Mechanics/Jet/Basic.lean) | `JetRing`, `OrderLE`, `totalDeriv`, `totalDeriv_q`, `dt_totalDeriv`, `d_zero_totalDeriv`, `d_succ_totalDeriv` |
| [Jet/Euler](../ProjectAInos/Mechanics/Jet/Euler.lean) | `euler`, `euler_totalDeriv`, `euler_add_totalDeriv`, `eulerLagrangeIdeal`, `Conserved`, `totalDeriv_mem_eulerLagrangeIdeal` |
| [Jet/Noether](../ProjectAInos/Mechanics/Jet/Noether.lean) | `momentum`, `energy`, `prolong`, `totalDeriv_energy`, `prolong_eq_euler_add_totalDeriv`, `conserved_noetherCharge`, `conserved_energy` |
| [Jet/Conservation](../ProjectAInos/Mechanics/Jet/Conservation.lean) | `naturalLagrangian`, `euler_naturalLagrangian`, `conserved_momentum`, `conserved_boost`, `conserved_linear`, `conserved_angularMomentum` |
| [TimeFunction](../ProjectAInos/Mechanics/TimeFunction.lean) | `TimeFunction`, `timeDerivative`, `TimeFunction.contDiff_apply_const`, `TimeFunction.ext_apply_const`, `TimeFunction.timeDerivative_apply`, `TimeFunction.eq_of_timeDerivative_eq_zero`, `TimeFunction.cos`, `TimeFunction.sin`, `TimeFunction.timeDerivative_cos`, `TimeFunction.timeDerivative_sin` |
| [Jet/Prolongation](../ProjectAInos/Mechanics/Jet/Prolongation.lean) | `prolongation`, `prolongation_totalDeriv`, `IsSolution`, `prolongation_eq_zero_of_mem`, `prolongation_eq_of_conserved`, `isSolution_naturalLagrangian_iff`, `energy_eq_of_isSolution`, `isSolution_oscillator_iff`, `isSolution_uniformMotion` |
| [Jet/Metric](../ProjectAInos/Mechanics/Jet/Metric.lean) | `kineticForm`, `metricLagrangian`, `conserved_momentum_of_cyclic`, `d_one_kineticForm`, `momentum_metricLagrangian`, `euler_metricLagrangian`, `euler_metricLagrangian_eq`, `energy_metricLagrangian`, `conserved_energy_metricLagrangian`, `energy_metricLagrangian_eq_inverse`, `metricLagrangian_diagonal` |
| [Jet/Polar](../ProjectAInos/Mechanics/Jet/Polar.lean) | `Polar.metric`, `Polar.lagrangian`, `Polar.euler_radial`, `Polar.euler_angular`, `Polar.momentum_angular`, `Polar.conserved_angularMomentum` |
| [Jet/Analytic](../ProjectAInos/Mechanics/Jet/Analytic.lean) | `firstOrder`, `orderLE_firstOrder`, `euler_firstOrder`, `realPath`, `realJet`, `prolongation_firstOrder_apply`, `fderiv_ofSmoothOperation`, `eulerLagrange_ofSmoothOperation`, `prolongation_euler_firstOrder_apply`, `isSolution_firstOrder_iff`, `isSolution_firstOrder_iff_stationary`, `prolongation_eq_of_stationary`, `energy_eq_of_stationary` |
| [Jet/Standard](../ProjectAInos/Mechanics/Jet/Standard.lean) | `StandardJet`, `jetRing`, `totalDeriv_eq_derivation`, `euler_q_mul_acceleration`, `euler_oscillator`, `conserved_energy_oscillator`, `conserved_boost_free` |
| [Constants](../ProjectAInos/Mechanics/Constants.lean) | `lift_eq_of_partialDerivation_eq_zero`, `eq_algebraMap_of_partialDerivation_eq_zero`, `lift_eq_of_derivation_eq_zero`, `lift_eq_of_partialDerivation_eq_zero_of_ne`, `lift_eq_self_of_partialDerivation_eq_zero` |
| [Jet/FreeParticle](../ProjectAInos/Mechanics/Jet/FreeParticle.lean) | `JetRing.d_sum_mul_q`, `JetRing.d_sum_mul_q_mul_q_of_isSymm`, `StandardJet.DependsOnVelocities`, `StandardJet.eq_algebraMap_of_dt_eq_zero_of_d_eq_zero`, `StandardJet.boost`, `StandardJet.IsBoostQuasiInvariant`, `StandardJet.boost_eq`, `StandardJet.d_one_d_one_eq_algebraMap`, `StandardJet.velocityPolynomial`, `StandardJet.isBoostQuasiInvariant_velocityPolynomial`, `StandardJet.exists_eq_velocityPolynomial`, `StandardJet.massMatrix`, `StandardJet.isBoostQuasiInvariant_iff`, `StandardJet.velocityPolynomial_eq_add_totalDeriv`, `StandardJet.velocityValue`, `StandardJet.velocityValue_velocityPolynomial`, `StandardJet.IsIsotropic`, `StandardJet.eq_smul_one_of_isIsotropic`, `StandardJet.exists_eq_of_isIsotropic`, `StandardJet.freeLagrangian_boost` |
| [Jet/Galilei](../ProjectAInos/Mechanics/Jet/Galilei.lean) | `JetRing.euler_apply`, `JetRing.apply_mem_eulerLagrangeIdeal`, `JetRing.dt_mem_eulerLagrangeIdeal`, `JetRing.prolong_eq_sum`, `JetRing.prolong_op`, `JetRing.prolongField`, `JetRing.prolong_q`, `JetRing.sum_sum_antisymm_eq_zero`, `StandardJet.evolutionary`, `StandardJet.evolutionary_totalDeriv`, `StandardJet.evolutionary_eq_prolongField`, `StandardJet.evolutionary_apply`, `StandardJet.affineShift`, `StandardJet.galileiCharacteristic`, `StandardJet.galileiField`, `StandardJet.galileiField_q`, `StandardJet.galileiField_totalDeriv`, `StandardJet.commutator_galileiField`, `StandardJet.commutator_dt_galileiField`, `StandardJet.d_galileiField`, `StandardJet.euler_galileiField`, `StandardJet.galileiField_mem_eulerLagrangeIdeal`, `StandardJet.galileiField_naturalLagrangian`, `StandardJet.boost_eq_galileiField`, `StandardJet.IsInertial`, `StandardJet.isInertial_naturalLagrangian` |
| [Poisson/RigidBody](../ProjectAInos/Mechanics/Poisson/RigidBody.lean) | `PhaseSpace`, `L`, `poisson`, `poisson_L_L`, `L_ne_zero`, `poisson_bracket`, `poisson_L_bracket`, `kineticEnergy`, `gradient_kineticEnergy`, `euler_equations`, `euler_equation_zero`, `casimir`, `poisson_casimir_left`, `isIntegral_casimir` |
| [Poisson/Epsilon](../ProjectAInos/Mechanics/Poisson/Epsilon.lean) | `epsilon`, `epsilon_skew`, `sum_epsilon_mul` |
| [Poisson/AngularMomentum](../ProjectAInos/Mechanics/Poisson/AngularMomentum.lean) | `M`, `canonical_M_q`, `canonical_M_p`, `canonical_M_M`, `canonical_M_dotProduct`, `isIntegral_M`, `isIntegral_M_sq`, `momentumMap`, `isPoissonHom_momentumMap` |
| [Poisson/HeavyTop](../ProjectAInos/Mechanics/Poisson/HeavyTop.lean) | `PhaseSpace`, `L`, `Γ`, `poisson`, `poisson_bracket`, `poisson_L_bracket`, `poisson_Γ_bracket`, `hamiltonian`, `poisson_L_hamiltonian`, `poisson_Γ_hamiltonian`, `poisson_Γ_sq_left`, `poisson_L_dot_Γ_left` |
| [Poisson/Galilei](../ProjectAInos/Mechanics/Poisson/Galilei.lean) | `K`, `freeHamiltonian`, `canonical_K_p`, `canonical_K_q`, `canonical_K_K`, `canonical_M_K`, `canonical_M_freeHamiltonian`, `canonical_p_freeHamiltonian`, `canonical_K_freeHamiltonian`, `K_sub_K` |
| [Poisson/Kepler](../ProjectAInos/Mechanics/Poisson/Kepler.lean) | `IsFrame`, `angularMomentum`, `hamiltonian`, `rungeLenz`, `constraint`, `distance`, `rungeLenz_dotProduct_angularMomentum`, `rungeLenz_dotProduct_q`, `rungeLenz_dotProduct_self`, `map_rungeLenz`, `IsFrame.q_hamiltonian`, `IsFrame.p_hamiltonian`, `IsFrame.angularMomentum_hamiltonian`, `IsFrame.p_constraint`, `IsFrame.rungeLenz_hamiltonian`, `IsFrame.angularMomentum_rungeLenz`, `IsFrame.rungeLenz_rungeLenz` |
| [Poisson/KeplerModel](../ProjectAInos/Mechanics/Poisson/KeplerModel.lean) | `PhaseSpace`, `q`, `p`, `ρ`, `structureMatrix`, `jacobi_generators`, `poisson`, `isFrame`, `constraintIdeal`, `isPoissonIdeal_constraintIdeal` |
| [Poisson/KeplerMotion](../ProjectAInos/Mechanics/Poisson/KeplerMotion.lean) | `curve`, `IsKeplerMotion`, `IsKeplerMotion.timeDerivative_R`, `IsKeplerMotion.isTrajectory`, `IsKeplerMotion.rungeLenz_eq`, `IsKeplerMotion.angularMomentum_eq`, `IsKeplerMotion.hamiltonian_eq`, `IsKeplerMotion.R_mul_distance`, `isKeplerMotion_circular` |
| [Poisson/RotatingFrame](../ProjectAInos/Mechanics/Poisson/RotatingFrame.lean) | `angularVelocity`, `canonical_bracket_dot_M`, `hamiltonian`, `velocity`, `canonical_q_hamiltonian`, `canonical_p_hamiltonian`, `canonical_velocity_hamiltonian`, `hamiltonian_eq_velocity` |
| [Poisson/Virial](../ProjectAInos/Mechanics/Poisson/Virial.lean) | `dilation`, `canonical_dilation_bracket`, `canonical_dilation_bracket_add`, `kineticEnergy`, `virial`, `oscillatorPotential`, `virial_oscillator` |
| [Poisson/Trajectory](../ProjectAInos/Mechanics/Poisson/Trajectory.lean) | `IsTrajectory`, `IsTrajectory.timeDerivative_lift`, `IsTrajectory.lift_eq_of_isIntegral`, `IsTrajectory.lift_eq_of_bracket_mem`, `IsTrajectory.lift_hamiltonian_eq`, `isTrajectory_canonical_iff`, `RigidBody.lift_casimir_eq`, `AngularMomentum.lift_M_eq`, `HeavyTop.lift_Γ_sq_eq`, `HeavyTop.lift_L_dot_Γ_eq`, `IsTrajectory.of_isPoissonHom` |
| [TwoBody/Kinematics](../ProjectAInos/Mechanics/TwoBody/Kinematics.lean) | `reducedMass`, `centreOfMassVelocity`, `total_mass_mul_kinetic`, `kineticEnergy_eq`, `velocity_one_eq`, `velocity_two_eq`, `momentum_one_centreOfMass`, `momentum_two_centreOfMass` |
| [TwoBody/Collisions](../ProjectAInos/Mechanics/TwoBody/Collisions.lean) | `disintegration_momentum_sq`, `disintegration_kinetic_one`, `disintegration_energy_nonneg`, `IsElastic`, `outgoingOne`, `outgoingTwo`, `IsElastic.relative_speed`, `isElastic_outgoing`, `isElastic_iff`, `outgoingOne_rest_dotProduct_self`, `outgoingTwo_rest_dotProduct_self`, `outgoingOne_headOn`, `energy_transfer_le`, `outgoing_rest_dotProduct_eq_zero` |
| [Poisson/TwoBody](../ProjectAInos/Mechanics/Poisson/TwoBody.lean) | `centre`, `relative`, `totalMomentum`, `relativeMomentum`, `canonical_centre_totalMomentum`, `canonical_relative_relativeMomentum`, `canonical_centre_relativeMomentum`, `canonical_relative_totalMomentum`, `kineticEnergy_eq_centre` |
| [Rigid/AngularVelocity](../ProjectAInos/Mechanics/Rigid/AngularVelocity.lean) | `hat`, `vee`, `hat_mulVec`, `hat_cross`, `hat_vee`, `hatEquiv`, `hatEquiv_cross`, `velocityField`, `velocityField_add`, `velocityField_injective`, `velocityField_change_of_origin`, `transpose_deriv_mul_transpose`, `angularVelocity`, `hasDerivAt_rigidMotion` |
| [Rigid/EulerAngles](../ProjectAInos/Mechanics/Rigid/EulerAngles.lean) | `rotZ`, `rotX`, `eulerMatrix`, `eulerMatrixDeriv`, `bodyAngularVelocity`, `spaceAngularVelocity`, `eulerMatrix_mul_transpose`, `det_eulerMatrix`, `transpose_mul_eulerMatrixDeriv`, `eulerMatrixDeriv_mul_transpose`, `eulerMatrix_mulVec_bodyAngularVelocity`, `symmetricTop_energy`, `det_eulerJacobian`, `eulerRotation`, `eulerRotation_mem_specialOrthogonalGroup`, `hasDerivAt_eulerRotation`, `angularVelocity_eulerRotation` |
| [Rigid/RegularPrecession](../ProjectAInos/Mechanics/Rigid/RegularPrecession.lean) | `symmetricTopMomentum`, `verticalAxis`, `eulerMatrix_mulVec_verticalAxis`, `transpose_eulerMatrix_mulVec`, `eulerMatrix_mulVec_symmetricTopMomentum`, `eulerMatrix_mulVec_symmetricTopMomentum_iff`, `regularPrecession_psi_rate`, `eulerRotation_mulVec_symmetricTopMomentum` |
| [Poisson/RigidBodyMotion](../ProjectAInos/Mechanics/Poisson/RigidBodyMotion.lean) | `isTrajectory_kineticEnergy_iff`, `isTrajectory_principalRotation`, `isTrajectory_symmetricTop`, `stabilityForm`, `isIntegral_stabilityForm`, `sum_mul_sq_eq`, `mul_sq_le_of_greatest`, `mul_sq_le_of_least`, `linearization_zero_two`, `linearization_two_zero`, `linearization_mul_pos_of_middle`, `linearization_mul_neg_of_greatest`, `linearization_mul_neg_of_least` |
| [Rigid/InertiaTensor](../ProjectAInos/Mechanics/Rigid/InertiaTensor.lean) | `inertia`, `transpose_inertia`, `inertia_mulVec`, `dotProduct_inertia_mulVec`, `dotProduct_inertia_mulVec_nonneg`, `trace_inertia`, `two_mul_dotProduct_inertia_mulVec_le_trace`, `inertia_add_apply`, `principalMoments`, `principalAxes`, `inertia_mulVec_principalAxes`, `principalMoments_nonneg`, `principalMoments_two_le` |
| [Rigid/Dynamics](../ProjectAInos/Mechanics/Rigid/Dynamics.lean) | `mulVec_cross`, `angularVelocityBody`, `deriv_eq_mul_hat`, `IsRigidMotion`, `IsRigidMotion.hasDerivAt_momentum`, `IsRigidMotion.sum_smul_cross_velocity`, `IsRigidMotion.hasDerivAt_angularMomentum`, `IsRigidMotion.hasDerivAt_bodyAngularMomentum`, `IsRigidMotion.hasDerivAt_bodyVector`, `sum_internal_force`, `sum_cross_internal_force`, `transpose_mulVec_sum_cross_weight`, `IsRigidMotion.sum_mul_velocity_sq` |
| [Rigid/Reconstruction](../ProjectAInos/Mechanics/Rigid/Reconstruction.lean) | `rotation`, `hasDerivAt_rotation`, `rotation_transpose_mul`, `det_rotation`, `isRigidMotion_rotation`, `angularVelocityBody_rotation`, `eq_rotation_of_hasDerivAt`, `contDiff_rotation`, `hasDerivAt_rotation_mulVec`, `rotation_mulVec_eq` |
| [Rigid/Variation](../ProjectAInos/Mechanics/Rigid/Variation.lean) | `curveVelocity`, `IsRotationFamily`, `familyVariation`, `IsRotationFamily.familyDeriv_parameter`, `IsRotationFamily.hasDerivAt_curveVelocity_family`, `IsRotationFamily.hasDerivAt_bodyVector_family` |
| [Rigid/RotationAction](../ProjectAInos/Mechanics/Rigid/RotationAction.lean) | `bodyLagrangian`, `rotationAction`, `eulerPoissonResidual`, `hasDerivAt_rotationAction`, `cayley`, `cayley_transpose_mul`, `isRotationFamily_mul_cayley`, `familyVariation_mul_cayley`, `eulerPoissonResidual_eq_zero_iff`, `stationary_rotationAction_iff` |
| [Poisson/RigidBodyEquations](../ProjectAInos/Mechanics/Poisson/RigidBodyEquations.lean) | `HeavyTop.field`, `HeavyTop.field_inl`, `HeavyTop.field_inr`, `IsRigidMotion.hasDerivAt_eulerField`, `IsRigidMotion.hasDerivAt_heavyTopField`, `hasDerivAt_heavyTopField_of_stationary`, `rotation_mulVec_eulerSolution`, `rotation_mulVec_ellipticMotion`, `stationary_rotationAction_rotation` |
| [Poisson/AsymmetricTop](../ProjectAInos/Mechanics/Poisson/AsymmetricTop.lean) | `eulerField`, `jacobiCurve`, `hasDerivAt_jacobiCurve`, `ellipticMotion`, `hasDerivAt_ellipticMotion`, `flow_eulerField_ellipticMotion`, `ellipticMotion_add_period`, `exists_ellipticMotion_eq`, `eq_ellipticMotion_of_hasDerivAt`, `hasDerivAt_ellipticMotion'`, `eq_ellipticMotion'_of_hasDerivAt`, `isTrajectory_ellipticTrajectory` |
| [Oscillations/Harmonic](../ProjectAInos/Mechanics/Oscillations/Harmonic.lean) | `TimeFunction.cosMul`, `TimeFunction.sinMul`, `TimeFunction.timeDerivative_cosMul`, `TimeFunction.timeDerivative_sinMul`, `amplitude`, `phase`, `amplitude_mul_cos_add`, `IsHarmonic`, `isHarmonic_cosMul`, `isHarmonic_sinMul`, `IsHarmonic.combination`, `IsHarmonic.eq_cos_add_sin`, `isHarmonic_iff`, `IsHarmonic.eq_of_initial`, `IsHarmonic.apply_eq_amplitude_mul_cos`, `IsHarmonic.apply_add_period`, `IsHarmonic.energy_eq`, `IsHarmonic.energy_eq_amplitude` |
| [Oscillations/Oscillator](../ProjectAInos/Mechanics/Oscillations/Oscillator.lean) | `StandardJet.isSolution_oscillator_iff_isHarmonic`, `Oscillator.hamiltonian`, `Oscillator.isTrajectory_iff`, `Oscillator.isTrajectory_iff_isHarmonic`, `Oscillator.flowMatrix`, `Oscillator.flowMatrix_zero`, `Oscillator.flowMatrix_add`, `Oscillator.det_flowMatrix`, `Oscillator.flowMatrix_add_period`, `Oscillator.apply_eq_flowMatrix_mulVec`, `Oscillator.flowCurve`, `Oscillator.isTrajectory_flowCurve` |
| [Oscillations/Linearization](../ProjectAInos/Mechanics/Oscillations/Linearization.lean) | `lift_curve_apply`, `lift_const_curve`, `isTrajectory_const_iff`, `isTrajectory_canonical_const_iff`, `displacement`, `hessian`, `hessian_symm`, `linearization`, `quadraticPart`, `partialDerivation_quadraticPart`, `canonical_bracket_quadraticPart`, `linearization_quadraticPart`, `isTrajectory_quadraticPart_iff`, `naturalHamiltonian`, `restPoint`, `isTrajectory_restPoint_iff`, `isHarmonic_of_isTrajectory_quadraticPart`, `isHarmonic_sqrt_of_isTrajectory_quadraticPart`, `pendulumHamiltonian`, `isHarmonic_pendulum` |
| [Oscillations/Damped](../ProjectAInos/Mechanics/Oscillations/Damped.lean) | `TimeFunction.expMul`, `TimeFunction.time`, `TimeFunction.eq_add_mul_time`, `TimeFunction.antitone_of_timeDerivative_nonpos`, `IsDamped`, `isDamped_zero_iff`, `isDamped_iff_expMul_mul`, `isDamped_iff_isHarmonic`, `IsDamped.apply_eq_underdamped`, `IsDamped.apply_eq_amplitude_mul_exp_mul_cos`, `IsDamped.abs_apply_le`, `IsDamped.apply_eq_critical`, `IsDamped.apply_eq_overdamped`, `IsDamped.eq_of_initial`, `IsDamped.timeDerivative_energy`, `IsDamped.energy_antitone`, `isDamped_expMul`, `isDamped_time_mul_expMul`, `IsHarmonic.isDamped_expMul_neg_mul` |
| [Oscillations/Dissipation](../ProjectAInos/Mechanics/Oscillations/Dissipation.lean) | `IsIntegralCurve`, `isIntegralCurve_hamiltonian_iff`, `IsIntegralCurve.timeDerivative_lift`, `velocity`, `frictionalForce`, `dissipativeFunction`, `dissipativeField`, `dissipativeField_q`, `dissipativeField_p`, `dissipativeField_self`, `lift_dissipativeFunction_nonneg`, `IsIntegralCurve.timeDerivative_energy`, `IsIntegralCurve.energy_antitone`, `Oscillator.isIntegralCurve_dissipativeField_iff`, `Oscillator.isIntegralCurve_dissipativeField_iff_isDamped`, `Oscillator.energy_antitone` |
| [Oscillations/Forced](../ProjectAInos/Mechanics/Oscillations/Forced.lean) | `IsForced`, `isForced_zero_iff`, `IsForced.add`, `IsForced.sub`, `IsForced.eq_of_initial`, `IsForced.timeDerivative_energy`, `IsDamped.tendsto_zero`, `IsForced.tendsto_sub`, `responseDenominator`, `steadyState`, `isForced_steadyState`, `steadyState_const_mul`, `steadyAmplitude`, `steadyPhase`, `steadyState_apply`, `sin_steadyPhase_nonpos`, `IsForced.apply_eq_transient_add_steadyState`, `IsForced.tendsto_sub_steadyState`, `steadyAmplitude_le`, `steadyAmplitude_eq_max`, `absorption`, `two_mul_dissipation_steadyState`, `mean_dissipation_steadyState`, `absorption_le`, `absorption_resonance`, `absorption_eq_half_max_iff` |
| [TimePrimitive](../ProjectAInos/Mechanics/TimePrimitive.lean) | `TimeFunction.hasDerivAt_apply_const`, `TimeFunction.continuous_apply_const`, `TimeFunction.apply_sub_apply_eq_integral`, `TimeFunction.primitive`, `TimeFunction.primitive_apply`, `TimeFunction.timeDerivative_primitive` |
| [Oscillations/Duhamel](../ProjectAInos/Mechanics/Oscillations/Duhamel.lean) | `isForced_zero_damping_iff`, `complexAmplitudeRe`, `complexAmplitudeIm`, `integral_mul_sin_sub`, `IsForced.complexAmplitudeRe_eq`, `IsForced.complexAmplitudeIm_eq`, `IsForced.timeDerivative_apply_eq_integral`, `IsForced.apply_eq_integral`, `IsForced.energy_apply`, `IsForced.energy_transfer`, `duhamel`, `isForced_duhamel`, `duhamel_apply`, `exists_isForced`, `isForced_cos_of_sq_ne`, `steadyState_zero_damping`, `IsForced.apply_eq_of_sq_ne`, `isForced_resonance`, `IsForced.eq_resonance_of_rest`, `IsForced.exists_abs_gt_of_resonance` |
| [Oscillations/NormalModes](../ProjectAInos/Mechanics/Oscillations/NormalModes.lean) | `exists_orthogonal_diagonalization`, `exists_transpose_mul_mul_eq_one`, `exists_simultaneous_diagonalization`, `mul_eq_mul_mul_diagonal`, `det_sub_smul_eq_zero_iff`, `lam_pos`, `IsSmallOscillation`, `normalCoordinates`, `map_mulVec_normalCoordinates`, `isSmallOscillation_iff`, `IsSmallOscillation.isHarmonic_normalCoordinates`, `isSmallOscillation_map_mulVec`, `IsSmallOscillation.apply_eq` |
| [Poisson/Quadratic](../ProjectAInos/Mechanics/Poisson/Quadratic.lean) | `eulerField`, `IsEulerHomogeneous`, `IsEulerHomogeneous.mul`, `IsEulerHomogeneous.partialDerivation`, `IsEulerHomogeneous.canonical_bracket`, `bilinearForm`, `quadraticForm`, `partialDerivation_quadraticForm`, `quadraticForm_injective`, `PhaseSpace.canonicalForm`, `PhaseSpace.canonical_bracket_generator_quadraticForm`, `PhaseSpace.canonical_bracket_quadraticForm`, `PhaseSpace.mem_sp_iff`, `PhaseSpace.canonicalForm_mul_mem_sp_iff`, `PhaseSpace.spHamiltonian`, `PhaseSpace.canonical_bracket_generator_spHamiltonian`, `PhaseSpace.canonical_bracket_spHamiltonian`, `PhaseSpace.spHamiltonian_injective` |
| [Oscillations/NormalForm](../ProjectAInos/Mechanics/Oscillations/NormalForm.lean) | `linearQ`, `linearP`, `canonical_linearQ_linearP`, `linearTransformation`, `linearTransformation_comp`, `isPoissonHom_linearTransformation`, `quadraticHamiltonian`, `quadraticHamiltonian_eq`, `quadraticHamiltonian_eq_normalForm`, `linearTransformation_normalForm`, `isPoissonHom_normalTransformation`, `linearTransformation_comp_inverse`, `linearTransformation_inverse_comp`, `isTrajectory_quadraticForm_iff`, `isTrajectory_quadraticHamiltonian_iff`, `isTrajectory_quadraticHamiltonian_iff_isSmallOscillation` |
| [Oscillations/QuadraticLagrangian](../ProjectAInos/Mechanics/Oscillations/QuadraticLagrangian.lean) | `JetRing.quadraticLagrangian`, `JetRing.momentum_quadraticLagrangian`, `JetRing.euler_quadraticLagrangian`, `StandardJet.isSolution_quadraticLagrangian_iff`, `NormalModes.isSymm_of_mul_eq_one`, `NormalModes.isTrajectory_quadraticHamiltonian_iff_isSolution` |
| [Oscillations/Symmetry](../ProjectAInos/Mechanics/Oscillations/Symmetry.lean) | `modeSpace`, `mem_modeSpace`, `mulVec_mem_modeSpace`, `isSmallOscillation_symmetry`, `card_ne_zero_eq_rank` |
| [Oscillations/SymmetryTypes](../ProjectAInos/Mechanics/Oscillations/SymmetryTypes.lean) | `modeSpace_eq_eigenspace`, `isInternal_modeSpace`, `finrank_modeSpace`, `IsSymmetryRep`, `modeSubrep`, `modeRep`, `character_eq_sum_modeRep`, `sum_finrank_intertwiningMap_modeRep`, `finrank_intertwiningMap_eq_sum` |
| [Oscillations/Molecule](../ProjectAInos/Mechanics/Oscillations/Molecule.lean) | `atom`, `displacementRep`, `atom_displacementRep`, `character_displacementRep`, `rigidMap`, `rigidRep`, `character_rigidRep`, `displacementRep_rigidMap`, `rigidEquiv`, `card_vibration_add_six`, `sum_finrank_vibration` |
| [Oscillations/SpringMolecule](../ProjectAInos/Mechanics/Oscillations/SpringMolecule.lean) | `massMatrix`, `bondVector`, `springMatrix`, `dotProduct_springMatrix_mulVec`, `springMatrix_mulVec_eq_zero_iff`, `rigidMap_mem_modeSpace_zero`, `isSymmetryRep_spring` |
| [Oscillations/Triatomic](../ProjectAInos/Mechanics/Oscillations/Triatomic.lean) | `rigidMap_injective`, `exists_rigidMap_eq`, `range_rigidMap_eq_modeSpace_zero`, `card_vibration_triatomic`, `sum_finrank_vibration_triatomic`, `scalarRep`, `Equilateral.sum_finrank_trivial`, `Equilateral.sum_finrank_sign`, `Equilateral.sum_finrank_permutation`, `Isosceles.sum_finrank_symmetric`, `Isosceles.sum_finrank_antisymmetric`, `Isosceles.sum_finrank_plane` |
| [Oscillations/Parametric](../ProjectAInos/Mechanics/Oscillations/Parametric.lean) | `mul_self_eq`, `sin_smul_pow_succ`, `exists_abs_pow_apply_le`, `IsHill`, `wronskian`, `IsHill.wronskian_eq`, `TimeFunction.shift`, `IsHill.shift`, `state`, `FundamentalSystem`, `FundamentalSystem.eq_combination`, `FundamentalSystem.matrix`, `FundamentalSystem.det_matrix`, `FundamentalSystem.state_eq`, `FundamentalSystem.matrix_add_nat_mul_period`, `FundamentalSystem.exists_abs_apply_le`, `FundamentalSystem.exists_abs_apply_le_of_abs_trace_lt`, `FundamentalSystem.harmonic` |
| [Oscillations/ParametricExistence](../ProjectAInos/Mechanics/Oscillations/ParametricExistence.lean) | `hillCoefficient`, `hillState`, `hasDerivAt_hillState`, `hillSolution`, `isHill_hillSolution`, `IsHill.eq_of_initial`, `exists_isHill`, `existsUnique_isHill`, `FundamentalSystem.ofCoefficient`, `FundamentalSystem.nonempty`, `FundamentalSystem.ofCoefficient_harmonic`, `monodromy`, `det_monodromy`, `trace_monodromy_harmonic` |
| [Oscillations/ParametricTrace](../ProjectAInos/Mechanics/Oscillations/ParametricTrace.lean) | `IsHill.const_mul`, `IsHill.add`, `IsHill.state_period`, `IsHill.shift_eq_of_mulVec_eq`, `exists_abs_apply_le_of_shift_eq`, `not_exists_abs_apply_le_of_shift_eq`, `exists_mulVec_eq_smul_of_two_lt_abs_trace`, `exists_isHill_not_bounded_of_two_lt_abs_trace`, `IsHill.exists_abs_apply_le_iff_of_two_lt_abs_trace`, `mulVec_mulVec_sub_of_trace_eq`, `IsHill.exists_abs_apply_le_iff_of_trace_eq`, `exists_isHill_not_bounded_of_trace_eq`, `forall_isHill_bounded_iff` |
| [Oscillations/ParametricZone](../ProjectAInos/Mechanics/Oscillations/ParametricZone.lean) | `planeTrace`, `trace_monodromy_eq`, `rotatingCoefficient`, `rotation`, `propagator_hillCoefficient_rotation`, `trace_monodromy_eq_neg`, `modulated`, `shift_modulated`, `zoneBound`, `norm_rotatingCoefficient_modulated_le`, `integralCoefficient_rotating_left`, `integralCoefficient_rotating_right`, `abs_trace_monodromy_modulated_sub_le`, `exists_isHill_not_bounded_modulated`, `exists_abs_apply_le_modulated`, `exists_isHill_not_bounded_modulated_resonance`, `exists_abs_apply_le_modulated_of_le` |
| [Oscillations/RapidForce](../ProjectAInos/Mechanics/Oscillations/RapidForce.lean) | `effectivePotential`, `RapidBounds`, `IsRapidMotion`, `IsSlowMotion`, `slowVelocity`, `IsRapidMotion.hasDerivAt_pair`, `IsRapidMotion.abs_integral_oscillation₁_le`, `IsRapidMotion.abs_integral_oscillation₂_le`, `exists_forall_abs_sub_le`, `IsRapidMotion.abs_velocity_le`, `exists_forall_abs_sub_le_of_initial`, `Pendulum.rapidBounds`, `Pendulum.pos_iff` |
| [Oscillations/RapidForceExistence](../ProjectAInos/Mechanics/Oscillations/RapidForceExistence.lean) | `extendedField`, `exists_isRapidMotion`, `exists_isSlowMotion`, `exists_forall_exists_abs_sub_le` |
| [Oscillations/NonlinearResonance](../ProjectAInos/Mechanics/Oscillations/NonlinearResonance.lean) | `IsMotionOn`, `amplitude`, `detuning`, `nonlinearity`, `forcing`, `averagedField`, `IsMotionOn.hasDerivAt_amplitude`, `amplitude_equation`, `exists_averagedField_eq_zero`, `exists_forall_norm_amplitude_sub_le`, `exists_forall_abs_sub_steady_le` |
| [Oscillations/AnharmonicNormalForm](../ProjectAInos/Mechanics/Oscillations/AnharmonicNormalForm.lean) | `hamiltonian`, `generator₃`, `generator₄`, `secondCoefficient`, `bracket_action_cubic`, `quarticPart_eq`, `lieExp_generator₃`, `lieExp_generator₄`, `exists_normal_form`, `physicalHamiltonian`, `scale_physicalHamiltonian`, `exists_normal_form_physical`, `two_mul_coefficient_mul_action` |
| [Oscillations/ParametricExamples](../ProjectAInos/Mechanics/Oscillations/ParametricExamples.lean) | `shift_algebraMap`, `exists_abs_apply_le_harmonic`, `FundamentalSystem.free`, `monodromy_free`, `IsHill.exists_abs_apply_le_free_iff`, `exists_isHill_free_not_bounded`, `FundamentalSystem.hyperbolic`, `trace_monodromy_hyperbolic`, `exists_isHill_hyperbolic_not_bounded`, `IsHill.exists_abs_apply_le_hyperbolic_iff` |
| [Oscillations/Adiabatic](../ProjectAInos/Mechanics/Oscillations/Adiabatic.lean) | `Parametric.action`, `Parametric.timeDerivative_inv`, `Parametric.timeDerivative_action`, `Parametric.timeDerivative_action_of_const` |
| [Oscillations/AdiabaticOscillator](../ProjectAInos/Mechanics/Oscillations/AdiabaticOscillator.lean) | `action`, `abs_mul_le_action`, `coefficient`, `hasDerivAt_action`, `hasDerivAt_correctedAction`, `exists_forall_abs_action_sub_le`, `exists_forall_abs_action_sub_le_exp`, `action_eq_of_const` |
| [Legendre](../ProjectAInos/Mechanics/Legendre.lean) | `positionsToJet`, `positionsToPhase`, `d_zero_positionsToJet`, `orderLE_positionsToJet`, `legendre`, `legendre_p_eq_momentum`, `legendre_hamiltonian`, `isTrajectory_natural_iff`, `isSolution_natural_iff`, `isTrajectory_natural_iff_isSolution` |
| [Hyperregular](../ProjectAInos/Mechanics/Hyperregular.lean) | `JetRing.sum_mul_d_q_self`, `VelocitySpace`, `VelocitySpace.momentum`, `VelocitySpace.legendre`, `VelocitySpace.energy`, `VelocitySpace.hessian`, `VelocitySpace.apply_legendre`, `VelocitySpace.IsHyperregular`, `VelocitySpace.hamiltonian`, `VelocitySpace.inverseHessian`, `IsHyperregular.inverseHessian_mul_hessian`, `IsHyperregular.legendre_hamiltonian`, `IsHyperregular.legendre_partialDerivation_inr_hamiltonian`, `IsHyperregular.legendre_partialDerivation_inl_hamiltonian`, `VelocitySpace.velocityCurve`, `VelocitySpace.toJet`, `VelocitySpace.prolongation_toJet`, `VelocitySpace.isSolution_toJet_iff`, `IsHyperregular.isTrajectory_iff`, `IsHyperregular.isTrajectory_iff_isSolution`, `VelocitySpace.lagrangeBracket`, `IsHyperregular.legendre_bracket`, `IsHyperregular.lagrangeBracket_q_v`, `VelocitySpace.natural`, `VelocitySpace.isHyperregular_natural`, `VelocitySpace.hamiltonian_natural`, `VelocitySpace.toJet_natural` |
| [Poisson/GeneratingFunction](../ProjectAInos/Mechanics/Poisson/GeneratingFunction.lean) | `PositionPair`, `oldPosition`, `newPosition`, `gradOld`, `gradNew`, `oldMap`, `newMap`, `mixedHessian`, `oldHessian`, `apply_oldMap`, `gradNew_oldMap`, `gradOld_oldMap`, `IsFree`, `transformation`, `momentumPart`, `positionPart`, `inverseMixed`, `IsFree.inverseMixed_mul_mixedHessian`, `IsFree.momentumPart_eq`, `IsFree.oldMap_bracket`, `IsFree.bracket_apply`, `IsFree.bracket_newPosition_gradNew`, `IsFree.bracket_gradNew_gradNew`, `IsFree.isPoissonHom_transformation`, `IsFree.transformation_comp_inverse`, `IsFree.inverse_comp_transformation`, `exchange`, `isFree_exchange`, `transformation_exchange_q`, `transformation_exchange_p` |
| [Poisson/CompleteIntegral](../ProjectAInos/Mechanics/Poisson/CompleteIntegral.lean) | `ActionSpace`, `substitution`, `IsHamiltonJacobi`, `along`, `momentum`, `timeDerivative_along`, `partialDerivation_substitution_q`, `isTrajectory_of_isHamiltonJacobi`, `freeAction`, `isHamiltonJacobi_freeAction`, `isTrajectory_freeAction` |
| [Poisson/Separation](../ProjectAInos/Mechanics/Poisson/Separation.lean) | `positionsToAction`, `parameter`, `substitution_p`, `substitution_positionsToPhase`, `stackelHamiltonian`, `substitution_stackelHamiltonian`, `isHamiltonJacobi_stackel`, `nestedHamiltonian`, `nestedMatrix`, `isHamiltonJacobi_nested`, `kinetic`, `isHamiltonJacobi_nested_of_separated`, `liouvilleHamiltonian`, `liouvilleMatrix`, `isHamiltonJacobi_liouville`, `isHamiltonJacobi_liouville_of_separated`, `linearAction`, `quadraticEnergy`, `isHamiltonJacobi_nested_freeAction`, `isHamiltonJacobi_liouville_freeAction` |
| [Poisson/ActionFunction](../ProjectAInos/Mechanics/Poisson/ActionFunction.lean) | `CompleteIntegral.IsHamiltonJacobi.timeDerivative_along` |
| [KnifeEdge](../ProjectAInos/Mechanics/KnifeEdge.lean) | `Configuration`, `cosθ`, `sinθ`, `cos_mul_cos_add_sin_mul_sin`, `along`, `turn`, `across`, `constraint`, `constraint_across`, `commutator_turn_along`, `derivation_apply`, `eq_algebraMap_of_along_eq_zero_of_turn_eq_zero` |
| [Rutherford](../ProjectAInos/Mechanics/Rutherford.lean) | `eccentricity_sq_sub_one`, `cot_half_eq`, `hasDerivAt_impactParameter`, `rutherford` |
| [Scattering/RadialMotion](../ProjectAInos/Mechanics/Scattering/RadialMotion.lean) | `IsFactor`, `parameter`, `radius`, `radialVelocity`, `IsFactor.radialVelocity_sq`, `IsFactor.radialVelocity_pos`, `IsFactor.radius_neg`, `IsFactor.tendsto_radius_atTop`, `IsFactor.hasDerivAt_radialVelocity`, `exists_isFactor_dividedDifference`, `angle`, `IsFactor.angle_neg` |
| [Scattering/Deflection](../ProjectAInos/Mechanics/Scattering/Deflection.lean) | `angleDensity`, `deflectionAngle`, `image_Ioc_radius`, `integral_angleDensity_eq`, `tendsto_angle_atTop`, `integrableOn_angleDensity_Ioi` |
| [Scattering/Asymptote](../ProjectAInos/Mechanics/Scattering/Asymptote.lean) | `IsFactor.tendsto_angle_atTop`, `IsFactor.tendsto_angle_atBot`, `IsFactor.tendsto_radialVelocity_atTop`, `position`, `velocity`, `position_cross_velocity`, `IsFactor.hasDerivAt_position`, `IsFactor.hasDerivAt_velocity`, `IsFactor.tendsto_velocity_atTop`, `IsFactor.tendsto_velocity_atBot`, `asymptote_inner`, `arccos_cos_deflection` |
| [Scattering/Coulomb](../ProjectAInos/Mechanics/Scattering/Coulomb.lean) | `speedSq`, `closest`, `factor`, `speedSq_eq`, `isFactor`, `hasDerivAt_primitive`, `integral_angleDensity`, `tendsto_angle_atTop`, `tendsto_velocity_atTop`, `tendsto_velocity_atBot`, `hasDerivAt_velocity`, `deflection`, `sin_half_deflection`, `cot_half_deflection`, `deflection_mem_Ioo`, `deflection_neg`, `abs_deflection_le`, `arccos_cos_deflection` |
| [Scattering/CrossSection](../ProjectAInos/Mechanics/Scattering/CrossSection.lean) | `impactMeasure`, `solidAngle`, `crossSection`, `crossSection_apply`, `Coulomb.impact`, `Coulomb.deflection_impact`, `Coulomb.impact_deflection`, `Coulomb.crossSection_coulomb`, `Coulomb.abs_deflection`, `Coulomb.crossSection_coulomb_abs` |
| [Oscillations/PhaseVolume](../ProjectAInos/Mechanics/Oscillations/PhaseVolume.lean) | `Oscillator.map_flowMatrix_volume`, `Oscillator.measurePreserving_flowMatrix` |
| [Poisson/Liouville](../ProjectAInos/Mechanics/Poisson/Liouville.lean) | `divergence`, `divergence_eq`, `divergence_hamiltonian`, `divergence_dissipativeField`, `Oscillator.divergence_dissipativeField` |
| [Poisson/HamiltonianField](../ProjectAInos/Mechanics/Poisson/HamiltonianField.lean) | `realCurve`, `lift_apply_const`, `isIntegralCurve_iff_hasDerivAt`, `isTrajectory_iff_hasDerivAt`, `traceCLM_fderiv_realField`, `hamiltonianField`, `contDiff_hamiltonianField`, `isTrajectory_canonical_iff_hasDerivAt`, `traceCLM_fderiv_hamiltonianField`, `volume_image_hamiltonianFlow`, `measurePreserving_hamiltonianFlow`, `IsTrajectory.flow_eq`, `exists_isTrajectory` |
| [Poisson/LiouvilleFlow](../ProjectAInos/Mechanics/Poisson/LiouvilleFlow.lean) | `Oscillator.flowDomain_hamiltonianField`, `Oscillator.measurePreserving_hamiltonianFlow`, `Pendulum.hamiltonian`, `Pendulum.flowDomain_hamiltonianField`, `Pendulum.measurePreserving_hamiltonianFlow`, `Pendulum.exists_isTrajectory`, `Oscillator.flowDomain_dissipativeField`, `Oscillator.volume_image_dissipativeFlow` |
| [Poisson/PhaseAction](../ProjectAInos/Mechanics/Poisson/PhaseAction.lean) | `liouvilleForm`, `phaseLagrangian`, `momentum_phaseLagrangian`, `pathEnergy_phaseLagrangian`, `eulerLagrange_phaseLagrangian`, `hamiltonian_flow_eq`, `hasDerivAt_action_hamiltonianFlow` |
| [Poisson/SymplecticFlow](../ProjectAInos/Mechanics/Poisson/SymplecticFlow.lean) | `symplecticForm`, `hessianForm`, `symplecticForm_fderiv_hamiltonianField`, `symplecticForm_fderiv_hamiltonianField_add`, `symplecticForm_fderiv_flow` |
| [Poisson/LocalAction](../ProjectAInos/Mechanics/Poisson/LocalAction.lean) | `startDomain`, `endPosition`, `endMomentum`, `exists_initialMomentum`, `localAction`, `actionDifferential`, `hasDerivAt_localAction_line`, `exists_localAction`, `localAction_hamiltonJacobi`, `flow_kineticEnergy`, `isInvertible_fderiv_endPosition_kineticEnergy`, `exists_localAction_kineticEnergy` |
| [Poisson/CyclicReduction](../ProjectAInos/Mechanics/Poisson/CyclicReduction.lean) | `momentumEquation`, `momentumIdeal`, `inclusion`, `restriction`, `restriction_inclusion`, `bracket_momentumEquation`, `mem_normalizer_iff`, `isCoisotropic_momentumIdeal`, `inclusion_mem_normalizer`, `isPoissonHom_inclusion`, `sub_fixMomenta_mem`, `partialDerivation_fixMomenta`, `sub_inclusion_restriction_mem`, `reductionHom`, `reductionHom_bijective`, `isPoissonHom_reductionHom`, `reductionHom_restriction`, `mem_normalizer_of_cyclic`, `isIntegral_p_of_cyclic`, `p_eq_algebraMap_of_cyclic`, `isTrajectory_restriction`, `map_mem_normalizer`, `apply_mem_normalizer`, `canonicalReductionHom`, `canonicalReductionHom_bijective`, `isPoissonHom_canonicalReductionHom`, `canonicalReductionHom_restriction` |
| [Poisson/ReducedMass](../ProjectAInos/Mechanics/Poisson/ReducedMass.lean) | `CentreSpace`, `centreCoordinates`, `particleCoordinates`, `centreCoordinates_particleCoordinates`, `particleCoordinates_centreCoordinates`, `isPoissonHom_centreCoordinates`, `totalMomentumIdeal`, `reducedMassHom`, `reducedMassHom_bijective`, `isPoissonHom_reducedMassHom`, `hamiltonian`, `relativeHamiltonian`, `particleCoordinates_hamiltonian`, `restriction_particleCoordinates_hamiltonian`, `hamiltonian_mem_normalizer`, `reducedMassHom_relativeHamiltonian`, `isIntegral_totalMomentum`, `isTrajectory_relative` |
| [Routhian](../ProjectAInos/Mechanics/Routhian.lean) | `RouthSpace`, `Routhian.partialLegendre`, `partialEnergy`, `partialHessian`, `apply_partialLegendre`, `IsPartiallyHyperregular`, `routhian`, `IsPartiallyHyperregular.inversePartialHessian_mul_partialHessian`, `IsPartiallyHyperregular.partialLegendre_partialDerivation_p_routhian`, `IsPartiallyHyperregular.partialLegendre_partialDerivation_q_routhian`, `IsPartiallyHyperregular.partialLegendre_partialDerivation_v_routhian`, `IsPartiallyHyperregular.partialDerivation_q_routhian_eq_zero`, `routhCurve`, `lift_routhCurve`, `IsRouthTrajectory`, `IsPartiallyHyperregular.isRouthTrajectory_routhCurve_iff`, `IsPartiallyHyperregular.eq_routhCurve`, `restriction`, `reducedRouthian`, `IsRouthTrajectory.p_eq_algebraMap`, `IsRouthTrajectory.isSolution_reducedRouthian`, `naturalInverse`, `isPartiallyHyperregular_natural` |
| [Elementary](../ProjectAInos/Mechanics/Elementary.lean) | `ringCos`, `ringSin`, `ringCos_mul_ringCos_add_ringSin_mul_ringSin`, `apply_ringCos`, `apply_ringSin`, `map_ringCos`, `map_ringSin`, `exp_zero`, `exp_mul_exp_neg`, `apply_exp` |
| [Poisson/CentralField](../ProjectAInos/Mechanics/Poisson/CentralField.lean) | `Plane`, `Polar`, `Radial`, `r`, `rInv`, `cosφ`, `sinφ`, `bracket_eq`, `polarCoordinates`, `isPoissonHom_polarCoordinates`, `polarCoordinates_q_sq`, `polarCoordinates_p_sq`, `angularMomentum`, `polarCoordinates_angularMomentum`, `hamiltonian`, `polarHamiltonian`, `logPotential`, `polarCoordinates_hamiltonian`, `partialDerivation_polarHamiltonian`, `radialHamiltonian`, `restriction_polarHamiltonian`, `radius`, `radialMomentum`, `radialHamiltonian_eq`, `canonical_radius_radialMomentum`, `polarHamiltonian_mem_normalizer`, `reductionHom_radialHamiltonian`, `isTrajectory_plane`, `lift_angularMomentum`, `pφ_eq_algebraMap`, `isTrajectory_radial`, `timeDerivative_angle`, `q_dotProduct_M`, `sum_q_mul_M_eq_zero` |
| [OneDimension/Well](../ProjectAInos/Mechanics/OneDimension/Well.lean) | `IsWell`, `wellFactor`, `IsWell.sub_eq`, `IsWell.wellFactor_pos`, `isWell_of_wellFactor_pos`, `exists_level_point`, `IsWell.exists_family`, `isWell_oscillator` |
| [OneDimension/Orbit](../ProjectAInos/Mechanics/OneDimension/Orbit.lean) | `orbitPosition`, `orbitMomentum`, `orbitRate`, `orbitPeriod`, `IsWell.orbit_energy`, `IsWell.orbitRate_mul_orbitMomentum`, `IsWell.hasDerivAt_orbitMomentum`, `IsWell.orbitPeriod_eq`, `IsWell.orbitPeriod_pos` |
| [OneDimension/Motion](../ProjectAInos/Mechanics/OneDimension/Motion.lean) | `field`, `energy`, `orbitTime`, `orbitAngle`, `wellMotion`, `IsWell.hasDerivAt_wellMotion`, `IsWell.wellMotion_add_period`, `IsWell.flow_field_eq`, `IsWell.exists_wellMotion_eq`, `IsWell.add_period_of_hasDerivAt`, `IsWell.position_add_period` |
| [OneDimension/Area](../ProjectAInos/Mechanics/OneDimension/Area.lean) | `orbitArea`, `IsWell.orbitArea_eq`, `contDiffOn_orbitMomentum_family`, `orbitMomentum_mul_deriv_energy`, `hasDerivAt_orbitArea`, `IsWell.exists_hasDerivAt_orbitArea` |
| [OneDimension/Abel](../ProjectAInos/Mechanics/OneDimension/Abel.lean) | `lintegral_inv_sqrt_mul_inv_sqrt`, `lintegral_levelTime_mul`, `IsWell.lintegral_inv_sqrt_eq`, `abel_inversion` |
| [OneDimension/ActionAngle](../ProjectAInos/Mechanics/OneDimension/ActionAngle.lean) | `orbitAction`, `orbitPhase`, `hasDerivAt_orbitAction`, `strictMonoOn_orbitAction`, `IsWell.orbitPhase_add_two_pi`, `IsWell.orbitPhase_orbitAngle`, `orbit_area_form` |
| [OneDimension/Oscillator](../ProjectAInos/Mechanics/OneDimension/Oscillator.lean) | `wellFactor_oscillator`, `orbitPeriod_oscillator`, `orbitAction_oscillator`, `abel_inversion_oscillator` |
| [OneDimension/Anharmonic](../ProjectAInos/Mechanics/OneDimension/Anharmonic.lean) | `potential`, `factor`, `wellFactor_potential`, `slopeEquation`, `potential_centre`, `exists_slope`, `exists_isWell`, `symRoot`, `inv_sqrt_add_inv_sqrt`, `kernel`, `periodFunction`, `orbitPeriod_eq_periodFunction`, `periodFunction_zero`, `hasDerivAt_kernel`, `hasDerivAt_periodFunction`, `hasDerivAt_frequency`, `exists_tendsto_frequency` |
| [OneDimension/WellFamily](../ProjectAInos/Mechanics/OneDimension/WellFamily.lean) | `slopeOf`, `contDiff_wellFactor_family`, `exists_level_point_family`, `IsWell.exists_family_param`, `contDiffOn_orbitRate_family`, `contDiffOn_orbitPeriod_family`, `contDiffOn_orbitArea_family`, `contDiffOn_integral_orbitRate_mul`, `orbitMomentum_mul_deriv_param`, `hasDerivAt_orbitArea_family`, `hasDerivAt_orbitArea_line`, `fderiv_orbitArea_family` |
| [OneDimension/AdiabaticInvariant](../ProjectAInos/Mechanics/OneDimension/AdiabaticInvariant.lean) | `IsWellFamily`, `exists_isWellFamily`, `period`, `area`, `parameterForce`, `fderiv_area`, `energyAt`, `frozenField`, `invariant`, `invariantDeriv`, `fderiv_invariant_frozenField`, `fderiv_invariant_parameter`, `wellRegion`, `exists_orbit`, `flow_extendedField`, `hasDerivAt_weighted_shift`, `corrector`, `contDiffAt_corrector`, `fderiv_corrector_frozenField`, `exists_forall_abs_invariant_sub_le`, `isWellFamily_oscillator`, `invariant_oscillator` |
| [Quadrature](../ProjectAInos/Mechanics/Quadrature.lean) | `integral_comp_eq_integral_div_sqrt`, `sub_eq_integral_one_div_sqrt`, `sub_eq_sqrt_mul_integral_of_energy` |
| [Poisson/OrbitIntegral](../ProjectAInos/Mechanics/Poisson/OrbitIntegral.lean) | `canonical_radius_radialHamiltonian`, `radiusAt`, `radialVelocityAt`, `radialSpeedSq`, `lift_radialHamiltonian_apply`, `hasDerivAt_radiusAt`, `continuous_radialVelocityAt`, `radialVelocityAt_sq`, `continuousOn_radialSpeedSq`, `sub_eq_integral_radius`, `angle_sub_eq_integral_radius`, `timeDerivative_angle_apply` |
| [TurningPoint](../ProjectAInos/Mechanics/TurningPoint.lean) | `turningParam`, `turningParam_image`, `turningParam_sub_mul_sub`, `integral_turningParam`, `integral_div_sqrt_turning`, `integrableOn_div_sqrt_turning`, `integral_comp_eq_integral_div_sqrt_turning`, `integral_comp_eq_integral_div_sqrt_turning_of_neg`, `sub_eq_integral_turningParam`, `sub_eq_sqrt_mul_integral_of_energy_turning`, `sqrt_mul_integral_oscillator`, `sub_eq_sqrt_mul_integral_oscillator` |
| [Poisson/Apsides](../ProjectAInos/Mechanics/Poisson/Apsides.lean) | `integral_comp_radiusAt_eq_integral_turningParam`, `integral_comp_radiusAt_eq_integral_turningParam_of_neg`, `sub_eq_integral_turningParam_radius`, `angle_sub_eq_integral_turningParam_radius`, `keplerPotential`, `radialSpeedSq_kepler`, `kepler_radialSpeedSq_eq`, `kepler_integral_turningParam`, `kepler_sub_eq`, `kepler_sub_eq_of_neg`, `kepler_period` |
| [Similarity](../ProjectAInos/Mechanics/Similarity.lean) | `TimeFunction.scale`, `TimeFunction.timeDerivative_scale`, `TimeFunction.scale_lift`, `dilate`, `lift_dilate`, `IsHomogeneous`, `IsHomogeneous.dilate_partialDerivation`, `StandardJet.IsSolution.similar`, `similar_apply_add_period` |
| [Poisson/VirialAverage](../ProjectAInos/Mechanics/Poisson/VirialAverage.lean) | `TimeFunction.tendsto_average_timeDerivative`, `IsTrajectory.tendsto_average_virial` |
| [Poisson/KeplerOrbit](../ProjectAInos/Mechanics/Poisson/KeplerOrbit.lean) | `IsKeplerMotion.conic`, `IsKeplerMotion.similar`, `similar_period` |
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
