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
brackets and the brackets of the inverse distance, `{ρ, qⱼ} = 0` and
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

`KeplerModel` shows that Kepler frames exist: the free C∞-ring on `q`, `p` and
`ρ` with these generator brackets is a Poisson structure (`KeplerModel.poisson`;
the only nontrivial case of the Jacobi identity is `ρ, pⱼ, pₖ`), and the ideal
generated by the constraint is a Poisson ideal
(`isPoissonIdeal_constraintIdeal`), so identities modulo the constraint are
compatible with the bracket.

`KeplerMotion` turns this into statements about solutions. A *Kepler motion* is
a triple of smooth functions of time with `R² |Q|² = 1`, `Q̇ = P / m` and
`Ṗ = −α R³ Q`: Newton's equations for the inverse-square force with `R` the
inverse distance. `IsKeplerMotion.timeDerivative_R` derives the evolution of `R`
from the constraint, `isTrajectory` shows that the motion is a trajectory of the
Kepler Hamiltonian, and `rungeLenz_eq`, `angularMomentum_eq` and
`hamiltonian_eq` prove that the Runge–Lenz vector, the angular momentum and the
energy, computed from `Q`, `P` and `R`, take the same value at all times. The
orbit identity then holds at every time with `r` the distance
(`R_mul_distance`, `distance_mul_distance`). `isKeplerMotion_circular` is the
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
is the equation of motion `Ṁ = 0`; it is not derived here from a Lagrangian.

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

The decomposition of the space of the modes into irreducible representations
and the number of modes of each symmetry type are not proved.

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

The existence of a fundamental system for a general smooth coefficient is not
proved; it is the data of the theorems. The cases in which solutions are
unbounded and the width of the instability zone are not treated.

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
  `gᵢ (∂S/∂qᵢ)²/2m + uᵢ = Σⱼ Φᵢⱼ αⱼ` and `∂S/∂t = −αⱼ₀`, then `S` satisfies the
  Hamilton–Jacobi equation.
- `nestedHamiltonian m ρ σ a b c` is
  `p₀²/2m + a + ρ (p₁²/2m + b + σ (p₂²/2m + c))`.
  `isHamiltonJacobi_nested_of_separated`: the equations
  `(∂S/∂q₀)²/2m + a = α₀ − ρ α₁`, `(∂S/∂q₁)²/2m + b = α₁ − σ α₂`,
  `(∂S/∂q₂)²/2m + c = α₂` and `∂S/∂t = −α₀` give a solution. In spherical
  co-ordinates `ρ = 1/r²` and `σ = 1/sin²θ`.
- `liouvilleHamiltonian m λ g₀ g₁ κ₀ κ₁ u₀ u₁ u₂` is
  `λ (g₀ p₀²/2m + u₀ + g₁ p₁²/2m + u₁ + (κ₀ + κ₁)(p₂²/2m + u₂))`.
  `isHamiltonJacobi_liouville_of_separated`: with `λ (w₀ + w₁) = 1`, the
  equations `g₀ (∂S/∂q₀)²/2m + u₀ = w₀ α₀ + α₁ − κ₀ α₂`,
  `g₁ (∂S/∂q₁)²/2m + u₁ = w₁ α₀ − α₁ − κ₁ α₂`, `(∂S/∂q₂)²/2m + u₂ = α₂` and
  `∂S/∂t = −α₀` give a solution. This is the form in parabolic and in
  elliptic co-ordinates.

The coefficient functions are elements of the free C∞-ring, smooth on all of
`ℝ³`. The coefficients `1/r²`, `1/sin²θ` and `1/(ξ + η)` of the classical
co-ordinate systems are smooth only on open subsets, so those systems are not
instances as stated. The quadratures that give `S` are not constructed, and
the completeness of the integral is not checked.

`Poisson/Liouville` defines the divergence `Σₐ ∂ₐ (X xₐ)` of a vector field on
a free C∞-ring with finitely many generators. `divergence_hamiltonian`: a
Hamiltonian vector field of the canonical bracket has zero divergence, the
infinitesimal form of Liouville's theorem (Landau–Lifshitz §46).
`divergence_dissipativeField`: with friction the divergence is
`−Σᵢ ∂fᵢ/∂pᵢ`, and for the oscillator with the friction coefficients `aᵢ` it
is the constant `−Σᵢ aᵢ/mᵢ` (`Oscillator.divergence_dissipativeField`). The
invariance of the Lebesgue measure under a flow is not proved.

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
`M = M(0)`, the equation of a conic with a focus at the centre.
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
| [Constants](../ProjectAInos/Mechanics/Constants.lean) | `lift_eq_of_partialDerivation_eq_zero`, `eq_algebraMap_of_partialDerivation_eq_zero` |
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
| [Poisson/Trajectory](../ProjectAInos/Mechanics/Poisson/Trajectory.lean) | `IsTrajectory`, `IsTrajectory.timeDerivative_lift`, `IsTrajectory.lift_eq_of_isIntegral`, `IsTrajectory.lift_eq_of_bracket_mem`, `IsTrajectory.lift_hamiltonian_eq`, `isTrajectory_canonical_iff`, `RigidBody.lift_casimir_eq`, `AngularMomentum.lift_M_eq`, `HeavyTop.lift_Γ_sq_eq`, `HeavyTop.lift_L_dot_Γ_eq` |
| [TwoBody/Kinematics](../ProjectAInos/Mechanics/TwoBody/Kinematics.lean) | `reducedMass`, `centreOfMassVelocity`, `total_mass_mul_kinetic`, `kineticEnergy_eq`, `velocity_one_eq`, `velocity_two_eq`, `momentum_one_centreOfMass`, `momentum_two_centreOfMass` |
| [TwoBody/Collisions](../ProjectAInos/Mechanics/TwoBody/Collisions.lean) | `disintegration_momentum_sq`, `disintegration_kinetic_one`, `disintegration_energy_nonneg`, `IsElastic`, `outgoingOne`, `outgoingTwo`, `IsElastic.relative_speed`, `isElastic_outgoing`, `isElastic_iff`, `outgoingOne_rest_dotProduct_self`, `outgoingTwo_rest_dotProduct_self`, `outgoingOne_headOn`, `energy_transfer_le`, `outgoing_rest_dotProduct_eq_zero` |
| [Poisson/TwoBody](../ProjectAInos/Mechanics/Poisson/TwoBody.lean) | `centre`, `relative`, `totalMomentum`, `relativeMomentum`, `canonical_centre_totalMomentum`, `canonical_relative_relativeMomentum`, `canonical_centre_relativeMomentum`, `canonical_relative_totalMomentum`, `kineticEnergy_eq_centre` |
| [Rigid/AngularVelocity](../ProjectAInos/Mechanics/Rigid/AngularVelocity.lean) | `hat`, `vee`, `hat_mulVec`, `hat_cross`, `hat_vee`, `hatEquiv`, `hatEquiv_cross`, `velocityField`, `velocityField_add`, `velocityField_injective`, `velocityField_change_of_origin`, `transpose_deriv_mul_transpose`, `angularVelocity`, `hasDerivAt_rigidMotion` |
| [Rigid/EulerAngles](../ProjectAInos/Mechanics/Rigid/EulerAngles.lean) | `rotZ`, `rotX`, `eulerMatrix`, `eulerMatrixDeriv`, `bodyAngularVelocity`, `spaceAngularVelocity`, `eulerMatrix_mul_transpose`, `det_eulerMatrix`, `transpose_mul_eulerMatrixDeriv`, `eulerMatrixDeriv_mul_transpose`, `eulerMatrix_mulVec_bodyAngularVelocity`, `symmetricTop_energy`, `det_eulerJacobian`, `eulerRotation`, `eulerRotation_mem_specialOrthogonalGroup`, `hasDerivAt_eulerRotation`, `angularVelocity_eulerRotation` |
| [Rigid/RegularPrecession](../ProjectAInos/Mechanics/Rigid/RegularPrecession.lean) | `symmetricTopMomentum`, `verticalAxis`, `eulerMatrix_mulVec_verticalAxis`, `transpose_eulerMatrix_mulVec`, `eulerMatrix_mulVec_symmetricTopMomentum`, `eulerMatrix_mulVec_symmetricTopMomentum_iff`, `regularPrecession_psi_rate`, `eulerRotation_mulVec_symmetricTopMomentum` |
| [Poisson/RigidBodyMotion](../ProjectAInos/Mechanics/Poisson/RigidBodyMotion.lean) | `isTrajectory_kineticEnergy_iff`, `isTrajectory_principalRotation`, `isTrajectory_symmetricTop`, `stabilityForm`, `isIntegral_stabilityForm`, `sum_mul_sq_eq`, `mul_sq_le_of_greatest`, `mul_sq_le_of_least`, `linearization_zero_two`, `linearization_two_zero`, `linearization_mul_pos_of_middle`, `linearization_mul_neg_of_greatest`, `linearization_mul_neg_of_least` |
| [Rigid/InertiaTensor](../ProjectAInos/Mechanics/Rigid/InertiaTensor.lean) | `inertia`, `transpose_inertia`, `inertia_mulVec`, `dotProduct_inertia_mulVec`, `dotProduct_inertia_mulVec_nonneg`, `trace_inertia`, `two_mul_dotProduct_inertia_mulVec_le_trace`, `inertia_add_apply`, `principalMoments`, `principalAxes`, `inertia_mulVec_principalAxes`, `principalMoments_nonneg`, `principalMoments_two_le` |
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
| [Oscillations/Parametric](../ProjectAInos/Mechanics/Oscillations/Parametric.lean) | `mul_self_eq`, `sin_smul_pow_succ`, `exists_abs_pow_apply_le`, `IsHill`, `wronskian`, `IsHill.wronskian_eq`, `TimeFunction.shift`, `IsHill.shift`, `state`, `FundamentalSystem`, `FundamentalSystem.eq_combination`, `FundamentalSystem.matrix`, `FundamentalSystem.det_matrix`, `FundamentalSystem.state_eq`, `FundamentalSystem.matrix_add_nat_mul_period`, `FundamentalSystem.exists_abs_apply_le`, `FundamentalSystem.exists_abs_apply_le_of_abs_trace_lt`, `FundamentalSystem.harmonic` |
| [Legendre](../ProjectAInos/Mechanics/Legendre.lean) | `positionsToJet`, `positionsToPhase`, `d_zero_positionsToJet`, `orderLE_positionsToJet`, `legendre`, `legendre_p_eq_momentum`, `legendre_hamiltonian`, `isTrajectory_natural_iff`, `isSolution_natural_iff`, `isTrajectory_natural_iff_isSolution` |
| [Hyperregular](../ProjectAInos/Mechanics/Hyperregular.lean) | `JetRing.sum_mul_d_q_self`, `VelocitySpace`, `VelocitySpace.momentum`, `VelocitySpace.legendre`, `VelocitySpace.energy`, `VelocitySpace.hessian`, `VelocitySpace.apply_legendre`, `VelocitySpace.IsHyperregular`, `VelocitySpace.hamiltonian`, `VelocitySpace.inverseHessian`, `IsHyperregular.inverseHessian_mul_hessian`, `IsHyperregular.legendre_hamiltonian`, `IsHyperregular.legendre_partialDerivation_inr_hamiltonian`, `IsHyperregular.legendre_partialDerivation_inl_hamiltonian`, `VelocitySpace.velocityCurve`, `VelocitySpace.toJet`, `VelocitySpace.prolongation_toJet`, `VelocitySpace.isSolution_toJet_iff`, `IsHyperregular.isTrajectory_iff`, `IsHyperregular.isTrajectory_iff_isSolution`, `VelocitySpace.lagrangeBracket`, `IsHyperregular.legendre_bracket`, `IsHyperregular.lagrangeBracket_q_v`, `VelocitySpace.natural`, `VelocitySpace.isHyperregular_natural`, `VelocitySpace.hamiltonian_natural`, `VelocitySpace.toJet_natural` |
| [Poisson/GeneratingFunction](../ProjectAInos/Mechanics/Poisson/GeneratingFunction.lean) | `PositionPair`, `oldPosition`, `newPosition`, `gradOld`, `gradNew`, `oldMap`, `newMap`, `mixedHessian`, `oldHessian`, `apply_oldMap`, `gradNew_oldMap`, `gradOld_oldMap`, `IsFree`, `transformation`, `momentumPart`, `positionPart`, `inverseMixed`, `IsFree.inverseMixed_mul_mixedHessian`, `IsFree.momentumPart_eq`, `IsFree.oldMap_bracket`, `IsFree.bracket_apply`, `IsFree.bracket_newPosition_gradNew`, `IsFree.bracket_gradNew_gradNew`, `IsFree.isPoissonHom_transformation`, `IsFree.transformation_comp_inverse`, `IsFree.inverse_comp_transformation`, `exchange`, `isFree_exchange`, `transformation_exchange_q`, `transformation_exchange_p` |
| [Poisson/CompleteIntegral](../ProjectAInos/Mechanics/Poisson/CompleteIntegral.lean) | `ActionSpace`, `substitution`, `IsHamiltonJacobi`, `along`, `momentum`, `timeDerivative_along`, `partialDerivation_substitution_q`, `isTrajectory_of_isHamiltonJacobi`, `freeAction`, `isHamiltonJacobi_freeAction`, `isTrajectory_freeAction` |
| [Poisson/Separation](../ProjectAInos/Mechanics/Poisson/Separation.lean) | `positionsToAction`, `parameter`, `substitution_p`, `substitution_positionsToPhase`, `stackelHamiltonian`, `substitution_stackelHamiltonian`, `isHamiltonJacobi_stackel`, `nestedHamiltonian`, `nestedMatrix`, `isHamiltonJacobi_nested`, `kinetic`, `isHamiltonJacobi_nested_of_separated`, `liouvilleHamiltonian`, `liouvilleMatrix`, `isHamiltonJacobi_liouville`, `isHamiltonJacobi_liouville_of_separated` |
| [Poisson/Liouville](../ProjectAInos/Mechanics/Poisson/Liouville.lean) | `divergence`, `divergence_eq`, `divergence_hamiltonian`, `divergence_dissipativeField`, `Oscillator.divergence_dissipativeField` |
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
