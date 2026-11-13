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

These statements are identities in a ring. The prolongation of a path turns them into statements about trajectories. `TimeFunction` is the C∞-ring of smooth functions of time and `timeDerivative` is `d/dt`; `TimeFunction.timeDerivative_apply` proves that it is Mathlib's `deriv` of the function of a real variable. Both live in their own module and are shared with the Hamiltonian trajectories below. For a smooth path `γ : ι → TimeFunction`, `StandardJet.prolongation γ` is the morphism from the standard jet ring that sends the time coordinate to `t` and `qᵢ⁽ᵏ⁾` to the `k`-th derivative of `γᵢ`. `prolongation_totalDeriv` proves that it turns the total derivative into `d/dt`. `IsSolution L γ` means that the prolongation annihilates every `Eᵢ(L)`; it then annihilates the Euler–Lagrange ideal, and `prolongation_eq_of_conserved` proves that a conserved element takes the same value at all times along a solution.

For a natural Lagrangian, `isSolution_naturalLagrangian_iff` identifies the solutions with the smooth solutions of Newton's equations `mᵢ γ̈ᵢ = −∂ᵢU` along the path, and `energy_eq_of_isSolution` proves that `Σᵢ ½ mᵢ γ̇ᵢ² + U(γ)` is constant in time when `∂ₜU = 0`. The isotropic oscillator has `mᵢ γ̈ᵢ = −k γᵢ`, and uniform motion is a solution of the free equations, so solutions exist. Paths are smooth and defined for all times.

`Jet/Analytic` identifies this notion of solution with the variational one at the top of this guide. A smooth function `f` of time, position and velocity gives the jet-ring element `firstOrder f` and the analytic Lagrangian `ofSmoothOperation f`. For a smooth path `γ` with real path `realPath γ`:

- `prolongation_firstOrder_apply`: the prolongation of `firstOrder f` at time `t` is the Lagrangian on the path;
- `prolongation_euler_firstOrder_apply`: the prolongation of `Eᵢ(firstOrder f)` at time `t` is the Euler–Lagrange residual of the path in the direction of the `i`-th coordinate;
- `isSolution_firstOrder_iff_stationary`: `γ` is a solution exactly when the action is stationary under fixed-endpoint variations on every interval `[a, b]` with `a < b`.

Hence `prolongation_eq_of_stationary`: a conserved element of the jet ring takes the same value at all times along a smooth stationary path. `energy_eq_of_stationary` is the case of the energy `Σᵢ q̇ᵢ ∂L/∂q̇ᵢ − L` for a Lagrangian with `∂f/∂t = 0`, stated with real derivatives and no jet ring in the conclusion. The statement quantifies over all intervals because a solution in the jet ring is a condition at all times; paths that are only `C²` or defined on one interval are not covered.

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
| [Jet/Analytic](../ProjectAInos/Mechanics/Jet/Analytic.lean) | `firstOrder`, `orderLE_firstOrder`, `euler_firstOrder`, `realPath`, `realJet`, `prolongation_firstOrder_apply`, `fderiv_ofSmoothOperation`, `eulerLagrange_ofSmoothOperation`, `prolongation_euler_firstOrder_apply`, `isSolution_firstOrder_iff`, `isSolution_firstOrder_iff_stationary`, `prolongation_eq_of_stationary`, `energy_eq_of_stationary` |
| [Jet/Standard](../ProjectAInos/Mechanics/Jet/Standard.lean) | `StandardJet`, `jetRing`, `totalDeriv_eq_derivation`, `euler_q_mul_acceleration`, `euler_oscillator`, `conserved_energy_oscillator`, `conserved_boost_free` |
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
| [Rigid/InertiaTensor](../ProjectAInos/Mechanics/Rigid/InertiaTensor.lean) | `inertia`, `transpose_inertia`, `inertia_mulVec`, `dotProduct_inertia_mulVec`, `dotProduct_inertia_mulVec_nonneg`, `trace_inertia`, `two_mul_dotProduct_inertia_mulVec_le_trace`, `inertia_add_apply`, `principalMoments`, `principalAxes`, `inertia_mulVec_principalAxes`, `principalMoments_nonneg`, `principalMoments_two_le` |
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
