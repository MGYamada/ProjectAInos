# Charged Particles and Electromagnetic Fields

This guide records the implemented §4.1 local-field and charged-particle core,
the flat vacuum field-action theorem in §4.2 / [#44](https://github.com/MGYamada/ProjectAinos/issues/44),
and the fixed-background Maxwell form API from §5.1 / [#52](https://github.com/MGYamada/ProjectAinos/issues/52).
The free-particle action is shared with §3.2. The
[C∞ electrodynamics research plan](cinfty-electrodynamics.md) carries forward
the design from [issue #8](https://github.com/MGYamada/ProjectAinos/issues/8),
including the remaining sourced-action, stress-energy, wave and radiation
targets. The flat vacuum result does not complete that wider program.

## Conventions and local fields

Coordinates are `(t,x,y,z)`, `c = 1`, the metric is `(-+++)`, and the orientation
is `dt ∧ dx ∧ dy ∧ dz`. A potential is a continuous alternating one-form field;
regularity is an explicit hypothesis on an open set `U`. Lean functions are
total, but the local theorems make no regularity assertion outside `U`.

`potentialOf` expresses `A = −φ dt + a·dx`. The curvature is `fieldTensor A = dA`.
For C² potentials, `dF = 0`, with a cyclic directional/component formula.
For C¹ potentials and C² gauge functions on `U`, `A + dχ` has the same curvature
on `U`. Curvature commutes with smooth pullback, including Lorentz and Poincaré
maps. A global potential for an arbitrary closed form is not assumed.

For a future unit observer `u`, `electric u F = −ιᵤF` and
`magnetic u F = ιᵤ⋆F`. Both annihilate `u`; the existing observer reconstruction
theorem recovers `F` from them. `covectorPairing` is the inverse-metric pairing,
identified with the metric of raised covectors. On covectors annihilating `u`
it is the nonnegative Euclidean rest-space norm. Thus the proved formulas are

\[
\tfrac12 F_{\mu\nu}F^{\mu\nu}=|B|^2-|E|^2,
\qquad \tfrac14 F_{\mu\nu}(\star F)^{\mu\nu}=E\cdot B.
\]

The first is invariant under every Lorentz map. The second transforms by
`det L`, so a transformation reversing spacetime orientation changes its sign.
Changing only the chosen orientation also changes the Hodge operator's sign.

## Fixed-background Maxwell forms

`Electrodynamics/Curved.lean` works on an arbitrary smooth four-dimensional
Lorentz manifold with time-first signature `(-+++)`, an explicitly supplied
orientation, and constitutive normalization one. `CurrentVector` is a smooth
section of the actual tangent bundle; `Field`, `CurrentForm` and `Potential`
are native smooth two-, three- and one-forms. The definitions are

\[
H=-\star F,\qquad J=\star(j^\flat),\qquad dF=0,\quad dH=J.
\]

`currentOneForm` uses the existing metric `lower` and the proved smooth
covector/one-form equivalence. `currentVector` constructs the inverse current
identification using `⋆²=+1` in degrees one and three, then raises the covector.
Both roundtrip theorems are proved. `Maxwell` states the two physical equations
as explicit premises. The sourced equation alone implies `dJ=0` by `d²=0`;
no field-action derivation is assumed.

`source` constructs the unique smooth vector current from the actual `dH`.
`maxwell_iff` is equivalent to closedness of `F` and equality with this source.
`potential_maxwell` supplies a field and source from any global potential;
it does not assert global exactness for all closed fields. Reversing orientation
negates both `H` and `J`, preserving the equations. `excitation_flat` gives
exact agreement with minus the existing flat physical star.

`CurvedExamples.lean` computes `F=t dt∧dx`, `H=t dy∧dz`, and
`J=dt∧dy∧dz` directly, proves `dF=0` and proves the resulting source is nonzero.
`CurrentExamples.lean` now proves the actual vector sign `j=-∂x`, using the
injective current identification and volume contraction, and its divergence
vanishes. The corresponding SymPy calculation agrees. This fixes the sign of
the public source convention `∇_μF^{μν}=j^ν`. The matter current compatible
with the flat conventions `F_{0i}=-E_i` and particle coupling `+e∫A` is `-j`;
the [source sign contract](cinfty-electrodynamics.md#sourced-variation-and-the-matter-current)
records that bridge as a proof obligation.
Typed API examples fix the current roundtrips, the sole source-equation premise
for conservation, orientation independence and exact flat normalization.

`Electrodynamics/Current.lean` proves `currentForm_volume`: the physical
three-form is `ιⱼ vol` on the actual tangent fibre. The shared geometric
identity holds for either Lorentz sign, using only a pointwise signature
witness and its orientation sign. `currentForm_chart` derives the signed,
positive-density coordinate expression. The actual native exterior derivative
and the proved density formula then give `exteriorDerivative_currentForm`:

\[
dJ=(\operatorname{div}j)\,\mathrm{vol}_g.
\]

Since the volume form is nowhere zero, `current_closed_iff_divergence` is an
equivalence, and `divergence_zero_of_source` needs only the sourced Maxwell
equation. No flatness or globally extended chart is assumed. Typed contracts
fix these premises and conclusions. Exact SymPy checks a curved four-dimensional
metric with mixed coefficients, a vector field with nonzero divergence, both
metric signatures and both orientations.

The shared `TwoFormDerivative` constructs the actual smooth covariant tensor,
with `twoFormDerivative F x v w u = ∇ᵤF(v,w)`. Its two Christoffel corrections
are derived from the Levi-Civita connection. `TwoFormExterior` proves that
exterior differentiation is its alternating sum, using torsion-freeness, and
proves both directions of the equivalence with the cyclic covariant component
equation in every smooth chart. This holds in every dimension and either
Lorentz signature, without an orientation or a global frame.

`Homogeneous.lean` exposes `Maxwell.homogeneous_covariant` and
`Maxwell.homogeneous_components` for the physical four-dimensional background.
`HomogeneousExamples.lean` verifies the closed electric field and a nonclosed
two-form whose cyclic sum is exactly `1`. A shared curved example has constant
coordinate area but nonzero covariant derivative `-4x`, while remaining closed.
Typed examples fix the connection formula, equivalences and physical premise.
Exact SymPy checks all three tensor slots under a nonlinear chart change on a
curved mixed-coordinate metric, as well as the nonzero cyclic sum.

`TwoFormDivergence` now constructs the actual smooth vector `∇ᵢFⁱʲ`: metric
contraction of the first form slot with the derivative direction gives a
covector, and `sharp` raises the remaining index. The two inverse-metric factors
in every chart are proved consequences of this construction. `DualDerivative`
proves that covariant differentiation commutes with raising. `TwoFormRaised`
uses actual raised coordinate covectors to derive the two positive Christoffel
corrections; torsion-freeness cancels the antisymmetric contraction and yields
`∇ᵢFⁱʲ = ρ⁻¹ ∂ᵢ(ρ Fⁱʲ)`. No orientation is needed for these results.

Lean computes the divergence of `dt∧dx` on the curved conformal plane as
`(-4x exp(-4x²), 0)`. `DivergenceExamples.lean` proves that the existing electric
field has two-form divergence `-∂x`, exactly its source constructed from `dH`.
Typed API checks fix the native smoothness, contraction, raising and density
formulas. Exact SymPy checks the density identity and vector transformation in
a curved mixed-coordinate metric, including overall metric-sign reversal.

`ExcitationChart.lean` identifies the actual excitation with the signed
volume dual of `ρ Fⁱʲ`. The metric-free `BivectorVolume` derivative lemma
requires only local differentiability and local antisymmetry. Applying it in
an actual oriented chart proves, in `CurvedComponents.lean`,

```text
exteriorDerivative_excitation : dH = currentForm (twoFormDivergence F)
source_eq_twoFormDivergence    : source F = twoFormDivergence F
sourced_iff_divergence         : dH = currentForm j ↔ twoFormDivergence F = j
maxwell_iff_components        : Maxwell F j ↔ both covariant chart equations
```

These are native smooth-section equalities, on any smooth four-dimensional
`(-+++)` Lorentz manifold with an explicit oriented atlas. No global frame,
flatness, global chart extension or homogeneous-field hypothesis is required
for the sourced identity. `source_density` exposes the density formula in every
smooth chart. `source_reverse` proves orientation independence of the source
vector, and `divergence_twoFormDivergence` proves conservation for every field.
Default-option typed contracts fix these hypotheses and both directions of
the component equivalence. Exact SymPy independently compares `d(-⋆F)` with
`⋆((∇ᵢFⁱʲ)♭)` for six varying components in a curved metric with a nonlinear
shear, checking both orientations and vector-current conservation.

The reference for local forms is [Tong, §3.2](https://davidtong.org/teaching/general-relativity/grhtml/S3).
Our Hodge operator is fixed by `α ∧ ⋆β = ⟨α,β⟩ vol`. Compared with the
output-index-first epsilon ordering written in his (3.97), moving the input
indices first introduces `(-1)^(p*(n-p))`: the two-form signs agree in four
dimensions, while odd-degree conversion needs care. His `J` in (3.114) denotes
a one-form; our `J` is a three-form. The public equations here use
`H = -⋆F`, `J = ⋆(j♭)` and are calibrated by the proved example
`F = t dt∧dx`, `j = -∂x`; current notation and epsilon ordering must therefore
be converted before identifying textbook formulas.

## Vacuum field action (§4.2)

[`VacuumAction`](../ProjectAinos/Electrodynamics/VacuumAction.lean) uses the
time-first orientation to integrate the coefficient of `−½ F ∧ ⋆F` against
Lebesgue measure. The Lagrangian is defined on first jets. For a globally
C² potential with integrable action density on an open region, stationarity
under all smooth one-form variations compactly supported in that region is
equivalent to `d⋆F = 0` there. The proof computes the derivative of the
action, integrates the exterior derivative of a compactly supported
three-form, and uses the nondegenerate wedge pairing and the fundamental
lemma. The homogeneous equation `dF = 0` follows independently from
`F = dA`. An exact gauge shift preserves the action under the stated local
regularity hypotheses. The uniform electric example on an open unit ball
checks positive density `1/2`, a nonzero field, and stationarity.

## Actual action and admissible variations

The action is

\[
S[\gamma]=-m\int_a^b\sqrt{-g(\dot\gamma,\dot\gamma)}\,ds
       +e\int_a^b A_{\gamma(s)}(\dot\gamma(s))\,ds.
\]

Physical use takes `m > 0`, a C² path, and timelike velocity throughout the
closed interval. The action is total as a Lean function; its variational
theorem uses only its open admissible jet domain. No global C² hypothesis is
placed on the square root at null velocities.

The shared localization lemma constructs a globally C² representative that
agrees near the compact reference jet. The compact tube lemma proves that
every sufficiently small smooth variation remains in that neighborhood,
uniformly in the interval parameter. The already proved compact-interval
domination and differentiation theorem then applies to the actual action.
Local equality also preserves its first variation and Euler–Lagrange residual.

`Stationary` means that the derivative of the action vanishes for every smooth
fixed-endpoint variation. For `a < b` it is proved equivalent to Euler–Lagrange
on `(a,b)`. Computing the position and velocity derivatives gives

\[
m\,\frac{dU}{ds}=eF^{\mu\nu}\dot\gamma_\nu,
\qquad U=\frac{\dot\gamma}{\sqrt{-g(\dot\gamma,\dot\gamma)}}.
\]

For proper-time parametrization this becomes `m dUμ/dτ = e Fμν Uν` with both
indices of `F` raised. Force orthogonality and `g(mU,mU) = −m²` are proved;
positive mass and zero charge give zero four-acceleration. The general
algebraic force equation permits any real `m`; the massive physical reading
uses the stated positive-mass condition.

Gauge transformation changes the action by
`e (χ(γ(b)) − χ(γ(a)))`, also when `A` and `χ` are regular only on `U`.
This requires C¹ `χ` for the endpoint identity. The local C² action theorem
and its gauge stationarity equivalence require C³ `χ`, since `dχ` is part of
the transformed potential. Endpoints and the potential domain are explicit.

## Homogeneous polynomial jets

The Maxwell dependency closure consists of 11 upstream modules at commit
`3456e5e75cf8d4cd558955a5c7638fba2d68f464`. Five were already imported by
[PR #41](https://github.com/MGYamada/ProjectAinos/pull/41);
[PR #48](https://github.com/MGYamada/ProjectAinos/pull/48) supplied the remaining six.
Original `YM` namespaces and mathematical statements are preserved. See the
[provenance and compatibility record](../ProjectAinos/External/YM/PROVENANCE.md)
and [NOTICE](../NOTICE).

For a closed homogeneous curvature jet of degree `j`, the generic real normed
target version proves radial gauge and

\[
A_\nu(x)=\frac1{j+2}\sum_\mu x^\mu F_{\mu\nu}(x),\qquad dA=F.
\]

It includes scalar coefficients, agrees with the upstream color-valued
`contracted`, and commutes with continuous linear component extraction.
In the finite-dimensional color space every real linear functional is
continuous. An explicit continuous linear equivalence swaps axes 0 and 3:
`(t,x,y,z) ↦ (z,x,y,t)`. Coefficient evaluation and exterior differentiation
commute with this map. No metric identification or Wick rotation is involved.
The result is restricted to homogeneous polynomial exterior differentiation
and reconstruction, not global potential existence or continuum dynamics.

## A charge in a given field (§§15–25)

**The Hamiltonian in a static field (E9a, §§16–19).** The scalar potential
`φ` and the vector potential `a` are elements of the free ring of the
positions, in `d` space dimensions. `PhaseSpace.ofPosition` maps them into
the phase space. With the kinetic momentum `π = p − e a`,
`ChargedParticle.hamiltonian m e φ a = √(m² + Σ πᵢ²) + e φ`.

| Statement | Declaration |
| --- | --- |
| `{qᵢ, H} = πᵢ/√(m² + Σ πⱼ²)`, and the speed is less than one | `canonical_q_hamiltonian`, `sum_velocity_mul_self`, `sum_sq_hamiltonianField_lt_one` |
| `{πᵢ, πⱼ} = e Fᵢⱼ` with `Fᵢⱼ = ∂ᵢaⱼ − ∂ⱼaᵢ` | `canonical_kineticMomentum_kineticMomentum` |
| The equation of motion `{πᵢ, H} = e (Eᵢ + Σⱼ Fᵢⱼ vⱼ)` with `Eᵢ = −∂ᵢφ` | `canonical_kineticMomentum_hamiltonian` |
| The work of the electric field, `{√(m² + Σ πⱼ²), H} = e Σᵢ Eᵢ vᵢ` | `canonical_kineticEnergy_hamiltonian` |
| The momentum of a cyclic co-ordinate is an integral | `isIntegral_p_of_cyclic`; instances `isIntegral_p_uniformScalar`, `isIntegral_p_landauPotential` |
| Hamilton's equations are the equation of the Lorentz force with `ẋ = v(π)` | `isTrajectory_iff_lorentzForce` |
| The gauge change `a ↦ a + ∇χ` is the canonical transformation `p ↦ p + e ∇χ` | `momentumShift_hamiltonian`, `isTrajectory_gaugeShift`, `magneticTensor_gaugeShift` |
| The flow exists for all times and points and preserves the volume | `flowDomain_hamiltonianField`, `measurePreserving_hamiltonianFlow`, `exists_isTrajectory` |

The flow is complete for all smooth static potentials: the speed is less than
one, so in a finite time the position stays in a bounded set, where the force
is bounded (`NonlinearODE.flowDomain_eq_univ_of_bounded_inl`).

**The action of space-time (§17, §23).** In three dimensions
`ChargedParticle.staticPotential φ a` is the potential `−φ dt + a · dx`.
`fieldTensor_staticPotential` gives its field, and on the velocity `(1, u)`
the force has the space components `e (Eᵢ + Σⱼ Fᵢⱼ uⱼ)` and the time component
`e Σᵢ Eᵢ uᵢ` (`lorentzForce_staticPotential_succ`,
`lorentzForce_staticPotential_zero`). On the graph `t ↦ (t, x(t))` of a curve
with a speed less than one the action is stationary if and only if
`d/dt (m γ ẋᵢ) = e (Eᵢ + Σⱼ Fᵢⱼ ẋⱼ)` (`stationary_graph_iff_lorentzForce`): the
time component of the equation of space-time follows from the space
components, because the force and the acceleration are orthogonal to the
velocity. For `m > 0` this holds if and only if the curve
`(x, m γ ẋ + e a(x))` solves Hamilton's equations
(`stationary_graph_iff_hamilton`), and the graph of the positions of a
trajectory is stationary on every interval
(`stationary_graph_of_isTrajectory`).

**A constant field (§§20–22).** For a constant two-form `F`,
`ConstantField.potential F` is `½ ι_x F`, and
`ConstantField.generator m e F = (e/m) F♯` is the linear map of the equation
`u′ = (e/m) F♯ u` in the proper time. `velocity m e F u₀` and
`motion m e F x₀ u₀` are its solution for all proper times
(`LinearODE.linearVelocity`, `LinearODE.linearMotion`).

| Statement | Declaration |
| --- | --- |
| The interval of the four-velocity is constant, and it stays future timelike | `intervalQuadratic_velocity`, `futureTimelike_velocity` |
| For a unit four-velocity the motion is stationary on every interval | `stationary_motion` |
| Every stationary curve in the proper time has this four-velocity | `deriv_eq_velocity_of_stationary` |
| For `F = α ∧ β` the generator `A` satisfies `A³ = κ A`, `κ = (e/m)² (⟨α, β⟩² − ⟨α, α⟩ ⟨β, β⟩)` | `generator_of_isSimple`, `generator_cube`, `lorentzGenerator_cube` |
| `κ = Ω² > 0`: `u = u₀ + (sinh Ωτ/Ω) A u₀ + ((cosh Ωτ − 1)/Ω²) A² u₀` | `velocity_of_pos`, `motion_of_pos`; electric field `velocity_electric` |
| `κ = −Ω² < 0`: the same with `sin` and `1 − cos` | `velocity_of_neg`, `motion_of_neg`; magnetic field `velocity_magnetic` |
| `κ = 0`: `u = u₀ + τ A u₀ + (τ²/2) A² u₀` | `velocity_of_zero`, `motion_of_zero`; null field `velocity_nullField` |
| Two fields whose generators have zero products: the sum of the velocities minus `u₀` | `velocity_add`; parallel fields `velocity_uniformField` |
| The hyperbola of the earlier example is the motion with its initial data | `motion_eq_hyperbola` |

The three closed forms are one statement about a bounded operator with
`A³ = κ A` and functions with `s′ = 1 + κ c`, `c′ = s`
(`LinearODE.linearVelocity_eq_of_cube`, `linearMotion_eq_of_cube`).

**The transformation of the field (§24).** In the frame of the co-ordinates
`electricVector F` is `Eᵢ = F(eᵢ, e₀)` and `magneticVector F` is
`(F₂₃, F₃₁, F₁₂)`; they are the components of the electric and the magnetic
covector of the observer at rest (`electric_restObserver_single`,
`magnetic_restObserver_single`), and `twoForm_apply_vectors` writes `F(v, w)`
in them. The boost with the velocity `V` along the first axis is
`t ↦ γ (t − V x)`, `x ↦ γ (x − V t)` (`boost_axisVelocity_apply`). It maps the
four-velocity of the observer with the velocity `V` to the axis of the time,
so the components of the field for this observer are those of the pullback by
the inverse boost (`electric_observer_apply`, `magnetic_observer_apply`):

| Component | Value for the observer with the velocity `V` | Declaration |
| --- | --- | --- |
| `E′` | `E₁`, `γ (E₂ − V B₃)`, `γ (E₃ + V B₂)` | `electricVector_moving` |
| `B′` | `B₁`, `γ (B₂ + V E₃)`, `γ (B₃ − V E₂)` | `magneticVector_moving` |

`electricVector_boost` and `magneticVector_boost` are the same formulas for
the pullback by the boost itself, with the opposite sign of `V`.

**The invariants and the kinds of a field (§§22, 25).** The invariants are
`I₁ = B² − E²` and `I₂ = E · B` (`scalarInvariant_vectors`,
`pseudoscalarInvariant_vectors`). The generator `A = (e/m) F♯` is the map
`v ↦ (e/m) (E · v, v⁰ E + v × B)` (`lorentzForce_vectors`), and it satisfies

- `A³ = −(e/m)² I₁ A − (e/m)³ I₂ D` and `A D = −(e/m) I₂`, where `D` is the
  map of the triples `−B` and `E` (`generator_cube_eq`,
  `generator_dualGenerator`);
- `A⁴ = −(e/m)² I₁ A² + (e/m)⁴ I₂²`, the equation of Cayley and Hamilton
  (`generator_quartic`).

| Invariants | Generator | Four-velocity | Declaration |
| --- | --- | --- | --- |
| `I₂ = 0`, `I₁ < 0` | `A³ = Ω² A` | hyperbolic | `velocity_of_scalarInvariant_neg` |
| `I₂ = 0`, `I₁ > 0` | `A³ = −Ω² A` | circular | `velocity_of_scalarInvariant_pos` |
| `I₁ = I₂ = 0` | `A³ = 0` | a polynomial of degree two | `velocity_of_invariants_zero`; `nullField_ne_zero` |
| `I₂ ≠ 0` | `(A² − a²)(A² + b²) = 0` | hyperbolic on the range of `(A² + b²)/(a² + b²)`, circular on its kernel | `velocity_of_quartic`, `exists_rates`; `velocity_uniformField_closed` |

The last case is the shared statement `LinearODE.linearVelocity_eq_of_quartic`
for a bounded operator, which uses a projection that commutes with the
operator (`linearVelocity_eq_of_projection`). A field of two covectors has
`I₂ = 0` (`pseudoscalarInvariant_of_isSimple`). The kinds are stated for the
generator; a frame in which `E` and `B` are parallel is not constructed.

**Potentials on a manifold (§§16, 18).** On a manifold modelled on space-time
`Curved.fieldOf A = dA` is the field of a one-form `A`. It satisfies `dF = 0`
(`fieldOf_closed`), it does not change under `A ↦ A + dχ`
(`fieldOf_gaugeShift`, `maxwell_gaugeShift_iff`), it is natural for smooth
maps (`fieldOf_pullback`), and on flat space-time it is the field tensor
(`fieldOf_ofFlat`). The [notes](electrodynamics-notes.md) ED03–ED08 record the
decisions.

## The field with a current (§§26–30)

**The action with a current (E14, E15, §27).** For a current three-form `J`,
`SourcedAction.lagrangian J` is the vacuum Lagrangian minus the coefficient of
`A ∧ J`. For a `C²` potential, a `C²` current and an integrable density on an
open set, the action is stationary if and only if `d⋆F + J = 0`, that is
`dH = J` with `H = −⋆F` (`stationary_iff`, `stationary_iff_excitation`);
without a current this is the vacuum equation (`lagrangian_zero`,
`stationary_zero_iff`). Under a gauge change with compact support the action
changes by `∫ χ dJ` (`action_gaugeShift`), so it is invariant under all of them
if and only if `dJ = 0` (`action_gaugeShift_eq_iff`).

**The current of the matter (§28).** A matter current `k = (ρ, 𝐤)` has the
current form `matterCurrentForm k = −ι_k vol`. Since `a ∧ ι_v vol = a(v) vol`
(`coefficient_wedge_interior_volume`), the source term of the Lagrangian is
`+A(k) = −φρ + a · 𝐤`, the sign of the coupling `e A(γ̇)` of a charge
(`lagrangian_matterCurrentForm`). The current form of `Curved.Maxwell` is
`ι_j vol`, so `k = −j` (`matterCurrentForm_eq_currentForm`).

**The equations for `E` and `B` (E16, §§26, 30).** In the frame of the
co-ordinates `electricField G i` and `magneticField G i` are the functions
`x ↦ Eᵢ(x)`, `x ↦ Bᵢ(x)`, with the derivative `partialAt f μ x`, the
divergence `divergence3` and the curl `curl`.

| Statement | Declaration |
| --- | --- |
| The components of `dG` are `div B` and `∂_t B + curl E` | `exteriorDerivative_spatial`, `exteriorDerivative_temporal` |
| `dF = 0` gives `div B = 0` and `∂_t B + curl E = 0`; this holds for the field of a `C²` potential | `homogeneous_of_closed`, `homogeneous_fieldTensor` |
| The excitation `H = −⋆F` has the electric part `B` and the magnetic part `−E` | `electricVector_excitation`, `magneticVector_excitation` |
| `dH = −ι_k vol` gives `div E = ρ` and `curl B − ∂_t E = 𝐤` | `inhomogeneous_of_excitation` |
| Where the action with the current of the matter is stationary, the four equations hold | `maxwell_of_stationary` |

**The conservation of the charge (§29).** `d(−ι_k vol) = −(div k) vol`
(`coefficient_exteriorDerivative_matterCurrentForm`), so the current form is
closed if and only if `div k = 0`; where the action is stationary for a `C³`
potential, `div k = 0` (`divergence4_eq_zero_of_stationary`). For a `C¹`
current with `div k = 0` on a box `[a, b]` of the co-ordinates, the charge in
the spatial box at the time `b⁰` minus that at `a⁰` is minus the flux through
the six faces during `[a⁰, b⁰]` (`charge_balance`), by the divergence theorem
of Mathlib on a box.

**The example.** The potential `(t²/2) dx` has the field `t dt ∧ dx` and the
excitation `t dy ∧ dz`, and `dH = dt ∧ dy ∧ dz = −ι_{∂x} vol`. On every bounded
open set the action with the current `∂x` is stationary at it
(`Examples.stationary_example`), and in the unit ball `div E = 0` and
`curl B − ∂_t E = (1, 0, 0)` (`Examples.maxwell_example`). This fixes the sign
against `Curved.Examples.electric_source`, whose vector current is `−∂x`. The
[notes](electrodynamics-notes.md) ED09–ED11 record the decisions.

## Energy and momentum (§§31, 33–35)

**The theorem of Poynting (§31).** In the frame of the co-ordinates
`energyDensity F = ½ (E² + B²)` and `poyntingVector F = E × B`. With
`∂_t B + curl E = 0` and `curl B − ∂_t E = 𝐤`, `∂_t u + div S = −E · 𝐤`
(`poynting_local`). With `div E = ρ` and `div B = 0` in addition, the stress of
Maxwell `σᵢⱼ = −(Eᵢ Eⱼ + Bᵢ Bⱼ) + δᵢⱼ u` gives
`∂_t Sᵢ + Σⱼ ∂ⱼ σᵢⱼ = −(ρ Eᵢ + (𝐤 × B)ᵢ)` (`momentum_local`). On a box of the
co-ordinates, `box_divergence` is the divergence theorem with the faces of the
time separated, and for a `C²` field the energy and each component of the
momentum in the spatial box change by minus the flux through its faces and
minus the work or the impulse on the current (`energy_balance`,
`momentum_balance`).

**The stress tensor (§33).** `stressForm G v w = g⁻¹(ι_v G, ι_w G) − ¼ g(v, w) G²`
is `T_{μν} = G_{μα} G_ν{}^α − ¼ g_{μν} G²`.

| Statement | Declaration |
| --- | --- |
| `T` is symmetric and trace-free | `stressForm_symm`, `stressForm_trace` |
| For every observer, `T(u, u) = ½ (\|E_u\|² + \|B_u\|²)` | `stressForm_observer` |
| `T₀₀ = u`, `T₀ᵢ = −Sᵢ`, `Tᵢⱼ = σᵢⱼ` in the frame of the co-ordinates | `stressForm_zero_zero`, `stressForm_zero_succ`, `stressForm_succ_succ` |
| `∂_μ T^{μ0} = −E · 𝐤` and `∂_μ T^{μ,i} = −(ρ Eᵢ + (𝐤 × B)ᵢ)` | `divergence_raisedStress_zero`, `divergence_raisedStress_succ` |

**Charged dust (§35).** `ChargedDust` has the densities `μ` of the rest mass
and `ρₑ` of the charge and the four-velocity `U`, with the current `ρₑ U` and the
stress `μ U^μ U^ν`. If the mass is conserved, the divergence of the stress is
`μ U^λ ∂_λ U^ν` (`ChargedDust.divergence_matterStress`). If the dust moves by
the force `ρₑ F♯ U` of `lorentzForce` and the field satisfies the equations of
Maxwell with its current, the total stress is conserved
(`total_stress_conserved`). The [notes](electrodynamics-notes.md) ED12–ED13
record the decisions.

## Proof and API map

All names below are under `ProjectAinos`, except imported `YM` names.

| Claim | Main declarations | Source |
| --- | --- | --- |
| Local gauge invariance, reconstruction | `Electrodynamics.fieldTensor_gauge_on`, `observer_reconstruction` | [Field](../ProjectAinos/Electrodynamics/Field.lean) |
| Bianchi components, covariance | `bianchi_components`, `fieldTensor_component`, `fieldTensor_poincare` | [Components](../ProjectAinos/Electrodynamics/Components.lean) |
| Observer invariants and rest norm | `scalarInvariant_observer`, `pseudoscalarInvariant_observer`, `covectorPairing_nonneg` | [Invariants](../ProjectAinos/Electrodynamics/Invariants.lean) |
| Lorentz determinant and orientation | `scalarInvariant_lorentz`, `pseudoscalarInvariant_lorentz` | [Covariance](../ProjectAinos/Electrodynamics/Covariance.lean) |
| Compact localization and admissibility | `Variational.exists_contDiff_extension_near_compact`, `eventually_mapsTo_open` | [LocalExtension](../ProjectAinos/Variational/LocalExtension.lean) |
| Local action derivative and stationarity | `Mechanics.hasDerivAt_action_firstVariation_on`, `stationary_iff_eulerLagrange_on` | [OpenDomain](../ProjectAinos/Mechanics/OpenDomain.lean) |
| Free action and kinetic momentum | `SpecialRelativity.freeAction_eq_action`, `kineticMomentum_eq` | [ParticleAction](../ProjectAinos/SpecialRelativity/ParticleAction.lean) |
| Charged action and derivatives | `Electrodynamics.chargedAction_eq`, `charged_force`, `charged_momentum` | [ParticleAction](../ProjectAinos/Electrodynamics/ParticleAction.lean) |
| Dynamics from the action | `stationary_iff_lorentzForce`, `stationary_properTime`, `lorentzForce_component` | [LorentzForce](../ProjectAinos/Electrodynamics/LorentzForce.lean) |
| Gauge boundary and local stationarity | `chargedAction_gauge_on`, `stationary_gauge_iff_on` | [GaugeAction](../ProjectAinos/Electrodynamics/GaugeAction.lean) |
| Scalar/color polynomial reconstruction | `Polynomial.radial_curl`, `radial_upstream`, `radial_map`, `mapCoefficients_closed` | [PolynomialRadial](../ProjectAinos/Electrodynamics/PolynomialRadial.lean) |
| Coordinate and derivative compatibility | `Polynomial.fieldTensor_potential`, `radial_formula`, `grad_transport` | [PolynomialBridge](../ProjectAinos/Electrodynamics/PolynomialBridge.lean) |
| Hamiltonian of a charge in a static field | `ChargedParticle.canonical_kineticMomentum_hamiltonian`, `isTrajectory_iff_lorentzForce`, `momentumShift_hamiltonian`, `flowDomain_hamiltonianField` | [Hamiltonian](../ProjectAinos/Electrodynamics/Hamiltonian.lean), [HamiltonianExamples](../ProjectAinos/Electrodynamics/HamiltonianExamples.lean) |
| Action of space-time on a graph | `ChargedParticle.fieldTensor_staticPotential`, `stationary_graph_iff_lorentzForce`, `stationary_graph_iff_hamilton`, `stationary_graph_of_isTrajectory` | [StaticField](../ProjectAinos/Electrodynamics/StaticField.lean) |
| Motion in a constant field | `ConstantField.stationary_motion`, `deriv_eq_velocity_of_stationary`, `generator_cube`, `velocity_of_pos`, `velocity_of_neg`, `velocity_of_zero`, `velocity_add` | [ConstantField](../ProjectAinos/Electrodynamics/ConstantField.lean), [ConstantFieldExamples](../ProjectAinos/Electrodynamics/ConstantFieldExamples.lean) |
| Transformation of `E` and `B` | `electricVector_boost`, `magneticVector_boost`, `electricVector_moving`, `magneticVector_moving`, `electric_observer_apply`, `magnetic_observer_apply` | [FieldTransformation](../ProjectAinos/Electrodynamics/FieldTransformation.lean) |
| Invariants and the kinds of a field | `ConstantField.generator_quartic`, `velocity_of_scalarInvariant_neg`, `velocity_of_scalarInvariant_pos`, `velocity_of_invariants_zero`, `velocity_of_quartic` | [FieldClassification](../ProjectAinos/Electrodynamics/FieldClassification.lean) |
| Potentials on a manifold | `Curved.fieldOf_closed`, `fieldOf_gaugeShift`, `fieldOf_pullback`, `fieldOf_ofFlat` | [CurvedPotential](../ProjectAinos/Electrodynamics/CurvedPotential.lean) |
| Action with a current, gauge change | `SourcedAction.stationary_iff`, `stationary_iff_excitation`, `action_gaugeShift`, `action_gaugeShift_eq_iff` | [SourcedAction](../ProjectAinos/Electrodynamics/SourcedAction.lean) |
| Current of the matter | `SourcedAction.lagrangian_matterCurrentForm`, `matterCurrentForm_eq_currentForm`, `stationary_iff_matterCurrent` | [MatterCurrent](../ProjectAinos/Electrodynamics/MatterCurrent.lean) |
| Equations for `E` and `B` | `homogeneous_of_closed`, `inhomogeneous_of_excitation`, `maxwell_of_stationary` | [ThreePlusOne](../ProjectAinos/Electrodynamics/ThreePlusOne.lean) |
| Conservation of the charge | `coefficient_exteriorDerivative_matterCurrentForm`, `divergence4_eq_zero_of_stationary`, `charge_balance` | [ChargeBalance](../ProjectAinos/Electrodynamics/ChargeBalance.lean) |
| Field with a nonzero current | `SourcedAction.Examples.stationary_example`, `maxwell_example` | [SourcedActionExamples](../ProjectAinos/Electrodynamics/SourcedActionExamples.lean) |
| Energy and momentum in an inertial frame | `poynting_local`, `momentum_local`, `box_divergence`, `energy_balance`, `momentum_balance` | [EnergyMomentum](../ProjectAinos/Electrodynamics/EnergyMomentum.lean) |
| Stress tensor | `stressForm_symm`, `stressForm_trace`, `stressForm_observer`, `divergence_raisedStress_zero`, `divergence_raisedStress_succ` | [StressTensor](../ProjectAinos/Electrodynamics/StressTensor.lean) |
| Charged dust | `ChargedDust.divergence_matterStress`, `total_stress_conserved` | [ChargedDust](../ProjectAinos/Electrodynamics/ChargedDust.lean) |
| Nonzero regression examples | `Examples.hyperbola_stationary`; `Polynomial.constantJet_reconstruction`, `linearJet_reconstruction` | [Examples](../ProjectAinos/Electrodynamics/Examples.lean), [PolynomialExamples](../ProjectAinos/Electrodynamics/PolynomialExamples.lean) |

## Verification and review

```sh
lake build --wfail ProjectAinos
lake exe mk_all --check --lib ProjectAinos
lake env lean -DwarningAsError=true checks/ElectrodynamicsAPI.lean
lake env lean -DwarningAsError=true checks/ElectrodynamicsCoreAPI.lean
lake env lean -DwarningAsError=true checks/ChargedParticleAPI.lean
lake env lean -DwarningAsError=true checks/FieldClassificationAPI.lean
lake env lean -DwarningAsError=true checks/SourcedFieldAPI.lean
lake env lean -DwarningAsError=true checks/FieldStressAPI.lean
lake env lean -DwarningAsError=true checks/AxiomAudit.lean
experiments/.venv/bin/python -m ainos_experiments.verify_electrodynamics
```

The required **Lean build** job checks warnings, root imports, API checks,
and transitive axioms. The explicit audit includes all imported `YM` and
`YangMills` declarations, including the new Maxwell closure. Only `propext`,
`Classical.choice`, and `Quot.sound` are allowed. The independent SymPy runner
uses exact expressions and no random seeds or floating-point tolerances; its
separate **Experiments** job remains non-required. It checks Hodge signs,
invariants, boosts/reflection, gauge curvature, radial coefficients, and the
hyperbolic worldline. Formal claims rest on the Lean proofs.

Changes to the pinned upstream port and its dependency closure require
independent review, separately from the physical signs, open-domain
regularity, and interpretation of the action theorem.
