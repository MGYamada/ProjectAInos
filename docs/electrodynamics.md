# Charged Particles and Electromagnetic Fields

This implements research-plan §4.1 of [issue #8](https://github.com/MGYamada/ProjectAInos/issues/8),
with the free-particle action needed from §3.2, and the fixed-background
Maxwell form API from §5.1 / [#52](https://github.com/MGYamada/ProjectAInos/issues/52).
The field-action derivation in §4.2, collision theory and quantum field theory
remain later stages. Issue #8 is a broader research plan and remains open.

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
vanishes. The corresponding SymPy calculation agrees.
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

The sourced component equation `∇ᵢFⁱʲ = jʲ` and its equivalence with `dH = J`
remain pending in stage F. The Maxwell action and its variational derivation
belong to §4.2 / #44.

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
[PR #41](https://github.com/MGYamada/ProjectAInos/pull/41); this change adds six.
Original `YM` namespaces and mathematical statements are preserved. See the
[provenance and compatibility record](../ProjectAInos/External/YM/PROVENANCE.md)
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

## Proof and API map

All names below are under `ProjectAInos`, except imported `YM` names.

| Claim | Main declarations | Source |
| --- | --- | --- |
| Local gauge invariance, reconstruction | `Electrodynamics.fieldTensor_gauge_on`, `observer_reconstruction` | [Field](../ProjectAInos/Electrodynamics/Field.lean) |
| Bianchi components, covariance | `bianchi_components`, `fieldTensor_component`, `fieldTensor_poincare` | [Components](../ProjectAInos/Electrodynamics/Components.lean) |
| Observer invariants and rest norm | `scalarInvariant_observer`, `pseudoscalarInvariant_observer`, `covectorPairing_nonneg` | [Invariants](../ProjectAInos/Electrodynamics/Invariants.lean) |
| Lorentz determinant and orientation | `scalarInvariant_lorentz`, `pseudoscalarInvariant_lorentz` | [Covariance](../ProjectAInos/Electrodynamics/Covariance.lean) |
| Compact localization and admissibility | `Variational.exists_contDiff_extension_near_compact`, `eventually_mapsTo_open` | [LocalExtension](../ProjectAInos/Variational/LocalExtension.lean) |
| Local action derivative and stationarity | `Mechanics.hasDerivAt_action_firstVariation_on`, `stationary_iff_eulerLagrange_on` | [OpenDomain](../ProjectAInos/Mechanics/OpenDomain.lean) |
| Free action and kinetic momentum | `SpecialRelativity.freeAction_eq_action`, `kineticMomentum_eq` | [ParticleAction](../ProjectAInos/SpecialRelativity/ParticleAction.lean) |
| Charged action and derivatives | `Electrodynamics.chargedAction_eq`, `charged_force`, `charged_momentum` | [ParticleAction](../ProjectAInos/Electrodynamics/ParticleAction.lean) |
| Dynamics from the action | `stationary_iff_lorentzForce`, `stationary_properTime`, `lorentzForce_component` | [LorentzForce](../ProjectAInos/Electrodynamics/LorentzForce.lean) |
| Gauge boundary and local stationarity | `chargedAction_gauge_on`, `stationary_gauge_iff_on` | [GaugeAction](../ProjectAInos/Electrodynamics/GaugeAction.lean) |
| Scalar/color polynomial reconstruction | `Polynomial.radial_curl`, `radial_upstream`, `radial_map`, `mapCoefficients_closed` | [PolynomialRadial](../ProjectAInos/Electrodynamics/PolynomialRadial.lean) |
| Coordinate and derivative compatibility | `Polynomial.fieldTensor_potential`, `radial_formula`, `grad_transport` | [PolynomialBridge](../ProjectAInos/Electrodynamics/PolynomialBridge.lean) |
| Nonzero regression examples | `Examples.hyperbola_stationary`; `Polynomial.constantJet_reconstruction`, `linearJet_reconstruction` | [Examples](../ProjectAInos/Electrodynamics/Examples.lean), [PolynomialExamples](../ProjectAInos/Electrodynamics/PolynomialExamples.lean) |

## Verification and review

```sh
lake build --wfail ProjectAInos
lake exe mk_all --check --lib ProjectAInos
lake env lean -DwarningAsError=true checks/ElectrodynamicsAPI.lean
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

Before merging, independent review should check the pinned upstream port and
its dependency closure separately from the physical signs, open-domain
regularity, and interpretation of the action theorem.
