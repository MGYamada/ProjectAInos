# Shared Local Variational Calculus

The foundation for [issue #7](https://github.com/MGYamada/ProjectAInos/issues/7)
treats a field as a section of the trivial bundle over a real coordinate
domain. The same Lean theorem handles a single time coordinate and a
higher-dimensional base. Its fibre is any real normed space, including a
tuple of field components. The pointwise and integral derivative results build
on the prototype in [PR #29](https://github.com/MGYamada/ProjectAInos/pull/29).

The [shared formalization notes](variational-notes.md) record the distinctions
between ambient and restricted measures, the two compactness arguments for
action derivatives, and the scope of the algebraic and analytic interfaces.

For a field `u`, the local first jet is the pair of its value and its Fréchet
derivative. A Lagrangian `L x (u x, Du x)` can depend explicitly on the base
point. The affine variation `u + ε • η` changes the field at a fixed base
point. The action integrates the resulting density against a specified measure.

## Euler–Lagrange endpoint

In coordinates, write `A(x)` for the derivative in the field value and
`Pᵢ(x)` for the derivative in the field derivative along coordinate `i`.
Both act linearly on fibre vectors. The Euler–Lagrange residual is
the covector `A(x) − Σᵢ ∂ᵢ Pᵢ(x)`. Lean proves

\[
\left.\frac{d}{d\varepsilon}S[u+\varepsilon\eta]\right|_{0}
=\int_\Omega \Bigl(A-\sum_i\partial_i P_i\Bigr)(\eta)\,d\mu.
\]

The endpoint `stationary_iff_eulerLagrange` equates vanishing of the actual
action derivative for every admissible variation with pointwise vanishing of
this residual throughout the open region Ω. The statement requires:

- A finite-dimensional coordinate base with an additive Haar measure μ.
- A Lagrangian jointly C² in the base point and the first jet, and a C² field.
  These are ambient functions whose action is evaluated on Ω.
- An integrable unperturbed density on Ω, including for unbounded regions.
- Smooth variations with compact topological support contained in Ω.

Compact support bounds the parameter derivative on a product of compact sets
and makes the change in the density integrable. The variation and its derivative
vanish off its support. Thus integration by parts uses the ambient Haar
measure, and the pairings can be restricted back to Ω. To infer the pointwise
equation, the proof tests against scalar smooth functions times a fixed fibre
vector. Mathlib's fundamental lemma gives almost-everywhere vanishing of the
scalar residual, and continuity together with positivity of Haar measure on
open sets gives pointwise vanishing.

## Proof entry points

| Module | Results |
| --- | --- |
| [Local](../ProjectAInos/Variational/Local.lean) | First jet and the pointwise chain rule along an affine variation |
| [Action](../ProjectAInos/Variational/Action.lean) | `hasDerivAt_action`, with explicit measurability, integrability and uniform domination |
| [Regularity](../ProjectAInos/Variational/Regularity.lean) | Compact support supplies domination; `hasDerivAt_action_restrict_compact` instead uses a compact base region, with no support condition on the variation |
| [IntegrationByParts](../ProjectAInos/Variational/IntegrationByParts.lean) | Interval identity with endpoint pairing, fixed-endpoint specialization, and directional Haar identities |
| [EulerLagrange](../ProjectAInos/Variational/EulerLagrange.lean) | Covector decomposition, derivative as the residual pairing, and `stationary_iff_eulerLagrange` |
| [Parameter](../ProjectAInos/Variational/Parameter.lean) | A positive derivative gives one open interval chart with a constructed C² inverse; endpoint neighborhoods extend closed-interval predicates |
| [IntervalParameter](../ProjectAInos/Variational/IntervalParameter.lean) | Local joint C¹ regularity along a compact reference segment gives differentiation of the actual parameter integral, with domination derived; intrinsic boundary/residual splitting |
| [ManifoldCurve](../ProjectAInos/Variational/ManifoldCurve.lean) | Actual fixed-endpoint C² manifold families and construction of supported chart perturbations, with gluing and coordinate velocity |
| [Examples](../ProjectAInos/Variational/Examples.lean) | Nonzero variations on time and four-dimensional bases, and a base-dependent momentum with a nonzero divergence residual |

The interval result keeps the term `[P η]ₐᵇ` and removes it when the variation
vanishes at both endpoints. The stationarity theorem uses interior variations.
The action derivative is a derivative along the specified real parameter.

The scalar parameter lemmas have no geometry or physics imports.
`ManifoldCurve` uses generic manifold calculus but no Lorentz metric or physics;
its constructor proves that localized chart tests are admissible families.
GR uses the parameter lemmas
to construct a single proper-time inverse over a finite timelike segment,
including the endpoint correspondence; see the [GR guide](general-relativity.md).

`LocalExtension` now supports every finite order and smoothness (`n : ℕ∞`),
while retaining the original zero-centered compact-family interface.
`IntervalParameter` extends only the scalar density near
`{ε₀} × [a,b]`. A common parameter neighborhood and a uniform derivative
bound follow from compactness, so its public integral derivative theorem asks
only for local joint C¹ regularity and the specified pointwise derivative.
This supports manifold curve families crossing chart boundaries without
constructing a global coordinate curve.

The [Mechanics specialization](mechanics.md) now derives the fixed-endpoint
Euler–Lagrange equations on a real time interval. It uses compactness of the
interval to justify the action derivative and `interval_firstVariation_pairing`
for the covector-valued boundary term.

[Electrodynamics §4.1](electrodynamics.md) uses the same variational API for the
[charged-particle action](../ProjectAInos/Electrodynamics/ParticleAction.lean).
`stationary_iff_lorentzForce` relates fixed-endpoint stationarity to the
[Lorentz-force equation](../ProjectAInos/Electrodynamics/LorentzForce.lean) on the
interval interior. It assumes a C² curve that stays in an open spacetime domain
with a C² potential and timelike velocity along the closed interval.
The [gauge-action formula](../ProjectAInos/Electrodynamics/GaugeAction.lean)
adds the endpoint term `e (χ(γ(b)) − χ(γ(a)))` for a C¹ gauge function on the
domain. Fixed-endpoint stationarity is gauge invariant under the theorem's C³
gauge-function hypothesis.

General coordinate changes for field jets and global jet bundles remain
subsequent stages. The vacuum Maxwell action derivation is tracked in
[#44](https://github.com/MGYamada/ProjectAInos/issues/44), separately from the
[curved fixed-background Maxwell equations](electrodynamics.md).
[Smooth algebra](smooth-algebra.md) supplies the smooth observables used by
`Mechanics.ofSmoothOperation` and their concrete directional chain rule.

Run the warning-free library build, root-import check, and transitive axiom
audit from the repository root:

```sh
lake build --wfail ProjectAInos
lake exe mk_all --check --lib ProjectAInos
lake env lean -DwarningAsError=true checks/AxiomAudit.lean
```
