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
| [Parameter](../ProjectAInos/Variational/Parameter.lean) | A positive derivative gives one open interval chart with a constructed C² inverse; endpoint neighborhoods extend closed-interval predicates; `contDiff_primitive`: a primitive of a continuously differentiable function is twice continuously differentiable |
| [IntervalParameter](../ProjectAInos/Variational/IntervalParameter.lean) | Local joint C¹ regularity along a compact reference segment gives differentiation of the actual parameter integral, with domination derived; intrinsic boundary/residual splitting |
| [MovingLimits](../ProjectAInos/Variational/MovingLimits.lean) | Leibniz's rule for an integral whose limits move with the parameter, `hasDerivAt_intervalIntegral_moving`, and its form for an integrand that is smooth on an open set containing the reference segment, `hasDerivAt_intervalIntegral_moving_on` |
| [ParametricIntegralOn](../ProjectAInos/Variational/ParametricIntegralOn.lean) | `contDiffAt_parametric_intervalIntegral`, `contDiffOn_parametric_intervalIntegral`: a parametric integral of a function that is smooth on an open set containing the segment of integration over a point is smooth at that point, for a parameter in a space of finite dimension |
| [SecondOrderBound](../ProjectAInos/Variational/SecondOrderBound.lean) | `abs_sub_sub_le_of_abs_le`: `|f(ε) − f(0) − ε f′(0)| ≤ M ε²` if `|f″| ≤ M` on `[−δ, δ]`; `exists_pos_forall_abs_le_mem`: an open set containing `{0} × K` for a compact `K` contains `[−δ, δ] × K`; `exists_second_order_bound`: the remainder of the expansion of the first order in `ε`, with one `δ` and one `M` for all parameters in a compact set |
| [LineDerivative](../ProjectAInos/Variational/LineDerivative.lean) | `hasDerivAt_line`, `hasDerivAt_line_sub`: the derivative along a line through a point of differentiability. `hasFDerivAt_of_hasDerivAt_line`: derivatives along the lines that are given by continuous linear maps depending continuously on the point are a derivative |
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

`ParametricIntegralOn` proves that `x ↦ ∫ₐᵇ f(x, t) dt` is smooth at `x₀` when
`f` is smooth on an open set that contains `{x₀} × [a, b]`
(`contDiffAt_parametric_intervalIntegral`): `f` is replaced near the segment by
a function that is smooth everywhere, by `LocalExtension`, and the theorem for
such functions is `SmoothAlgebra.contDiff_infty_parametric_intervalIntegral`.
The parameter lies in a space of finite dimension. `eventually_uIcc_mem_open`
of `MovingLimits` is stated for a parameter in any topological space.

`SecondOrderBound` bounds the remainder of an expansion of the first order.
If `f(ε, l)` is twice continuously differentiable at the points `(0, l)` with
`l` in a compact set `K` of a normed space, there are `δ > 0` and `M` with
`|f(ε, l) − f(0, l) − ε ∂f/∂ε(0, l)| ≤ M ε²` for all `l ∈ K` and `|ε| ≤ δ`
(`exists_second_order_bound`): the set of points at which `f` is twice
continuously differentiable is open, so it contains `[−δ, δ] × K`
(`exists_pos_forall_abs_le_mem`), and the second derivative in `ε` is bounded
on this compact set.

`LineDerivative`: if `f` has at every point `s` of an open set, for every
direction `a`, the derivative `A s a` along the line `ε ↦ s + ε a`, where `A s`
is a continuous linear map that depends continuously on `s`, then `A s` is the
derivative of `f` at `s` (`hasFDerivAt_of_hasDerivAt_line`). The proof is the
mean value inequality for `t ↦ f(s + t h) − t A s h` on `[0, 1]`.

`MovingLimits` differentiates `s ↦ ∫_{a(s)}^{b(s)} F(s, t) dt` for a smooth
integrand and differentiable limits:
`∫ ∂F/∂s dt + F(s, b) b′ − F(s, a) a′`. The integral is a smooth function of
the parameter and of the two limits together
(`SmoothAlgebra.contDiff_infty_parametric_intervalIntegral_limits`), and its
three partial derivatives are identified. For an integrand that is smooth on
an open set `U` containing `{s₀} × [a(s₀), b(s₀)]`, the integrand is extended
from a neighbourhood of that segment, and `eventually_uIcc_mem_open` keeps the
segment between the moving limits inside the neighbourhood. The hypothesis is
smoothness on an open set, since smoothness at a point does not hold in a
neighbourhood of the point.

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

The [flat vacuum Maxwell action](electrodynamics.md#vacuum-field-action-42)
uses compactly supported first-jet variations in four dimensions. Its
stationarity theorem combines the shared action derivative with exterior
integration by parts. General coordinate changes for field jets and global
jet bundles remain subsequent stages.
[Smooth algebra](smooth-algebra.md) supplies the smooth observables used by
`Mechanics.ofSmoothOperation` and their concrete directional chain rule.

Run the warning-free library build, root-import check, and transitive axiom
audit from the repository root:

```sh
lake build --wfail ProjectAInos
lake exe mk_all --check --lib ProjectAInos
lake env lean -DwarningAsError=true checks/AxiomAudit.lean
```
