# Shared variational foundation: local prototype for issue #7

Review date: 11 November 2026 (Japan). This is an experimental implementation
proposal for issue #7. It does not freeze the public API or the future geometric
framework.

## Baseline and recommendation

The inspected Project AInos `main` is
`8b57c63bd570e17f1bc272a500ca99a3bf2b2eb2`. Its existing library contains only
Thermodynamics. The README plans smooth algebra, differential forms, jet rings,
and variational mechanics; these are not existing implementation dependencies.
[Issue #7](https://github.com/MGYamada/ProjectAInos/issues/7) sets the shared-first
architecture. [Issue #8](https://github.com/MGYamada/ProjectAInos/issues/8) remains
a provisional Electrodynamics outline, not an additional acceptance criterion.

The reproducible implementation target is **Lean 4.35.0 and Mathlib v4.35.0**,
Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`, exactly as pinned in
`lean-toolchain` and `lake-manifest.json`. Online generated Mathlib documentation
can track a newer toolchain; the code below was checked against the pinned source.

**Recommendation:** start with a fixed trivialization of a finite-dimensional
real vector bundle and an explicit measure. Keep the pointwise chain rule,
differentiation under the integral, and integration by parts separate. Treat this
as the local analytic model of future geometry, without freezing a general jet
bundle or a C-infinity-ring interface now.

The pointwise kernel in fact needs only real normed spaces `E, F`; specializing
to `E = Fin n → ℝ`, `F = Fin m → ℝ` supplies the requested finite-dimensional
case. Finite dimensionality is imposed where the multivariable integration by
parts theorem needs it. No inner product or Lorentzian metric is built into the
kernel.

## Comparing the two starting points

| Question | Fixed local trivialization | General smooth bundle and section jets |
|---|---|---|
| Geometric data | An ambient coordinate space `E`, value space `F`, and fields `E → F`; a region is selected by the measure | A smooth locally trivial bundle `π : Y → M`, its vertical tangent bundle, and smooth sections |
| First jet | At a fixed base point, `F × (E →L[ℝ] F)` | At `y` over `x`, a splitting `ℓ : TₓM → TᵧY` satisfying `dπᵧ ∘ ℓ = id` |
| Variation | `u + ε • η` | A smooth family of sections; its velocity lies in `u*VY`. Addition of sections is unavailable for a general nonlinear fibre |
| Existing support | Fréchet derivatives, chain rules, dominated parameter integrals, interval and directional integration by parts | Manifolds, tangent maps, vector bundles, bundle morphisms, pullbacks, smooth sections; substantial assembly still needed |
| First result | Checked first variation of the action under explicit hypotheses | Must first build or adapt section jets, chart transitions, vertical variations, and density-valued integration |
| Scope limitation | Coordinates, ambient extensions, and a chosen measure are visible | Supports topology and nonlinear fibres, but entails more initial obligations |
| Future reuse | Local theorem used in each chart, after proving compatibility | Intrinsic statement whose local expression is the present theorem |

For a smooth bundle, `J¹π → Y` is generally an **affine** bundle, modelled on
`T*M ⊗ VY`. A connection can choose a splitting, but should not be silently
required by the variational foundation. Even for a vector bundle, its derivative
component in a changing frame is not independently tensorial. The local product
type is therefore explicitly called `JetFiber`, not presented as the intrinsic
definition of `J¹π`.

The pinned Mathlib tree was searched for jet-bundle, Euler–Lagrange, and
C-infinity-ring implementations; no reusable end-to-end framework was found.
This is not a claim about all external Lean projects. In particular,
[Sphere Eversion's OneJetBundle](https://github.com/leanprover-community/sphere-eversion/blob/master/SphereEversion/Global/OneJetBundle.lean)
constructs jets of maps between manifolds and their smooth prolongations. It is
an informative external implementation, not a dependency of this prototype.
Jets of sections additionally impose the projection/splitting condition above;
that repository is not already a shared variational-calculus API.

## The implemented API

The namespace is `ProjectAInos.Variational`, independently of Mechanics and
Thermodynamics. All four new modules are imported by the library root.

```lean
JetFiber E F := F × (E →L[ℝ] F)
Lagrangian E F := E → JetFiber E F → ℝ
jet u x := (u x, fderiv ℝ u x)
perturb u η ε x := u x + ε • η x
density L u x := L x (jet u x)
firstVariationDensity L u η x :=
  fderiv ℝ (L x) (jet u x) (jet η x)
action μ L u := ∫ x, density L u x ∂μ
firstVariation μ L u η := ∫ x, firstVariationDensity L u η x ∂μ
```

The definitions use Mathlib's **total** `fderiv` and integral operations. Merely
writing these expressions does not prove differentiability or integrability.
Their analytic meaning is established by the theorems and their hypotheses.
In particular, a zero value returned outside the differentiable/integrable
case must never be interpreted as a stationary physical configuration.

| Module | Checked statements | Scope |
|---|---|---|
| `Variational/Local.lean` | `jet_add`, `jet_const_smul`, `jet_perturb` | Jets of differentiable fields respect affine variations |
| same | `hasDerivAt_density_perturb`, `hasDerivAt_density` | Chain rule at any parameter value, and at zero |
| same | `firstVariationDensity_split`, `_add`, `_smul` | Value/derivative decomposition and linearity in differentiable variations |
| `Variational/Action.lean` | `hasDerivAt_action` | Integrability of the variation density and the actual derivative of the integrated action |
| `Variational/IntegrationByParts.lean` | `interval_firstVariation_identity`, `_fixedEndpoints` | Scalar coefficient identity with boundary term, and its fixed-endpoint consequence |
| same | `directional_integrationByParts`, `finite_firstVariation_identity` | Whole-space Haar-measure identity and a finite sum of directional terms |
| `Variational/Examples.lean` | `timeCoordinates`, `time_derivative_apply`, dimension specializations and quadratic examples | Time/velocity interpretation, arbitrary field-component count, and nonzero derivative checks |

In mathematical notation, the checked action theorem says

\[
 \left.\frac{d}{d\varepsilon}S[u+\varepsilon\eta]\right|_0
 =\int d_{(u,p)}L(x,u(x),Du(x))\,[\eta(x),D\eta(x)]\,d\mu(x),
\]

under the hypotheses below. Since the base point is fixed, no `∂L/∂x` term
appears in this vertical variation. Moving boundaries and variations of base
coordinates are outside its scope.

This is a derivative along a specified affine family. It is **not** a proof of
Fréchet differentiability on a Banach, Sobolev, or Fréchet space of fields.
The formal algebraic splitting of `dL` into value and derivative contributions
does not require a Riesz identification with a gradient.

## Exact analytic contracts and useful sufficient conditions

| Stage | Actual hypotheses in the Lean prototype |
|---|---|
| Pointwise first variation | `u` and `η` differentiable at `x`; `L x` differentiable at the relevant jet. No spatial differentiability of `L` or boundary condition is needed for this chain rule |
| Action derivative | `u, η` differentiable almost everywhere for `μ`; one set `s ∈ 𝓝 0`; for almost every `x`, fibre differentiability of `L x` at every varied jet for `ε ∈ s`; measurable varied densities for parameters near zero; integrable unvaried density; measurable first-variation density at zero; an integrable function `bound x` dominating the absolute parameter derivative for all `ε ∈ s`, almost everywhere |
| Interval integration by parts | Certified derivatives `P', η'` of `P, η` at every point of `uIcc a b`; interval integrability of `P', η'`; integrability of `Aη`. This uses full ambient derivatives also at endpoints, a convenient stronger-than-necessary contract |
| Removing interval boundary term | Explicit equalities `η a = 0` and `η b = 0` |
| Whole-space directional integration by parts | Finite-dimensional real `E`, Borel structure, additive Haar measure; integrability of `Pη`, `(DᵥP)η`, `P(Dᵥη)`; differentiability of `P` on `tsupport η`, and of `η` on `tsupport P` |
| Finite directional sum | The previous product and differentiability hypotheses for each coefficient and direction, plus integrability of `Aη` |

These are explicit assumptions, not new axioms and not fields that assume the
desired first-variation identity. The parameter derivative is obtained from
the local chain rule; the exchange with integration is a Mathlib theorem.

For a bounded region with compact closure, a convenient *future convenience
theorem* would assume `u, η` are C¹ on a neighborhood of the closure, and `L` is
jointly C¹ near the compact set swept out by their jets for `|ε| ≤ δ`. With
Lebesgue measure restricted to the region, compactness and continuity supply
measurability, finite integrals, and a uniform bound. This sufficient-condition
wrapper is not implemented here.

For an open coordinate domain, the prototype represents fields by functions on
the ambient vector space. It does not yet prove independence from the chosen
extension outside the domain. A domain-native API should use open-set derivative
locality, or `fderivWithin` with `UniqueDiffWithinAt`; an arbitrary closed-set
derivative is not automatically unique.

For compactly supported interior variations, `tsupport η ⊆ Ω` and compactness
are a natural later admissibility contract. To use the whole-space identity for
fields originally defined only on `Ω`, one must justify smooth extension or
localization by a cutoff. The current identity does not perform that step.

Compact support of `η` **does not make `S[u]` finite on an unbounded region**.
The prototype retains the baseline integrability assumption. A relative action
`∫ (L(j¹(u+εη)) - L(j¹u))` is a reasonable separate extension, not a result
already established by this patch.

The arbitrary measure in `hasDerivAt_action` must not be carried unchanged into
the Haar-measure integration-by-parts theorem. For a density `ρ(x) dx`, the
classical coefficient becomes `ρ A - ∂ᵢ(ρ Pⁱ)`. An arbitrary restricted-domain
measure is not Haar measure. Boundary integrals, weighted divergence, and
distributional/Sobolev formulations require their own contracts.

## Checks for one and four dimensions

For time, `Coordinates 1 ≃L[ℝ] ℝ` is constructed using Mathlib's `piUnique`.
The lemma `p t = t • p 1` identifies a linear derivative map on time with its
velocity. `mechanics_firstVariation` specializes the common chain rule to
`ℝ → (Fin m → ℝ)` for arbitrary `m`. No second implementation is introduced.

`spacetime_firstVariation` specializes the same theorem to
`(Fin 4 → ℝ) → (Fin m → ℝ)`, including `m = 4`. This supplies the coordinate
shape of a four-component potential, but not a connection, Maxwell action,
Lorentzian Hodge operator, gauge theorem, or Maxwell equation. The norm on the
coordinate space is used only for calculus; metric signature belongs in `L`.

The nonlinear diagnostic is `L(j) = ℓ(j)²`, with checked derivative
`δL = 2ℓ(j¹u)ℓ(j¹η)`. Two literal nonzero checks accompany the general theorem:

* In one dimension, `u(t) = η(t) = t`, `ℓ(q,p) = p(1)`: the varied density is
  `(1+ε)²`, and its derivative at zero is `2`.
* In four dimensions, `u(x) = x₀`, `η(x) = x₁`, and
  `ℓ(q,p) = p(1,1,1,1)`: the derivative is again `2`. Different coordinate
  directions exercise the derivative component, beyond a dimension alias.

The `*_hasDerivAt` lemmas certify actual derivatives in both examples; the
`*_nonzero`/`*_mixed` lemmas also verify the variation-density expressions.

## Euler–Lagrange: what is and is not proved

The interval coefficient theorem proves the identity

\[
 \int_a^b (A\eta+P\eta')\,dt
 =[P\eta]_a^b+\int_a^b(A-P')\eta\,dt.
\]

The multidimensional coefficient theorem proves, for fixed directions `vᵢ`,

\[
 \int \left(A\eta+\sum_iP^i D_{v_i}\eta\right)dx
 =\int\left(A-\sum_iD_{v_i}P^i\right)\eta\,dx.
\]

Choosing coordinate basis vectors yields the usual divergence expression.
The finite sum is implemented for scalar fields; a componentwise vector-field
version can be obtained with another finite sum, but is not included here.

The following are still **design/proof obligations**, not checked conclusions:

1. Extract coordinate coefficients `Aₐ = ∂L/∂uᵃ`, `Pₐⁱ = ∂L/∂pᵃᵢ` from the
   Fréchet derivative and prove their finite-coordinate contraction formula.
2. Prove regularity of those coefficient fields. Joint `L ∈ C²` and `u ∈ C²`
   are convenient sufficient assumptions for classical differentiability of
   `P(x,j¹u(x))`; they are stronger than the pointwise first-variation needs.
3. Formalize admissible variations and their support/boundary conditions,
   including restriction/extension lemmas for open domains.
4. Combine the action derivative and coefficient identity, then use a fundamental
   lemma: against all compactly supported smooth test variations, a continuous
   residual vanishes pointwise; with only local integrability, one obtains an
   almost-everywhere/distributional statement under the corresponding theorem.
5. Derive stationarity iff the Euler–Lagrange equations, with the same test class
   and analytic hypotheses in both directions. Stationarity is not minimality.

For free endpoint/boundary variations the boundary pairing must remain, giving
natural boundary conditions only after specifying which variations are free.
No boundary term is silently discarded. General-domain Stokes/divergence is
also not assumed: the pinned Mathlib has a useful divergence theorem on boxes,
which is not a ready-made theorem for every smooth or Lipschitz domain.

## Extension to Joyce's C-infinity geometry

Joyce's cotangent module represents derivations satisfying the chain rule for
**all smooth operations**, not just polynomial operations on the underlying
real algebra. See [Joyce, §5.2, Definition 5.3 and Remark 5.5](https://arxiv.org/pdf/1001.0023).
Mathlib's algebraic `KaehlerDifferential` is useful infrastructure, but cannot
simply be renamed as that smooth cotangent module.

Proposed bridge: implement smooth operations and smooth derivations separately;
prove their agreement with ordinary differentials on `C∞(U)`; then identify
the local section-jet representation with the appropriate smooth algebraic
construction. Define that construction by its universal property before
choosing a quotient presentation. Dual numbers for an infinitesimal variation
and first jets of sections must not be conflated.

The current `HasDerivAt` theorem would serve as the analytic realization of this
bridge. It proves none of the bridge yet. Keep integration, supports, boundary
conditions, and domination in an analytic layer: smooth algebra alone does not
supply them. Singular C-infinity schemes can have cotangent modules that are
not vector bundles, so the normed-space implementation should remain a local
model, not the ultimate definition.

## Decisions before adoption and suggested order

| Decision | Suggested initial choice | Still open |
|---|---|---|
| Public status | Keep this API experimental until coefficient and domain lemmas are reviewed | Final names, module boundaries, bundled regularity certificates |
| Domain representation | Explicit open coordinate domains and restriction/locality lemmas next | Ambient extensions versus a domain-native field type |
| Variations | Compactly supported smooth interior variations first | Fixed boundary traces, natural boundary conditions, Sobolev spaces |
| Differential notion | Derivatives along certified families now | Fréchet differentiability of the action on a chosen field space |
| Integration data | Scalar `L` relative to an explicit measure locally | Intrinsic densities versus top forms plus orientation; relative actions |
| Jet geometry | Prove local coordinate-change compatibility before globalizing | Splitting-based section jets, external implementation reuse, higher jets |
| Smooth algebra | A separate smooth-operation/cotangent layer with a comparison theorem | The exact C-infinity-ring and jet-ring presentations |

Proposed implementation order: (1) this local kernel and dominated action
derivative; (2) coordinate coefficients, test variations, and localization;
(3) weak first-variation identity; (4) fundamental lemma and classical
Euler–Lagrange theorem; (5) Mechanics and flat-space field-theory examples;
(6) chart covariance and bundle/density globalization, with the smooth-algebra
comparison developed alongside. This is a proposed sequence, not a new fixed
requirement for issue #7 or the provisional issue #8 outline.

## Reproduction and verification

From the repository root, using its pinned toolchain:

```sh
lake exe cache get
lake build --wfail ProjectAInos
lake exe mk_all --check --lib ProjectAInos
lake env lean -DwarningAsError=true checks/VariationalAudit.lean
```

`checks/VariationalAudit.lean` audits transitive axioms of every imported
declaration in the `ProjectAInos` namespace, requiring the repository's
allowlist: `propext`, `Classical.choice`, `Quot.sound`. It also prints the axiom
dependencies of the main prototype endpoints. This is a local check; the
existing CI workflow was not changed.

Final validation: the warning-free full build passed (2,922 Lake jobs), the
root-import check reported `No update necessary`, and the transitive-axiom audit
passed for 1,467 project declarations, including 61 variational declarations
(these counts include generated declarations, not just named theorems).
The main endpoints use only `propext`, `Classical.choice`, and `Quot.sound`.
Neither a `sorry` placeholder nor a new mathematical axiom is used in the
prototype. The absence of placeholders is not a claim that the unimplemented
geometric or Euler–Lagrange bridge has already been proved.

## Pinned Mathlib sources used

All links below identify the tested Mathlib commit, not the moving documentation
site.

* [Fréchet derivative chain rule for scalar-parameter paths](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Calculus/Deriv/Comp.lean): `HasFDerivAt.comp_hasDerivAt`.
* [Parameter integrals](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Calculus/ParametricIntegral.lean): `hasDerivAt_integral_of_dominated_loc_of_deriv_le`.
* [Interval integration by parts](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/MeasureTheory/Integral/IntervalIntegral/IntegrationByParts.lean): `intervalIntegral.integral_mul_deriv_eq_deriv_mul` and its weaker variants.
* [Directional integration by parts](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean): `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`.
* [Divergence on boxes](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean).
* [Smooth vector-bundle sections](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Geometry/Manifold/VectorBundle/ContMDiffSection.lean), [derivatives of smooth maps](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Geometry/Manifold/ContMDiffMFDeriv.lean).
* [Algebraic Kähler differentials](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/RingTheory/Kaehler/Basic.lean).
