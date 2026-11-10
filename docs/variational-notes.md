# Shared Variational Formalization Notes

These notes record mathematical distinctions and interface decisions in `ProjectAInos/Variational`. They complement the [shared calculus guide](variational.md), [smooth-algebra guide](smooth-algebra.md), and [Mechanics notes](mechanics-notes.md). Each entry distinguishes proved results from remaining research targets. They document the formal model rather than claim new mathematical results.

## V01. Restricting a Haar measure changes the integration-by-parts problem

**Observation.** A measure restricted to a region is generally not translation invariant. A whole-space integration-by-parts theorem for an additive Haar measure therefore cannot simply be applied with `μ.restrict Ω`. Boundary terms have to be accounted for.

**Interface decision.** The shared interior-variation proof first integrates by parts with the ambient Haar measure. The variation and its derivative vanish outside its compact support, which lies inside Ω. This allows the whole-space integrals to be identified with the restricted integrals. For a time interval and fixed endpoint values, the separate interval theorem instead retains the boundary pairing explicitly.

**Proof status.** `directional_integrationByParts` requires an ambient Haar measure. `firstVariation_eq_integral_eulerLagrange` proves the support-based passage to and from restricted integrals. `interval_firstVariation_pairing` retains the boundary term. A divergence theorem for arbitrary domains, natural boundary conditions, and boundary traces are not supplied by the current interface. [Integration by parts](../ProjectAInos/Variational/IntegrationByParts.lean) · [Interior Euler–Lagrange theorem](../ProjectAInos/Variational/EulerLagrange.lean)

## V02. Compact support and a compact base give different domination arguments

**Observation.** To differentiate an action, the parameter derivative must have an integrable bound uniform near the variation parameter. There are two useful sources of compactness. A compactly supported variation localizes the change in density, even when the base region is unbounded. A compact base region bounds the derivative without any support condition on the variation.

**Interface decision.** `hasDerivAt_action_of_compactSupport` retains integrability of the unperturbed density as an explicit premise: compact support of η does not make the background action finite on an unbounded region. `hasDerivAt_action_restrict_compact` instead derives the needed integrability on a compact region from regularity and local finiteness of the measure. Both discharge the hypotheses of the same common `hasDerivAt_action` theorem.

**Proof status.** Both routes are proved from joint C² regularity, using continuity of the varied first-variation density on a product with a compact parameter interval. The compact-base version is used by Mechanics for variations that need not vanish near the interval's endpoints. [Regularity](../ProjectAInos/Variational/Regularity.lean) · [Action derivative interface](../ProjectAInos/Variational/Action.lean)

## V03. A first jet identity needs differentiability

**Observation.** Mathlib's `fderiv` is a total function, including at points where a function is not differentiable. Thus an unconditional algebraic rewrite of `jet (u + ε • η)` as `jet u + ε • jet η` would be unjustified. The analytic first jet is also distinct from a freely generated abstract jet algebra.

**Interface decision.** `jet_add`, `jet_const_smul`, and `jet_perturb` carry explicit differentiability hypotheses. The higher-level regularity theorems discharge them from C² assumptions. The first jet is `F × (E →L[ℝ] F)`, with the ordinary Fréchet derivative in its second slot. A globally defined function represents a section of a fixed trivial bundle; no global jet bundle or algebraic quotient is implicit in the type.

**Proof status.** The jet identities and the local first-variation chain rule are proved under the stated hypotheses. The construction of abstract jet C∞-rings and their comparison with these analytic jets remains a separate stage. [Local calculus](../ProjectAInos/Variational/Local.lean)

## V04. The field equation is recovered from scalar tests

**Observation.** The first variation initially gives an integral identity. The fundamental lemma supplies almost-everywhere vanishing, not an immediate pointwise equation. For a vector-valued field, the residual naturally lies in the continuous dual of the fibre.

**Interface decision.** The proof tests with `η(x) = g(x) • v` for each smooth scalar test function g and fixed fibre vector v. Each scalar residual pairing is continuous. Positivity of Haar measure on nonempty open sets upgrades its almost-everywhere vanishing to pointwise vanishing, and extensionality gives equality of covectors. This avoids choosing an inner product on the fibre.

**Proof status.** `stationary_iff_eulerLagrange` proves the full equivalence for a finite-dimensional coordinate base and an arbitrary real normed fibre. Finite dimensionality belongs to the coordinate and Haar-measure part of this theorem; the basic local chain rule and parameter differentiation interfaces do not require a finite-dimensional fibre. Weak solutions without residual continuity would need a different endpoint statement. [Euler–Lagrange](../ProjectAInos/Variational/EulerLagrange.lean) · [Action](../ProjectAInos/Variational/Action.lean)

## V05. The smooth algebra and the analytic model have different assumptions

**Observation.** An abstract C∞-ring supports every finite smooth operation, but need not carry a topology or be nontrivial. Its existing commutative real-algebra structure must agree with these operations. In contrast, differentiating a real smooth function uses its normed-space model and ordinary calculus.

**Interface decision.** `SmoothRing A` is additional structure on `[CommRing A] [Algebra ℝ A]`; it does not install a second ring structure. `SmoothRingHom` preserves all smooth operations and derives its real-algebra homomorphism. On the concrete free smooth-function rings, `directionalEvaluation_op` proves the chain rule for arbitrary smooth substitution. Mechanics uses smooth-ring evaluation to turn such an observable into a real Lagrangian. C∞ regularity is carried by the bundled observables, while C² suffices for the current analytic first-variation theorem.

**Proof status.** The compatibility, free-ring universal property, evaluation and pullback morphisms, nonpolynomial exponential identity, and concrete directional chain rule are proved. No universal smooth cotangent module, quotient C∞-ring construction, or coefficient-valued fundamental lemma is inferred from these results. [Smooth-ring interface](../ProjectAInos/Variational/SmoothAlgebra/Basic.lean) · [Free models](../ProjectAInos/Variational/SmoothAlgebra/Models.lean) · [Directional chain rule](../ProjectAInos/Variational/SmoothAlgebra/Differential.lean) · [Mechanical model](../ProjectAInos/Mechanics/SmoothLagrangian.lean)
