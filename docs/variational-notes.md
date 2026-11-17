# Shared Variational Formalization Notes

These notes record mathematical distinctions and interface decisions in `ProjectAinos/Variational`. They complement the [shared calculus guide](variational.md), [smooth-algebra guide](smooth-algebra.md), and [Mechanics notes](mechanics-notes.md). Each entry distinguishes proved results from remaining research targets. They document the formal model rather than claim new mathematical results.

## V01. Restricting a Haar measure changes the integration-by-parts problem

**Observation.** A measure restricted to a region is generally not translation invariant. A whole-space integration-by-parts theorem for an additive Haar measure therefore cannot simply be applied with `μ.restrict Ω`. Boundary terms have to be accounted for.

**Interface decision.** The shared interior-variation proof first integrates by parts with the ambient Haar measure. The variation and its derivative vanish outside its compact support, which lies inside Ω. This allows the whole-space integrals to be identified with the restricted integrals. For a time interval and fixed endpoint values, the separate interval theorem instead retains the boundary pairing explicitly.

**Proof status.** `directional_integrationByParts` requires an ambient Haar measure. `firstVariation_eq_integral_eulerLagrange` proves the support-based passage to and from restricted integrals. `interval_firstVariation_pairing` retains the boundary term. A divergence theorem for arbitrary domains, natural boundary conditions, and boundary traces are not supplied by the current interface. [Integration by parts](../ProjectAinos/Variational/IntegrationByParts.lean) · [Interior Euler–Lagrange theorem](../ProjectAinos/Variational/EulerLagrange.lean)

## V02. Compact support and a compact base give different domination arguments

**Observation.** To differentiate an action, the parameter derivative must have an integrable bound uniform near the variation parameter. There are two useful sources of compactness. A compactly supported variation localizes the change in density, even when the base region is unbounded. A compact base region bounds the derivative without any support condition on the variation.

**Interface decision.** `hasDerivAt_action_of_compactSupport` retains integrability of the unperturbed density as an explicit premise: compact support of η does not make the background action finite on an unbounded region. `hasDerivAt_action_restrict_compact` instead derives the needed integrability on a compact region from regularity and local finiteness of the measure. Both discharge the hypotheses of the same common `hasDerivAt_action` theorem.

**Proof status.** Both routes are proved from joint C² regularity, using continuity of the varied first-variation density on a product with a compact parameter interval. The compact-base version is used by Mechanics for variations that need not vanish near the interval's endpoints. [Regularity](../ProjectAinos/Variational/Regularity.lean) · [Action derivative interface](../ProjectAinos/Variational/Action.lean)

## V03. A first jet identity needs differentiability

**Observation.** Mathlib's `fderiv` is a total function, including at points where a function is not differentiable. Thus an unconditional algebraic rewrite of `jet (u + ε • η)` as `jet u + ε • jet η` would be unjustified. The analytic first jet is also distinct from a freely generated abstract jet algebra.

**Interface decision.** `jet_add`, `jet_const_smul`, and `jet_perturb` carry explicit differentiability hypotheses. The higher-level regularity theorems discharge them from C² assumptions. The first jet is `F × (E →L[ℝ] F)`, with the ordinary Fréchet derivative in its second slot. A globally defined function represents a section of a fixed trivial bundle; no global jet bundle or algebraic quotient is implicit in the type.

**Proof status.** The jet identities and the local first-variation chain rule are proved under the stated hypotheses. The construction of abstract jet C∞-rings and their comparison with these analytic jets remains a separate stage. [Local calculus](../ProjectAinos/Variational/Local.lean)

## V04. The field equation is recovered from scalar tests

**Observation.** The first variation initially gives an integral identity. The fundamental lemma supplies almost-everywhere vanishing, not an immediate pointwise equation. For a vector-valued field, the residual naturally lies in the continuous dual of the fibre.

**Interface decision.** The proof tests with `η(x) = g(x) • v` for each smooth scalar test function g and fixed fibre vector v. Each scalar residual pairing is continuous. Positivity of Haar measure on nonempty open sets upgrades its almost-everywhere vanishing to pointwise vanishing, and extensionality gives equality of covectors. This avoids choosing an inner product on the fibre.

**Proof status.** `stationary_iff_eulerLagrange` proves the full equivalence for a finite-dimensional coordinate base and an arbitrary real normed fibre. Finite dimensionality belongs to the coordinate and Haar-measure part of this theorem; the basic local chain rule and parameter differentiation interfaces do not require a finite-dimensional fibre. Weak solutions without residual continuity would need a different endpoint statement. [Euler–Lagrange](../ProjectAinos/Variational/EulerLagrange.lean) · [Action](../ProjectAinos/Variational/Action.lean)

## V05. The smooth algebra and the analytic model have different assumptions

**Observation.** An abstract C∞-ring supports every finite smooth operation, but need not carry a topology or be nontrivial. Its existing commutative real-algebra structure must agree with these operations. In contrast, differentiating a real smooth function uses its normed-space model and ordinary calculus.

**Interface decision.** `SmoothRing A` is additional structure on `[CommRing A] [Algebra ℝ A]`; it does not install a second ring structure. `SmoothRingHom` preserves all smooth operations and derives its real-algebra homomorphism. On the concrete free smooth-function rings, `directionalEvaluation_op` proves the chain rule for arbitrary smooth substitution. Mechanics uses smooth-ring evaluation to turn such an observable into a real Lagrangian. C∞ regularity is carried by the bundled observables, while C² suffices for the current analytic first-variation theorem.

**Proof status.** The compatibility, free-ring universal property, evaluation and pullback morphisms, nonpolynomial exponential identity, and concrete directional chain rule are proved. No universal smooth cotangent module, quotient C∞-ring construction, or coefficient-valued fundamental lemma is inferred from these results. [Smooth-ring interface](../ProjectAinos/SmoothAlgebra/Basic.lean) · [Free models](../ProjectAinos/SmoothAlgebra/Models.lean) · [Directional chain rule](../ProjectAinos/SmoothAlgebra/Differential.lean) · [Mechanical model](../ProjectAinos/Mechanics/SmoothLagrangian.lean)

## V06. Relativistic fibre derivatives use the physical velocity

**Observation.** The massive spatial Lagrangian is smooth for `‖v‖ < 1`.
The proper velocity `w = γv` gives a global chart of this ball. In one
spatial dimension the pulled-back Lagrangian has derivative
`m w/(1 + w²)^(3/2)` in `w`. The physical momentum is the derivative in
`v` evaluated at that velocity and equals `m w`.

**Interface decision.** Start SR-D4 with the open velocity ball and take
the fibre derivative in `v`. Use the proper-velocity formula for the inverse
momentum map. A later formulation in the chart must transport the vertical
derivatives and keep `q̇ = v(w)` as the trajectory relation.

**Proof status.** The open-domain action and stationarity/EL equivalence
are proved for the timelike spacetime model. The spatial Legendre comparison
and its charged-particle specialization are targets. [SR particle action](../ProjectAinos/SpecialRelativity/ParticleAction.lean) · [SR-D4](cinfty-special-relativity.md#energy-and-the-coordinate-time-hamiltonian) · [Charged Hamiltonian](cinfty-electrodynamics.md#actual-worldline-variation)

## V07. The multi-indices of a field jet are multisets, and the total derivatives must be shown to commute

**Observation.** For one independent variable the jet co-ordinates are indexed by the order, and `D^k` is an iterate. For several independent variables a jet co-ordinate `uᵃ_K` has a multi-index, and `D^K` is defined only if the total derivatives commute. This is a statement to prove: `D_μ = ∂_μ + Σ_K Σₐ uᵃ_{μ+K} ∂ᵃ_K`, and in `D_μ D_ν F` the term `Σ_K Σₐ uᵃ_{μ+ν+K} ∂ᵃ_K F` is symmetric because `μ + ν + K = ν + μ + K` as multisets. The Euler operator needs it before it can be written. The axiom of finiteness is also different: an element has finite order in the one-variable ring, and here it involves finitely many multi-indices.

**Interface decision.** A multi-index is a `Multiset ι`, and `uᵃ_{μ+K}` is `u a (μ ::ₘ K)`; the commutation of the indices is `Multiset.cons_swap`. `FieldJetRing` has the axiom `finite_support`, a finite set of multi-indices outside of which all `∂ᵃ_K F` vanish, and `SupportIn F S` names such a set; a total derivative has the support `S ∪ (μ + S)`. `iterTotalDeriv` is the fold of the total derivatives over the multiset, which the commutation makes well defined. Noether's identity and the stress tensor are stated for a Lagrangian of the first order, as in mechanics. The standard model has the index type `ι ⊕ κ × Multiset ι`, which is infinite, so the comparison of `D_μ` with `∂_μ` on a prolongation uses `FreeSmoothRing.map_derivation_eq`, which checks the generators, and not the chain rule for finitely many generators.

**Proof status.** `FieldJetRing.totalDeriv_comm`, `d_totalDeriv`, `euler_totalDeriv`, `prolong_eq_euler_add_divergence`, `divergence_stress`, `conserved_stress` and `StandardFieldJet.prolongation_totalDeriv` are proved. The second identity of Noether, for a symmetry that depends on an arbitrary function, and the identities of the Lagrangian of Maxwell are not in these modules. [Basic](../ProjectAinos/Variational/FieldJet/Basic.lean) · [Euler](../ProjectAinos/Variational/FieldJet/Euler.lean) · [Noether](../ProjectAinos/Variational/FieldJet/Noether.lean) · [Standard](../ProjectAinos/Variational/FieldJet/Standard.lean)
