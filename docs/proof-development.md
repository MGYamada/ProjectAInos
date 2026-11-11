# Proof Development

This record traces the development of the Lean proofs. The research plan and subject outline are in the [project README](../README.md).

## Thermodynamics Proof Development

The Lean library derives spectator cancellation from A6, constructs the real Grothendieck completion and its process cone, and proves order reflection and sequential order closedness. Under exchange comparison and a nonzero process direction, the real-cut construction gives an entropy coordinate. Linear extension then gives the entropy principle on matched conservation sectors, the relative cutoff formula, and the classification of entropy extensions by conserved linear quantities.

Concrete models cover nonnegative real states, two independent monotones, lexicographic failure of sequential order closedness, equality-only accessibility, and a conserved amount coordinate. The ideal-gas development proves homogeneity, concavity, and the fixed-amount operational entropy principle. Its composite algebraic consistency model identifies the completion with entropy-amount pairs and the conservation quotient with amount. Composition in this model uses the sum of separate-box entropies; this construction does not supply a geometric simple system or thermal family.

The [reservoir model](../ProjectAInos/Thermodynamics/ReservoirModel.lean) supplies a nonempty family satisfying the full simple-system and thermal interfaces, closed under positive scaling and thermal joins. Entropy equals energy and pressure is zero, so it exercises the universal-isotherm case. The [join assumption audit](thermodynamics-join-audit.md) distinguishes contact and splitting from the geometric regularity required of joined systems.

The physical development constructs coherent finite composites and their adiabatic quotient. It proves composition-label conservation for the A1–A6 closure of nonreactive elementary processes and constructs common scaled products for states with equal composition labels. Forward sectors are convex and relatively closed in an open convex finite-dimensional equilibrium domain. Irreversibility and unique finite-slope support imply nonempty interior; the supporting plane is inherited at every relative-boundary point. Energy orientation is constant throughout each simple system, giving the fixed-work accessibility criterion. The boundary is a differentiable graph whose derivative is the negative pressure form. Locally Lipschitz pressure gives local uniqueness of these graphs, and boundary connectedness propagates reversibility. These results establish simple-system comparison, strict nesting of distinct forward sectors, and openness of strict reference strips. Energy reflection handles the opposite orientation without changing the physical premises.

Typed thermal families connect actual scaled coordinate domains, thermal joins, and the positive scaled-copy clause of T2. Thermal contact fixes a common energy orientation across systems, and the zeroth law gives independent scaling invariance. Simple-system comparison and transversality establish local mixture intervals; connectedness joins their affine reference lines. These results give single-system product comparison and normalized concave continuous entropy. Thermal equilibrium between two copies is equivalent to fixed-total-energy entropy maximization, or intersection of their supporting-slope intervals. This criterion requires no extra differentiability assumption on entropy.

The location-of-isotherms dichotomy and crossed-calibrator existence are proved, including the universal-isotherm case. A concrete splitting and mixing cycle establishes thermal equilibrium between a joined state and each component. Pairwise calibrators align all simple-system reference directions, giving comparison in every finite scaled product. Canonical coordinate atoms provide the finite composite presentation and fixed-composition labels. Common-product realization then gives ECH for nonreactive accessibility. The final physical entropy endpoints take the explicit geometric and thermal premises, with no CH, ECH, or calibrator-existence assumption.

The reaction development defines direct, chained, and catalytic transition costs, proves their positive homogeneity, and selects compatible entropy constants by Hahn–Banach. The physical entropy theorem supplies the required calibrated monotonicity within each composition label. Absence of sinks is expressed using actual transitions, independently of entropy or costs. The resulting total entropy is additive, extensive, monotone for all accessible transformations, and characterizes accessibility when composition labels match. Infinite costs for unreachable labels remain allowed, including after adding catalysts.

The current physical endpoints use A1–A7, S1–S3 and T1–T4, with M added for reactions. Every admitted primitive simple system satisfies transversality T4; no extra T5 assumption is needed for this scope. Extending the theory to systems without T4, or proving temperature regularity, belongs to subsequent work. The ideal-gas phase-volume derivation remains in the statistical-mechanics stage of the research plan.

The public physical endpoints are in [PhysicalEntropyPrinciple](../ProjectAInos/Thermodynamics/PhysicalEntropyPrinciple.lean); [AtomicSystems](../ProjectAInos/Thermodynamics/AtomicSystems.lean) specializes them to canonical coordinate atoms. The [mathematical guide](thermodynamics.md) presents the algebraic theory, physical comparison, reactions, and models with proof links. The [implementation checklist](thermodynamics-status.md) maps the eight planned stages to their proof modules and scope.

Every completed stage must pass the warning-free Lean build, root-import check, and transitive axiom audit. Physical premises remain explicit in theorem statements. [Lean library entry point](../ProjectAInos.lean)

[Thermodynamics formalization notes](thermodynamics-notes.md) record the mathematical distinctions and modeling decisions exposed by the proofs, together with their current proof status.

See the [Landau–Lifshitz correspondence](landau-lifshitz.md) for the Mechanics proof targets and reference volumes for the other subjects.

## Shared Smooth Algebra and Geometry

The shared mathematical layers for Mechanics, Special Relativity, Electrodynamics, and General Relativity (research-plan topics 2–5) live in `ProjectAInos/SmoothAlgebra` and `ProjectAInos/SmoothGeometry`, independently of the physics and variational calculus. C∞-rings have finite smooth operations, substitution laws, and compatibility with a commutative real algebra. Morphisms preserve every smooth operation; their real-algebra homomorphisms are derived. The concrete models are ℝ, products, and C∞(ℝⁿ), including dimension zero. The smooth-function ring is proved free on its coordinate functions, with evaluation and pullback as morphisms. A nonpolynomial check proves `exp(a + b) = exp(a) * exp(b)` in every C∞-ring.

The geometry follows mathlib's progression from ringed spaces through `Spec` to `Scheme`, with Joyce's real points and C∞ operations. Smooth congruence quotients and cutoff functions construct point localizations with their universal property. Locally represented sections form the structure sheaf, and its stalks are identified with the localizations. The resulting spectrum functor supplies the actual affine models in the local-affine definition of a C∞ scheme. Affine schemes are the essential image of this functor. Examples include affine spaces and the empty scheme.

Free C∞-rings on arbitrary sets give general localizations with their smooth universal property. Their spectra are identified with the surviving-point subspaces; principal localizations give open immersions. These supply open subschemes and pullbacks along open immersions. Open gluing data construct actual C∞ schemes, with descent and uniqueness of compatible morphisms proved as a categorical colimit. The manifold comparison identifies the Euclidean smooth-function sheaf with its affine spectrum, then proves local affineness for boundaryless finite-dimensional smooth manifolds using coordinate charts. Smooth maps induce scheme morphisms with identity and composition laws.

`LorentzMetric` equips the actual tangent bundle with a smooth bilinear form of Lorentz signature, without requiring a global frame. `LorentzManifold.toScheme` uses the same manifold construction for every such metric. Minkowski space is an instance with constant coefficients, a proved affine scheme comparison, and proved local inertial coordinates. The [smooth-geometry guide](smooth-geometry.md) and [formalization notes](smooth-geometry-notes.md) record these constructions and their scope. The Γ–Spec adjunction, full faithfulness of the manifold construction, universal cotangent modules, and curvature are subsequent stages.

## Minkowski Geometry and Relativistic Kinematics

Section 3.1 now has an explicit two-signature geometry layer and a `(-+++)`,
`c = 1` physics layer. The Lean library proves causal-cone convexity and affine
causal order, Lorentz matrix and determinant identities, Poincaré scheme
automorphisms, observer decompositions, passive boosts, velocity composition,
proper-time invariance, and normalized four-velocity. Regularity and causal
premises are hypotheses, including local C¹ assumptions for reparameterization.

Flat forms use mathlib's exterior derivative and a proved comparison with
exterior powers. The wedge normalization, graded Leibniz rule, pullback laws,
and exterior-derivative locality are proved. Hodge duality has explicit metric
and orientation parameters, a proved signed-inverse comparison with mathlib's
operator, square/sign/naturality laws, and observer reconstruction of arbitrary
two-forms. Exact examples include a nonzero boost, time dilation, `A = t dx`,
and all six coordinate two-form Hodge signs. The [guide](special-relativity.md)
records the API, scope, and verification commands for
[issue #40](https://github.com/MGYamada/ProjectAInos/issues/40), the shared
prerequisite of [issue #8](https://github.com/MGYamada/ProjectAInos/issues/8).

## Shared Variational Foundation

The shared variational calculus uses sections of a trivial bundle over a finite-dimensional real coordinate space. For a jointly C² Lagrangian and a C² field with integrable density, Lean proves the action derivative for smooth variations with compact support inside an open region. It then proves that stationarity is equivalent to the pointwise Euler–Lagrange equation. The theorem covers time and four-dimensional bases and keeps the choice of Haar measure explicit. The interval integration-by-parts identity also retains the endpoint term for fixed-endpoint applications.

This supplies the common local foundation for [issue #7](https://github.com/MGYamada/ProjectAInos/issues/7), building on [PR #29](https://github.com/MGYamada/ProjectAInos/pull/29). The [variational guide](variational.md) describes the endpoint and its hypotheses. The [smooth-algebra guide](smooth-algebra.md) describes the free smooth-function rings and their directional chain rule. Compact base regions now also supply domination without a support condition on the variation, and the interval identity handles covector–vector pairings.

[Shared variational formalization notes](variational-notes.md) record the measure, regularity, and smooth-algebra distinctions exposed by these proofs.

## Mechanics Proof Development

The [C∞ mechanics research plan](cinfty-mechanics.md) preserves the mathematical blueprint, the 52 Landau–Lifshitz targets, proposed proofs, experiment ledger, and references from the former local TeX manuscript. It distinguishes the implemented real analytic model from the planned abstract C∞-ring constructions.

`ProjectAInos/Mechanics` uses the shared foundation for a real time interval and a real normed position space, including any finite number of generalized coordinates. For a jointly C² Lagrangian `L(t,q,v)` and a C² path, Lean proves the derivative of the actual action, its first-variation formula with the endpoint momentum pairing, and the equivalence between fixed-endpoint stationarity and the Euler–Lagrange equations on `(a,b)` for `a < b`. Variations may have nonzero derivatives at the endpoints. Smooth operations from the shared C∞-ring give mechanical Lagrangians with the required regularity automatically. The natural scalar Lagrangian yields `m q'' = −V'(q)`.

Adding the total time derivative of a function of time and position changes the action by its endpoint difference. Lean proves that fixed-endpoint stationarity is preserved and that the Euler–Lagrange covector agrees pointwise. [Total time derivatives](mechanics.md#total-time-derivatives)

The mechanics guide gives the assumptions and proof map. The formalization notes record distinctions and design decisions exposed by the proofs. Conservation identities, Noether's theorem, and further mechanical models are the next stages of the plan. Abstract quotients, dual numbers, cotangent modules and jet rings, followed by Poisson and Hamiltonian mechanics, remain research-plan stages. [Mechanics guide](mechanics.md) · [Formalization notes](mechanics-notes.md)
