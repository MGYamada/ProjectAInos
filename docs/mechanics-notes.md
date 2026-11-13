# Mechanics Formalization Notes

These notes record mathematical distinctions and modeling decisions made explicit by the Lean development, following the [thermodynamics notes](thermodynamics-notes.md). Each entry states its effect on the interface and its proof status. These are clarifications of the formal model, not claims of new physical results.

The [research plan](cinfty-mechanics.md) preserves the long-term programme. The [mechanics guide](mechanics.md) states the implemented endpoint and its hypotheses. Add future observations here with proof links; keep unresolved claims explicit.

## M01. Fixed endpoints are weaker than interior compact support

**Observation.** A fixed-endpoint variation satisfies `η(a)=η(b)=0`, but may have nonzero derivatives at both ends and may be nonzero arbitrarily close to them. For `a < b`, the scalar variation `η(t)=(t−a)(b−t)` has `η'(a)=b−a ≠ 0`.

**Interface decision.** `FixedEndpointVariation` requires smoothness and the two value equations, with no support condition. The previous common theorem for compactly supported interior variations alone would not cover this full class. The new common action-derivative theorem uses compactness of the base interval. Integration by parts retains the momentum pairing until the endpoint values cancel it.

**Proof status.** `polynomial_fixedEndpointVariation` and `polynomial_variation_left_derivative` check this example. `firstVariation_fixedEndpoints` covers the full variation class. Compactly supported interior tests are used only to infer the differential equation in the forward implication; the converse covers every fixed-endpoint variation. [Examples](../ProjectAInos/Mechanics/Examples.lean) · [First variation](../ProjectAInos/Mechanics/FirstVariation.lean) · [Euler–Lagrange](../ProjectAInos/Mechanics/EulerLagrange.lean)

## M02. The action derivative needs analytic justification

**Observation.** The identity for the pointwise derivative of `L(t,qε,qε')` does not, by itself, justify differentiating its integral. On a finite interval, joint C² regularity bounds that derivative on a compact product of parameter and time intervals. The resulting constant bound is integrable for restricted Lebesgue measure.

**Interface decision.** `hasDerivAt_action_restrict_compact` proves this analytic step in the common layer. The mechanics endpoint consequently has no assumed first-variation formula, no assumed fundamental lemma, and no independent domination or integrability premise. The theorem still explicitly assumes C² regularity of the ambient Lagrangian and path.

**Proof status.** The common domination argument and the actual `HasDerivAt` statement are proved. Reducing the hypotheses to functions defined only on a closed interval, or to weaker Sobolev regularity, remains future work. [Common regularity](../ProjectAInos/Variational/Regularity.lean) · [Mechanical action derivative](../ProjectAInos/Mechanics/FirstVariation.lean)

## M03. Momentum and the residual are covectors

**Observation.** Both `∂L/∂q` and `∂L/∂v` naturally act on configuration vectors. Writing them as vectors would introduce an inner product and a dual-space identification that the variational argument does not require. In one-dimensional time, the common derivative `Dq : ℝ →L[ℝ] Q` becomes velocity by evaluation at `1`.

**Interface decision.** `force`, `momentum`, and `eulerLagrange` take values in `Q →L[ℝ] ℝ`. `positionVelocity` is an explicit continuous linear map connecting the shared first jet to the mechanical pair. The proof works for any real normed `Q`, and thus for every finite number of generalized coordinates, without a metric on `Q`.

**Proof status.** The jet identification, fibre derivative decomposition and covector-valued endpoint formula are proved. Coordinate transformations and cotangent bundles on a nonlinear configuration manifold are not yet implemented. [Basic interfaces](../ProjectAInos/Mechanics/Basic.lean) · [Covector integration by parts](../ProjectAInos/Variational/IntegrationByParts.lean)

## M04. A nondegenerate interval is necessary to detect an equation

**Observation.** When `a = b`, the action is identically zero for all paths. Stationarity then supplies no differential information. Also, the measure-theoretic fundamental lemma initially gives an almost-everywhere equation; it becomes pointwise because the residual is continuous and Lebesgue measure is positive on nonempty open intervals.

**Interface decision.** The equation-detecting equivalence requires `a < b` and states the equation on `(a,b)`. The first-variation identity itself retains oriented interval integrals. Changing between `[a,b]`, `(a,b]`, and `(a,b)` in scalar integrals uses the fact that endpoints have zero measure; it does not silently change the admissible endpoint values of a path.

**Proof status.** `stationary_self` proves the zero-length case, while `stationary_iff_eulerLagrange` contains the fundamental-lemma and continuity steps. No theorem about natural boundary conditions or free endpoints is asserted. [Euler–Lagrange](../ProjectAInos/Mechanics/EulerLagrange.lean) · [Examples](../ProjectAInos/Mechanics/Examples.lean)

## M05. Stationarity, regularity of the Lagrangian, and minimality differ

**Observation.** Deriving Euler–Lagrange from first-order stationarity requires neither a positive velocity Hessian nor an invertible one. Invertibility is needed for later steps such as solving the equations for accelerations or constructing a Legendre equivalence. First-order stationarity alone makes no assertion of local or global minimality.

**Interface decision.** `Stationary` is defined by the actual parameter derivative, independently of the field equation. The equivalence assumes joint C² regularity but no Hessian condition. For the natural Lagrangian, Newton's equation is retained as `m q'' = −V'(q)`; this statement makes sense even at zero mass. Existence, uniqueness and minimality of trajectories are separate targets.

**Proof status.** The first-order equivalence and `stationary_natural_iff` are proved. No second-variation test, Legendre theorem or existence theorem is claimed. [Definitions](../ProjectAInos/Mechanics/Basic.lean) · [Natural Lagrangian](../ProjectAInos/Mechanics/Examples.lean)

## M06. The concrete smooth model does not settle arbitrary coefficient rings

**Observation.** A real smooth operation supplies an actual C∞ observable, and evaluation at `(t,q,v)` preserves all smooth substitutions. This connects the common algebraic API to the analytic action. It does not establish a fundamental lemma with coefficients in an arbitrary quotient C∞-ring, the unresolved issue noted in the original manuscript.

**Interface decision.** `ofSmoothOperation` uses the existing `SmoothRingHom` evaluation, derives joint C∞ regularity, and then invokes the real analytic theorem. The algebraic theory is not duplicated inside Mechanics. The analytic jet remains the pair of a field and its Fréchet derivative; it is not presented as a constructed abstract jet ring.

**Proof status.** `ofSmoothOperation_op` and `stationary_ofSmoothOperation_iff` prove the concrete bridge. Abstract quotients, dual numbers, universal smooth differentials, jet rings, and the coefficient-valued fundamental lemma remain research targets. [Smooth Lagrangians](../ProjectAInos/Mechanics/SmoothLagrangian.lean) · [Original critical-subfunctor discussion](cinfty-mechanics.md#rem:fundamental)

## M07. A boundary term shifts momentum and preserves the equations

For $F(t,q)$, the action shift is $F(b,q(b))-F(a,q(a))$. Every path with the same endpoints receives the same shift, so the action differences between such paths are preserved. Along a fixed-endpoint variation, the shift is constant even when the endpoint velocities vary. The action identity and stationarity equivalence use C¹ regularity of $F$ and the path and continuity of $L$.

The velocity derivative of the added density is $\partial_q F$, so the momentum covector shifts by that amount. Along the path, the derivative of this shift cancels the extra position derivative by symmetry of $d^2F$. This proves pointwise equality of the Euler–Lagrange residuals with C² $F$, $L$, and $q$. At that regularity, the added density is guaranteed to be C¹, which is why the proof computes the cancellation directly. The momentum shift also identifies the correction to track when a symmetry changes a Lagrangian by a total derivative in the planned Noether development. [Lean proofs](../ProjectAInos/Mechanics/TotalTimeDerivative.lean) · [Noether target](cinfty-mechanics.md#prop:noether-jet)

## M08. The chain rule is the only law of a C∞-derivation

**Observation.** For a C∞-ring `A` and an `A`-module `M`, a map `d : A → M` satisfying the chain rule for every finite smooth operation is automatically additive (binary addition), satisfies the Leibniz rule (multiplication), vanishes on real constants (nullary operations), and is real linear. The chain rule also gives identities that ordinary derivations of the underlying real algebra need not satisfy, such as `d (exp a) = exp a • d a`.

**Interface decision.** `SmoothDerivation A M` has the chain rule as its single field. `map_add`, `map_mul`, `map_algebraMap` and `map_smul` are theorems, so no redundant law has to be proved when a derivation is constructed. `toDerivation` produces Mathlib's `Derivation ℝ A M`. It needs `[Module ℝ M] [IsScalarTower ℝ A M]` because the definition assumes only an `A`-module; the constant-multiple law `map_algebraMap_mul` holds without a real action on `M`.

**Proof status.** The derived laws, `map_exp` and `toDerivation` are proved. The manuscript's counterexample showing that the converse fails (Kähler differentials of `C∞(ℝ)`) is not formalized. [Derivations](../ProjectAInos/SmoothAlgebra/Derivation.lean)

## M09. Dual numbers need partial derivatives as operations

**Observation.** The smooth structure on `A[ε]` is `Φ_f(c + ε b) = Φ_f(c) + ε Σᵢ Φ_{∂ᵢf}(c) bᵢ`. Its substitution law is the multivariable chain rule, read as an identity between operations. A derivative evaluated at a real point, which was all the algebra layer had (`directionalEvaluation`), cannot state this law for an abstract ring: `∂ᵢf` has to be an operation that the ring can interpret.

**Interface decision.** `SmoothOperation.partialDeriv` returns an operation, and `partialDeriv_comp` is the chain rule in that form. The instance is placed on Mathlib's `DualNumber A`, so the ring and real-algebra structures are Mathlib's and no second ring instance exists. The general square-zero extension `A ⊕ M` is deferred: Mathlib's `TrivSqZeroExt` commutative-ring instance needs `Module Aᵐᵒᵖ M` and `IsCentralScalar A M`, which a consumer holding only an `A`-module would have to supply. For `M = A` they are automatic.

**Proof status.** The `SmoothRing (DualNumber A)` instance, the projection `fstHom`, the zero section `inlHom` and the nonpolynomial check `exp_inl_add_inr` are proved. [Partial derivatives](../ProjectAInos/SmoothAlgebra/PartialDerivative.lean) · [Dual numbers](../ProjectAInos/SmoothAlgebra/DualNumber.lean)

## M10. Tier A statements still rest on calculus of the operations, including (S)

**Observation.** The manuscript labels the dual-number structure (Example 2(c)) and the Lie algebra of vector fields (Definition 17) as tier A, "algebra over an abstract C∞-ring, no analysis", and says that milestones M1 and M2 depend on no analytic lemma except (H). The statements are indeed about an abstract ring, but their proofs use analytic facts about the operations `ℝⁿ → ℝ` themselves. The dual-number structure uses the chain rule. Closure of vector fields under the commutator uses the symmetry of second partial derivatives, the interface lemma (S): in `ξ(η(Φ_f(a))) − η(ξ(Φ_f(a)))` the second-order terms `Σ_{i,j} Φ_{∂ⱼ∂ᵢf}(a) (ξ(aⱼ) η(aᵢ) − η(aⱼ) ξ(aᵢ))` cancel only because `∂ⱼ∂ᵢf = ∂ᵢ∂ⱼf`.

**Interface decision.** The calculus facts are isolated in one module as identities between operations: `partialDeriv_comp` and `partialDeriv_comm`. Algebra over an abstract ring cites these identities and uses no analysis of its own. `commutator_chain` is the single place where (S) enters the theory of derivations.

**Proof status.** Both identities and the Lie-ring instance on `SmoothDerivation A A` are proved. The tier labels in the manuscript are unchanged; the accurate reading is that M2 depends on (S) through M1 as well as on (H) for quotients. [Partial derivatives](../ProjectAInos/SmoothAlgebra/PartialDerivative.lean) · [Derivations](../ProjectAInos/SmoothAlgebra/Derivation.lean)

## M11. Derivations of the free ring are free without constructing Ω

**Observation.** Proposition 16(a) says the cotangent module of `C∞(ℝⁿ)` is free on `dx₁, …, dxₙ`. The same content can be stated without the universal module: derivations of `C∞(ℝⁿ)` into any module correspond to arbitrary `n`-tuples of values on the coordinates. One direction is a single use of the chain rule, because every `f` equals `Φ_f(x₁, …, xₙ)`.

**Interface decision.** `apply_eq_sum_partialDeriv` and `equivCoordinates` state this Hom form. The coordinate fields `partialDerivation i` give a nondegenerate instance of `SmoothDerivation`, and `lie_partialDerivation_proj_smul` (`[∂ᵢ, xⱼ ∂ₖ] = δᵢⱼ ∂ₖ`) shows that the bracket is not trivial. These statements use the default `SmoothRing` instance on `SmoothOperation n`, whose operation is substitution; the lower-priority manifold instance on the same type agrees with it only after unfolding.

**Proof status.** The classification is proved as a bijection; its linearity is not packaged. The universal cotangent module `Ω_A`, its universal property, and Proposition 16(b) and (c) are not constructed. [Derivations](../ProjectAInos/SmoothAlgebra/Derivation.lean)

## M12. Infinitesimal automorphisms are stated over the same ring

**Observation.** Proposition 18 identifies vector fields with morphisms `A → A[ε]` that reduce to the identity at `ε = 0`. Proposition 12 is more general: a `B`-point of the tangent functor is a morphism `φ : A → B` with a derivation along `φ`. A derivation along `φ` takes values in `B` regarded as an `A`-module through `φ`, which needs a module structure that depends on a morphism.

**Interface decision.** `equivInfinitesimalAut` uses the subtype of morphisms `φ` with `(φ a).fst = a` for all `a`; `fstHom_comp_toInfinitesimalAut` gives the equivalent form `fstHom ∘ φ = id`. Derivations along a morphism are left to the stage that introduces the tangent functor, so that the module structure through `φ` is designed once.

**Proof status.** Proposition 18 is proved. Propositions 12 and 13 and the tangent functor are not implemented. [Derivations](../ProjectAInos/SmoothAlgebra/Derivation.lean)

## M13. A Poisson bracket cannot reuse the bracket notation of a ring

**Observation.** The manuscript's sketch declares `class PoissonCinftyRing (P) extends CinftyRing P, Bracket P P`. Mathlib already gives every ring the instance `Ring.instBracket`, the commutator `⁅x, y⁆ = x * y - y * x`. On a commutative ring this commutator is identically zero. Extending `Bracket P P` would therefore install a second instance on the same type, and `⁅f, g⁆` could resolve to the zero commutator.

**Interface decision.** None yet. The Poisson stage should carry the bracket as its own operation with dedicated notation, or wrap the ring in a type synonym. The problem does not arise for vector fields: `SmoothDerivation A A` is not a ring, so its `Bracket` instance is the only one.

**Proof status.** Not implemented. This records a constraint for the second half of milestone M2.

## M14. The standard jet ring can probably reuse the free ring on generators

**Observation.** The standard jet model `Jₙ` is the ring of smooth functions of `t` and finitely many of the variables `qᵢ⁽ᵏ⁾`. `FreeSmoothRing ι` is already the ring of smooth functions on real assignments to `ι` with finite coordinate dependence, so `ι = Unit ⊕ (Fin n × ℕ)` gives the same carrier together with its universal property.

**Interface decision.** None yet. Using it for jets needs partial derivatives on `FreeSmoothRing`, which exist so far only on `SmoothOperation n`, and a proof that they commute.

**Proof status.** Not implemented, and the identification is a design observation, not a theorem. Abstract jet rings need this model as their nondegenerate instance, so the two should land together. [Free rings](../ProjectAInos/SmoothAlgebra/Free.lean)
