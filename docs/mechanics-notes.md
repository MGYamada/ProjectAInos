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

**Interface decision.** `PoissonStructure P` is a structure with a field `bracket`, written `π.bracket f g`, and no notation. A structure also allows several Poisson structures on one ring, which a class would not: the canonical bracket and a Lie–Poisson bracket can live on the same free ring. The problem does not arise for vector fields: `SmoothDerivation A A` is not a ring, so its `Bracket` instance is the only one, and `hamiltonian_bracket` uses it on the right-hand side.

**Proof status.** Implemented in the second half of milestone M2. [Poisson structures](../ProjectAInos/SmoothAlgebra/Poisson/Basic.lean)

## M14. The standard jet ring is the free ring on time and the jet coordinates

**Observation.** The standard jet model `Jₙ` is the ring of smooth functions of `t` and finitely many of the variables `qᵢ⁽ᵏ⁾`. `FreeSmoothRing ι` is already the ring of smooth functions on real assignments to `ι` with finite coordinate dependence, so `ι = Unit ⊕ (Fin n × ℕ)` gives the same carrier together with its universal property.

**Interface decision.** `StandardJet ι` is `FreeSmoothRing (Option (ι × ℕ))`, with `none` for time and `some (i, k)` for `qᵢ⁽ᵏ⁾`. The partial derivatives it needs were first expected to require calculus on the free ring; M15 records why they do not.

**Proof status.** Implemented: `StandardJet.jetRing` is a `JetRing`, and it landed together with the abstract structure so that the structure has a nondegenerate instance. The universal property of the standard jet ring among jet rings is not stated. [Free rings](../ProjectAInos/SmoothAlgebra/Free.lean) · [Standard jet ring](../ProjectAInos/Mechanics/Jet/Standard.lean)

## M15. Vector fields on a free ring come from the dual numbers, without analysis

**Observation.** A vector field on the free C∞-ring should exist for every choice of values on the generators. Proving this by differentiating cylinder functions would need calculus on an infinite product and a proof that the result is again a cylinder function. Neither is necessary. The universal property of the free ring gives a morphism into its dual numbers that sends each generator `x` to `x + ε w(x)`; this morphism reduces to the identity at `ε = 0`, and by Proposition 18 its infinitesimal part is a derivation. Uniqueness is the chain rule applied to a presentation. Two coordinate vector fields commute because their commutator is a derivation that vanishes on every generator.

**Interface decision.** `FreeSmoothRing.derivation`, `derivation_ext` and `partialDerivation_comm` are stated for the free ring on any set of generators. The standard jet ring takes its `∂ₜ` and `∂ᵢ⁽ᵏ⁾` from them. The manuscript lists symmetry of second derivatives as the analytic input of the standard model; in Lean that input is used once, in the Lie-ring structure of derivations (M10), and the model itself is algebra.

**Proof status.** Proved. This construction gives vector fields with values in the ring itself. Derivations of a free ring into an arbitrary module would need the square-zero extension deferred in M09. [Derivations of free rings](../ProjectAInos/SmoothAlgebra/FreeDerivation.lean)

## M16. A jet ring has no time coordinate, and boosts need one

**Observation.** Definition 32 gives a jet ring the vector field `∂ₜ` but no element `t`. The energy, momentum and angular-momentum laws never mention time. The boost of Corollary 38 has `ξ = t u`, so the centre-of-mass integral `u · (t P − Σ m q)` cannot even be written without a time coordinate.

**Interface decision.** `JetRing` follows Definition 32 and has no time field. `conserved_boost` takes an element `τ` with `∂ₜτ = 1` and `∂ᵢ⁽ᵏ⁾τ = 0` as explicit hypotheses and proves `Dτ = 1` from them. In the standard jet ring these hold for `StandardJet.time`.

**Proof status.** Proved, with the hypotheses instantiated in the standard model (`conserved_boost_free`). [Conservation laws](../ProjectAInos/Mechanics/Jet/Conservation.lean)

## M17. The Noether identity holds for every variation

**Observation.** Proposition 37 assumes that the components `ξᵢ` have order at most zero. The identity `pr ξ(L) = Σᵢ ξᵢ Eᵢ(L) + D(Σᵢ ξᵢ pᵢ)` for a first-order Lagrangian is only the Leibniz rule and holds for every `ξ`. The order restriction matters when `pr ξ` is read as the prolongation of a point transformation; the algebra does not use it.

**Interface decision.** `prolong` is defined for arbitrary `ξ` as `Σₖ Σᵢ (Dᵏ ξᵢ) ∂ᵢ⁽ᵏ⁾`, and `prolong_eq_euler_add_totalDeriv` has no hypothesis on `ξ`. The Euler operator and `euler_totalDeriv` are likewise stated for elements of every order, which covers the second-order Euler operator of experiment E9b.

**Proof status.** Proved. That `pr ξ` commutes with `D` for evolutionary `ξ` is not stated. [Noether identity](../ProjectAInos/Mechanics/Jet/Noether.lean)

## M18. Coordinates are indexed by a finite type, and the cross product comes from Mathlib

**Observation.** The manuscript indexes coordinates by `1, …, n`. Particles in space are naturally indexed by pairs (particle, component), and re-indexing them as `Fin (3 N)` would hide the structure that angular momentum uses. Mathlib's cross product `⨯₃` is defined on `Fin 3 → R` for every commutative ring `R`, so it applies to vectors whose entries are elements of a jet ring.

**Interface decision.** `JetRing ι J` takes any index type, with `[Fintype ι]` where sums occur. Angular momentum uses `ι = κ × Fin 3`: the variation is `n ⨯₃ qₐ`, the kinetic term vanishes by `(n × v) · v = 0`, and `axis_cross_dotProduct` rewrites the charge as `n · (q × p)`. Mathlib provides the Lie ring of the cross product only as a definition, `Cross.lieRing`, because `Fin 3 → R` is already a ring under componentwise multiplication and carries the commutator bracket. This is the same clash as in M13, so the rigid-body stage should use `⨯₃` directly and not bracket notation.

**Proof status.** `conserved_angularMomentum` and `conserved_linear` are proved. The rigid body of M24 uses `⨯₃` in the same way. The `so(3)` momentum map of the row for §9 is not formalized.

## M19. Conservation in a jet ring is ideal membership, not constancy along a path

**Observation.** In a jet ring, "conserved" means that the total derivative lies in the Euler–Lagrange ideal. This is a statement about elements of a ring. It becomes "constant along every solution" only after a path is prolonged to a morphism out of the jet ring that kills the Euler–Lagrange ideal and turns `D` into `d/dt`. For a first-order Lagrangian the energy identity involves the second derivative of the path, so that bridge needs at least `C²` paths, and the full ideal needs all derivatives.

**Interface decision.** `Conserved L F` is defined as `D F ∈ eulerLagrangeIdeal L`, and the ideal is proved stable under `D`. Nothing in `Mechanics/Jet` mentions a path. The real analytic statements (`Mechanics.stationary_iff_eulerLagrange` and its relatives) remain separate.

**Proof status.** The algebraic laws are proved, and the ledger rows for §§6–9 are *proved* for their stated main target, the jet-ring identity. The bridge to smooth trajectories is M29. [Euler operators](../ProjectAInos/Mechanics/Jet/Euler.lean)

## M20. Bilinearity and the Leibniz rule of a Poisson bracket are theorems

**Observation.** Definition 20 asks for an `ℝ`-bilinear bracket with antisymmetry (P1), the Jacobi identity (P2) and the chain rule in the first argument (P3). Bilinearity is redundant. The chain rule applied to the addition and multiplication operations gives additivity and the Leibniz rule in the first argument, applied to a constant operation it gives `{r, h} = 0`, and antisymmetry transports all three to the second argument. This is the same reduction as for derivations (M08), because (P3) says that `{·, h}` is a C∞-derivation.

**Interface decision.** `AlmostPoissonStructure` has the fields `bracket`, `antisymm` and `chain`; `PoissonStructure` adds `jacobi`. The lemmas `bracket_add_left`, `bracket_mul_left`, `bracket_algebraMap_left`, `bracket_smul_left` and their right-hand versions are derived through `hamiltonian h : SmoothDerivation P P`.

**Proof status.** Proved. `checks/PoissonAPI.lean` pins the derived laws. [Poisson structures](../ProjectAInos/SmoothAlgebra/Poisson/Basic.lean)

## M21. On a free ring the Jacobi identity is a condition on generators

**Observation.** The manuscript marks the Jacobi identity of the canonical bracket and of a Lie–Poisson bracket as needing the symmetry of second derivatives. In Lean that input is used once and abstractly. For any almost-Poisson structure the Jacobiator `{{f, g}, h} + {{g, h}, f} + {{h, f}, g}` satisfies the chain rule in its first argument: the second-order terms of the three summands cancel by `partialDeriv_comm`. It is cyclic, so it is a derivation in each argument, and on a free ring it vanishes as soon as it vanishes on generators.

**Interface decision.** `jacobiator_op` is stated for every C∞-ring. `FreeSmoothRing.jacobiator_eq_zero` is stated for every set of generators, and `poissonOfCoordinates` takes the Jacobi identity on generators as its only hypothesis beyond skewness. For the canonical bracket the generator brackets are constants, so the hypothesis is `0 + 0 + 0 = 0` (`poissonOfConstants`); for the rigid body it is 27 cases decided by `fin_cases`.

**Proof status.** Proved. A general Lie–Poisson structure for a Lie algebra with a finite basis is not stated; `poissonOfCoordinates` reduces it to the Jacobi identity of the structure constants.

## M22. The coordinate bracket is defined for vector fields on any ring, then specialized

**Observation.** The first definition of the bracket `Σ_{a,b} ∂_a f ∂_b g w a b` was written directly on `FreeSmoothRing κ`. Its chain-rule proof timed out in definitional unfolding (`isDefEq`). The likely cause is that the free ring is a subalgebra of a function algebra, so each `ring` or `simp` step has to see its ring instances through that subtype; this was not profiled further. The same formula for a finite family of vector fields `D a` on an arbitrary C∞-ring and a skew family `w a b` elaborates at once, because the ring is a variable.

**Interface decision.** `AlmostPoissonStructure.ofDerivations D w hw` lives in the abstract file, and `FreeSmoothRing.almostPoisson w hw` is its instance with `D = partialDerivation`. The abstract form is also the mathematically natural one: it is the bracket of the bivector `Σ w a b · D_a ∧ D_b`. The same pattern was used for `FreeSmoothRing.derivation` (M15) and is the default for later constructions on free rings: prove over a variable ring, specialize last.

**Proof status.** Proved. `Poisson/Free.lean` compiles in about ten seconds.

## M23. Reduction, Hamilton–Jacobi and Maupertuis are statements about ideals

**Observation.** Proposition 28 concludes that `N(I)/I` is a Poisson C∞-ring, which needs the quotient of a C∞-ring by an ordinary ideal and therefore Hadamard's lemma. Every other part of the proposition is free of quotients: the normalizer is a subalgebra closed under the bracket and under smooth operations, it contains a coisotropic ideal, and the bracket of two normalizer elements changes by an element of `I` when the arguments change by elements of `I`. Propositions 54 and 55 are of the same kind. Proposition 55 assumes that `u` is a unit, but the congruence `{g, H'} ≡ u {g, H}` modulo `(H − E)` holds for every `u`; the unit is needed only to conclude that the two ideals are equal, so that the roles of `H` and `H'` can be exchanged.

**Interface decision.** `normalizer I` is a `Subalgebra ℝ P`, with `bracket_mem_normalizer`, `op_mem_normalizer` and `bracket_sub_bracket_mem` as separate theorems. `hamiltonJacobi` and `maupertuis` are stated as ideal memberships, and `maupertuis` has no unit hypothesis. `bracket_mul_sub_algebraMap` records the exact identity behind it.

**Proof status.** Proved, except the quotient ring. Once quotients by ideals exist, `bracket_sub_bracket_mem` is the well-definedness statement they need. The row for §44 stays at *evidence* and the row for §47 at *informal*, because the Jacobi metric, the variational statement and Jacobi's theorem on complete integrals are not formalized. [Poisson ideals](../ProjectAInos/SmoothAlgebra/Poisson/Ideal.lean)

## M24. The rigid body: sign, the gradient form, and total inverses

**Observation.** With `X_h = {·, h}` and `{q, p} = 1`, the body-frame angular momentum has `{Lᵢ, Lⱼ} = −εᵢⱼₖ Lₖ`, the opposite sign to the space-frame components `q × p`. With this sign the equation of motion for any Hamiltonian is `{Lₐ, H} = (L × ∇H)ₐ`, and the whole bracket is `{f, g} = −L · (∇f × ∇g)`. Euler's equations and the Casimir property of `|L|²` are then instances of two identities of the cross product, `∇H = Ω` and `L · (L × v) = 0`. The kinetic energy `Σ Lᵢ² / 2Iᵢ` divides by the moments of inertia. Lean's real inverse is total, and the identities hold for every `I : Fin 3 → ℝ`, including `I i = 0`, where the corresponding term of the energy is zero.

**Interface decision.** `RigidBody.structureMatrix` is the explicit skew matrix, so that the generator brackets reduce by `rfl` and case analysis. The general statements `poisson_bracket` and `poisson_L_bracket` are in vector form with `⨯₃`, and Euler's equations are stated both in vector form and by components. No positivity or nonvanishing of `I` is assumed, since no proof uses it. `L_ne_zero` evaluates at the point `(1, 1, 1)` through `FreeSmoothRing.lift` to show that the bracket is not the zero bracket.

**Proof status.** Proved: the row for §36 is *proved*. The heavy top is M27. The quotient by `|L|² − r²`, stability of the principal rotations (§37) and the link to the Lagrangian on `T(SO(3))` are not formalized. [Rigid body](../ProjectAInos/Mechanics/Poisson/RigidBody.lean)

## M25. The canonical phase space is all of ℝ²ⁿ

**Observation.** Example 22(a) takes `P = C∞(U × ℝⁿ)` for an open `U ⊆ ℝⁿ`. `PhaseSpace ι` is the free ring, which is the case `U = ℝⁿ`. Kepler's problem lives on `ℝ³ ∖ {0}`, where `1/r` is a smooth function; in the free ring `r` is not invertible and `1/r` does not exist. A bracket on an open set needs the bracket to extend to a localization: a derivation extends uniquely to a C∞-localization, so the extension should exist, but it is not proved.

**Interface decision.** None yet. The models of this stage are polynomial or globally smooth, so they need no localization. The Kepler stage has two options: extend a Poisson structure along `GeneralLocalization`, or state the Runge–Lenz identities with an element `ρ` and the hypothesis `ρ * r = 1` in an arbitrary Poisson C∞-ring.

**Proof status.** Not implemented. This records a constraint for the model stage of issue #78. [Canonical bracket](../ProjectAInos/SmoothAlgebra/Poisson/Canonical.lean)

## M26. A momentum map is a Poisson morphism out of a free ring, checked on generators

**Observation.** Definition 57 asks for a linear map `ξ ↦ μ_ξ` with `X_{μ_ξ} = ξ_M` and `{μ_ξ, μ_η} = μ_[ξ, η]`, and remarks that the second condition says that the induced morphism `C∞(𝔤*) → P` is a Poisson morphism. In Lean the remark is the usable statement. `C∞(𝔤*)` is a free C∞-ring, a morphism out of it is a choice of images of the generators, and both `φ {f, g}` and `{φ f, φ g}` satisfy the chain rule in each argument, so the morphism is Poisson as soon as it preserves the brackets of generators. For rotations of one particle the generator condition is `{Mₐ, M_b} = εₐ_bc M_c`. The rigid-body ring uses the body-frame sign `{Lₐ, L_b} = −εₐ_bc L_c`, so the Poisson morphism is `L ↦ −M`.

**Interface decision.** `IsPoissonHom π ρ φ` is a predicate on morphisms of C∞-rings between almost-Poisson structures, with `FreeSmoothRing.isPoissonHom_of_generators` as the criterion. `AngularMomentum.momentumMap` is `FreeSmoothRing.lift fun a => -M a`. No Lie algebra, group action or infinitesimal action is defined; the first condition of Definition 57 is not stated.

**Proof status.** `isPoissonHom_momentumMap` is proved. Momentum maps of a general Lie algebra, and the identification of `X_{Mₐ}` with the infinitesimal rotation, are not formalized. `SmoothRingHom` gained `map_sum`, `map_neg` and `map_sub`; they were first stated next to their first use and now live in the morphism file. [Poisson morphisms](../ProjectAInos/SmoothAlgebra/Poisson/Hom.lean) · [Angular momentum](../ProjectAInos/Mechanics/Poisson/AngularMomentum.lean)

## M27. The heavy top: one matrix for the structure constants, vector form for the statements

**Observation.** The brackets of the heavy top, of the rigid body and of `q × p` all have the form `± Σ_c εₐ_bc x_c`. Writing the matrix once, as `epsilon x`, lets the generator brackets reduce by evaluation of a matrix literal, and the Jacobi identity on the six generators is 216 cases closed by one `simp` call in a few seconds. The matrix form is wrong for stating results: `Σ_b ∂_b H · (−εₐ_bc L_c)` and `(L × ∇H)ₐ` agree only after renaming the summation index, so a termwise comparison fails and the equations of motion are proved by expanding the three components.

**Interface decision.** `Mechanics.epsilon` with `epsilon_skew` and `sum_epsilon_mul` is a small shared module. The statements are in vector form with `⨯₃` and `⬝ᵥ`: `poisson_L_bracket`, `poisson_Γ_bracket` and `poisson_bracket` for any Hamiltonian, then the specialization to `Σ Lᵢ² / 2Iᵢ + k Γ · χ`. The Casimirs `|Γ|²` and `L · Γ` are proved for every second argument, from the general equations of motion and the triple-product identities.

**Proof status.** Proved, including the Jacobi identity for all elements; experiment E6f tested it on polynomials. The row for §34 stays *informal* because the equation for the momentum, general torques and the link to the Lagrangian on `T(SO(3))` are missing. [Heavy top](../ProjectAInos/Mechanics/Poisson/HeavyTop.lean)

## M28. In a free ring `simp` does not normalize signs, and `ring` does

**Observation.** In goals over `FreeSmoothRing κ`, `simp` leaves terms such as `x * -1` and `-(x * -1)` unsimplified, and reports `mul_neg` and `mul_one` as unused. `ring` closes the same goals. The same proofs over a variable commutative ring need no `ring` step. The cause was not isolated; the ring structure of the free ring comes from a subalgebra of a function algebra, and `simp` lemmas about negation may fail to unify their instance arguments with it.

**Interface decision.** Case-analysis proofs in the model files end with `simp [...] <;> ring`. General statements are proved over a variable ring where possible (M22).

**Proof status.** A proof-engineering observation, with no mathematical content. It is recorded because it recurred in the canonical bracket, the angular momentum and the heavy top.

## M29. Prolongation turns ideal membership into constancy along a path

**Observation.** The bridge announced in M19 needs no new structure. The ring of smooth functions of time is the C∞-ring `SmoothOperation 1`, and `d/dt` is its coordinate vector field. A smooth path is a tuple of elements of that ring, and the universal property of the free ring sends the time coordinate to `t` and `qᵢ⁽ᵏ⁾` to the `k`-th derivative of `γᵢ`. That this morphism turns `D` into `d/dt` is checked on generators only: both sides satisfy the chain rule, so a presentation of an arbitrary element reduces the claim to `D t = 1` and `D qᵢ⁽ᵏ⁾ = qᵢ⁽ᵏ⁺¹⁾`. This is the third use of the same argument, after M21 and M26; it is a uniqueness statement for derivations along a morphism, proved without defining them (M12). Calculus enters once, in the statement that a smooth function on the line with zero derivative is constant.

**Interface decision.** `StandardJet.IsSolution L γ` is defined by the prolongation: it annihilates each `Eᵢ(L)`. With this definition the Euler–Lagrange ideal is annihilated by induction on the span, using `prolongation_totalDeriv` for the higher total derivatives, and `prolongation_eq_of_conserved` follows. For natural Lagrangians `isSolution_naturalLagrangian_iff` unfolds the definition to Newton's equations, so the hypothesis of `energy_eq_of_isSolution` is a differential equation and not a statement about ideals. Paths are smooth and defined on all of `ℝ`, which is what a morphism of C∞-rings out of the jet ring requires.

**Proof status.** Proved, with uniform motion as a solution of the free equations. Two things are open. The real analytic model treats `C²` paths on a compact interval and defines solutions by stationarity of the action; no theorem relates `IsSolution` to `Mechanics.Stationary`. And a smooth path on an open interval, or one that leaves a region where the Lagrangian is defined, is not covered. [Prolongation](../ProjectAInos/Mechanics/Jet/Prolongation.lean)

## M30. The mass is a central term, and the boost generator carries time as a parameter

**Observation.** On the phase space of one particle, `{Kₐ, p_b} = m δₐ_b` for `K = m q − t p`: boosts and translations commute as vector fields, and their generators commute only up to the constant `m`. This is the central extension of the Galilei algebra, and it is visible only on the Hamiltonian side; the jet-ring statement `conserved_boost` shows the same constant as the total derivative that the boost adds to the Lagrangian. The phase space has no time coordinate (compare M16), so `t` is a real parameter of `K`. Conservation of the centre-of-mass integral is then two statements, `{K_t, H₀} = p` and `K_t − K_s = −(t − s) p`, which cancel. The bracket `{K, H₀} = p` needs `m ≠ 0`, the only place in the model files where a nonvanishing hypothesis is used, because it cancels `m · m⁻¹`.

**Interface decision.** `Galilei.K m t` takes the time as an argument. The relations are stated for one particle in space, reusing `AngularMomentum.M` and `epsilon`. Definition 23's time-dependent systems, with `ḟ = ∂ₜf + {f, H}` on a phase space extended by time, are not introduced for this single use.

**Proof status.** Proved for one particle. The Galilei algebra acting on the jet ring, several particles, and the invariance of the Euler–Lagrange ideal under finite boosts (the main target of the row for §3) are not formalized. [Galilei algebra](../ProjectAInos/Mechanics/Poisson/Galilei.lean)

## M31. Homogeneity enters the virial identity as Euler's relation

**Observation.** `{Σ qᵢ pᵢ, H} = Σᵢ pᵢ ∂H/∂pᵢ − Σᵢ qᵢ ∂H/∂qᵢ` holds for every Hamiltonian; it is the Leibniz rule and Hamilton's equations. Homogeneity of degree `k` is used only through Euler's relation `Σᵢ qᵢ ∂U/∂qᵢ = k U`, which is a statement about an element of the ring and needs no notion of a homogeneous function, no scaling action and no real powers. The potentials of interest in Landau–Lifshitz §10 include `r^k` with negative or fractional `k`, which are not elements of the free ring (M25).

**Interface decision.** `PhaseSpace.virial` takes Euler's relation and independence of the momenta as hypotheses on `U`; the kinetic energy satisfies its own relation as a theorem. `virial_oscillator` shows that the hypotheses are satisfiable with `k = 2`.

**Proof status.** Proved. The row for §10 stays *evidence*: scaling as a symmetry of the Euler–Lagrange ideal and the virial theorem for time averages are missing. [Virial identity](../ProjectAInos/Mechanics/Poisson/Virial.lean)
