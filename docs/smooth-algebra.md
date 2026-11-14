# Shared Mathematical Foundation: Smooth Algebra

This is the first shared algebraic stage of [issue #7](https://github.com/MGYamada/ProjectAInos/issues/7).
It provides C∞-rings, morphisms, and concrete smooth-function models for
[smooth geometry](smooth-geometry.md), mechanics, and classical field theory.

All declarations are in `ProjectAInos.SmoothAlgebra`. The original dependency
order is `Operations` → `Basic` → `Hom` → `Models` → `Differential`.
`Category` bundles smooth rings and their morphisms. `Congruence` constructs
quotients by smooth congruences; `LocalInverse` and `Localization` construct
localization at real points and prove its C∞ universal property. The library
also constructs free rings on arbitrary sets, general C∞ localizations,
and limits. `SmoothFunctions` provides the smooth-function algebras on
manifolds used by the geometric layer. `PartialDerivative`, `DualNumber` and
`Derivation` add the differential algebra that starts the
[mechanics plan](cinfty-mechanics.md): `Operations` → `PartialDerivative`, then
`Models` and `PartialDerivative` → `DualNumber` → `Derivation`. The library root
imports all these modules. This layer has no dependency on `Variational`,
`Mechanics`, or a particular physical theory.

## Smooth operations and real-algebra compatibility

`SmoothOperation n` is an abbreviation for Mathlib's `ContMDiffMap` type of
smooth maps `(Fin n → ℝ) → ℝ`. Regularity is `∞` (all finite derivative orders),
not `ω` (analytic). This reuses the existing pointwise commutative ring and real
algebra instances. `ofContDiff` accepts an ordinary `ContDiff ℝ ∞` certificate.

`SmoothOperation.comp f g` substitutes a finite tuple of smooth functions into
`f`. Projections, constants, substitution, and equality are all defined using
actual smooth functions. In particular, equality of operation symbols is
extensional, and their smoothness certificates are not additional algebraic data.

On an existing commutative real algebra `A`, `SmoothRing A` provides

```lean
op : {n : ℕ} → SmoothOperation n → (Fin n → A) → A
```

Writing this interpretation as Φ, the defining laws are

\[
\Phi_{\pi_i}(a)=a_i,\qquad
\Phi_{f\circ(g_1,\ldots,g_n)}(a)
=\Phi_f\bigl(\Phi_{g_1}(a),\ldots,\Phi_{g_n}(a)\bigr).
\]

The nullary constant with value `r` must interpret as `algebraMap ℝ A r`.
The binary addition and multiplication operations must agree with the existing
ring operations. General constant operations, zero, one, negation, subtraction,
and real scalar multiplication then follow as theorems. No topology or
nontriviality is imposed on `A`. A real algebra is not automatically given a
`SmoothRing` instance: interpreting all smooth operations is additional structure.

This is the finite-operation presentation of C∞-rings from
[Joyce, *Algebraic Geometry over C∞-rings*, §2.1–2.2](https://arxiv.org/pdf/1001.0023),
expressed compatibly with Mathlib's real-algebra hierarchy. Rather than replacing
an existing ring instance, the compatibility fields identify its arithmetic
with the corresponding smooth operations. There is no claim here that arbitrary
real-algebra homomorphisms preserve smooth operations.

Arity zero is included throughout: `Fin 0 → A` has one element, and there are
no zero-arity projections. The substitution law applies even when either arity
is zero. `SmoothRing.op_const` derives all constant interpretations from the
nullary case. The exponential operation is an explicit nonpolynomial example;
`SmoothRing.exp_add` follows from the ordinary real exponential identity and
the substitution laws.

## Morphisms and concrete models

`SmoothRingHom A B` consists of a function preserving every smooth operation,
including nullary constants. Its `toAlgHom` is constructed by deriving
preservation of constants, addition, and multiplication. Identity, composition,
extensionality, and compatibility of `toAlgHom` with identity and composition
are proved. Smooth-ring morphisms also preserve the exponential operation.

The concrete instances include:

- On ℝ, `op f a = f a`.
- On `SmoothOperation m = C∞(ℝᵐ)`, `op f g = SmoothOperation.comp f g`, so
  `(op f g)(x) = f (fun i => g i x)`.
- On any dependent product of C∞-rings, operations are pointwise. The empty
  product gives the zero ring used by the empty C∞ scheme.
- On the smooth real functions on a manifold, operations are pointwise smooth
  substitution; evaluation and pullback are C∞ morphisms.

For any C∞-ring `A` and tuple `a : Fin n → A`, `SmoothOperation.lift a`
sends a smooth function `f` to `op f a`. It is a smooth-ring morphism and sends
the coordinate projection `i` to `a i`. The theorem `existsUnique_lift` proves
that it is the unique morphism with those coordinate values. Thus `C∞(ℝⁿ)` is
free on its `n` coordinate functions, including the empty family when `n = 0`.

`eval x` specializes this construction to a real point. `pullback g` specializes
it to a smooth map represented by its component functions
`g : Fin n → SmoothOperation m`. It sends `f` to `f ∘ g`; pullback reverses the
composition of the underlying maps. Evaluation after pullback equals evaluation
at the image point.

## Free rings, general localization, and limits

`FreeSmoothRing ι` consists of smooth cylinder functions on real assignments
to `ι`, with finite coordinate dependence. Interpretation is independent of
the chosen finite presentation in every C∞-ring. This gives a unique smooth
lift of any assignment of the generators, including into higher universes.
The function representation applies to the free ring; it does not identify
arbitrary C∞-rings with functions on their real points.

`SmoothLocalization S` is a smooth congruence quotient of the free ring on
`A ⊕ S`. The relations preserve the original smooth operations and make the
generator corresponding to each `s : S` an inverse of `s`. Its existence
and uniqueness theorem supplies the localization universal property in
C∞-rings. This works for arbitrary sets, including the empty set and sets
containing zero. `LocalizationComparison` proves that localization at a
surviving real point recovers the original point-local ring.

`Limits` constructs compatible families in products with pointwise smooth
operations and proves their limiting property. The forgetful functor to
commutative rings preserves these limits, so the geometric layer can pass
between C∞-valued sheaves and their underlying ring-valued sheaves.

## Partial derivatives, dual numbers, and derivations

`SmoothOperation.partialDeriv i f` is the `i`-th partial derivative of a smooth
operation, again a smooth operation of the same arity. The Fréchet derivative is
recovered as `fderiv ℝ f x v = ∑ i, v i * partialDeriv i f x`. The chain rule
`partialDeriv_comp` is an identity between operations, and `partialDeriv_comm`
states that second partial derivatives commute. These are facts about the
concrete operations and are proved from Mathlib's calculus.

For every C∞-ring `A`, Mathlib's dual numbers `DualNumber A` (`A[ε]`) carry the
smooth operations

$$
\Phi_f(c+\varepsilon b)=\Phi_f(c)+\varepsilon\sum_i\Phi_{\partial_i f}(c)\,b_i .
$$

The ring and real-algebra structures are Mathlib's. The substitution law of this
`SmoothRing` instance is exactly `partialDeriv_comp`. The projection
`DualNumber.fstHom` (setting `ε = 0`) and the zero section `DualNumber.inlHom`
are morphisms of C∞-rings. `DualNumber.exp_inl_add_inr` checks a nonpolynomial
operation: `exp (a + ε b) = exp a + ε (exp a · b)`.

A `SmoothDerivation A M` is a map `d : A → M` into an `A`-module with the single
law

$$
d\,\Phi_f(a_1,\dots,a_n)=\sum_i\Phi_{\partial_i f}(a_1,\dots,a_n)\cdot d a_i .
$$

Additivity, the Leibniz rule, vanishing on real constants and real linearity are
theorems, so `toDerivation` gives Mathlib's `Derivation ℝ A M` whenever `M` has a
compatible real action. `map_exp` is a consequence that an ordinary derivation of
the underlying algebra need not satisfy. Derivations form a module over `A`.
Vector fields `SmoothDerivation A A` are closed under the commutator and form a
Lie ring; the proof uses `partialDeriv_comm`. `equivInfinitesimalAut` identifies
them with the morphisms `A → A[ε]` that reduce to the identity at `ε = 0`.

On the free ring `SmoothOperation n` the coordinate fields `partialDerivation i`
are derivations, every derivation satisfies
`d f = ∑ i, partialDeriv i f • d (proj i)`, and `equivCoordinates` identifies
derivations into any module with `n`-tuples of values on the coordinates. The
regression `lie_partialDerivation_proj_smul` proves `[∂ᵢ, xⱼ ∂ₖ] = δᵢⱼ ∂ₖ`, so
the bracket is not trivial.

On the free ring `FreeSmoothRing ι` over any set of generators,
`FreeSmoothRing.derivation w` is the vector field with prescribed values `w` on
the generators, and `derivation_ext` shows that a derivation is determined by
those values. Existence uses the universal property of the free ring to build a
morphism into its dual numbers and reads off the infinitesimal part; no calculus
on an infinite product is needed. Coordinate vector fields commute because their
commutator is a derivation that vanishes on every generator. The standard jet
ring of the [mechanics guide](mechanics.md#jet-rings-and-conservation-laws) is
built from these. The first stage is tracked in [issue #74](https://github.com/MGYamada/ProjectAInos/issues/74).

## Points and tangent vectors

`Point A` is the type of morphisms `A → ℝ` and `TangentPoint A` the type of
morphisms `A → ℝ[ε]`. A morphism `f : A → B` acts on them in the opposite
direction (`Point.map`, `TangentPoint.map`), and a pair of inverse morphisms
gives a bijection of the tangent vectors (`TangentPoint.congr`): a change of
co-ordinates.

The value of an element `s` of a free ring at the point `a` is the value of
the function `s` at `a` (`FreeSmoothRing.lift_real`), so an element is
determined by its values at the points (`FreeSmoothRing.ext_lift`).

For the free ring on `ι`:

- `FreeSmoothRing.pointEquiv`: the points are the families `a : ι → ℝ`.
- `FreeSmoothRing.tangentPointEquiv`: the tangent vectors are the pairs
  `(a, v)`. `tangentPoint a v` is the morphism `xᵢ ↦ aᵢ + ε vᵢ`.
- `fst_tangentPoint`, `snd_tangentPoint`: for a finite index type,
  `s(a + εv) = s(a) + ε Σᵢ (∂ᵢ s)(a) vᵢ`.
- `tangentPoint_map_lift`: the substitution `xᵢ ↦ yᵢ` takes `(a, v)` to
  `(y(a), J v)` with `Jᵢⱼ = (∂ⱼ yᵢ)(a)`.

For a family of relations `r` on `A`, `SmoothRingCon.generateHomEquiv r`
identifies the morphisms out of the quotient by the generated congruence with
the morphisms out of `A` that respect `r`. `FreeSmoothRing.Presented e` is the
ring presented by the generators `ι` and the equations `eₖ = 0`.

- `presentedPointEquiv`: its points are the families `a` with `eₖ(a) = 0`.
- `presentedTangentPointEquiv`: its tangent vectors are the pairs `(a, v)` with
  `eₖ(a) = 0` and `Σᵢ (∂ᵢ eₖ)(a) vᵢ = 0`.
- `circleTangentPointEquiv`: for `x₀² + x₁² − 1 = 0` they are the pairs with
  `|a|² = 1` and `a · v = 0`.

The quotient is by the C∞-congruence generated by the equations. That this is
the congruence of the ideal generated by the `eₖ`, which is Hadamard's lemma,
is not proved; the statements above do not need it.

## Poisson structures

A `PoissonStructure P` on a C∞-ring is a bracket with three laws: antisymmetry,
the chain rule in the first argument,
`{Φ_f(c), h} = Σᵢ Φ_{∂ᵢf}(c) {cᵢ, h}`, and the Jacobi identity. Additivity,
the Leibniz rule and vanishing on constants in both arguments are theorems. The
bracket is a field of a structure. It is not Mathlib's `Bracket` class, because
every ring already carries the commutator bracket, which is zero on a
commutative ring. An `AlmostPoissonStructure` omits the Jacobi identity.

`hamiltonian h` is the vector field `X_h = {·, h}`. The Jacobi identity is
equivalent to `{{f, g}, h} = {{f, h}, g} + {f, {g, h}}` (`bracket_bracket`), so
`X_h` is a derivation of the bracket, and `hamiltonian_bracket` gives
`X_{f, g} = −[X_f, X_g]`. `IsIntegral H f` means `{f, H} = 0`. Integrals of the
motion are closed under the bracket (Poisson's theorem, `IsIntegral.bracket`),
under every smooth operation (`IsIntegral.op`) and form the real subalgebra
`integrals H`. `isIntegral_iff_hamiltonian_eq_zero` is Noether's theorem in
Hamiltonian form.

For an ideal `I`, `normalizer I` is `{f | {f, I} ⊆ I}`. It is a real subalgebra
closed under the bracket and under every smooth operation, a coisotropic ideal
lies in it, and `bracket_sub_bracket_mem` proves that the bracket of the
normalizer is well defined modulo `I`. `hamiltonJacobi` proves `{I, H} ⊆ I` for
a coisotropic ideal containing `H − E`. `maupertuis` proves
`{g, H'} ≡ u {g, H}` modulo `(H − E)` when `H' − E' = u (H − E)`. These are
statements about ideals. The quotient ring `N(I)/I` is not constructed, because
quotients of C∞-rings by ordinary ideals are not formalized.

The Jacobiator of an almost-Poisson structure satisfies the chain rule in each
argument (`jacobiator_op`); the second-order terms cancel by
`partialDeriv_comm`. Hence on a free C∞-ring the Jacobi identity holds if it
holds on generators (`FreeSmoothRing.jacobiator_eq_zero`).
`AlmostPoissonStructure.ofDerivations D w` is the bracket
`Σ_{a,b} D_a f · D_b g · w a b` of a finite family of vector fields and a skew
family `w`. On the free ring over a finite type with the coordinate vector
fields this is `FreeSmoothRing.almostPoisson w`, with `{x_a, x_b} = w a b`.
`poissonOfCoordinates` requires the Jacobi identity on generators only, and
`poissonOfConstants` covers generator brackets with vanishing partial
derivatives.

`PhaseSpace ι` is the free C∞-ring on positions `q i` and momenta `p i`, and
`PhaseSpace.canonical ι` is its canonical Poisson structure:
`{qᵢ, pⱼ} = δᵢⱼ`, `{qᵢ, qⱼ} = {pᵢ, pⱼ} = 0`. `canonical_bracket` gives
`{f, g} = Σᵢ (∂f/∂qᵢ ∂g/∂pᵢ − ∂f/∂pᵢ ∂g/∂qᵢ)`, and `canonical_q_bracket` and
`canonical_p_bracket` are Hamilton's equations `{qᵢ, H} = ∂H/∂pᵢ` and
`{pᵢ, H} = −∂H/∂qᵢ`.

`IsPoissonHom π ρ φ` says that a morphism of C∞-rings preserves the bracket.
Both sides satisfy the chain rule in each argument, so a morphism out of a free
C∞-ring is a Poisson morphism if it preserves the brackets of the generators
(`FreeSmoothRing.isPoissonHom_of_generators`). The rigid body, the angular
momentum and the heavy top are in the
[mechanics guide](mechanics.md#poisson-models). This stage is tracked in
[issue #78](https://github.com/MGYamada/ProjectAInos/issues/78).

## Proof map and verification

| Module | Main checked results |
| --- | --- |
| [Operations](../ProjectAInos/SmoothAlgebra/Operations.lean) | `proj_comp`, `comp_proj`, `comp_assoc`, `exponential_addition` |
| [Basic](../ProjectAInos/SmoothAlgebra/Basic.lean) | `op_const`, `op_add`, `op_mul`, `op_neg`, `op_sub`, `op_smul`, `op_sum`, `exp_add` |
| [Hom](../ProjectAInos/SmoothAlgebra/Hom.lean) | `toAlgHom`, identity/composition laws, `map_neg`, `map_sub`, `map_sum`, `map_exp` |
| [Models](../ProjectAInos/SmoothAlgebra/Models.lean) | Real and function-ring instances; `hom_ext`, `lift_unique`, `existsUnique_lift`, `pullback_comp`, `eval_comp_pullback` |
| [Differential](../ProjectAInos/SmoothAlgebra/Differential.lean) | `directionalEvaluation_op`, the chain rule for every finite smooth operation on the concrete model; `directionalEvaluation_eq_sum` |
| [PartialDerivative](../ProjectAInos/SmoothAlgebra/PartialDerivative.lean) | `partialDeriv`, `fderiv_apply_eq_sum_partialDeriv`, `partialDeriv_mul`, `partialDeriv_comp`, `partialDeriv_comm`, `partialDeriv_exponential` |
| [DualNumber](../ProjectAInos/SmoothAlgebra/DualNumber.lean) | `SmoothRing (DualNumber A)`, `fst_op`, `snd_op`, `fstHom`, `inlHom`, `exp_inl_add_inr` |
| [FreeDerivation](../ProjectAInos/SmoothAlgebra/FreeDerivation.lean) | `FreeSmoothRing.derivation`, `derivation_generator`, `derivation_ext`, `map_derivation_eq`, `derivationEquiv`, `partialDerivation_comm`, `exists_finset_partialDerivation_eq_zero` |
| [FreeChainRule](../ProjectAInos/SmoothAlgebra/FreeChainRule.lean) | `FreeSmoothRing.derivation_lift`, `FreeSmoothRing.derivation_lift_mul`: the chain rule `E (s(y)) = Σₐ (∂ₐ s)(y) • E (yₐ)` for a substitution out of a free ring on finitely many generators. `FreeSmoothRing.apply_eq_sum_partialDerivation`, `FreeSmoothRing.apply_eq_zero_of_partialDerivation_eq_zero`: on any free ring a vector field is `Σₐ (∂ₐ s) E(xₐ)`, summed over the generators of a presentation of `s` |
| [Point](../ProjectAInos/SmoothAlgebra/Point.lean) | `Point`, `TangentPoint`, `TangentPoint.congr`, `FreeSmoothRing.pointEquiv`, `FreeSmoothRing.lift_real`, `FreeSmoothRing.ext_lift`, `FreeSmoothRing.tangentPointEquiv`, `FreeSmoothRing.fst_tangentPoint`, `FreeSmoothRing.snd_tangentPoint`, `FreeSmoothRing.tangentPoint_map_lift`, `SmoothRingCon.generateHomEquiv`, `FreeSmoothRing.Presented`, `FreeSmoothRing.presentedPointEquiv`, `FreeSmoothRing.presentedTangentPointEquiv`, `FreeSmoothRing.circleTangentPointEquiv` |
| [Poisson/Basic](../ProjectAInos/SmoothAlgebra/Poisson/Basic.lean) | `AlmostPoissonStructure`, `PoissonStructure`, `hamiltonian`, `bracket_mul_left`, `bracket_op_op`, `jacobiator_op`, `ofDerivations`, `bracket_bracket`, `hamiltonian_bracket`, `IsIntegral.bracket`, `IsIntegral.op`, `integrals`, `isIntegral_iff_hamiltonian_eq_zero` |
| [Poisson/Ideal](../ProjectAInos/SmoothAlgebra/Poisson/Ideal.lean) | `IsPoissonIdeal`, `IsCoisotropic`, `isPoissonIdeal_span_singleton`, `normalizer`, `bracket_mem_normalizer`, `op_mem_normalizer`, `bracket_sub_bracket_mem`, `hamiltonJacobi`, `maupertuis` |
| [Poisson/Free](../ProjectAInos/SmoothAlgebra/Poisson/Free.lean) | `jacobiator_eq_zero`, `almostPoisson`, `almostPoisson_bracket_generator`, `almostPoisson_bracket_eq_sum_left`, `poissonOfCoordinates`, `poissonOfConstants` |
| [Poisson/Canonical](../ProjectAInos/SmoothAlgebra/Poisson/Canonical.lean) | `PhaseSpace`, `canonical`, `canonical_q_p`, `canonical_bracket`, `canonical_q_bracket`, `canonical_p_bracket`, `canonical_hamiltonian_apply` |
| [Poisson/Hom](../ProjectAInos/SmoothAlgebra/Poisson/Hom.lean) | `IsPoissonHom`, `IsPoissonHom.comp`, `FreeSmoothRing.isPoissonHom_of_generators` |
| [Derivation](../ProjectAInos/SmoothAlgebra/Derivation.lean) | `SmoothDerivation`, `map_mul`, `map_exp`, `toDerivation`, module and Lie-ring instances, `sum_apply`, `commutator_chain`, `equivInfinitesimalAut`, `equivCoordinates`, `lie_partialDerivation_proj_smul` |
| [Category](../ProjectAInos/SmoothAlgebra/Category.lean) | `SmoothRingCat`, faithful forgetful functors, isomorphisms from bijective morphisms |
| [Congruence](../ProjectAInos/SmoothAlgebra/Congruence.lean) | Smooth quotients, projection, factorization, generated smooth congruences |
| [LocalInverse](../ProjectAInos/SmoothAlgebra/LocalInverse.lean) | `exists_localInverse`, a smooth inverse on the support of a cutoff |
| [Localization](../ProjectAInos/SmoothAlgebra/Localization.lean) | Point localization, `existsUnique_lift`, real residue, local-ring property, induced local maps |
| [Free](../ProjectAInos/SmoothAlgebra/Free.lean) | Free C∞-rings on arbitrary generators, presentation independence, lift and uniqueness |
| [GeneralLocalization](../ProjectAInos/SmoothAlgebra/GeneralLocalization.lean) | General C∞ localization, `existsUnique_lift`, `hom_ext`, induction on smooth expressions |
| [LocalizationComparison](../ProjectAInos/SmoothAlgebra/LocalizationComparison.lean) | Point-local ring isomorphism after general localization |
| [Limits](../ProjectAInos/SmoothAlgebra/Limits.lean) | Compatible-family limits and preservation by the forgetful functor |
| [SmoothFunctions](../ProjectAInos/SmoothAlgebra/SmoothFunctions.lean) | Smooth operations, evaluation, and pullback on manifold function algebras |

The models module also checks dimension zero (`nullary_eq_const`), nonlinear
evaluation in dimension one (`eval_exp_square`), and a two-variable exponential
operation pulled back to four mixed coordinates (`eval_four_dimensional`). These
are Lean theorems, not symbolic or numerical evidence.

From the repository root:

```sh
lake exe cache get
lake build --wfail ProjectAInos
lake exe mk_all --check --lib ProjectAInos
lake env lean -DwarningAsError=true checks/AxiomAudit.lean
lake env lean -DwarningAsError=true checks/SmoothAlgebraAPI.lean
lake env lean -DwarningAsError=true checks/SmoothGeometryAPI.lean
git diff --check
```

The local audit inspects transitive axiom dependencies of every imported
declaration in the `ProjectAInos` namespace. Its allowlist is `propext`,
`Classical.choice`, and `Quot.sound`, matching the existing required Lean CI job.
The required Lean CI job also checks the external smooth-geometry API,
including open immersions and categorical gluing, and pins the differential
part of this layer with typed examples in `checks/SmoothAlgebraAPI.lean`. No
dependency change is needed.

## Ordinary differentials and further algebraic stages

On `C∞(ℝⁿ)`, `directionalEvaluation x v` applies the ordinary Fréchet derivative
at `x` to a vector `v`. Its chain rule expresses the derivative of smooth
substitution in terms of the values and derivatives of the substituted
functions. This connects smooth operations to the same ordinary calculus used
for local jets and first variations in the [variational guide](variational.md).

Smooth congruence quotients and general localizations now support the
[C∞ scheme construction](smooth-geometry.md). Abstract smooth derivations
satisfying the chain rule for every smooth operation, and the infinitesimal
thickening `A[ε]`, are implemented as described above, and so are Poisson
structures. Subsequent algebraic stages include quotients by arbitrary ordinary
ideals, which need Hadamard's lemma and give the reduced Poisson rings, the
universal cotangent module with its universal property, derivations along a
morphism, and comparison theorems with ordinary local jets.
