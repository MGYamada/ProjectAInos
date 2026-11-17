# Shared Mathematical Foundation: Smooth Algebra

This is the first shared algebraic stage of [issue #7](https://github.com/MGYamada/ProjectAinos/issues/7).
It provides C∞-rings, morphisms, and concrete smooth-function models for
[smooth geometry](smooth-geometry.md), mechanics, and classical field theory.

All declarations are in `ProjectAinos.SmoothAlgebra`. The original dependency
order is `Operations` → `Basic` → `Hom` → `Models` → `Differential`.
`Category` bundles smooth rings and their morphisms. `Congruence` constructs
quotients by smooth congruences; `LocalInverse` and `Localization` construct
localization at real points and prove its C∞ universal property. The library
also constructs free rings on arbitrary sets, general C∞ localizations,
and limits. `SmoothFunctions` provides the smooth-function algebras on
manifolds used by the geometric layer. `PartialDerivative`, `DualNumber` and
`Derivation` add the differential algebra that starts the
[mechanics plan](cinfty-mechanics.md): `Operations` → `PartialDerivative`, then
`Models` and `PartialDerivative` → `DualNumber` → `Derivation`.
`ParametricIntegral` → `Hadamard` → `IdealQuotient` prove Hadamard's lemma and
construct the quotient by an ordinary ideal, and `Poisson/Reduction` gives the
quotients of Poisson structures. `FormalSeries` holds the formal power series
in `q` and `p` with their Poisson bracket and the Birkhoff normal form, on top
of Mathlib's `MvPowerSeries`; it uses no C∞-ring. The library root imports all these modules. This layer has no dependency on `Variational`,
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
built from these. The first stage is tracked in [issue #74](https://github.com/MGYamada/ProjectAinos/issues/74).

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

The quotient is by the C∞-congruence generated by the equations. This is the
congruence of the ideal generated by the `eₖ`
(`FreeSmoothRing.presented_projection_eq_zero_iff`, in the next section); the
statements above do not need it.

`FreeCalculus` reads the elements of a free ring on finitely many generators as
differentiable functions on the normed space `κ → ℝ`.

- `FreeSmoothRing.contDiff_val`: an element is a smooth function.
- `FreeSmoothRing.fderiv_val_apply`: its Fréchet derivative is
  `D s(z) w = Σₐ (∂ₐ s)(z) wₐ`, with the partial derivations of the ring.
- `FreeSmoothRing.realField D`: a derivation `D` of the ring is the vector
  field `z ↦ ((D xₐ)(z))ₐ` on `κ → ℝ`. It is smooth (`contDiff_realField`), and
  `fderiv_realField_apply` gives its derivative.

`ImplicitFunction` proves the implicit function theorem on a neighbourhood
(`exists_contDiffOn_implicitFunction`): if `f : E₁ × E₂ → F` is smooth on an
open set `W` and its partial derivative in the second variable is invertible
at every point of `W`, then through each point of `W` there is an implicit
function that is smooth on an open neighbourhood. Mathlib's theorem gives
smoothness at the base point only, which for infinite order does not extend to
a neighbourhood; the implicit function of the base point agrees near each
point of its graph with the implicit function of that point.

`ImplicitFunctionReal` is the case of one real equation `Φ(s, y) = Φ(u)` in
one real unknown with one real parameter
(`exists_contDiffOn_implicitFunction_real`): the hypothesis is that the
derivative in `y`, given as a continuous function, does not vanish at `u`, and
the implicit function is smooth on an open set of parameters.

`DividedDifference` treats a smooth function `U` of one variable.
`dividedDifference U (x, y)` is `∫₀¹ U′(y + t (x − y)) dt`, with
`U(x) − U(y) = (x − y) U[x, y]` (`sub_eq_mul_dividedDifference`), and
`dividedDifference₂ U (a, b, x)` is the second divided difference, with
`U[b, x] − U[b, a] = (x − a) U[a, b, x]` (`dividedDifference_sub`). Both are
smooth in all their arguments, also where the arguments coincide. Hence, for
`a ≠ b` with `U(a) = U(b) = E`,
`E − U(x) = (x − a)(b − x) U[a, b, x]` (`sub_eq_mul_mul_dividedDifference₂`).

`LineDerivative` proves `hasFDerivAt_of_hasDerivAt_line`: if a real function
has, at every point `y` near `x` and in every direction `v`, the derivative
`ℓ(y) v` along the line `s ↦ y + s v`, and the field of linear forms `ℓ` is
continuous at `x`, then the function has the Fréchet derivative `ℓ(x)` at `x`.

## Hadamard's lemma and quotients by ideals

`ParametricIntegral` proves the interface statement (I) of the
[mechanics plan](cinfty-mechanics.md#sec:interface). For a function `f` of a
parameter `x` in a finite-dimensional space and of a real variable `t`:

- `hasFDerivAt_parametric_intervalIntegral`: if `f` is `C¹`, the derivative of
  `x ↦ ∫ₐᵇ f(x, t) dt` is the integral of the derivative of `f` in `x`.
- `contDiff_parametric_intervalIntegral`: if `f` is `Cⁿ`, so is the integral.
- `contDiff_infty_parametric_intervalIntegral_limits`: if `f` is smooth, the
  integral is smooth in `x`, `a` and `b` together.

The induction on `n` passes from `f` to its derivative in `x`, a function with
values in a space of linear maps. So the parameter space and the space of
values are in one universe.

`SmoothOperation.hadamard i f` is the operation
`gᵢ(x, y) = ∫₀¹ (∂ᵢ f)(y + t (x − y)) dt` of `2n` arguments, and
`apply_sub_apply_eq_sum_hadamard` is Hadamard's lemma, the interface statement
(H): `f(x) − f(y) = Σᵢ (xᵢ − yᵢ) gᵢ(x, y)`. It is an identity between
operations (`comp_castAdd_sub_comp_natAdd`), so it holds in every C∞-ring:
`SmoothRing.op_sub_op` is `Φ_f(a) − Φ_f(b) = Σᵢ (aᵢ − bᵢ) Φ_{gᵢ}(a, b)`.

Hence the relation `a − b ∈ I` of an ideal `I` is a C∞-congruence,
`SmoothRingCon.ofIdeal I`, and its quotient is a C∞-ring (Corollary 4 of the
plan):

- `ofIdeal_projection_eq_iff`, `ofIdeal_projection_eq_zero_iff`: two elements
  have the same class when their difference is in `I`, and the kernel of the
  projection is `I`.
- `ofIdealHomEquiv`: the morphisms out of the quotient are the morphisms that
  vanish on `I`.
- `generated_iff_sub_mem_span`,
  `FreeSmoothRing.presented_projection_eq_zero_iff`: the congruence generated
  by the equations `eₖ = 0` is the congruence of the ideal `(eₖ)`. A ring
  presented by equations is the quotient by the ideal of the equations.
- `FreeSmoothRing.hom_sub_hom_mem`: two morphisms out of a free ring that agree
  modulo `I` on the generators agree modulo `I` on every element. The
  reductions use Hadamard's lemma in this form.

The projection is surjective, so this is the only C∞-ring structure on the
quotient for which the projection is a morphism. The uniqueness is not stated
as a theorem.

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
statements about ideals. `isCoisotropic_span` and `mem_normalizer_span` reduce
the two conditions to the generators of an ideal.

The quotients are C∞-rings by the previous section, and `Poisson/Reduction`
gives them brackets:

- `ofSurjective`: a Poisson structure descends along a surjective morphism when
  the bracket respects its fibres.
- `quotient I hI`: the quotient by a Poisson ideal is a Poisson C∞-ring, and
  the projection is a Poisson morphism (`quotient_bracket`).
- `restrictNormalizer I`: the normalizer is a C∞-ring, as a subalgebra closed
  under the smooth operations (`SmoothRing.ofSubalgebra`), with the restricted
  bracket. The elements of `I` in it form a Poisson ideal
  (`isPoissonIdeal_normalizerIdeal`). This holds for every ideal `I`.
- `Reduction I`, `reduction I`: the reduced ring `N(I)/I` with its bracket
  (Proposition 28 of the plan). `reductionMap` is the projection of the
  normalizer, with `reduction_bracket` and `reductionMap_eq_iff`. For a
  coisotropic ideal, `I ⊆ N(I)`, and the quotient is by all of `I`.
- `toReduction_bijective`, `isPoissonHom_toReduction`: a criterion that
  identifies the reduced ring with a model `Q`. It takes a Poisson morphism
  `σ : Q → P` with values in `N(I)` and a morphism `r : P → Q` with
  `r ∘ σ = id` that vanishes on `I`, such that `f − σ (r f) ∈ I` for every
  `f ∈ N(I)`.

The reductions with respect to cyclic co-ordinates and by translations are in
the [mechanics guide](mechanics.md#reduction-and-the-routhian).

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
[issue #78](https://github.com/MGYamada/ProjectAinos/issues/78).

`Poisson/LinearMomentum` and `Poisson/OrbitalCharge` give the charges of
affine maps of the co-ordinates. A vector `a` and a matrix `A` give
`translationMomentum a = Σ aᵢ pᵢ` and `linearMomentum A = Σ A μ ν q μ p ν`,
with `{ℓ_A, P_a} = P_{a ᵥ* A}` and `{ℓ_A, ℓ_B} = ℓ_{BA − AB}`. A matrix `η`
lowers the index of the co-ordinates, `x_μ = Σ η μ α q α`, and the orbital
charges `orbitalCharge η μ ν = x_μ p_ν − x_ν p_μ` of a symmetric `η` satisfy
`{J_μν, J_ρσ} = η_μρ J_νσ − η_νρ J_μσ + η_νσ J_μρ − η_μσ J_νρ` and
`{J_μν, p_ρ} = η_μρ p_ν − η_νρ p_μ`. If `G` is the inverse of `η`, they have
zero bracket with `momentumQuadratic G = Σ G σ τ p σ p τ`, and
`{x_μ, G(p, p)} = 2 p_μ`.

`RelEnergy` defines the energy `√(m² + Σ πᵢ²)` of a tuple `π` of elements of
any C∞-ring, for `m ≠ 0`. The function `√(1 + Σ wᵢ²)` is smooth on all of
`ℝᵈ`, and `relEnergy m π = m · √(1 + Σ (πᵢ/m)²)`. Its statements follow from
`relEnergy_mul_self`, `relEnergy_mul_relEnergyInv` and
`SmoothDerivation.apply_relEnergy`: `E² = m² + Σ πᵢ²`, `E E⁻¹ = 1` and
`D E = E⁻¹ Σ πᵢ D πᵢ` for every vector field `D`. These three modules are
used by the [relativistic particle](special-relativity.md#relativistic-particle-mechanics-the-algebraic-layer).

## Formal power series in `q` and `p`

`SmoothAlgebra/FormalSeries` treats the ring `ℝ[[q, p]]` as
`PhaseSeries = MvPowerSeries (Fin 2) ℝ`, with `q = X 0` and `p = X 1`, and
proves the Birkhoff normal form in one degree of freedom. No smooth function
is involved: the series are not identified with the smooth functions modulo
the functions flat at a point.

`Filtration`, for any set of variables: `orderGE σ n` is the space of the
series all of whose terms have degree at least `n`. A product adds the orders
and a partial derivative lowers the order by one (`mul_mem_orderGE`,
`pderiv_mem_orderGE`). `seqLimit s` is the limit of a sequence whose
successive differences have increasing orders (`seqLimit_sub_mem`), and a
series of every order is zero (`eq_zero_of_forall_mem_orderGE`).

`LieExp`: `Raises D j` states that a linear map raises the order by `j`.

- `lieExp D` is `Σ Dᵏ/k!`, the limit of the partial sums `expPartial D n`;
  `lieExp_sub_expPartial_mem` bounds the remainder.
- `lieExp_bilinear`: if `D` is a derivation of a bilinear map `B` that lowers
  the order by at most `c`, then `lieExp D (B f g) = B (lieExp D f)
  (lieExp D g)`. The proof is the Leibniz rule for the terms of the series
  (`expTerm_bilinear`) and a triangular sum (`expPartial_bilinear`).
- `bijective_of_raises_sub_id`: a linear map that differs from the identity by
  a map raising the order is bijective; hence `bijective_lieExp`.
- `lieExp_add_sub_mem`: adding to `D` a map `D'` that raises the order by `j'`
  changes `lieExp D g` by `D' g` up to the order `m + j' + 1`, for `g` of
  order `m`.

`Bracket`: `bracket f g = ∂f/∂q ∂g/∂p − ∂f/∂p ∂g/∂q`. It is a derivation in
each argument, satisfies the Jacobi identity (`bracket_bracket`) and lowers
the order by at most two (`bracket_mem_orderGE`). `ad F` is the bracket with
`F`; for `F` of order at least three, `lieExp (ad F)` preserves the product
and the bracket (`lieExp_ad_mul`, `lieExp_ad_bracket`), and `lieAlgEquiv F` is
this Lie transform as an automorphism of the algebra.

`Homological`: `action = (q² + p²)/2`, and `homogeneous k` is the space of the
series all of whose terms have degree `k`, a space of finite dimension
(`finiteDimensional_homogeneous`).

- `bracket_action`: the bracket with the action is `q ∂/∂p − p ∂/∂q`.
- `fischer k f g = Σ a! b! f_{ab} g_{ab}` over the monomials `qᵃ pᵇ` of degree
  `k`. Multiplication by a variable is adjoint to the derivative in it
  (`fischer_X_zero_mul`, `fischer_X_one_mul`), so the bracket with the action
  is skew (`fischer_bracket_action`).
- `resonant k` is `action ^ (k/2)` for even `k` and zero for odd `k`.
  `eq_smul_resonant`: a homogeneous series of degree `k` whose bracket with
  the action vanishes is a multiple of `resonant k`.
- `exists_homological`: every homogeneous `G` of degree `k` is
  `bracket action F + c • resonant k` with `F` homogeneous of degree `k`.

`NormalForm`: let `H − ω • action` have order at least three, `ω ≠ 0`.

- `normalize_step`: adding `ω⁻¹` times a solution of the homological equation
  of degree `k` to a generator `W` makes the component of degree `k` of
  `lieExp (ad W) H` resonant and changes this series only from the degree `k`
  on.
- `generator ω H N` is the limit of the partial generators `generatorSeq`,
  which start at the degree `N`; `exists_component_generator` states that the
  transformed series has a resonant component in every degree from `N` on.
- `exists_eq_subst_action`: a series all of whose components are resonant is
  `PowerSeries.subst action h` for a power series `h` in one variable, and
  `coeff_eq_of_homogeneousComponent` reads off a coefficient of `h`.
- `exists_birkhoff_normal_form`: there are an automorphism `Ψ` of the algebra
  with `Ψ (bracket f g) = bracket (Ψ f) (Ψ g)` and a power series `h` with
  `Ψ H = h(action)`, `h = ω x + ⋯`. `exists_normal_form_of_resonant` is the
  version that starts at a degree `N` below which `H` is already normal, with
  `Ψ H − H` of order at least `N`.

`Scaling`: `scale λ` is the substitution `q ↦ λ q`, `p ↦ λ⁻¹ p` for `λ ≠ 0`, an
automorphism that preserves the bracket (`scale_bracket`), by Mathlib's
`MvPowerSeries.rescale`.

The application to the anharmonic oscillator is in the
[mechanics guide](mechanics.md#anharmonic-oscillations).

## Proof map and verification

| Module | Main checked results |
| --- | --- |
| [Operations](../ProjectAinos/SmoothAlgebra/Operations.lean) | `proj_comp`, `comp_proj`, `comp_assoc`, `exponential_addition` |
| [Basic](../ProjectAinos/SmoothAlgebra/Basic.lean) | `op_const`, `op_add`, `op_mul`, `op_neg`, `op_sub`, `op_smul`, `op_sum`, `exp_add` |
| [Hom](../ProjectAinos/SmoothAlgebra/Hom.lean) | `toAlgHom`, identity/composition laws, `map_neg`, `map_sub`, `map_sum`, `map_exp` |
| [Models](../ProjectAinos/SmoothAlgebra/Models.lean) | Real and function-ring instances; `hom_ext`, `lift_unique`, `existsUnique_lift`, `pullback_comp`, `eval_comp_pullback` |
| [Differential](../ProjectAinos/SmoothAlgebra/Differential.lean) | `directionalEvaluation_op`, the chain rule for every finite smooth operation on the concrete model; `directionalEvaluation_eq_sum` |
| [PartialDerivative](../ProjectAinos/SmoothAlgebra/PartialDerivative.lean) | `partialDeriv`, `fderiv_apply_eq_sum_partialDeriv`, `partialDeriv_mul`, `partialDeriv_comp`, `partialDeriv_comm`, `partialDeriv_exponential` |
| [DualNumber](../ProjectAinos/SmoothAlgebra/DualNumber.lean) | `SmoothRing (DualNumber A)`, `fst_op`, `snd_op`, `fstHom`, `inlHom`, `exp_inl_add_inr` |
| [FreeDerivation](../ProjectAinos/SmoothAlgebra/FreeDerivation.lean) | `FreeSmoothRing.derivation`, `derivation_generator`, `derivation_ext`, `map_derivation_eq`, `derivationEquiv`, `partialDerivation_comm`, `exists_finset_partialDerivation_eq_zero` |
| [FreeChainRule](../ProjectAinos/SmoothAlgebra/FreeChainRule.lean) | `FreeSmoothRing.derivation_lift`, `FreeSmoothRing.derivation_lift_mul`: the chain rule `E (s(y)) = Σₐ (∂ₐ s)(y) • E (yₐ)` for a substitution out of a free ring on finitely many generators. `FreeSmoothRing.apply_eq_sum_partialDerivation`, `FreeSmoothRing.apply_eq_zero_of_partialDerivation_eq_zero`: on any free ring a vector field is `Σₐ (∂ₐ s) E(xₐ)`, summed over the generators of a presentation of `s` |
| [FreeCalculus](../ProjectAinos/SmoothAlgebra/FreeCalculus.lean) | `FreeSmoothRing.contDiff_val`, `fderiv_val_apply`, `realField`, `contDiff_realField`, `fderiv_realField_apply`: the elements of a free ring on finitely many generators as differentiable functions, and derivations as vector fields |
| [DividedDifference](../ProjectAinos/SmoothAlgebra/DividedDifference.lean) | `dividedDifference`, `sub_eq_mul_dividedDifference`, `dividedDifference₂`, `dividedDifference_sub`, `sub_eq_mul_mul_dividedDifference₂`: Hadamard's lemma in one variable, applied twice |
| [ImplicitFunction](../ProjectAinos/SmoothAlgebra/ImplicitFunction.lean) | `exists_contDiffOn_implicitFunction`: a smooth implicit function on an open neighbourhood |
| [ImplicitFunctionReal](../ProjectAinos/SmoothAlgebra/ImplicitFunctionReal.lean) | `exists_contDiffOn_implicitFunction_real`: one real equation in one real unknown |
| [FormalSeries/Filtration](../ProjectAinos/SmoothAlgebra/FormalSeries/Filtration.lean) | `orderGE`, `mem_orderGE_iff_le_order`, `mul_mem_orderGE`, `pderiv_mem_orderGE`, `eq_zero_of_forall_mem_orderGE`, `seqLimit`, `seqLimit_sub_mem` |
| [FormalSeries/LieExp](../ProjectAinos/SmoothAlgebra/FormalSeries/LieExp.lean) | `Raises`, `expPartial`, `lieExp`, `lieExp_sub_expPartial_mem`, `lieExp_sub_self_mem`, `lieExp_add_sub_mem`, `pow_apply_bilinear`, `expPartial_bilinear`, `lieExp_bilinear`, `bijective_of_raises_sub_id`, `bijective_lieExp` |
| [FormalSeries/Bracket](../ProjectAinos/SmoothAlgebra/FormalSeries/Bracket.lean) | `PhaseSeries`, `bracket`, `bracket_mul_right`, `bracket_bracket`, `bracket_mem_orderGE`, `ad`, `raises_ad`, `lieExp_ad_mul`, `lieExp_ad_bracket`, `lieAlgEquiv` |
| [FormalSeries/Homological](../ProjectAinos/SmoothAlgebra/FormalSeries/Homological.lean) | `homogeneous`, `action`, `bracket_action`, `resonant`, `eq_zero_of_bracket_action_eq_zero`, `eq_smul_resonant`, `fischer`, `fischer_bracket_action`, `eq_zero_of_fischer_self`, `finiteDimensional_homogeneous`, `exists_homological` |
| [FormalSeries/NormalForm](../ProjectAinos/SmoothAlgebra/FormalSeries/NormalForm.lean) | `homologicalSolution`, `normalize_step`, `generatorSeq`, `generator`, `exists_component_generator`, `homogeneousComponent_subst_action`, `exists_eq_subst_action`, `exists_normal_form_of_resonant`, `exists_birkhoff_normal_form` |
| [FormalSeries/Scaling](../ProjectAinos/SmoothAlgebra/FormalSeries/Scaling.lean) | `pderiv_rescale`, `bracket_rescale`, `scale`, `scale_bracket`, `scale_X_zero`, `scale_X_one` |
| [LineDerivative](../ProjectAinos/SmoothAlgebra/LineDerivative.lean) | `hasFDerivAt_of_hasDerivAt_line`: derivatives along all lines, with a continuous field of linear forms, give the Fréchet derivative |
| [Point](../ProjectAinos/SmoothAlgebra/Point.lean) | `Point`, `TangentPoint`, `TangentPoint.congr`, `FreeSmoothRing.pointEquiv`, `FreeSmoothRing.lift_real`, `FreeSmoothRing.ext_lift`, `FreeSmoothRing.tangentPointEquiv`, `FreeSmoothRing.fst_tangentPoint`, `FreeSmoothRing.snd_tangentPoint`, `FreeSmoothRing.tangentPoint_map_lift`, `SmoothRingCon.generateHomEquiv`, `FreeSmoothRing.Presented`, `FreeSmoothRing.presentedPointEquiv`, `FreeSmoothRing.presentedTangentPointEquiv`, `FreeSmoothRing.circleTangentPointEquiv` |
| [ParametricIntegral](../ProjectAinos/SmoothAlgebra/ParametricIntegral.lean) | `fderivLeft`, `hasFDerivAt_parametric_intervalIntegral`, `contDiff_parametric_intervalIntegral`, `contDiff_infty_parametric_intervalIntegral`, `contDiff_infty_parametric_intervalIntegral_limits`: a parametric integral of a smooth function is smooth |
| [Hadamard](../ProjectAinos/SmoothAlgebra/Hadamard.lean) | `SmoothOperation.segment`, `SmoothOperation.hadamard`, `apply_sub_apply_eq_sum_hadamard`, `comp_castAdd_sub_comp_natAdd`, `SmoothRing.op_sub_op`: Hadamard's lemma for operations and in a C∞-ring |
| [IdealQuotient](../ProjectAinos/SmoothAlgebra/IdealQuotient.lean) | `SmoothRingCon.ofIdeal`, `ofIdeal_projection_eq_iff`, `ofIdeal_projection_eq_zero_iff`, `ofIdealHomEquiv`, `generated_iff_sub_mem_span`, `FreeSmoothRing.presented_projection_eq_iff`, `FreeSmoothRing.presented_projection_eq_zero_iff`, `FreeSmoothRing.hom_sub_hom_mem`, `SmoothRingHom.mem_of_mem_span`, `SmoothRingHom.eq_zero_of_mem_span` |
| [Poisson/Basic](../ProjectAinos/SmoothAlgebra/Poisson/Basic.lean) | `AlmostPoissonStructure`, `PoissonStructure`, `hamiltonian`, `bracket_mul_left`, `bracket_op_op`, `jacobiator_op`, `ofDerivations`, `bracket_bracket`, `hamiltonian_bracket`, `IsIntegral.bracket`, `IsIntegral.op`, `integrals`, `isIntegral_iff_hamiltonian_eq_zero` |
| [Poisson/Ideal](../ProjectAinos/SmoothAlgebra/Poisson/Ideal.lean) | `IsPoissonIdeal`, `IsCoisotropic`, `isPoissonIdeal_span_singleton`, `normalizer`, `bracket_mem_normalizer`, `op_mem_normalizer`, `bracket_sub_bracket_mem`, `hamiltonJacobi`, `maupertuis`, `mem_normalizer_span`, `isCoisotropic_span` |
| [Poisson/Free](../ProjectAinos/SmoothAlgebra/Poisson/Free.lean) | `jacobiator_eq_zero`, `almostPoisson`, `almostPoisson_bracket_generator`, `almostPoisson_bracket_eq_sum_left`, `poissonOfCoordinates`, `poissonOfConstants` |
| [Poisson/Canonical](../ProjectAinos/SmoothAlgebra/Poisson/Canonical.lean) | `PhaseSpace`, `canonical`, `canonical_q_p`, `canonical_bracket`, `canonical_q_bracket`, `canonical_p_bracket`, `canonical_hamiltonian_apply`, `isPoissonHom_of_canonical` |
| [Poisson/Hom](../ProjectAinos/SmoothAlgebra/Poisson/Hom.lean) | `IsPoissonHom`, `IsPoissonHom.comp`, `FreeSmoothRing.isPoissonHom_of_generators` |
| [Poisson/Reduction](../ProjectAinos/SmoothAlgebra/Poisson/Reduction.lean) | `SmoothRing.ofSubalgebra`, `PoissonStructure.ofSurjective`, `ofSurjective_bracket`, `quotient`, `quotient_bracket`, `isPoissonHom_projection`, `normalizerInclusion`, `restrictNormalizer`, `normalizerIdeal`, `isPoissonIdeal_normalizerIdeal`, `Reduction`, `reduction`, `reductionMap`, `reductionMap_eq_iff`, `reduction_bracket`, `toNormalizer`, `toReduction`, `isPoissonHom_toReduction`, `toReduction_apply_eq`, `toReduction_bijective` |
| [Poisson/LinearMomentum](../ProjectAinos/SmoothAlgebra/Poisson/LinearMomentum.lean) | `PhaseSpace.translationMomentum`, `linearMomentum`, `canonical_linearMomentum_q`, `canonical_linearMomentum_p`, `canonical_linearMomentum_translationMomentum`, `canonical_linearMomentum_linearMomentum`: `{ℓ_A, ℓ_B} = ℓ_{BA − AB}` |
| [Poisson/OrbitalCharge](../ProjectAinos/SmoothAlgebra/Poisson/OrbitalCharge.lean) | `PhaseSpace.loweredCoordinate`, `orbitalCharge`, `momentumQuadratic`, `canonical_orbitalCharge_p`, `canonical_orbitalCharge_orbitalCharge`, `canonical_loweredCoordinate_momentumQuadratic`, `canonical_orbitalCharge_momentumQuadratic` |
| [RelEnergy](../ProjectAinos/SmoothAlgebra/RelEnergy.lean) | `SmoothOperation.lorentzFactor`, `partialDeriv_lorentzFactor`, `SmoothRing.op_algebraMap`, `relEnergy`, `relEnergyInv`, `relEnergy_mul_self`, `relEnergy_mul_relEnergyInv`, `SmoothDerivation.apply_relEnergy`, `SmoothDerivation.apply_relEnergyInv`, `sum_relEnergyInv_mul_sq`, `relEnergy_real`, `sum_sq_relEnergyInv_mul_lt_one` |
| [Derivation](../ProjectAinos/SmoothAlgebra/Derivation.lean) | `SmoothDerivation`, `map_mul`, `map_exp`, `toDerivation`, module and Lie-ring instances, `sum_apply`, `commutator_chain`, `equivInfinitesimalAut`, `equivCoordinates`, `lie_partialDerivation_proj_smul` |
| [Category](../ProjectAinos/SmoothAlgebra/Category.lean) | `SmoothRingCat`, faithful forgetful functors, isomorphisms from bijective morphisms |
| [Congruence](../ProjectAinos/SmoothAlgebra/Congruence.lean) | Smooth quotients, projection, factorization, generated smooth congruences |
| [LocalInverse](../ProjectAinos/SmoothAlgebra/LocalInverse.lean) | `exists_localInverse`, a smooth inverse on the support of a cutoff |
| [Localization](../ProjectAinos/SmoothAlgebra/Localization.lean) | Point localization, `existsUnique_lift`, real residue, local-ring property, induced local maps |
| [Free](../ProjectAinos/SmoothAlgebra/Free.lean) | Free C∞-rings on arbitrary generators, presentation independence, lift and uniqueness, `map_lift` |
| [GeneralLocalization](../ProjectAinos/SmoothAlgebra/GeneralLocalization.lean) | General C∞ localization, `existsUnique_lift`, `hom_ext`, induction on smooth expressions |
| [LocalizationComparison](../ProjectAinos/SmoothAlgebra/LocalizationComparison.lean) | Point-local ring isomorphism after general localization |
| [Limits](../ProjectAinos/SmoothAlgebra/Limits.lean) | Compatible-family limits and preservation by the forgetful functor |
| [SmoothFunctions](../ProjectAinos/SmoothAlgebra/SmoothFunctions.lean) | Smooth operations, evaluation, and pullback on manifold function algebras |

The models module also checks dimension zero (`nullary_eq_const`), nonlinear
evaluation in dimension one (`eval_exp_square`), and a two-variable exponential
operation pulled back to four mixed coordinates (`eval_four_dimensional`). These
are Lean theorems, not symbolic or numerical evidence.

From the repository root:

```sh
lake exe cache get
lake build --wfail ProjectAinos
lake exe mk_all --check --lib ProjectAinos
lake env lean -DwarningAsError=true checks/AxiomAudit.lean
lake env lean -DwarningAsError=true checks/SmoothAlgebraAPI.lean
lake env lean -DwarningAsError=true checks/ReductionAPI.lean
lake env lean -DwarningAsError=true checks/FormalSeriesAPI.lean
lake env lean -DwarningAsError=true checks/SmoothGeometryAPI.lean
git diff --check
```

The local audit inspects transitive axiom dependencies of every imported
declaration in the `ProjectAinos` namespace. Its allowlist is `propext`,
`Classical.choice`, and `Quot.sound`, matching the existing required Lean CI job.
The required Lean CI job also checks the external smooth-geometry API,
including open immersions and categorical gluing, and pins the differential
part of this layer with typed examples in `checks/SmoothAlgebraAPI.lean`,
the quotients in `checks/ReductionAPI.lean` and the formal power series in
`checks/FormalSeriesAPI.lean`. No dependency change is needed.

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
structures, quotients by ordinary ideals and the reduced Poisson rings.
Subsequent algebraic stages include the universal cotangent module with its
universal property, derivations along a morphism, and comparison theorems with
ordinary local jets.
