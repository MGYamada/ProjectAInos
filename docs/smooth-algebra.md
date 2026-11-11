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
manifolds used by the geometric layer. The library root imports all these
modules. This layer has no dependency on `Variational`,
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

## Proof map and verification

| Module | Main checked results |
| --- | --- |
| [Operations](../ProjectAInos/SmoothAlgebra/Operations.lean) | `proj_comp`, `comp_proj`, `comp_assoc`, `exponential_addition` |
| [Basic](../ProjectAInos/SmoothAlgebra/Basic.lean) | `op_const`, `op_add`, `op_mul`, `op_neg`, `op_sub`, `op_smul`, `exp_add` |
| [Hom](../ProjectAInos/SmoothAlgebra/Hom.lean) | `toAlgHom`, identity/composition laws, `map_exp` |
| [Models](../ProjectAInos/SmoothAlgebra/Models.lean) | Real and function-ring instances; `hom_ext`, `lift_unique`, `existsUnique_lift`, `pullback_comp`, `eval_comp_pullback` |
| [Differential](../ProjectAInos/SmoothAlgebra/Differential.lean) | `directionalEvaluation_op`, the chain rule for every finite smooth operation on the concrete model |
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
lake env lean -DwarningAsError=true checks/SmoothGeometryAPI.lean
git diff --check
```

The local audit inspects transitive axiom dependencies of every imported
declaration in the `ProjectAInos` namespace. Its allowlist is `propext`,
`Classical.choice`, and `Quot.sound`, matching the existing required Lean CI job.
The required Lean CI job also checks the external smooth-geometry API,
including open immersions and categorical gluing. No dependency change is
needed.

## Ordinary differentials and further algebraic stages

On `C∞(ℝⁿ)`, `directionalEvaluation x v` applies the ordinary Fréchet derivative
at `x` to a vector `v`. Its chain rule expresses the derivative of smooth
substitution in terms of the values and derivatives of the substituted
functions. This connects smooth operations to the same ordinary calculus used
for local jets and first variations in the [variational guide](variational.md).

Smooth congruence quotients and general localizations now support the
[C∞ scheme construction](smooth-geometry.md). Subsequent algebraic stages
include quotients by arbitrary ordinary ideals and
abstract smooth derivations satisfying the chain rule for every smooth
operation. Cotangent and infinitesimal constructions require their own
universal properties and comparison theorems with ordinary local jets.
