# The Algebraic Entropy Theorem

This chapter develops the algebraic part of the [thermodynamics formalization](thermodynamics.md): cancellation, completion, the process cone, its real entropy coordinate, and the conservation quotient. Physical accessibility supplies the assumptions through the [physical construction](thermodynamics-physical.md). The algebraic results can also be applied to other ordered semimodules.

## Ordered states and stability

Let `M` denote states modulo mutual adiabatic accessibility. Its order `x ≤ y` means that `y` is accessible from `x`. Addition is composition of separate systems. Nonnegative scalar multiplication changes the amount of a system. Addition here is distinct from coordinate mixing inside a simple system.

The Lean input is

```lean
variable {M : Type*} [AddCommMonoid M] [PartialOrder M]
  [Module ℝ≥0 M] [IsOrderedAddMonoid M] [PosSMulMono ℝ≥0 M]
```

Stability is an explicit hypothesis `hS : Stability M`. For fixed `x`, `y`, `z₀`, and `z₁`, it asserts

$$
\varepsilon_n>0,\quad \varepsilon_n\longrightarrow0,\quad
x+\varepsilon_n z_0\le y+\varepsilon_n z_1\ (\forall n)
\quad\Longrightarrow\quad x\le y.
$$

Only the scalar sequence has a topology. No topology on `M` or its completion is assumed. Zero scaling and the empty state are part of the semimodule structure; the auxiliary scales in A6 are strictly positive. [Definition: `Stability`](../ProjectAInos/Thermodynamics/Basic.lean).

## Cancellation from A6

Suppose `x + z ≤ y + z`. Induction, using monotone addition, proves

$$
n x+z\le n y+z\qquad(n\in\mathbb N).
$$

The successor step replaces one copy of `x` by `y` using the original premise, then replaces the remaining copies using the induction hypothesis. Apply the result with `n + 1` copies and scale by `εₙ = 1/(n+1)`:

$$
x+\varepsilon_n z\le y+\varepsilon_n z.
$$

A6 removes the auxiliary system and gives `x ≤ y`. Applying this to both directions of an equality gives `x + z = y + z → x = y`.

[Cancellation](../ProjectAInos/Thermodynamics/Cancellation.lean) exposes `Stability.le_of_add_le_add_right`, `Stability.eq_of_add_eq_add_right`, and `Stability.isOrderedCancelAddMonoid`. Cancellation is installed from this proof where needed; it is not an additional physical premise. This is the spectator cancellation of LY Theorem 2.1.

## Grothendieck completion and real scalars

Set

$$
V=K(M),\qquad \iota:M\longrightarrow V.
$$

The implementation uses `Algebra.GrothendieckAddGroup M`, abbreviated `Completion M`, and its additive map `Completion.of`. Every vector is `ι y − ι x`. Cancellation implies that `ι` is injective.

For `a ≥ 0`, lift `x ↦ ι(a x)` to an additive endomorphism `Tₐ` of `V`. Uniqueness in the group-completion universal property gives

$$
T_0=0,\quad T_1=\mathrm{id},\quad
T_{a+b}=T_a+T_b,\quad T_{ab}=T_a\circ T_b.
$$

For a real scalar use its positive and negative parts:

$$
r^+=\max(r,0),\quad r^-=\max(-r,0),\qquad
r v=T_{r^+}(v)-T_{r^-}(v).
$$

If `r = a − b = a′ − b′`, then `a + b′ = a′ + b`, so the same difference of endomorphisms results. For `s = c − d`, the decompositions

$$
r+s=(a+c)-(b+d),\qquad rs=(ac+bd)-(ad+bc)
$$

give scalar addition and multiplication. Thus `V` is a real vector space extending the nonnegative action on `M`. The extension is unique. An additive, nonnegatively homogeneous map from `M` to any real vector space extends uniquely to a real linear map from `V`.

[Completion](../ProjectAInos/Thermodynamics/Completion.lean) provides `exists_sub_of`, `nnrealEndHom`, `realEndHom`, `module_unique`, `ofLinear`, `liftLinear`, `liftLinear_unique`, and `of_injective`. The real action itself needs no order or stability; stability is used to obtain injectivity for the ordered-state application.

## Process cone and order reflection

Define

$$
P=\{\iota y-\iota x\mid x\le y\},\qquad
v\le_P w\ \Longleftrightarrow\ w-v\in P.
$$

Reflexivity supplies `0 ∈ P`. Parallel composition adds process differences, and nonnegative scaling scales them. These properties define `processCone M : PointedCone ℝ (Completion M)`. In mathlib, this type supplies cone closure and zero membership; absence of a nonzero line is the separate `Salient` property proved below.

The key reflection theorem is

$$
x\le y\quad\Longleftrightarrow\quad\iota y-\iota x\in P.
$$

For the reverse implication, write `ι y − ι x = ι b − ι a` with `a ≤ b`. Injectivity gives `y + a = x + b`, so `x + a ≤ y + a`; cancellation removes `a`. If both `v` and `−v` lie in `P`, reflection gives mutual accessibility between representatives. Antisymmetry implies `v = 0`. Therefore

$$
P\cap(-P)=\{0\}.
$$

The cone order is a partial order on the whole completion. There is no remaining radical to quotient out: mutual accessibility has already been quotiented at the state level, and cancellation has been proved. [Cone](../ProjectAInos/Thermodynamics/Cone.lean): `processCone_reflects`, `processCone_salient`, `completionPartialOrder`, and `completion_of_le_iff`.

## Sequential closure and the Archimedean property

For a cone in a real vector space, `SequentialOrderClosed P` means

$$
\varepsilon_n>0,\quad\varepsilon_n\to0,\quad
v+\varepsilon_n w\in P\ (\forall n)
\quad\Longrightarrow\quad v\in P.
\tag{SC}
$$

This is closure along vanishing perturbations in one fixed direction, with no ambient topology. To derive it from A6, write

$$
v=\iota y-\iota x,\qquad w=\iota z_1-\iota z_0.
$$

Order reflection turns each cone membership into `x + εₙ z₀ ≤ y + εₙ z₁`. Stability gives the limiting process.

SC also gives

$$
(\forall n\ge1,\ n v\le_P w)\quad\Longrightarrow\quad v\le_P0.
\tag{AR}
$$

Indeed, scaling the hypotheses gives `−v + w/n ∈ P`, to which SC applies. Once the process span has a linear order, this supplies its usual `Archimedean` instance. [Cone: `processCone_sequentialOrderClosed`](../ProjectAInos/Thermodynamics/Cone.lean); [Representation: `SequentialOrderClosed.archimedean`, `coneSpan_archimedean`](../ProjectAInos/Thermodynamics/Representation.lean).

## Exchange comparison is totality on the process span

Define

$$
W=\operatorname{span}_{\mathbb R}P=P-P.
$$

The equality follows from cone closure: differences of cone elements form a real subspace containing `P`. The implementation uses mathlib's `PointedCone.mem_span` to obtain this decomposition.

`ExchangeComparison M` is the precise comparison input:

$$
x\le y,\quad u\le v
\quad\Longrightarrow\quad
x+v\le y+u\ \text{or}\ y+u\le x+v.
\tag{ECH}
$$

For `w = (ι y − ι x) − (ι v − ι u)`, we have

$$
w=\iota(y+u)-\iota(x+v).
$$

Reflection proves

$$
\mathrm{ECH}\quad\Longleftrightarrow\quad
\forall w\in W,\ w\in P\ \text{or}\ -w\in P.
$$

Equivalently, `W = P ∪ (−P)`. The induced order on `W` is total. The order on `V` remains partial.

A useful sufficient condition is an additive label map `d : M → D` whose values are conserved by accessibility, together with comparison whenever labels agree. For the two processes above,

$$
d(x+v)=d(x)+d(v)=d(y)+d(u)=d(y+u),
$$

so comparison within that label proves ECH. Elementary-system CH alone does not establish this premise; the physical development constructs common scaled products for equal-label composites.

[Comparison](../ProjectAInos/Thermodynamics/Comparison.lean): `ExchangeComparison`, `exchangeComparison_of_sectors`; [Cone](../ProjectAInos/Thermodynamics/Cone.lean): `exchangeComparison_iff_coneTotal`; [Representation](../ProjectAInos/Thermodynamics/Representation.lean): `ConeTotalOnSpan`, `coneSpanLinearOrder`.

## The real cut and rank-one representation

Assume SC, salience, totality on `W`, and a nonzero `e ∈ P`. For `w ∈ W`, define

$$
A_w=\{r\in\mathbb R\mid re\le_P w\},\qquad s_e(w)=\sup A_w.
$$

The cut is nonempty and bounded above. Otherwise every positive multiple `n e` would lie below `w`, or below `−w`; AR and salience would contradict `e ≠ 0`. Totality supplies the bounds in the remaining direction.

Let `α = sup A_w`. Downward closure gives `re ≤ w` for `r < α`; totality gives `w ≤ re` for `r > α`. Consequently, for `εₙ = 1/(n+1)`,

$$
(w-\alpha e)+\varepsilon_n e\in P,\qquad
(\alpha e-w)+\varepsilon_n e\in P.
$$

SC puts both limiting vectors in `P`. Salience gives `w = αe`. Thus

$$
s_e:W\simeq_{\mathbb R}\mathbb R,\qquad
s_e(e)=1,\qquad
0\le s_e(w)\ \Longleftrightarrow\ w\in P.
$$

The inverse is `r ↦ re`; additivity and real homogeneity follow from uniqueness of that coefficient. Any other order-preserving and order-reflecting linear equivalence is `a sₑ` for one unique `a > 0`. In particular, fixing the value at `e` fixes the coordinate. This uniqueness concerns linear entropy coordinates, not arbitrary increasing functions of entropy.

The related ordered-group fact is that every additive order automorphism of the real line is multiplication by one positive real number. Additivity fixes its values on rationals, and order bounds between rational approximations fix its values on every real. Arbitrary increasing bijections of the real line have much greater freedom. This is background explaining the role of additivity; the dedicated Lean uniqueness theorem here is the classification of order-preserving linear entropy coordinates.

[Representation](../ProjectAInos/Thermodynamics/Representation.lean) proves `entropyCut_nonempty`, `entropyCut_bddAbove`, `entropyCut_sSup_smul`, `coneEntropyEquiv`, `coneEntropyEquiv_nonneg_iff`, `coneEntropyEquiv_generator`, and `coneEntropyEquiv_unique_up_to_pos`. [Entropy](../ProjectAInos/Thermodynamics/Entropy.lean) specializes this construction to `entropyCoordinate` using A6 and ECH.

If `P = {0}`, then `W = 0`; there is no distinguished entropy direction or unit. The [degenerate model](thermodynamics-models.md) records this separate case.

## Entropy extensions and conserved sectors

Fix an entropy coordinate `s : W ≃ₗ[ℝ] ℝ`. The public type is

$$
\operatorname{Ent}_s(V)=
\{S:V\to_{\mathbb R}\mathbb R\mid S|_W=s\}.
$$

`EntropyExtension s` is exactly this subtype of linear maps. `LinearMap.exists_extend` gives existence. The state entropy `𝒮(x) = S(ι x)` is additive and homogeneous for every nonnegative scalar, including zero:

$$
\mathcal S(x+y)=\mathcal S(x)+\mathcal S(y),\qquad
\mathcal S(tx)=t\mathcal S(x).
$$

Put `C = V/W` and let `π : V → C` be the quotient map. The complete entropy criterion is

$$
\pi(\iota x)=\pi(\iota y)
\quad\Longrightarrow\quad
\bigl(x\le y\ \Longleftrightarrow\ \mathcal S(x)\le\mathcal S(y)\bigr).
$$

Sector equality is equivalent to `ι y − ι x ∈ W`, where the coordinate detects cone membership. Every accessible process lies in `W`, so entropy is monotone on all accessible pairs. An entropy inequality alone says nothing about pairs in different conserved sectors. The [entropy–amount model](thermodynamics-models.md) demonstrates this obstruction.

[Conservation](../ProjectAInos/Thermodynamics/Conservation.lean): `entropyExtension_nonempty`, `EntropyExtension.le_iff`, `conservation_eq_iff`; [Entropy](../ProjectAInos/Thermodynamics/Entropy.lean): `EntropyExtension.state`, `EntropyExtension.state_le_iff`, `EntropyExtension.state_monotone`, `exists_normalized_entropy`.

## Signed cutoff and relative entropy

Choose a strict reference process `x₀ < x₁`, normalize `s(ι x₁ − ι x₀) = 1`, and suppose `x` is in the same conserved sector as `x₀`. Interpret a signed reference mixture using only nonnegative physical amounts:

$$
(1-\lambda)^+x_0+\lambda^+x_1
\le x+(1-\lambda)^-x_0+\lambda^-x_1.
$$

This is `signedReferenceLE x₀ x₁ x λ`, defined for every real `λ`. Reflection converts it to

$$
\iota x-\iota x_0-\lambda(\iota x_1-\iota x_0)\in P,
$$

and the entropy coordinate converts it to `λ ≤ 𝒮(x) − 𝒮(x₀)`. Hence

$$
\sup\{\lambda\in\mathbb R\mid
\operatorname{signedReferenceLE}(x_0,x_1,x,\lambda)\}
=\mathcal S(x)-\mathcal S(x_0).
$$

The normalization fixes a difference, so the cutoff measures **relative** entropy. It equals `𝒮(x)` only with the further choice `𝒮(x₀) = 0`. The proof covers `λ < 0`, `λ > 1`, and the endpoints, where the relation becomes `x₀ ≤ x` or `x₁ ≤ x`.

[Cutoff](../ProjectAInos/Thermodynamics/Cutoff.lean): `signedReferenceLE_iff`, `signedReferenceLE_iff_entropy_le`, `reference_cutoff_eq_relative_entropy`, `signedReferenceLE_zero`, `signedReferenceLE_one`. See also [formalization note T03](thermodynamics-notes.md#t03-the-reference-cutoff-measures-relative-entropy).

## Conservation and the freedom in entropy

The quotient has the exact sequence

$$
0\longrightarrow W\overset{i}{\longrightarrow}V
\overset{\pi}{\longrightarrow}C\longrightarrow0.
$$

For every real vector space `E`, a linear map `q : V → E` vanishes on each process difference if and only if it factors uniquely through `C`. The proof uses `W = span ℝ P` and the quotient universal property. Thus `C` is the universal target of additive, extensive conserved quantities. Neither its construction nor this property requires ECH or a nonzero process cone. Identifying `C` with particular species or element amounts requires a separate model.

Once one extension `S₀` of a fixed `s` is chosen, every extension has the form

$$
S=S_0+\varphi\circ\pi,\qquad
\varphi:C\to_{\mathbb R}\mathbb R,
$$

for a unique `φ`. Indeed, `S − S₀` vanishes on `W`; conversely adding any conserved linear functional preserves the restriction to `W`. This makes the extensions a nonempty affine family, or torsor, over the dual of `C`. The implementation exposes the unique-difference theorem and a bijective parametrization, rather than requiring an additional torsor typeclass.

Via `s⁻¹`, an extension is equivalently a linear retraction `V → W` of the inclusion. Changing the positive scale of `s` changes the entropy unit; changing `φ` changes composition-dependent offsets. A nonzero constant added uniformly to every composite is generally incompatible with additivity and zero entropy for the empty state.

[Conservation](../ProjectAInos/Thermodynamics/Conservation.lean): `conservation_exact`, `existsUnique_process_factor_iff`, `existsUnique_conservation_factor_iff`, `EntropyExtension.existsUnique_difference`, `EntropyExtension.addConserved`, and `EntropyExtension.equivConserved`.
