# Shared Smooth Geometry: Joyce C∞ Schemes

`ProjectAinos/SmoothAlgebra/` and `ProjectAinos/SmoothGeometry/` are the
mathematical foundation shared by Mechanics, Special Relativity,
Electrodynamics, and General Relativity (research-plan topics 2–5).
The shared smooth-algebra, geometry and variational layers may use one another
through an acyclic module graph. They import neither project physics nor the
vendored Yang–Mills theory; `checks/CoreImports.lean` enforces this boundary.
The implementation sequence and subsequent research stages are in the
[shared foundations plan](shared-smooth-algebra-and-geometry.md#foundation-implementation-plan).

## Correspondence with mathlib

The source review and implementation target the pinned mathlib v4.35.0,
commit `56a005855ea17e0b0958f73ec801ae140b0a1679`.

| mathlib layer | Project Ainos layer | Mathematical change |
| --- | --- | --- |
| `CommAlgCat ℝ` | `SmoothAlgebra.Category` | Morphisms preserve every smooth operation |
| Ring limits and localization | `SmoothAlgebra.Limits`, `GeneralLocalization` | Compatible families and localization universal properties in C∞-rings |
| `PrimeSpectrum` | `SmoothGeometry.RealSpectrum` | Points are `SmoothRingHom A ℝ` |
| `AlgebraicGeometry.StructureSheaf` | `SmoothGeometry.StructureSheaf` | Sections locally represented in C∞ point localizations |
| `Geometry.RingedSpace.SheafedSpace` | `SmoothGeometry.RingedSpace` | Smooth structure on all sections and restrictions |
| `Geometry.RingedSpace.LocallyRingedSpace` | `SmoothGeometry.LocallyRingedSpace` | Real residue fields and smooth morphisms |
| `AlgebraicGeometry.Spec` | `SmoothGeometry.Spec` | The constructed real spectrum, contravariantly |
| `AlgebraicGeometry.Scheme` | `SmoothGeometry.Scheme` | The same local-affine condition using C∞ spectra |
| `AlgebraicGeometry.AffineScheme` | `SmoothGeometry.AffineScheme` | Essential image of C∞ Spec |
| Open immersions and scheme restriction | `SmoothGeometry.OpenImmersion`, `Restrict` | Principal C∞ localizations give affine open neighbourhoods |
| `AlgebraicGeometry.Gluing` | `SmoothGeometry.Gluing` | Open gluing data, constructed glued schemes, and their universal property |
| `Scheme.Cover.fromGlued` | `SmoothGeometry.OpenCover` | A descent of open immersions that is bijective on points is an isomorphism |
| `Geometry.Manifold.Sheaf` | `SmoothGeometry.Manifold` | Actual smooth-function sheaves and their local-affine comparison |

The topology, presheaves, gluing condition, stalk colimits, and restrictions use
mathlib's infrastructure. `SmoothStructure` equips an ordinary ring-valued
presheaf with compatible C∞ operations. Its `presheaf` bundles the same data
with values in `SmoothRingCat`. This presentation retains the existing
commutative-ring instances and lets the construction reuse mathlib's ringed
spaces directly.

## Constructed affine models

`SmoothRingCon` is a ring congruence compatible with all finite smooth
operations. Its quotient has an induced `SmoothRing`, a smooth projection,
and a factorization API. `Generated` constructs the least smooth equivalence
closure of a family of equations, using reflexivity, symmetry, transitivity,
and finite smooth substitution.

For a real point `x : SmoothRingHom A ℝ`, `PointLocalization x` is the quotient
by the generated equations

\[
a s = b s,\qquad x(s)\ne 0.
\]

Smooth cutoff functions construct inverses for elements nonzero at `x`.
`existsUnique_lift` proves the universal property among **C∞ morphisms**.
`residue` maps the localization to ℝ, preserves real constants, is surjective,
and detects units. Consequently this is a local ring with residue field ℝ.
This construction does not postulate smooth operations on an ordinary ring
localization.

`RealSpectrum A` has the basic opens `D(a) = {x | x(a) ≠ 0}`. Their basis
property and continuous precomposition maps are proved. The structure sheaf
on an open `U` consists of dependent functions

\[
s\in\prod_{x\in U} A_x
\]

that locally are images of an element of `A`. Finite intersections of
neighbourhoods prove closure under every smooth operation, including arity
zero. Mathlib's `LocalPredicate` construction proves the sheaf condition.
`stalkIso` identifies the actual sheaf stalk with the constructed localization.
Equality in a localization persists on a neighbourhood by induction on its
finite congruence proof; no assumption that the ring is reduced is used.

`Spec.toLocallyRingedSpace` constructs the affine model and its morphisms.
Its stalk maps agree with the induced maps of localizations.
`Scheme.local_affine` requires each point to have an open neighbourhood whose
restriction is isomorphic to one of these models. `Scheme.Spec` therefore
lands in the category of C∞ schemes.

## General localization and open subschemes

`FreeSmoothRing` constructs the free C∞-ring on an arbitrary set of
generators. `SmoothLocalization S` uses it to adjoin inverses for all elements
of `S` and impose the original smooth operations. Its `existsUnique_lift`
proves the universal property for smooth morphisms into any C∞-ring that
inverts `S`. Unlike point localization, this construction need not be a
quotient of the original ring.

`SmoothGeometry.Localization.homeomorph` identifies its spectrum with the
subspace of real points nonzero on every element of `S`. The stalk maps are
isomorphisms. For a singleton `{a}`, this gives an open immersion with image
`D(a)`. An arbitrary infinite intersection of such opens need not be open;
the general theorem is a subspace comparison.

`Scheme.ofOpenImmersion` proves local affineness of an open subspace by
refining affine neighbourhoods to principal opens. Consequently
`Scheme.restrict` constructs open subschemes, and `Scheme.ofOpenCover`
establishes the scheme property from a covering family of open immersions.
Pullbacks along open immersions are constructed as restrictions and satisfy
their categorical universal property. Scheme-level instances recognize
isomorphisms, compositions, and open inclusions as open immersions, so these
pullbacks can be inferred directly from the public API.

## Gluing schemes

`Scheme.GlueData` extends mathlib's `CategoryTheory.GlueData` with the open
immersion condition. Its overlap maps and cocycle conditions have the same
form as those for ordinary schemes. The construction first glues sheaves
with values in `SmoothRingCat`, so all smooth operations descend along with
the ring operations. Limits of C∞-rings and their preservation by the
forgetful functor supply the underlying ring-valued sheaves.

The open inclusions of the pieces prove that the glued stalks are local
with real residues, and that the result is locally affine. `GlueData.glued`
is therefore an actual C∞ scheme. The inclusions `ι` are open immersions,
jointly cover the result, and satisfy the gluing equations. Compatible maps
out of the pieces descend through `desc`; `ι_desc` and `hom_ext` prove the
factorization and uniqueness. `gluedIsColimit` packages the universal
property as a multicoequalizer of the gluing diagram.

At both the smooth locally ringed space and scheme levels, the existence of
this colimit is registered as `HasMulticoequalizer`. The public `glued` and
`ι` are the same chosen object and legs as mathlib's generic gluing API;
`desc` uses `Multicoequalizer.desc`. `isoConstructed` compares this choice
with the concrete sheaf construction and identifies their inclusion maps.

## Comparing manifolds with schemes

`Manifold.locallyRingedSpace` equips mathlib's smooth-function sheaf with
its C∞ operations. `Manifold.euclideanIso` identifies this entire smooth
locally ringed space on ℝⁿ with `Spec C∞(ℝⁿ)`. The proof compares sections
on every open set and their restrictions, using the equivalence between
point-localization equality and equality of smooth germs. Smooth bump
functions supply global representatives near a chosen point.

`Manifold.scheme n M` then proves local affineness from coordinate charts.
The structure sheaf remains the actual smooth-function sheaf. Smooth maps
induce `schemeMap`, with identity and composition laws. This construction
currently accepts boundaryless finite-dimensional manifolds modeled on
`Fin n → ℝ`, with `M : Type` as in the reused real-valued sheaf API.
The local-affine proof requires neither global Hausdorffness nor
countability; the cutoff comparison is applied in Euclidean charts.

## The common spacetime interface

`LorentzMetric σ d M` is a smooth section of bilinear forms on the actual
tangent bundle. `LorentzConvention.timePositive` selects `(+,-,...,-)` and
`timeNegative` selects `(-,+,...,+)`. The convention is an explicit argument
to `minkowskiForm`, `LorentzMetric`, and `LorentzManifold`. Symmetry and nondegeneracy follow from the signature
condition. Pairing smooth vector fields yields a smooth real function in
the same C∞ algebra used by the structure sheaf. The metric is additional
data; the underlying smooth scheme does not depend on it.

`LorentzManifold.toScheme` applies the manifold construction uniformly.
`minkowski σ d` is a concrete instance of this interface, with one time and
`d` spatial coordinates. Its constant metric is smooth and nondegenerate;
`minkowskiSchemeIso` identifies its scheme with `Spec C∞(ℝ^(d+1))`.
`LorentzMetric.IsLocallyMinkowski` expresses the existence of local inertial
coordinates using the manifold derivative. Minkowski space satisfies this
condition by its global inertial coordinates. General Lorentz manifolds
are not required to satisfy it or to admit a global frame. For physical
four-dimensional spacetime, take `d = 3`.

Negation is constructed by `LorentzMetric.opposite` and
`LorentzManifold.opposite`. It preserves smoothness, symmetry, nondegeneracy,
and local Minkowski coordinates; the underlying scheme is unchanged.
Existing positive-time uses now pass `.timePositive` explicitly.

The `Minkowski` modules provide affine causal order, Lorentz and Poincaré
symmetries, observers and metric duality. `DifferentialForm` supplies the
metric-independent flat calculus and the exterior-power comparison. The
[Minkowski guide](special-relativity.md) describes the oriented Hodge operator
and its use by `SpecialRelativity`; shared geometry does not import physics.

## A two-piece gluing of the smooth affine line

`SmoothGeometry/GluingExample.lean` constructs the open restrictions
`x < 1` and `-1 < x` of the smooth affine line. Their intersection
`-1 < x < 1` is nonempty and proper in both pieces. The overlap
inclusions give a categorical pullback over the line. The off-diagonal
transition is the identity on that overlap, and mathlib's two-piece
gluing data construction supplies the diagonal maps and cocycle.

The resulting `Scheme.GlueData` gives open-immersion inclusions into the
glued scheme. Its compatible inclusions into the line descend to the
surjective morphism `toLine`. Its restriction to each canonical inclusion
recovers the original open inclusion, and its sheaf maps preserve every
smooth operation. The public API check exercises these constructions on
the populated datum.

`SmoothGeometry/OpenCover.lean` gives the general criterion. Let `g i : U i ⟶ Y`
be a jointly surjective family of open immersions and `h : Y ⟶ X` a morphism
such that every `g i ≫ h` is an open immersion. Then the stalk maps of `h` are
isomorphisms (`stalkMap_isIso_of_cover`) and `h` is an open map
(`isOpenMap_of_cover`). If `h` is injective on points it is an open immersion
(`isOpenImmersion_of_cover`), and if it is bijective on points it is an
isomorphism (`isIso_of_cover`). The statements hold for smooth locally ringed
spaces and for C∞ schemes. `Scheme.GlueData.desc_isOpenImmersion` and
`desc_isIso` are the case of the descent of open immersions out of a gluing.
Injectivity on points is a hypothesis: it is the statement that the overlaps
of the gluing datum are the whole intersections of the images.

`SmoothGeometry/GluingExampleIso.lean` proves that hypothesis for the two
half-lines. `overlapToPiece_ι` extracts from the gluing condition that the two
inclusions of the overlap agree in the gluing, so two points of the pieces
over the same point of the line are equal there (`ι_eq_of_val_eq`,
`toLine_injective`). Hence `toLine` is an open immersion and an isomorphism of
C∞ schemes. `gluedIsoLine : datum.glued ≅ line` has `toLine` as its morphism
and `fromLine` as its inverse, with `toLine_fromLine`, `fromLine_toLine` and
`pieceInclusion_fromLine`. `toLine_stalkMap_isIso` states the isomorphism of
the local rings, and `line_hom_ext` that a morphism out of the line is
determined by its restrictions to the two pieces.

The same module follows one section through the gluing. Sections of the line
and of its open pieces are smooth real functions; `sectionEval`, `pieceEval`
and `overlapEval` take their values, and `sectionEval_op` computes a smooth
operation on values. `coordinate` is the function `x ↦ x 0`, which is not
constant. Its restriction `pieceCoordinate i` has the value `y 0` at a point
`y` of the piece. The two restrictions agree on the overlap
(`pieceCoordinate_overlap`), where both have the value of the coordinate
(`overlapEval_pieceCoordinate`). `gluedCoordinate` is the corresponding global
section of the gluing: it restricts to `pieceCoordinate i` on each piece
(`ι_gluedCoordinate`), `fromLine` sends it to `coordinate`
(`fromLine_gluedCoordinate`), and it is the only global section with these
restrictions (`gluedCoordinate_unique`, from `glued_section_ext`). A smooth
operation `g` applied to it has the value `g (y 0)` on each piece
(`pieceEval_op_gluedCoordinate`).

| Claim | Main declarations | Source |
| --- | --- | --- |
| Open immersion and isomorphism on a cover | `LocallyRingedSpace.isOpenImmersion_of_cover`, `isIso_of_cover`, `Scheme.isIso_of_cover` | [OpenCover](../ProjectAinos/SmoothGeometry/OpenCover.lean) |
| Descent of open immersions | `Scheme.GlueData.desc_isOpenImmersion`, `desc_isIso` | [OpenCover](../ProjectAinos/SmoothGeometry/OpenCover.lean) |
| The gluing is the line | `toLine_bijective`, `toLine_isIso`, `gluedIsoLine`, `fromLine` | [GluingExampleIso](../ProjectAinos/SmoothGeometry/GluingExampleIso.lean) |
| Coordinate section | `pieceCoordinate_overlap`, `ι_gluedCoordinate`, `gluedCoordinate_unique` | [GluingExampleIso](../ProjectAinos/SmoothGeometry/GluingExampleIso.lean) |

The comparison is for this model. A Γ–Spec equivalence and the gluing of
morphisms of arbitrary schemes along an open cover are not used and not proved.

## GR 5.1: metric duality and the first chart regression

`Lorentzian/Dual.lean` constructs `LorentzMetric.flat` and `sharp` as
continuous linear equivalences on each actual tangent fibre and its
continuous dual. `flat_apply` identifies the forward map with the metric;
`sharp_flat` and `flat_sharp` prove the inverse laws. `flat_smooth` and
`sharp_smooth` assert smoothness as sections of the corresponding hom
bundles. The inverse proof uses smooth inversion in bundle charts and
pointwise nondegeneracy, without selecting a smooth orthonormal frame.

`lower` and `raise` act on smooth sections, with inverse laws
`raise_lower` and `lower_raise`. `inversePairing` produces a smooth scalar
from two smooth covectors. `flat_naturality` and `sharp_naturality` state
the transformation rules under a metric-preserving tangent equivalence:
covectors pull back, while raised vectors transform by its inverse.
Negating the metric negates both dual maps. On Minkowski space they agree
with the existing `Minkowski.flat` and `Minkowski.sharp`.

`Tensor/Bilinear.lean` provides fibrewise pullback of covariant bilinear
tensors, its identity/composition laws and symmetry preservation, and
smoothness of pullback and contraction against vectors.

`Tensor/Bundle.lean` builds arbitrary finite tangent/cotangent tensor types
by iterated native hom bundles. `Shape.mixed r s` has `r` contravariant
and `s` covariant slots, represented as multilinear maps on covectors and
vectors, respectively. `SmoothBundle` retains the model, actual fibres,
topology, and proved smooth-bundle instances needed by this recursion.
Only the local model is normed; no preferred norm on tangent fibres or
global trivialization is introduced. `LorentzMetric.toTensor` uses the
same smooth-section type as the constructed covariant two-tensor bundle.

`Shape.map` transports all slots through an invertible tangent map;
`pullback` uses its inverse. Identity, composition and inverse laws are
proved. These are fibrewise maps, including between different manifolds
with the same model. `coefficients` extracts local representations from
geometric smooth sections; their smoothness and transition rule hold in
every atlas trivialization on its domain.

`Tensor/HomMap.lean` proves smoothness of inversion and induced hom maps
in local bundle coordinates. `Tensor/Pullback.lean` uses these results
recursively to construct `Shape.pullbackField` for every tensor shape
along a smooth diffeomorphism between manifolds with the same model.
The tangent map is the actual manifold derivative; its inverse is proved
smooth rather than assumed. Pullback preserves smooth sections, reverses
composition, respects identity and inverse diffeomorphisms, and commutes
with full and partial contraction. Covector and covariant two-tensor
evaluation formulas explicitly use `mfderiv`. No isometry or global
frame is required.

`Tensor/HomPullback.lean` extends the hom-coordinate argument to arbitrary
continuous linear input/output maps over independent manifold models. Fixed-map
`precomp` and `postcomp` are continuous on native fibres; joint smoothness is
proved in normed bundle coordinates. No fibre norm or inverse map is introduced.
`Tensor/CovariantPullback.lean` uses this to construct
`Shape.covariantPullback I J n L` and `Shape.covariantPullbackField I J n f T`
for every rank `n` and smooth `f : C^∞⟮I, M; J, N⟯`. The source and target may
have different dimensions, and `mfderiv I J f` may be singular or zero.

- `covariantPullback_succ_apply` applies the tangent map to each successive slot;
  the one- and two-tensor field formulas explicitly use `mfderiv`.
- `contMDiffAt_covariantPullback` proves smoothness for smooth tangent-map families
  over a third manifold, with both bundle base points varying independently.
- `covariantPullbackField_id` and `covariantPullbackField_comp` prove identity and
  contravariant composition as equalities of smooth sections.
- `covariantPullbackField_const` makes every positive rank vanish for a constant map;
  rank zero is ordinary scalar composition.
- `covariantPullbackField_diffeomorph` identifies this construction with the existing
  mixed-tensor pullback on diffeomorphisms.

`Lorentzian/PullbackExamples.lean` restricts the nonlinear-chart metric along
`t ↦ (t,0)` to `(-1+4t²) dt²`, while standard Minkowski restricts to `-dt²`.
The induced tensor vanishes at `t=1/2`; this API produces a covariant tensor,
without asserting it is a Lorentz metric. The nonconstant singular projection
`(t,x) ↦ (t,0)` retains the time coefficient and kills spatial slots. Constant-map
pullback is also checked. Typed API examples use independent models and default
elaborator options. Exact SymPy checks cover these examples and nonlinear,
noninvertible composition with a nonsymmetric two-tensor.

`Tensor/Operations.lean` uses `Shape.slots` to represent a tensor with a
specified list of input types. The standard mixed shape lists cotangent slots
first, then tangent slots. `tensorProductField` concatenates the slot lists and
`evaluate_tensorProduct` identifies evaluation with the product of the two
scalar evaluations. The fibre operation is bilinear. A `SlotPermutation` records
adjacent exchanges and their compositions with typed input and output slots.
`evaluate_tensorMap` gives the induced reordering of arguments, and
`tensorMap_symm` proves the inverse law.

`contractSlotsField` brings the selected cotangent and tangent slots to the end
of the list and traces the induced cotangent endomorphism. The remaining
arguments stay in the specified order. `evaluate_contractSlots_eq_sum` proves
that the value is the sum over any tangent basis and its dual. Smoothness
follows by testing on local smooth arguments. Tensor product, permutation and
contraction commute with invertible tangent transport and diffeomorphism
pullback, so their smooth local coefficients obey the same transition rule.

`Tensor/OperationsExamples.lean` computes the nonsymmetric `dT ⊗ dX` product
after the nonlinear shear and contracts the first and third slots of
`∂ₓ ⊗ dt ⊗ dx` to obtain `dt`. The typed contracts include dimension-changing
pullback of an elementary covariant product. Exact SymPy checks the nonlinear
product and exchange laws and the mixed contraction in both charts.

`Tensor/BundleOperations.lean` proves that fibrewise composition of smooth
bundle homomorphisms is smooth: the intermediate coordinate maps cancel.
`Tensor/Contraction.lean` constructs intrinsic trace contraction and proves
coordinate invariance. The fibre trace functional is itself a smooth
section, permitting `SmoothBundle.partialContract` to retain other tensor
arguments. For example, it contracts a `(1,2)` tensor to a covector, and
`Shape.partialTrace_map` proves that the remaining slot transforms correctly.

`Lorentzian/Tensor.lean` raises and lowers an index of smooth covariant
two-tensors/tangent endomorphisms, with inverse laws. `contractField` is
the smooth scalar obtained by raising an index and taking the trace.
`contract_eq_sum_components` proves its coordinate expression
`∑ i, ∑ j, Bᵢⱼ gⁱʲ`, with inverse coefficients derived from `sharp`, not
supplied as separate arrays. Contraction commutes with metric-preserving
tangent coordinate maps. Contracting the metric gives `d+1`; contracting
an elementary covector tensor gives the inverse-metric pairing. Negating
the metric negates contraction of a fixed covariant tensor.

`Lorentzian/ChartExamples.lean` addresses [#43](https://github.com/MGYamada/ProjectAinos/issues/43)
on the plane. The standard chart has coordinates `(t,x)`; `inertialChart`
uses `(T,X) = (t,x+t²)`. They are actual open partial homeomorphisms in the
smooth maximal atlas, their overlap is the whole plane, and their
transition Jacobian is nonconstant. Pulling back `-dT²+dX²` gives

\[
g=(-1+4t^2)\,dt^2+4t\,dt\,dx+dx^2.
\]

The off-diagonal matrix entry is `2t`; the line element contains two
equal mixed terms. `metric_covariance` uses `mfderiv` of the actual
transition, and the component theorems evaluate the constructed metric.
`metric_nonconstant` and `jacobian_nonconstant` compare `(0,0)` and `(1,0)`.
The example also checks lowering, raising, and `opposite` across charts.
`metric_tensor_pullback` identifies the nonlinear metric with the
pullback of the Minkowski metric as an equality of smooth tensor fields.
Its `spacetime` instance uses `LorentzManifold.toScheme`, with the same
underlying smooth scheme as the standard Minkowski plane.
The smooth tensor `spatialTensor`, the pullback of `dX ⊗ dX`, has the
nonconstant coefficient matrix `[[4t²,2t],[2t,1]]`; its contraction with
the inverse metric is proved to be 1 in both charts. The arbitrary-tensor
contraction covariance theorem does not require symmetry of the tensor.
The subsequent curvature increment proves that this metric's intrinsic
Riemann, Ricci and scalar curvature vanish. Flatness is a theorem about this
example, with no flatness premise on an arbitrary Lorentz metric.

The conventions agree with [Tong, §§3.1.2–3.1.3](https://davidtong.org/teaching/general-relativity/grhtml/S3):
time is index zero, `timeNegative` has signature `(-,+,…)`, and lowering
means `v ↦ g(v,·)`. The shared API also supports `timePositive` by metric
negation. The positive-definite inner-product identification of a space
with its dual is not used to define the Lorentz musical maps.

`checks/LorentzGeometryAPI.lean` fixes the hypotheses and conclusions of
these interfaces in typed examples with default elaborator options. It
runs in required CI alongside the root-import and transitive axiom checks.
The separate Experiments workflow runs exact SymPy checks of the inverse
chart, Jacobian, metric, inverse metric, duality, full/partial tensor
contraction and sign reversal. It also checks Levi-Civita coefficients,
torsion and metric compatibility for the standard, nonlinear and conformal
examples, and the nonlinear chart's Hessian transformation term. Curvature
checks cover first Bianchi and metric symmetries, Ricci/scalar contractions,
both flat examples, the conformal scalar `-4 exp(-2x²)`, and nonzero
curvature covariance under the nonlinear shear:

```sh
experiments/.venv/bin/python -m pip install ./experiments
experiments/.venv/bin/python -m ainos_experiments.verify_lorentz_geometry
```

These computations use exact real symbolic expressions, with no random
parameters or numerical tolerances. The formal acceptance evidence is
the Lean proofs. The connection construction below is proved; its concrete
coordinate examples are still experimental checks at this point.

## GR 5.1: Lorentz Levi-Civita construction

`Lorentzian/Connection.lean` expresses metric compatibility directly with
`LorentzMetric.form` and mathlib's `CovariantDerivative`. A native connection
acts as `cov Y x v`, meaning differentiation of `Y` in direction `v` at `x`.
`IsLeviCivita` requires this compatibility and zero intrinsic torsion.
`IsLeviCivita.koszul_eq` derives the Koszul formula; `uniqueness` states
equality of action on fields differentiable at the evaluation point.
This qualification is necessary: the carrier does not constrain values on
nondifferentiable fields.

`Lorentzian/LeviCivita.lean` constructs `LorentzMetric.leviCivita`. Koszul
is proved tensorial in its first and third arguments, and `sharp` turns
the resulting covector into the connection's value. Local differentiable
extensions test nondegeneracy without a global frame. The construction
chooses zero at points where the differentiated field is not differentiable.
`isLeviCivita_leviCivita` proves metric compatibility and zero torsion;
`IsLeviCivita.eq_leviCivita` identifies any other such connection on
differentiable fields. `leviCivita_opposite` is equality of the constructed
connections under whole-metric sign reversal, since both use the same
zero extension.

`Tensor/Regularity.lean` proves that a finite-rank hom-bundle section is
`C^n` at a point if it sends every locally smooth section to a locally
`C^n` section. The proof uses bundle trivializations on neighborhoods,
with norms only on the models. `Lorentzian/Regularity.lean` applies this
criterion to the metric dual of the connection. Directional derivatives
and Lie brackets lose at most one derivative; the smooth `sharp` recovers
the connection. `contMDiffAt_leviCivita` maps locally `C^(n+1)` vector fields
to locally `C^n` hom sections for `n : ℕ∞`, including the smooth case.
`leviCivita_contMDiff` registers the native
`CovariantDerivative.ContMDiffCovariantDerivative` instance at each of these
orders. These regularity conclusions are proved from the smooth metric.

`Lorentzian/Christoffel.lean` works on the coordinate model, using its
canonical identification with its actual tangent bundle. `christoffel`
evaluates the constructed connection on constant coordinate fields;
`christoffel_eq` proves the inverse-metric formula. The coefficients are
smooth, symmetric in the lower indices and invariant under metric-sign
reversal. `leviCivita_model_coordinates` expresses the connection on any
differentiable coordinate vector field as its ordinary derivative plus
the Christoffel sum. `minkowski_christoffel` proves zero coefficients for
both flat signatures in every dimension.

`Lorentzian/ChartConnection.lean` extends these interfaces to arbitrary smooth
maximal-atlas charts. `chartTangentMap` and `chartField` use the actual tangent
derivative and its inverse on the chart source. `chartChristoffel_eq` derives
the inverse-metric formula, with scalar derivatives in the chart basis;
`chartChristoffel_contMDiffAt`, `chartChristoffel_symmetric`, and
`chartChristoffel_opposite` prove smoothness, lower-index symmetry and sign
invariance. `leviCivita_chart_coordinates` gives the derivative plus coefficient
formula for locally differentiable coordinate components. The standard model
chart agrees with `christoffel` via `chartChristoffel_model`.

For `τ = e' ∘ e.symm` and a point in both chart sources,
`chartChristoffel_transformation` proves
`∑ₗ Dτᵏₗ Γₑˡᵢⱼ = D²τᵏᵢⱼ + ∑ₐᵦ Γₑ'ᵏₐᵦ Dτᵃᵢ Dτᵇⱼ`.
The proof uses coordinate-field changes, locality of the native connection,
the Leibniz rule and the chain rule. Its hypotheses require only smooth atlas
membership and overlap membership, with no global chart or frame assumption.

`Lorentzian/ConnectionExamples.lean` computes the actual connection for
the two-chart shear example. `christoffel_shear` gives all eight
coefficients, with only `Γˣ_tt = 2` nonzero. `shear_hessian` differentiates
the actual transition Jacobian; `connection_shear_transformation` proves
that the Jacobian carries the connection term to this Hessian, as required
when the inertial connection coefficients vanish. `chartChristoffel_standard`
recovers those coefficients in the actual standard chart;
`chartChristoffel_inertial` proves zero coefficients for the same metric in
the actual inertial chart. `chart_transformation_shear` applies the general
overlap law to these two charts and recovers the Hessian identity.

`Lorentzian/Pullback.lean` constructs a Lorentz metric from a smooth map
with invertible tangent derivatives. It proves smoothness and signature on
the actual fibres, and identity, composition and sign-reversal laws. Global
bijectivity of the map is unnecessary. `Lorentzian/Naturality.lean` proves
`koszul_naturality` by the scalar chain rule and Lie-bracket naturality.
`leviCivita_naturality_of_metric` then states that a smooth metric-preserving
map intertwines the two constructed connections on pulled-back fields
differentiable at the target point. Its derivative invertibility is derived
from metric nondegeneracy and equal dimension. The input fields are total
sections with only local differentiability hypotheses.

`Manifold/OpenSubset.lean` proves an open inclusion is a smooth local
diffeomorphism with invertible tangent derivative. `Lorentzian/Restriction.lean`
uses this to construct `restrict U`, and `leviCivita_restrict` identifies its
connection with the ambient connection on restricted differentiable fields.
Both the metric and connection statements use the derivative of the
inclusion to identify the actual tangent fibres. The nonlinear metric agrees
with the general metric pullback, and `leviCivita_shear_naturality` verifies
the native connection identity for arbitrary differentiable target fields.

The construction works for either Lorentz convention with the existing
smooth metric interface. It assumes no Hausdorffness, orientation, time
orientation, global frame or positive-definite tangent metric. The
Koszul existence/uniqueness argument adapts mathlib's Riemannian proof,
replacing its positive-definite duality with proved Lorentz `flat`/`sharp`.
The regularity proof is supplied separately here.

Typed contracts in `checks/LorentzGeometryAPI.lean` cover the carrier,
compatibility equation, full Koszul formula, torsion, uniqueness, sign
reversal, local/native finite and smooth regularity, the full coordinate
formula on models and manifold charts, the complete overlap transformation
law, metric pullback, naturality, open restriction and the nonlinear
connection examples at default elaborator settings. The stage B connection
proof endpoints are implemented and merged into `main`.
The curvature endpoints below are implemented. Finite-segment parallel
transport and local inertial coordinates are described in the motion section.
Native form bundles, pullback, exterior differentiation, wedge, density and
oriented volume and smooth Hodge are described below. Fixed-background Maxwell
and the Newtonian motion limit are implemented in stages F and G; sourced
field-action dynamics and the Newtonian gravitational field-equation limit
remain separate targets in the [research trilogy](cinfty-general-relativity.md).

## GR 5.1: curvature and intrinsic contractions

`Tensor/Tensoriality.lean` supplies `ContMDiffTensorialAt` for operations on
locally `Cⁿ` sections (`n : ℕ∞`). Linearity over scalar germs implies
locality and dependence only on the fibre value. Local frames prove this
without global extensions, a global frame, or Hausdorff assumptions.
`mkHom` constructs a continuous linear map on the actual fibre.

`Lorentzian/Curvature.lean` defines the field commutator using the native
Levi-Civita connection, with convention

\[
R(X,Y)Z=\nabla_X\nabla_Y Z-\nabla_Y\nabla_X Z-\nabla_{[X,Y]}Z.
\]

Its scalar-linearity and additivity in all three locally `C²` arguments
are proved. `curvatureField_pointwise` proves independence of the chosen
extensions; `curvature` bundles the resulting continuous trilinear map.
`curvature_apply` identifies it with the commutator under exactly the three
local `C²` hypotheses. `curvature_swap` and `curvature_first_bianchi` state
antisymmetry and the algebraic cyclic identity on arbitrary tangent vectors.
Reversing the entire metric leaves this tensor unchanged.

`CurvatureRegularity.lean` proves smoothness by testing the iterated native
hom bundle on local smooth fields. `curvatureBundle` retains the recursively
constructed model instances, and `curvatureTensor` bundles the section and
its proof. Only the model carries a norm; no preferred tangent norm is added.

`CurvatureNaturality.lean` differentiates connection naturality using locality
and finite regularity. `curvature_naturality_of_metric` states that the
derivative of a smooth metric-preserving map intertwines the two curvature
tensors. The map need not be globally bijective. `curvature_pullback` applies
this to the constructed pullback metric.

`ChartCurvature.lean` extracts `Rˡᵢⱼₖ = (R(∂ᵢ,∂ⱼ)∂ₖ)ˡ` from the native tensor.
The coefficients are smooth on chart sources. `chartCurvature_eq_fderiv`
proves their Christoffel formula with ordinary derivatives of chart-coordinate
representatives, including the two quadratic connection terms.
`chartCurvature_transformation` proves the full overlap law with one output
Jacobian and three input Jacobians, with no Hessian term. The hypotheses are
only smooth maximal-atlas membership and membership in the overlap.
`curvature_model_coordinates` recovers the standard model-coordinate formula.

The operator sign agrees with [Tong, §3.2.2, equations (3.106)–(3.107)](https://davidtong.org/teaching/general-relativity/grhtml/S3).
The argument order is explicit: `chartCurvature e x l i j k` corresponds to
Tong's `Rˡₖᵢⱼ`, because his differentiated-vector index comes first among the
three lower indices. Our trace `Ric(u,v)=tr(w ↦ R(w,u)v)` gives his Ricci
components with the two arguments exchanged; the proved Ricci symmetry
identifies them. The scalar contraction therefore has the same sign.

`ChartDerivatives.lean` transports scalar first and mixed second derivatives
through a smooth chart under local `C¹`/`C²` hypotheses. `CurvatureSymmetry.lean`
uses differentiated metric compatibility and scalar derivative commutation
to prove `curvature_skewAdjoint` and `curvature_pair_swap`. Together with the
algebraic first Bianchi identity these give `curvature_pair_interchange`.
No normal coordinates, positive-definite tangent metric or global frame
are assumed in these proofs.

`Ricci.lean` fixes the contraction as
`Ric(u,v) = trace (w ↦ R(w,u)v)`. `ricciTensor` is a smooth covariant
two-tensor and `scalarCurvature` its smooth inverse-metric contraction.
`ricci_eq_sum` and `scalarCurvature_eq_sum` give the component sums in any
chosen tangent equivalence, while the naturality lemmas prove invariance
under equivalences intertwining curvature (and preserving the metric for
the scalar). Metric-sign reversal preserves Ricci and negates scalar
curvature. `ricci_symmetric` proves symmetry using curvature pair interchange
and a Lorentz signature basis chosen only at the evaluation point.

`CurvatureExamples.lean` proves zero Riemann, Ricci and scalar curvature for
standard Minkowski in every dimension and both signatures, and for the
nonlinear shear metric whose connection has `Γˣ_tt = 2`. These evaluate the
constructed tensor, not a separate coordinate array. Typed API examples
fix the commutator, native carriers, Bianchi, contraction order, naturality,
signs and these concrete conclusions at default elaborator settings.

`Conformal.lean` constructs `g.conformal φ = exp(2φ) g` for a smooth real
function on the manifold, preserving either Lorentz signature.
`ConformalExample.lean` specializes this to `φ(t,x)=x²`. It derives the native
connection, all sixteen Riemann components, the Ricci matrix `diag(2,-2)`,
the inverse metric from `sharp`, and scalar curvature `-4 exp(-2x²)`.
`christoffel_origin`, `curvature_origin_ne_zero` and `scalarCurvature_origin`
prove zero connection coefficients but nonzero curvature and scalar `-4`
at the origin. This is pointwise vanishing of the connection coefficients,
not vanishing on a neighborhood.

Stage C's proof endpoints are implemented and merged into `main`.
Typed API examples fix the chart formula/overlap hypotheses, all metric
symmetries, Ricci symmetry, conformal signature construction and curved
example conclusions. Exact experiments independently check these examples
and nonzero curvature covariance under the shear. The differential and
contracted Bianchi identities were deferred to 5.2; they are proved in F10
([below](#the-covariant-derivative-of-the-curvature-and-the-einstein-tensor)).

The completed stage C increment passes the warning-free full Lean build
(9,265 jobs), root-import check, all six API checks and the transitive audit
of 6,541 declarations (2,376 in smooth geometry), using only `propext`,
`Classical.choice` and `Quot.sound`. The installed-package exact Lorentz
experiment also passes. These checks do not imply completion of the later
motion, curved-form or Newtonian-limit stages.

## GR 5.1: differentiation along curves and geodesic initial data

`AlongCurve.lean` defines `curveVelocity γ t` using the manifold derivative
and the canonical unit vector in the parameter line. `AlongField γ` is
`∀ t, TangentSpace I (γ t)`, including at self-intersections or zero velocity.
`covariantAlong` takes values in these same native fibres. Its defining
chart formula is the derivative of the vector components plus the native
connection acting on the frozen coordinate field in the velocity direction.

`chartCovariantAlong_eq` proves independence of the chart on overlaps,
assuming only smooth maximal-atlas membership, membership of the curve point
in both sources, differentiability of the curve and of its source-chart
vector components. There is no immersion or ambient-extension assumption.
`covariantAlong_eq_chart` uses intrinsic differentiability of the along
field as a map into the total tangent bundle. `covariantAlong_ambient`
recovers the original Levi-Civita derivative for the restriction of a
differentiable ambient field. `covariantAlong_congr`, `covariantAlong_add`
and `covariantAlong_smul` give germ locality, additivity and Leibniz.
`covariantAlong_coordinates` proves, in every admissible chart,

```text
(D_t V)^k = d(V^k)/dt + Σᵢⱼ Γ^k_ij(q) q̇^i V^j.
```

`AlongCurveMetric.lean` proves `hasDerivAt_pairing_along` for two arbitrary
differentiable along fields on a differentiable curve:

```text
d g(V,W)/dt = g(D_t V,W) + g(V,D_t W).
```

The proof uses smooth coordinate bilinear forms and the native connection's
metric compatibility. Normed structures are confined to the coordinate
models, with no norm or positive-definite inner product imposed on tangent
fibres. No orientation, time orientation or global frame is needed.

`CurveFamily.lean` defines directional velocities of a two-parameter manifold
family by `mfderiv`. A jointly C² family has C¹ velocity fields into the actual
tangent bundle. `curveVelocity_family` identifies them with differentiation
along parameter paths, and `covariantAlong_family_interchange` proves
`D_ε ∂t Γ = D_t ∂ε Γ` using symmetry of second derivatives and zero torsion.
Parameter velocities may vanish and the family need not be an immersion.
Slice regularity and C¹ variation-field regularity are proved. An actual
endpoint fixed for nearby variation parameters has zero native variation
field there, by locality of `mfderiv`. `contDiffAt_pairing_along` preserves
the finite regularity of arbitrary native fields along a curve.
The theorem supports both Lorentz conventions and introduces no physical
imports. Its typed contracts are in `LorentzGeometryAPI`; the
[GR guide](general-relativity.md) describes the resulting actual action
derivatives, intrinsic boundary terms, subdivision and both stationarity
equivalences. `AccelerationRegularity` derives continuous native acceleration
and extension of the geodesic equation to closures. `LocalizedVariation`
identifies actual chart-family velocities with the specified test fields;
`VariationTesting` proves the nondegenerate fundamental lemma by local scalar
tests realized by those families. These shared modules import no physics.

`AlongCurveReparam.lean` proves `C^(n+1)` velocity regularity, the chain rule
for `curveVelocity`, and both reparametrization identities:

```text
D_t^(γ∘r)(V∘r) = r' (D_s^γ V)∘r
D_t^(γ∘r) velocity(γ∘r) = r'' velocity(γ)∘r + (r')² (D_s^γ velocity γ)∘r.
```

These hold even at zeros of `r'`; neither statement divides by parameter
speed. General parameter changes have the displayed acceleration term.
`IsGeodesicOn.affine_reparam` proves preservation of the affine equation for
`r(t)=at+b`, including reversal and constant maps. `IsParallelOn.reparam`
preserves parallelism for differentiable parameter maps into the original
parameter domain.

`Geodesic.lean` defines `IsParallelOn` by native differentiability and zero
covariant derivative. `IsGeodesicOn` requires local `C²` regularity and
`D_t velocity γ=0`. Regularity is at each parameter, rather than only within
the parameter set; closed-interval uses therefore require regular extensions
at endpoints. `parallel_pairing_eq` proves preservation on convex parameter
sets. `IsGeodesicOn.metric_velocity_eq`, `timelike_iff` and `null_norm_iff`
give velocity-norm, timelike and zero-norm preservation for both metric
conventions. Zero norm alone does not assert that the velocity is nonzero.
`covariantAcceleration_coordinates` and
`geodesic_equation_iff_coordinates` prove the arbitrary-chart second-order ODE.

`MotionODE.lean` derives `chartGeodesicField`, the phase field
`(q,v) ↦ (v,−Γ(q)(v,v))`, from these connection coefficients.
`chartGeodesicField_contDiffAt` proves smoothness on the chart target.
`exists_chartGeodesic` uses mathlib's local ODE theorem, shrinks the time
interval to keep position in the chart, and derives `C²` phase regularity.
`isGeodesicOn_of_chartPhase` and `hasDerivAt_chartPhase` bridge that phase
equation to native geodesics. The public intrinsic endpoints are:

- `exists_geodesic g p v t₀`: a positive `ε`, a curve through `p` with the
  specified actual tangent velocity `v`, and the geodesic equation on
  `(t₀−ε,t₀+ε)`. The base-point equality transporting the initial vector is
  explicit in the statement.
- `geodesic_unique`: geodesics defined near `t₀`, with equal initial positions
  and transported tangent velocities, agree on a neighborhood of `t₀`.
  Local Lipschitzness is derived from the smooth phase field.

These are local existence and germ uniqueness. Neither completeness nor a
common global existence interval is asserted.

`MotionExamples.lean` proves that model-coordinate differentiation agrees
with ordinary differentiation for standard Minkowski, and every affine line
is an affine geodesic for both signatures. For the nonlinear shear metric,
`inertialTimePath_geodesic` proves that `(s,−s²)` is an affine geodesic.
`parallelField_parallel` proves that `(a,b−2sa)` is parallel along it, and
`parallelField_inertial_components` evaluates the field in the actual
inertial chart to the constant vector `(a,b)`.
`parallelTransport_model` evaluates the constructed endpoint equivalence as
`(v₀,v₁) ↦ (v₀,v₁−2(s₁−s₀)v₀)` in the nonlinear coordinates.
The separate exact experiment checks these equations, metric preservation,
transport subdivision/reversal, a nonzero null parallel field, and both
terms in the acceleration reparametrization formula, including a change
with zero parameter speed.

`AlongCurveRegularity.lean` proves that native along-field differentiability
is equivalent to differentiability of components in any admissible chart,
assuming a differentiable base curve. It also reconstructs `Cⁿ` fields for
`n : ℕ∞`; smooth charts do not silently supply analytic regularity.
`ParallelLocal.lean` constructs the linear operator
`A(t)v = -Γ(γ(t))(q'(t),v)` and proves the equivalence of parallelism with
`V' = A(t)V`. For a `C²` curve, the operator is locally `C¹`. The augmented
ODE `(τ,w)' = (1,A(τ)w)` gives `exists_parallel_local`, and local operator
bounds give `parallel_unique_local`. Neither existence nor a Lipschitz
bound is an extra public hypothesis.

`exists_localParallelFrame` solves for a finite chart basis and takes a
common interval for all initial vectors. Pairing with its columns and
nondegeneracy prove `parallel_eq_iff` on arbitrary convex parameter sets.
`IsParallelOn.eq_zero_iff` and `IsGeodesicOn.null_iff` then preserve
nonvanishing as well as zero metric norm. These proofs do not assume a
global frame, global chart, or global Hausdorffness of the manifold.

`ParallelExtension.lean` glues local frames using this uniqueness and
propagates the construction along connected parameter intervals.
`exists_parallelFrameOn_segment` and `exists_parallel_on_segment` provide
solutions on the whole `uIcc a b` of a prescribed `C²` curve, with regularity
at each point (including endpoint extensions). They do not assert geodesic
completeness. `ParallelTransport.lean` exports:

- `parallelTransport hγ : TangentSpace I (γ a) ≃L[ℝ] TangentSpace I (γ b)`;
- `parallelTransport_apply_eq`: every parallel field computes that map;
- `parallelTransport_metric` and `parallelTransport_self`;
- `parallelTransport_reverse`: exchanging endpoints gives the inverse;
- `parallelTransport_trans`: subdivision at `b ∈ uIcc a c` composes maps;
- `parallelTransport_reparam`: a `C²` parameter map whose image stays in
  the original segment preserves endpoint transport, even with zero speed.

`RegularPath.lean` packages a segment regular on `[0,1]` with named endpoints.
`toPath` retains its actual continuous path, and `tangentCongr` uses equality
alone to identify endpoint tangent fibres. `transport_apply_eq`,
`exists_parallel`, `parallel_unique` and `transport_reverse` compare its
transport with native parallel fields. `parallelPath` is a continuous path
in the tangent bundle; `parallelPath_map` proves it projects to `toPath`.

`PiecewisePath.lean` constructs finite concatenations, including corners,
with their usual half-interval parametrization as continuous paths.
The type retains the chosen finite decomposition; it is not a quotient
by homotopy or equality of parametrized paths. `HasParallelLift` is an
independent predicate: each piece carries a native parallel field, and
the endpoint vectors agree at every junction. The main endpoints are:

- `hasParallelLift_iff` and `existsUnique_parallelLift`: the composed map
  gives exactly the possible endpoint of a matching family of parallel fields;
- `transport_unique`: compatibility with those fields uniquely determines
  the transport map;
- `exists_continuous_parallelLift`: matching fields concatenate to an
  actual continuous tangent-bundle path projecting to the underlying path;
- `transport_trans`, `transport_assoc`, `transport_reverse` and
  `transport_metric`: composition, regrouping, inversion and metric preservation;
- `toPath_reverse`: reversing the pieces reverses the actual continuous path.

`PathExamples.lean` proves component preservation for model affine segments
and broken lines for both signatures, including the corner from `(0,0)`
through `(1,0)` to `(1,1)`. Velocities need not match at junctions. The exact
experiment also verifies segment ODEs and the ordered composition/reversal
of four transports around a rectangle in `exp(2x²)(-dt²+dx²)`. That curved
rectangle calculation is an experimental check, not a formal holonomy claim.

### Local inertial coordinates at a point

`QuadraticChart.exists_manifoldChart` in `Manifold/QuadraticChart.lean`
constructs an actual smooth maximal-atlas chart with a prescribed invertible transition Jacobian and
symmetric Hessian at the center. The quadratic polynomial and its inverse
are locally analytic; this does not impose analyticity on the manifold.

`Lorentzian.LocalInertial` obtains the Hessian from the native connection's
chart coefficients. `chartChristoffelBilinear` is a coordinate bilinear map,
not a tensor: its transformation includes the transition Hessian. The
positive quadratic correction `½ L(Γ(q-q₀,q-q₀))` makes the new connection
coefficients vanish at the base point. The main endpoints are:

- `exists_chart_tangent_christoffel`: a prescribed tangent equivalence is
  the chart derivative and all Christoffel coefficients vanish at the point;
- `chartComponent_fderiv_eq_zero`: zero connection coefficients imply zero
  first coordinate derivatives of the metric, by metric compatibility;
- `IsInertialChartAt`: a smooth chart centered at the point with `g = η`,
  `Γ = 0` and `∂g = 0` there;
- `exists_inertialChart_for_equiv`: realizes any specified Lorentz basis;
- `exists_inertialChart`: every smooth Lorentz metric has such a chart at
  each point, in either signature convention and without global-frame,
  Hausdorffness or completeness assumptions.

`LocalInertialExamples` recovers the exact shear `(t,x+t²)` as the correction
at the origin. The ordinary chart for `exp(2x²)(-dt²+dx²)` is inertial at the
origin even though the native curvature is nonzero and the scalar curvature
is `-4`. Thus pointwise `IsInertialChartAt` is distinct from the existing
`IsLocallyMinkowski` condition on open neighborhoods. The exact experiment
checks the metric and connection transformations at nonzero base points,
with a nontrivial Lorentz basis and both metric-sign conventions.

### Local flatness and parallel coframe integration

`LocalFlatness` proves `IsLocallyMinkowski.curvature_eq_zero`. The proof uses
`curvature_restrict` on actual tangent fibres and curvature naturality under
the local metric-preserving diffeomorphism. `Manifold.OpenTangent` proves
that open-inclusion derivatives are identities in inherited model
coordinates, constructs diffeomorphisms from arbitrary maximal-atlas charts,
and supplies restrictions with convex targets. `isLocallyMinkowski_of_charts`
connects metric normalization on entire chart sources to the original
open-submanifold definition.

`Manifold.TangentSpace` states the instance `tangentSpace_isNormableSpace`: the topology of a
tangent space is the topology of a norm, for the module structure of the tangent space. Mathlib
derives this instance with the module structure of the model space, and instance search does not
find it; without it `ContinuousLinearMap.flip` does not apply to a bilinear map of tangent spaces.
No norm is chosen. The library sets no `backward` option and no heartbeat limit; the repairs that
made this possible are described in
[note G02](smooth-geometry-notes.md#g02-the-tangent-space-of-a-vector-space-is-the-space-and-lean-has-to-be-told).

The converse separates construction and integration of a parallel
coframe. Both steps are now proved; the integration API is:

- `ClosedCoframe.exists_smooth_primitive` integrates a smooth closed
  vector-valued one-form on an open convex coordinate domain using Poincaré's
  lemma; its derivative is the original form everywhere on that domain.
- `ClosedCoframe.exists_chart` and `exists_manifoldChart` use invertibility
  to give actual smooth local charts with the prescribed derivative on
  their entire sources, including a smooth inverse.
- `IsParallelChartCoframeOn` states `∂θ(q)(u)(v) = θ(q)(Γ(q)(u,v))`, using
  the native connection's chart coefficients. Torsion-freeness proves that
  this coframe is closed.
- `exists_chart_zeroChristoffel_of_parallelCoframe` integrates a smooth
  invertible parallel coframe and proves all connection coefficients vanish
  throughout the resulting chart source.
- `chartComponent_eq_of_zeroChristoffel` and `chartPairing_eq_of_zeroChristoffel`
  propagate constancy on a connected chart target via metric compatibility.
- `exists_minkowskiChart_of_parallelCoframe` needs metric normalization only
  at the base point and constructs a Minkowski chart on an open neighborhood.

`LocalFlatnessExamples` proves the shear Jacobian is a nonconstant smooth
parallel coframe and obtains `IsLocallyMinkowski` through this integration
theorem. It also proves the conformal metric is not locally Minkowski,
despite having an inertial chart at every point. Exact checks integrate the
shear coframe from arbitrary base points and evaluate the nonzero conformal
curvature matrix obstructing an invertible parallel coframe.

### Linear ODE dependence on coefficient curves

`ODE.Volterra`, in namespace `LinearODE`, supplies the analytic step toward
constructing the parallel coframe. `Curve E` is the Banach space
`C(unitInterval, E)`. The bounded linear map `volterra` sends a coefficient
curve `A` to `f ↦ ∫₀ᵗ A(s) f(s) ds`, with `‖volterra A‖ ≤ ‖A‖`.

- `equationOperator_isInvertible` derives invertibility of `id - volterra A`
  from `‖A‖ < 1`, using a convergent geometric series. Invertibility is a
  conclusion, not a premise.
- `solutionOperator A` is continuous and linear in the initial value.
  `solution_integral_eq`, `solution_initial` and `solution_hasDerivWithinAt`
  give the integral equation, initial condition and ODE, including one-sided
  derivatives at the endpoints.
- `eq_solution_of_hasDerivAt` proves uniqueness from continuity on the closed
  interval and the differential equation on its interior; no endpoint
  differentiability assumption is needed.
- `solution_norm_le` gives `‖solutionOperator A y‖ ≤ ‖y‖ / (1 - ‖A‖)`.
- `solution_contDiffAt` proves joint smooth dependence on the entire coefficient
  curve in supremum norm and on the initial value. `solution_family_contDiffAt`
  composes this with smooth parameter maps; `solution_eval_contDiffAt` evaluates
  at any fixed time.
- `VolterraExamples` proves `LinearODE.solution_ramp`: that the resolvent-defined solution
  for `A(t) = (t/2) id` is `exp(t²/4) y₀`, in any real Banach space. The zero
  coefficient specialization is also proved. Exact SymPy checks verify the
  nonconstant equation and its parameter-variation equation.

`ODE.VolterraInverse` removes the bound on the coefficient. The Volterra
operator is quasi-nilpotent: `volterra_pow_apply_norm_le` gives
`‖(volterra A)ⁿ f(t)‖ ≤ ‖A‖ⁿ tⁿ/n! · ‖f‖` and `volterra_pow_norm_le` gives
`‖(volterra A)ⁿ‖ ≤ ‖A‖ⁿ/n!`. Hence `isInvertible_equationOperator` holds for
every coefficient curve, and `solutionOperator_integral_eq`,
`solutionOperator_hasDerivWithinAt`, `eq_solutionOperator_of_integral_eq`,
`eq_solutionOperator_of_hasDerivAt` repeat the statements above without the
hypothesis `‖A‖ < 1`. `solutionOperator_contDiff` is smoothness on the whole
space of coefficient curves.

`ODE.Propagator` treats a continuous coefficient `A : C(ℝ, E →L[ℝ] E)` on the
real line. `propagator A t s` is the value at the end of the unit interval of
the solution for the coefficient `σ ↦ (t − s) • A (s + σ (t − s))`, for every
pair of real times; no interval is subdivided.

- `propagator_self`, `hasDerivAt_propagator_apply`, `hasDerivAt_propagator`:
  `Φ(s, s) = 1` and `∂ₜ Φ(t, s) = A(t) Φ(t, s)` at every real `t`.
- `eq_propagator_apply_of_hasDerivAt`: a function that is continuous between
  `s` and `t` and solves the equation in the open interval has the value
  `Φ(t, s) f(s)` at `t`.
- `propagator_comp`, `propagator_isInvertible`: `Φ(t, s) Φ(s, r) = Φ(t, r)`,
  and `Φ(s, t)` is the inverse of `Φ(t, s)`.
- `continuous_propagator`: joint continuity in the two times, in the operator
  norm.
- `propagator_contDiff`: if `A : P × ℝ → V →L[ℝ] V` is smooth in a parameter
  and the time, the propagator is smooth in the parameter and the two times.
  `P` and `V` are in the same universe. `propagator_contDiff_of_contDiff` is
  the case without a parameter.
- `propagator_const`: for a constant coefficient the propagator is
  `exp ((t − s) A₀)`.

`ODE.PropagatorExpansion` treats a coefficient that is small between two
times `s ≤ t`, `‖A(r)‖ ≤ g`.

- `norm_propagator_apply_le`: `‖Φ(t, s) y‖ ≤ e^{g (t − s)} ‖y‖`, by Gronwall's
  inequality.
- `firstOrder A s y` and `secondOrder A s y` are the terms `∫ A(r) y dr` and
  `∫ A(r) (∫ A(x) y dx) dr` of the series of the propagator in the
  coefficient. `norm_propagator_apply_sub_secondOrder_le`:
  `‖Φ(t, s) y − y − firstOrder − secondOrder‖ ≤ e^{g (t − s)} (g (t − s))³/6 · ‖y‖`.
  `norm_propagator_apply_sub_le` and `norm_propagator_apply_sub_firstOrder_le`
  are the bounds of first and second order.
- `integralCoefficient A s t` is `∫ A` as an operator and
  `secondOrderOperator A s t` the term of second order as an operator
  (`firstOrder_eq`, `secondOrder_eq`). In finite dimension
  `traceCLM_secondOrderOperator` states that the trace of the term of second
  order is half the trace of the square of `integralCoefficient A s t`. The
  proof differentiates both sides in `t` and uses `tr (XY) = tr (YX)`; no
  double integral is exchanged.

`ODE.PropagatorBound`: `norm_le_mul_exp_integral_of_norm_deriv_le`, Gronwall's
inequality with a continuous coefficient, `‖f(t)‖ ≤ ‖f(s)‖ exp ∫ₛᵗ a` if
`‖f′‖ ≤ a ‖f‖`; `norm_propagator_apply_le_exp_integral`,
`‖Φ(t, s) y‖ ≤ ‖y‖ exp ∫ₛᵗ ‖A‖`, a bound that does not depend on the length of
the interval when `‖A‖` is integrable; `propagator_apply_comm`, a continuous
linear map that commutes with the coefficient commutes with the propagator.

`ODE.PropagatorDeformation` treats a coefficient `A(p, s)` that is smooth in a
parameter `p` and the time `s`, with a continuous linear map `J` that commutes
with it and `∂A/∂p = c(p) J ∂A/∂s`. This is the Cauchy–Riemann equation of
`A(p, s) = a(s + i η(p))` for a holomorphic `a`, with `J` the multiplication by
`i` and `c = η′`.

- `hasDerivAt_propagator_apply_param`:
  `∂/∂p Φ_p(s₁, s₀) y₀ = c(p) J (A(p, s₁) Φ_p(s₁, s₀) y₀ − Φ_p(s₁, s₀) A(p, s₀) y₀)`.
  The difference of the two sides solves the equation in `s₁` and vanishes at
  `s₁ = s₀`; the equation of `∂Φ/∂p` is the symmetry of the second derivative.
- `norm_propagator_apply_sub_le_of_deformation`: the propagators for two
  parameters differ by at most `C K (M₁ + M₀) ‖y₀‖ (p₁ − p₀)`, for bounds `C` of
  `c`, `K` of the propagators and `M₀`, `M₁` of the coefficient at the two ends.

`ODE.PropagatorDet` gives the determinant of the propagator on a
finite-dimensional space.

- `hasDerivAt_det_of_eq_one`: Jacobi's formula at the identity. If
  `M(t₀) = 1`, the derivative of `det M(t)` at `t₀` is the trace of the
  derivative of `M`. The proof uses `Matrix.det_one_add_smul`.
- `hasDerivAt_det_propagator` and `det_propagator`: `δ′ = tr A · δ` for
  `δ(t) = det Φ(t, s)`, and Liouville's formula
  `det Φ(t, s) = exp (∫ₛᵗ tr A)`. A coefficient of trace zero has a
  propagator of determinant one (`det_propagator_of_trace_eq_zero`).
- `eq_propagator_comp_of_hasDerivAt`, `det_eq_det_mul_exp_integral_trace`: a
  family of operators that solves `M′ = A(t) M` between two times is
  `Φ(t, s) M(s)`, and its determinant is multiplied by the same factor.

`ODE.FlowVariation` and `ODE.LocalFlow` treat a given family of solutions of
an autonomous equation `ẋ = X(x)`. Nothing is constructed.

- `hasDerivAt_fderiv_of_isLocalFlow`: if `Φ(t, x)` is twice continuously
  differentiable at a point and solves the equation near it, the derivative
  `M(t) = D_x Φ(t, x)` solves the variational equation `M′ = DX(Φ) M`. The
  proof exchanges the derivatives in `t` and `x`.
- `eq_of_hasDerivAt_of_eq`: two solutions of an equation with a continuously
  differentiable field that agree at one time agree at every time between
  which both are defined. The field is Lipschitz on the compact union of the
  two curves, and Mathlib's uniqueness theorem applies.
- `IsLocalFlowOn X Φ Ω`: `Ω` is an open set of times and points, `Φ` is twice
  continuously differentiable on it and solves the equation, `Φ(0, x) = x`,
  and the times of each point form an interval that contains zero.
  `isLocalFlowOn_translation` and `isLocalFlowOn_linear` (the propagator of a
  constant coefficient) are instances.
- `IsLocalFlowOn.eq_of_hasDerivAt`, `injOn`, `apply_add`: a solution through a
  point is the solution of the family, `Φ(t, ·)` is injective on its domain,
  and a family defined for all times and points satisfies
  `Φ(s + t, x) = Φ(s, Φ(t, x))`.
- `IsLocalFlowOn.det_fderiv`: in finite dimension
  `det D_x Φ(t, x) = exp (∫₀ᵗ tr DX(Φ(s, x)) ds)`.
- `IsLocalFlowOn.measure_image` and `measurePreserving`: if `tr DX = 0`, the
  map `Φ(t, ·)` preserves the Haar measure of every measurable set in its
  domain, and a family defined for all times and points is measure
  preserving. This is Liouville's theorem for a given flow.
  `measurePreserving_propagator_const` is the case of a linear field of trace
  zero.

- `IsLocalFlowOn.measure_image_of_trace_eq`: a flow of a field of constant
  divergence `d` multiplies the measure of every measurable set in its domain
  by `exp (d t)`.

`ODE.Superposition` treats the operator `γ ↦ X ∘ γ` on `C(K, E)` for a compact
`K`. `Superposition.hasFDerivAt_comp`: for a continuously differentiable `X`
its derivative at `γ` is `η ↦ (t ↦ DX(γ(t)) η(t))`, by the mean value
inequality on the segments from `γ(t)` to `η(t)`.
`Superposition.comp_contDiff`: for a smooth `X` the operator is smooth.
`ContinuousFamily.slices_contDiff` does not apply, since there the inner
function is fixed.

`ODE.FlowEquation` writes the solution of `ẋ = X(x)` through `x`, traversed
up to the time `τ`, as a curve on the unit interval:
`IsFlowCurve X τ x γ` is `γ(σ) = x + τ ∫₀^σ X(γ)`. The time is a factor in the
equation, so one space of curves serves for all times of both signs.

- `IsFlowCurve.eq`: a flow curve is unique, for a continuously differentiable
  field. `IsFlowCurve.rescale`: `σ ↦ γ(cσ)` is the flow curve of the time `cτ`.
  `exists_isFlowCurve_of_hasDerivWithinAt`: a solution between the times `0`
  and `t` gives a flow curve of the time `t`.
- `equation X` is the map `((τ, x), γ) ↦ γ − x − τ ∫ X(γ)`. It is smooth
  (`equation_contDiff`), and its derivative in `γ` is the equation operator of
  the linear equation with the coefficient `τ DX(γ)` (`equation_fderiv_inr`),
  which is invertible for every coefficient.
- `exists_local_family`: every flow curve belongs to a smooth family of flow
  curves on an open set of times and points.

`ODE.Flow` defines the flow of a vector field on a Banach space.
`flowDomain X` is the set of `(t, x)` that have a flow curve, and
`flow X (t, x)` is the value of that curve at the end of the unit interval.

- `mem_flowDomain_iff`: `(t, x)` is in the domain if and only if a solution
  through `x` exists between the times `0` and `t`. The section of the domain
  at a point is an interval that contains zero
  (`mem_flowDomain_of_mem_uIcc`); it is the maximal interval of existence.
- `isOpen_flowDomain`, `contDiffOn_flow`: for a smooth field the domain is
  open and the flow is smooth in the time and the point together.
- `hasDerivAt_flow`, `flow_integral_eq`: the flow solves the equation.
  `flow_eq_of_hasDerivWithinAt`: a solution between `0` and `t` is the flow.
- `isLocalFlowOn_flow`: the flow is a local flow, so the variational equation,
  the determinant formula and the statements about volume above apply to it.

`ODE.FlowComplete`:

- `neg_mem_flowDomain`, `flow_add`: `Φ(−t, Φ(t, x)) = x`, and
  `Φ(s + t, x) = Φ(t, Φ(s, x))` whenever the right-hand side is defined, for
  times of any signs.
- `mem_flowDomain_of_isCompact`: a solution that stays in a compact set, as
  long as it exists, exists for the whole time.
- `flowDomain_eq_univ_of_norm_le`: on a finite-dimensional space a field with
  `‖X(x)‖ ≤ a + b ‖x‖` has a flow defined for all times and points, by
  Gronwall's inequality (`norm_flow_le_gronwallBound`).
- `flowDomain_linear`, `flow_linear`: the flow of a linear field is the
  propagator of the constant coefficient.

`ODE.FlowBounded`:

- `flowDomain_eq_univ_of_bounded_inl`: a field on `ι ⊕ κ → ℝ` whose components
  `Sum.inl i` are bounded, and whose components `Sum.inr k` are bounded where
  the co-ordinates `Sum.inl i` are bounded, has a flow defined for all times
  and points. The relativistic motion of a charge is of this kind.

`ODE.LinearMotion`:

- `linearVelocity A u₀` is the solution of `u′ = A u` with `u(0) = u₀` for a
  bounded operator `A`, and `linearMotion A x₀ u₀` is the curve with this
  velocity from `x₀`; both are smooth, and the solution is unique
  (`eq_linearVelocity_of_hasDerivAt`).
- `linearVelocity_eq_of_cube`, `linearMotion_eq_of_cube`: if `A³ = κ A` and
  `s′ = 1 + κ c`, `c′ = s`, `C′ = c` with the value zero at `0`, then
  `u = u₀ + s A u₀ + c A² u₀` and `x = x₀ + τ u₀ + c A u₀ + C A² u₀`.
- `linearVelocity_add`: for `A₁ A₂ = A₂ A₁ = 0` the solution of the sum is the
  sum of the solutions minus the initial value.
- `linearVelocity_eq_of_projection`: for a projection `P` that commutes with
  `A`, with `A² = κ₁` on its range and `A² = κ₂` on its kernel, the solution is
  the sum of the two solutions of the kind `A³ = κ A`.
- `linearVelocity_eq_of_quartic`: if `(A² − a²)(A² + b²) = 0` and
  `a² + b² ≠ 0`, then `hyperbolicProjection A a b = (A² + b²)/(a² + b²)` is
  such a projection, with `κ₁ = a²` and `κ₂ = −b²`.

`ODE.FlowInvariant`: a function whose derivative vanishes between two times
takes the same value at them (`eq_of_hasDerivAt_zero`), so a quantity whose
derivative vanishes along every solution is constant along the flow
(`flow_invariant`), also when the flow is not defined for all times.

`ODE.ScalarFlow`: a smooth field `g` on the line with `0 < g ≤ C` has a flow
for all times (`flowDomain_eq_univ_of_abs_le`). The time
`scalarTime g φ = ∫₀^φ ds/g(s)` and the solution through `0` are inverse to
each other (`scalarTime_flow`, `flow_scalarTime`), so the solution is a
strictly increasing bijection of the line. If `g` has the period `P`, the
solution advances by `P` in the time `scalarTime g P`
(`flow_add_scalarTime_of_periodic`).

The shared module `SpecialFunctions.JacobiElliptic` applies this flow theorem.
The historical import `SmoothGeometry.ODE.JacobiElliptic` exports its declarations. For `k² < 1` the amplitude `am k` is the solution
through `0` of `φ′ = √(1 − k² sin² φ)`, and `sn = sin ∘ am`, `cn = cos ∘ am`,
`dn = √(1 − k² sn²)`. Mathlib has Weierstrass's `℘` and no Jacobi functions.

- `hasDerivAt_sn`, `hasDerivAt_cn`, `hasDerivAt_dn`: `sn′ = cn dn`,
  `cn′ = −sn dn`, `dn′ = −k² sn cn`; the functions are smooth.
- `sn_sq_add_cn_sq`, `dn_sq`, `dn_pos`: `sn² + cn² = 1`, `dn² + k² sn² = 1`
  and `dn > 0`.
- `am_surjective`, `strictMono_am`: the amplitude is an increasing bijection
  of the line.
- `am_add_halfPeriod`: `am (u + 2K) = am u + π` with
  `halfPeriod k = ∫₀^π dφ/√(1 − k² sin² φ)`, so `sn` and `cn` change sign and
  `dn` is unchanged after `2K`.

The modulus is real with `k² < 1`. The addition theorems, the complex period
and the case `k² = 1` are not treated.

`ODE.Averaging` is the method of averaging to the first order.

- `abs_integral_mul_sin_le`, `abs_integral_mul_cos_le`: for `|φ| ≤ M₀` and
  `|φ′| ≤ M₁` on `[0, t]`, `|∫₀ᵗ φ(s) sin ωs ds| ≤ (2 M₀ + t M₁)/ω`;
  `norm_integral_sin_smul_le` and `norm_integral_cos_smul_le` are the
  statements for amplitudes with values in a Banach space.
- `norm_sub_le_of_norm_integral_le`: if `ż = F(z) + r(t)` and `Ż = F(Z)` on
  `[0, L]` with the same initial value, `F` is Lipschitz with the constant `K`
  on a set that contains both curves, and `‖∫₀ᵗ r‖ ≤ δ`, then
  `‖z(t) − Z(t)‖ ≤ δ e^{K t}`. The perturbation `r` need not be small.
- `exists_forall_norm_sub_le`: for a field `F` and amplitudes `P_j`, `Q_j` of
  class `C¹`, a perturbation
  `Σ_j (cos (n_j γ t) P_j(z) + sin (n_j γ t) Q_j(z))` (`harmonics`) and a compact
  convex set `K`, there is a constant `C` such that for every `γ > 0` the
  two solutions differ by at most `C/γ` on `[0, L]` while they stay in `K`.
- `gronwallBound_le_mul_exp`: `gronwallBound δ K ε t ≤ (δ + ε L) e^{K L}` for
  `0 ≤ t ≤ L`.

`ODE.SlowParameter` is the estimate behind adiabatic invariance, for a field
`X(z, λ)` on a normed space with a parameter `λ = Λ(εt)`.

- `abs_sub_le_of_corrector`: let `I` and `G` be differentiable on a set `S` of
  pairs `(z, λ)`, with `dI(X, 0) = 0` and `dI(0, 1) = dG(X, 0)` there: `I` is
  invariant under the field with a fixed parameter, and its derivative in the
  parameter is the derivative of `G` along that field. If `|Λ′| ≤ L₁`,
  `|Λ″| ≤ L₂` on `[0, T]` and `|G| ≤ M₀`, `|∂G/∂λ| ≤ M₁` on `S`, then a
  solution of `ż = X(z, Λ(εt))` that stays in `S` on `[0, T/ε]` has
  `|I(t) − I(0)| ≤ ε (T (L₂ M₀ + L₁² M₁) + 2 L₁ M₀)` there. The function
  `I − ε Λ′(εt) G` has a derivative of the order `ε²` along the solution.

Only the first order of the method is treated: the constant is not explicit,
and there is no statement on times of the order of the frequency.

`ODE.CommutingFlows`: two smooth fields `A`, `B` commute if
`DA(y) B(y) = DB(y) A(y)`.

- `fderiv_flow_apply_of_commute`: `D_x Φ_A(t, x) B(x) = B(Φ_A(t, x))`. The
  difference of the two sides solves a linear equation along the solution, by
  the variational equation, and vanishes at the time zero.
- `flow_add_of_commute`: the flow of `A + B` is `Φ_A(T, Φ_B(T, x))`, where
  these are defined. `flow_smul_field`: the flow of `c A` at the time `T` is
  the flow of `A` at the time `c T`.

`ODE.JointFlow`: for fields `Xᵢ`, `i ∈ ι`, `jointField X t = Σᵢ tᵢ Xᵢ` and
`jointFlow X t x` is the flow of this field at the time `1`.

- `PairwiseCommute X`; `jointField_commute`: the fields `Σᵢ tᵢ Xᵢ` commute.
- `IsInvariantSet X M`: the flows of all these fields are defined for all
  times on `M` and preserve it; `isInvariantSet_of_isCompact`: a compact set
  that the flows preserve, as long as they exist.
- `jointFlow_add`, `jointFlow_zero`, `jointFlow_neg`, `jointFlow_comm`: on an
  invariant set the joint flow is an action of `ℝ^ι`. `jointFlow_smul`:
  `r ↦ jointFlow X (r • t) x` is the solution of `Σᵢ tᵢ Xᵢ` through `x`.

`ODE.JointFlowSmooth`: `contDiffAt_jointFlow`, the joint flow is smooth in the
times and the point together, from the flow of the field
`(t, y) ↦ (0, Σᵢ tᵢ Xᵢ(y))`; `hasFDerivAt_jointFlow_zero`: at `(0, x)` its
derivative is `(τ, v) ↦ Σᵢ τᵢ Xᵢ(x) + v`.

`ODE.PeriodLattice`: `IsLocallyFree X M` states that at every point `x` of `M`
the map `t ↦ g^t x` is injective near zero and that `M` is, near `x`, its image
of a neighbourhood of zero.

- `exists_jointFlow_eq`: on a connected set the joint flow is transitive.
- `periods`: the subgroup of the `t` with `g^t x = x`; `jointFlow_eq_iff`,
  `periods_eq`, `discreteTopology_periods`.
- `span_periods_eq_top`, `exists_basis_periods`: on a compact set the periods
  span `ℝ^ι` and are the integer combinations of a basis.
- `exists_torus_chart`: there is a basis `b` such that for every `x ∈ M` the
  map `θ ↦ g^{Σ θᵢ bᵢ} x` is onto `M`, two angles give the same point exactly
  when they differ by integers, and the flow of `Σᵢ sᵢ Xᵢ` at the time `r` adds
  `r b⁻¹ s` to the angles.

`ODE.LevelSetFlow`: for a smooth `F : E → ℝ^κ` on a space of finite dimension
with `DF(y) Xᵢ(y) = 0` and `dim E = |ι| + |κ|`.

- `flow_jointField_levelSet`, `isInvariantSet_levelSet`: `F` is constant along
  the flows, and a compact level set is invariant with complete flows.
- `exists_levelSet_chart`, `isLocallyFree_levelSet`: at a point `x` of a level
  set at which `DF(x)` is onto and the `Xᵢ(x)` are linearly independent,
  `(t, s) ↦ g^t (x + L s)` is a homeomorphism near zero, `L` being a right
  inverse of `DF(x)`, and its points with `s ≠ 0` are not on the level set; so
  the joint flow is locally free on such a level set.
- `exists_torus_chart_levelSet`: the conclusion of `exists_torus_chart` for a
  compact connected regular level set of commuting fields.
- `exists_levelSet_chart_of_transversal`: the chart `(t, s) ↦ g^t (x + L s)` for
  any linear map `L` for which `DF(x) ∘ L` is invertible; its inverse is smooth
  at `x`, and `s ↦ F(x + L s)` is injective on the parameters of the chart.

`ODE.LevelSetTube`: `exists_isInvariantSet_tube`. If the level set `F = c` is
compact, there are an open set `U` with compact closure that contains it and
an open set `B` of values that contains `c` such that `F⁻¹(B) ∩ U` is invariant
with complete flows. `U` is a bounded neighbourhood and `B` is the complement
of the image of its frontier; a level set over `B` does not meet the frontier.

`ODE.PeriodFamily`: `hasFDerivAt_jointFlow`, the derivative
`(τ, v) ↦ Σᵢ τᵢ Xᵢ(g^t y) + D_y g^t(y) v` of the joint flow at a point of an
invariant set; `exists_period_family`, for a point `x` of an open invariant
set, a transversal `L` and a period `b` of `x` there is a function `e` of the
parameter of the transversal, smooth at zero with `e(0) = b`, such that
`g^{e(s)} (x + L s) = x + L s` for small `s`.

`PeriodicInjective`: `exists_injOn_modPeriod`. Let `Ψ(J, φ)` have the period
`T` in each angle for `J` in an open set, and let it be continuous and locally
injective at the points `(J₀, φ)`. If two angles give the same point
`Ψ(J₀, ·)` only when they differ by multiples of `T`, then on a neighbourhood
of `J₀` the equality `Ψ(J, φ) = Ψ(J′, φ′)` holds only when `J = J′` and the
angles differ by multiples of `T`.

The field is smooth on the whole space. A field that is smooth only on an
open set, and a field that depends on the time, are not treated.

`Volterra` and `ContinuousFamily` are stated for types in arbitrary universes.

### Smooth radial families and local coordinate coefficients

`ODE.ContinuousFamily` proves the missing lift into continuous-function
spaces. `hasStrictFDerivAt` assembles a continuous family of pointwise
derivatives into a strict Fréchet derivative, using a uniform mean-value
bound. `slices_contDiff_nat` and `slices_contDiff` show that restricting one
variable of a jointly regular function to a fixed compact continuous family
preserves finite regularity and smoothness in the other variable. The target
carries the supremum norm.

For a smooth coordinate coefficient field `Γ`, `ODE.Radial` defines
`radialCoefficient Γ hΓ p x t = -Γ(p + t • x) x`. The curve-valued coefficient
map is smooth and vanishes at zero displacement. `exists_radial_ball` gives
a positive common radius on which the coefficients have norm less than one,
the endpoint maps `radialEndpoint` are invertible, and both endpoints and
inverses `radialCoframe` are smooth. Their value at the center is the identity.
Each defining solution satisfies the radial vector-transport ODE.

`RadialReparam` supplies `LinearODE.radialEndpoint_on_ray`, which proves
`P(s • x)v = solution_x(v)(s)` for `s ∈ [0,1]`, including zero, by differential
equation uniqueness. `radialEndpoint_fderiv_radial` then identifies the
radial derivative as `DP(x)(x)v = -Γ(p+x)(x, P(x)v)`. This is an equation for
the constructed smooth endpoint family, not an extra premise.

`SmoothExtension` supplies `Manifold.exists_contDiff_extension_near_compact`,
which extends
vector-valued `C^n` functions off an open domain, preserving their values on
an open neighborhood of a compact subset. `RadialFrame` proves smoothness
of bundled native chart coefficients and constructs a smooth extension
agreeing near a chosen point. This makes the radial construction applicable
to local chart data without a global chart premise. No norm is added to
native tangent fibres, and no analytic metric or global frame is assumed.

`RadialExamples` proves `LinearODE.quadratic_radialEndpoint`: the nonconstant real
connection `Γ(q)(u,v) = -(q/2)uv` has endpoint `exp(x²/4)v` for every prefix
of the unit ray. Exact SymPy checks also verify the radial ODE, rescaling,
radial endpoint derivative, inverse coframe and its one-dimensional equation.

### Flat radial frames and parallel coframe existence

`ODE.FlatFrame` supplies the curvature argument. `IsFlatConnectionOn Γ U`
fixes the coordinate convention
`DᵤΓ(v)w - DᵥΓ(u)w + Γ(u)(Γ(v)w) - Γ(v)(Γ(u)w) = 0` on `U`.
`frameDefect Γ P = DP + ΓP` measures parallelness. Its antisymmetric
derivative follows from Hessian symmetry and flatness. The radial condition
then gives a homogeneous equation for `t Q(t x)(u)v`, with zero initial
value. `eq_zero_of_radial_equation` applies the existing ODE uniqueness
theorem; it does not divide by time at the center.

- `radialEndpoint_fderiv_of_flat` proves `DP(x)(u)v = -Γ(x)(u, P(x)v)`
  in **every** direction on a ball with small radial coefficients.
- `inverse_fderiv_of_parallel` differentiates the inverse frame;
  `radialCoframe_fderiv_of_flat` gives `Dθ(x)(u)v = θ(x)(Γ(x)(u,v))`.
- `exists_parallel_radialCoframe` constructs a positive smaller ball inside
  any neighborhood where the coordinate curvature vanishes. On that ball
  the coframe is smooth, invertible, parallel and identity at the center.
  No parallelness or invertibility premise is imposed on an unconstructed frame.
- `Lorentzian.FlatFrameExamples` identifies the nonzero native shear
  coefficients with a flat coordinate connection, proves its constructed
  endpoint is `P(x)v = (v₀, v₁ - 2x₀v₀)`, and applies the general existence
  theorem. The exact experiment checks both directions of the frame and
  coframe equations and the curvature term's sign for a curved example.

### Native curvature and the local flatness equivalence

`ODE.CoordinateCurvature` bundles the coefficient expression as the trilinear
map `coefficientCurvature`. A finite coordinate basis tests its vanishing,
and agreement of coefficient germs preserves it. `Lorentzian.FlatConnection`
proves `coefficientCurvature_basis`: these components equal the native
`chartCurvature`, in the established `R(∂ᵢ,∂ⱼ)∂ₖ` order. Differentiating the
bundled Christoffel coefficients commutes with evaluation on fixed basis
vectors and output coordinates. The existing native component formula then
supplies the equality, including its derivative and quadratic terms.
`isFlatConnectionOn_of_curvature_eq_zero` derives the full coordinate flatness
condition from native curvature, without an extra compatibility premise.

`LocalFlatnessConverse` supplies
`LorentzMetric.exists_minkowskiChart_of_curvature_eq_zero_near`, requiring
only `∀ᶠ x in 𝓝 p, g.curvature x = 0`.
It starts from an inertial chart at `p`, whose center is zero and whose metric
there is already normalized. A smooth extension preserves the connection
germ, and a sufficiently small ball lies inside the flat neighborhood. The
radial construction gives a smooth invertible parallel coframe with identity
at the center. Its normalization therefore comes from the chosen inertial
chart, and integration supplies an actual smooth maximal-atlas chart whose
metric is Minkowski on its entire source.

`isLocallyMinkowski_of_curvature_eq_zero` and
`isLocallyMinkowski_iff_curvature_eq_zero` finish the converse and equivalence:
`g.IsLocallyMinkowski ↔ ∀ p, g.curvature p = 0`. The shear example obtains
local Minkowski geometry directly from native zero curvature. Standard
Minkowski in every dimension and both signatures also specializes the
criterion; the curved conformal example remains an obstruction.

`FlatTransport` proves the path-independence consequence explicitly. Metric
normalization throughout a chart makes all its Christoffel coefficients
zero. `RegularPath.transport_eq_chart` and `PiecewisePath.transport_eq_chart`
identify intrinsic transport with the endpoint chart tangent equivalences.
The latter includes corners and uses containment of the actual continuous
path, not a premise on a chosen parallel lift. Two finite piecewise paths
in the same flat chart with the same endpoints therefore have equal
transport, regardless of their decompositions.
`LorentzMetric.exists_pathIndependent_neighborhood` derives such an open
neighborhood from native curvature zero near the point. The nonlinear
shear example proves this equality for arbitrary piecewise paths.

Stage D's principal proof endpoints are implemented and merged into `main`.
No global frame, global chart, analytic metric, Hausdorff premise or
geodesic completeness is assumed or concluded. Stage E's principal particle-
variation endpoints are now implemented; see the [GR guide](general-relativity.md).
The curved Maxwell and Newtonian trajectory theorems are implemented in
stages F and G. See the [GR guide](general-relativity.md).

The stage D checkpoint passed the warning-free full build (9,302 jobs), root-import
check, all six API checks and the transitive audit of 7,309 declarations
(3,144 in smooth geometry). Only `propext`, `Classical.choice` and `Quot.sound`
are permitted. Typed contracts fix the native along-field carrier, overlap
and regularity hypotheses, metric and parameter-change formulas, coordinate
ODE, local initial-value existence/uniqueness, finite-segment transport,
its laws, piecewise paths and continuous lifts, nonzero-null preservation,
prescribed-basis inertial charts, their first and second derivative contracts,
curvature restriction, coframe integration with explicit hypotheses,
the Volterra equation, ODE uniqueness, norm bound and smooth dependence,
compact-family smoothness, radial rescaling and differentiation, local
connection-coefficient extension, full parallelness under the explicit
flatness equation, constructed parallel-coframe existence, native coordinate
curvature, the near-point Minkowski chart, the full local-flatness equivalence,
local path independence for actual piecewise paths,
and flat/curved concrete examples at default elaborator settings. The installed-package
exact Lorentz experiment also passed at that checkpoint. These historical checks
validate stage D; later stage checks are recorded separately.

## GR 5.1: native differential-form foundation

`DifferentialForm/Bundle.lean` equips mathlib's existing continuous-alternating-
map bundle topology with a proved smooth vector-bundle structure. Its
transition maps are polynomial compositions of the original smooth bundle
transitions. `NativeForm I M k` assigns an alternating covector to each actual
tangent fibre; `SmoothForm I M k` is a smooth section of that bundle. No norm
or global frame is installed on native tangent fibres. These constructions
need neither a metric nor finite-dimensional models.

`NativeCoordinates` extracts `coefficients` in any atlas tangent
trivialization. `coefficients_change` proves the overlap law,
`SmoothForm.contMDiffAt_coefficients` proves local smoothness, and
`coefficients_recover` reconstructs the native value from the coefficients.
`smoothGlue` in `NativeGluing.lean` glues
compatible local native forms over any open cover. Each representative only
needs to be smooth on its own open set; there is no global extension
hypothesis. `smoothGlue_apply` and `smoothForm_ext_of_cover` prove restriction
and uniqueness.

`smoothPullback` in `NativePullback.lean` precomposes every slot with `mfderiv I J f x`.
It is a smooth section for every smooth map, including different source and
target dimensions and singular derivatives. `smoothPullback_id`,
`smoothPullback_comp`, `smoothPullbackLinear` and `smoothPullback_const` give
identity, contravariant composition, linearity and annihilation of positive
degrees by constant maps. In degree zero `nativePullback_degreeZero` is
ordinary scalar composition. The names are in `DifferentialForm`, not nested
module namespaces.

`ofFlat` in `NativeFlat.lean` identifies flat smooth forms with native sections on the
model manifold. `nativePullback_flat` and `smoothPullback_flat` prove exact
agreement with the existing flat pullback. `NativeExamples` computes
`dX = dx + 2t dt` under the nonlinear shear, the preserved area form,
`2t dt` on the time axis, and the vanishing area pullback under a nonconstant
singular projection. These are identities of actual smooth native sections.
Typed contracts in `checks/SmoothGeometryAPI.lean` fix the bundle, pullback,
coefficient, gluing and flat-comparison interfaces. Exact SymPy checks cover
the same nonlinear and dimension-changing examples and a variable two-form
under nonlinear composition.

Native exterior differentiation, wedge, volume density and oriented volume
and smooth Hodge are described below. The curved Maxwell component bridge was
delivered with #52 and is described in the [electrodynamics guide](electrodynamics.md).
Maxwell action variation remains in §4.2/#44, and Einstein dynamics
remains in §5.2.

### Exterior differentiation and chart independence

`NativeChart.lean` works on boundaryless smooth real manifolds with arbitrary
normed model spaces. `chartCoefficients` pulls a native form through the actual
inverse chart derivative, and `chartLift` uses the forward derivative.
Their source/target inverse laws and transition laws are proved only where
the charts are defined. The supporting `contMDiffAt_nativePullback` theorem
requires smoothness of the map at the source point and of the native section
at its image. No global smooth extension of a chart is assumed.

`NativeExteriorDerivative.lean` differentiates those model coefficients using
mathlib's normalized `extDeriv`. `chartExtDeriv_transition` proves the overlap
law using the derivative pullback theorem and locality. Then
`chartLift_extDeriv_independent` identifies the native results on overlaps.
`nativeExteriorDerivative` chooses a chart at each point, while
`nativeExteriorDerivative_eq_chart` proves equality with every smooth chart
containing it. This supplies the regularity proof for the bundled
`smoothExteriorDerivative`, rather than storing regularity or chart
independence as assumptions.

`chartCoefficients_smoothExteriorDerivative` is the standard coordinate
formula in every chart. `smoothExteriorDerivative_squared` proves `d² = 0`;
`smoothExteriorDerivativeLinear` and `smoothExteriorDerivative_local` give
linearity and dependence only on the local native section. The construction
requires no metric, orientation, global frame, finite-dimensional model or
Hausdorff assumption. The operator API currently acts on smooth sections.

`NativeNaturality.lean` proves `smoothExteriorDerivative_pullback` for every
smooth map between these manifolds, with independent source and target model
spaces. In coordinates the proof includes the map derivative and all of its
second derivatives; the alternating cancellation comes from mathlib's model
pullback theorem. No inverse derivative is required.
`smoothExteriorDerivative_flat` is exact agreement with the existing flat
operator.

`NativeExteriorExamples.lean` proves `d(T dX) = dT ∧ dX` in the plane, with a
nonzero exact area form and `d(area) = 0`. The nonlinear shear, its actual
maximal-atlas chart, and the time-axis inclusion test naturality. The SymPy
runner independently checks forward/inverse shear coefficients and exterior
derivatives, a three-variable mixed-partial cancellation for `d²`, and a
nonlinear two-to-three-dimensional pullback of a nonconstant potential.
Typed contracts in `checks/SmoothGeometryAPI.lean` fix local regularity,
chart independence, the coordinate formula, linearity/locality, `d²`, general
pullback naturality and flat specialization.

### Native exterior product and graded calculus

`NativeWedge.lean` works on boundaryless smooth manifolds modeled on
`Fin n → ℝ`, including the Lorentz manifolds used by GR. This is a local
coordinate-model requirement, not a global chart or frame. The preceding
native derivative and pullback API still supports arbitrary normed models.

`nativeWedge` lifts the existing normalized coordinate product through an
actual chart. `chartWedge_transition`, `chartLift_wedge_independent` and
`nativeWedge_eq_chart` prove chart independence even for nonsmooth native
forms. Local coefficient regularity and `wedge_contDiffAt` prove smoothness
before bundling `smoothWedge`. `chartCoefficients_smoothWedge` gives the
coordinate formula in every smooth chart. No native tangent norm, metric,
orientation, global frame or Hausdorff hypothesis is introduced.

`smoothWedgeLinear` supplies bilinearity. `smoothPullback_wedge` holds for
every smooth map, including noninvertible maps and different source/target
dimensions. The flat `pullback_wedge` was generalized to these dimensions
without changing its name or existing specializations. `smoothWedge_flat`
proves exact agreement with the established determinant normalization.

`NativeWedgeCalculus.lean` proves `smoothWedge_assoc`, `smoothWedge_comm`,
`smoothWedge_one_left`, `smoothWedge_one_right` and
`smoothExteriorDerivative_wedge`. These are equalities of smooth native
sections. `smoothDegreeCast` explicitly transports degrees such as
`(k+1)+l = (k+l)+1`; it does not introduce a premise about the forms.
The commutation sign is `(-1)^(k*l)` and the Leibniz sign is `(-1)^k`.
`smoothOne` is the constant degree-zero scalar one, whose derivative is zero.

`NativeWedgeExamples.lean` identifies the wedge of the temporal/spatial
covectors with the previously constructed nonzero area form. It checks the
actual nonlinear maximal-atlas chart, the shear, a nonconstant singular
projection and the one-dimensional time-axis inclusion. A direct
three-dimensional derivative proves
`d(dx⁰ ∧ x¹ dx²) = -dx⁰ ∧ dx¹ ∧ dx²`, detecting the minus sign with a
nonzero result. Default-option typed API examples cover the full product
interfaces. Exact SymPy additionally tests variable one-forms, graded
Leibniz and wedge naturality under a nonlinear two-to-three-dimensional map.

### Lorentz density and oriented volume

`MetricDensity.value B v` is `sqrt(abs(det(gram B v)))` for a bilinear form
and an ordered vector family. `value_change` proves multiplication by
`abs(det A)` under every change matrix, including singular ones. No
orientation or norm is involved. `LorentzMetric.volumeDensity` applies this
construction directly to the metric on each actual tangent fibre.
`volumeDensity_basis_pos` proves positivity on bases from nondegeneracy;
`volumeDensity_naturality` proves invariance under metric-preserving tangent
maps, and `opposite_volumeDensity` handles whole-metric sign reversal.

`chartDensity` is the familiar `sqrt(abs(det(g_ij)))`.
`volumeDensity_eq_chart` expresses intrinsic density using the determinant
of the input vectors' chart components. `chartDensity_transition` proves
the absolute-Jacobian change rule between any two actual smooth charts,
with explicit source membership. `chartDensity_contMDiffAt` proves local
smoothness using the nonzero determinant and its finite polynomial
expansion. Only the finite coordinate model carries a norm.

`OrientedAtlas` records a covering chart around each point and a constant
sign of square one in each chart. Its overlap condition compares those signs
using the transition Jacobian. This is explicit local orientation data;
it requires no global frame or chart, metric, or Hausdorff premise.
`localVolume` multiplies the pulled-back normalized coordinate top form by
the signed density. `localVolume_compatible` proves equality on overlaps,
so `volumeForm` uses the existing native gluing theorem to construct a
`SmoothForm` of degree `d+1`. Neither smoothness nor existence of the global
volume is an input premise.

`chartCoefficients_volumeForm` gives the signed-density coefficient in every
selected chart. `volumeForm_ne_zero` and `abs_volumeForm` identify a nonzero
oriented top form whose absolute value is precisely the intrinsic density.
`volumeForm_reverse` negates it when the orientation is reversed;
`opposite_volumeForm` leaves it unchanged when the whole metric is negated.
`volumeForm_eq_of_compatible` proves that a different signed chart cover
describing the same orientation gives the same native section.

`VolumeExamples.lean` proves density one and the standard coordinate volume
for Minkowski metrics in either sign convention and every dimension. The
nonlinear shear metric has unit density in both actual atlas charts, and a
cover made from the inertial charts gives the same volume. The conformal
plane `exp(2x²)(-dt²+dx²)` has density `exp(2x²)` and that coefficient times
the existing native area form. An orientation-reversing rescaling has
volume `-6` and density `6`. These interfaces have default-option typed
examples in `checks/LorentzGeometryAPI.lean`. The exact SymPy runner also
checks a nonlinear chart with nonconstant, negative Jacobian determinant.
The density divergence formula `divergence_density` is described under
[Intrinsic divergence and the positive density](#intrinsic-divergence-and-the-positive-density).

### Native Lorentz Hodge

`FiniteDual.lean` works on finite-dimensional Hausdorff topological real
vector spaces. These hypotheses hold for each tangent fibre; they impose
no global Hausdorff hypothesis on the manifold. Algebraic alternating forms
are continuous by a finite coordinate expansion, giving `finiteToExterior`.
Its pullback theorem holds between independent vector spaces, even for
singular linear maps. No norm is placed on a native fibre. `FiniteWedge`
constructs the intrinsic exterior product and proves it equals the existing
chart-defined `nativeWedge` at every point.

The volume in `DifferentialForm.hodge` is a functional on top exterior
covectors. `VolumeNormalization` builds that functional from a nonzero volume
vector: `volumeNormalizer` sends `r • vol` to `r`. In particular, multiplying
the volume form by `r` multiplies this functional by `r⁻¹` and Hodge by `r`.
This reciprocal normalization is proved explicitly. `FiniteHodge` transports
the established wedge-normalized algebraic Hodge to continuous forms and
proves the wedge equation and uniqueness. `finiteDegreeCast` records the
degree arithmetic. `HodgeTransport` proves naturality between separate
finite topological fibres and the inverse-metric precomposition identity
used in the local regularity proof below.

`LorentzMetric.coMetric` is the inverse metric on the algebraic cotangent
space, derived from the existing `sharp`; its bijectivity and symmetry are
proved. `hodgeFiber g o x hkl` is a linear equivalence of the actual
alternating tangent fibres. `formPairing` is the exterior-power pairing of
the inverse metric. `hodgeFiber_wedge` and `hodgeFiber_unique` prove
`α ∧ ⋆β = ⟨α,β⟩ vol`, after the explicit degree transport. The unbundled
`nativeHodge` satisfies the same equality with the existing native wedge.

`hodgeFiber_reverse` negates the operator when only orientation is reversed.
`hodgeFiber_opposite` multiplies it by `(-1)^k` under whole-metric reversal.
`hodgeFiber_naturality` applies to tangent equivalences that preserve both
the metric and the oriented volume; it does not claim that Hodge commutes
with arbitrary pullback.

`HodgeFlat.lean` proves exact agreement with `Minkowski.hodgeFiber` in every
dimension and either metric convention, including the top-degree casts and
volume normalization. `HodgeExamples.lean` transfers all six four-dimensional
coordinate two-form signs and the two-form square `-1`. The nonconstant
shear metric has proved Hodge transport under its actual tangent shear map,
using separately proved metric and oriented-volume preservation.
Default-option typed contracts are in `checks/LorentzGeometryAPI.lean`.
Exact SymPy independently checks all degrees under a nonlinear chart with
nonconstant Jacobian magnitude, both Jacobian orientations, whole-metric
reversal, and the conformal plane.

`HodgeFormula` proves a reference-metric formula on independent finite
topological fibres. `ChartDuality` identifies the chart metric `G` with native
metric duality conjugated by the actual chart tangent equivalence.
`chartSharp` is its inverse, smooth on the chart source by smooth inversion.
For a selected signed chart, `HodgeCoordinates` proves

```
⋆g α = sρ ⋆η (α.compContinuousLinearMap (G⁻¹η))
```

Here `s` is the chart's orientation sign, `ρ = sqrt(abs(det G))`, and `η`
is the time-negative reference metric even when `g` uses the opposite
signature. Precomposition acts in every covariant slot. The formula is
proved both for a lifted form and for the actual inverse-chart coefficients
of `nativeHodge`. It is valid locally and needs no globally extended chart.

`HodgeSmooth` proves preservation of local smoothness, then bundles
`smoothHodge` as a linear map between smooth native sections. Its orientation
and metric-sign laws and flat specialization follow from the pointwise API.
`HodgeSquare` proves `⋆⋆α = (-1)^(k*l + σ.negativeIndex d) • α` on native
fibres and as an equality of smooth sections. A pointwise signature witness
gives a frame whose oriented volume has square one; that sign cancels in
the square. No global frame, flatness or additional Hausdorff assumption is
used.

For `g = exp(2x²)(-dt² + dx²)`, `HodgeCurvedExamples` proves the inverse-metric
chart map is `exp(-2x²)` times the identity and all one-form Hodge values
agree with flat Hodge. It also proves the smooth-section version and checks
the square together with scalar curvature `-4 exp(-2x²)`. Typed API examples
fix the explicit local formula, regularity hypotheses, smooth linear map and
general square. Exact SymPy additionally checks that local formula in all
degrees with variable, non-diagonal metrics and either signature.

### Intrinsic divergence and the positive density

`Lorentzian/Divergence.lean` defines `divergence V x` as the intrinsic trace
of `g.leviCivita V x` on the actual tangent fibre. `smoothDivergence` bundles
the result for smooth vector fields. `divergence_eq_sum` proves invariance
under arbitrary pointwise tangent-coordinate equivalences, and
`divergence_chart` derives `∂ᵢVⁱ + ΓⁱᵢⱼVʲ` for a field differentiable at the
point in any smooth maximal-atlas chart containing that point. Both metric
sign conventions are supported; whole-metric sign reversal preserves divergence.

`MetricDensityDerivative.lean` differentiates the row-multilinear determinant
and proves the trace formula in directions `A G + G Aᵀ`. Differentiating
`sqrt(abs(det G))` requires only nonzero determinant. This algebraic step
does not assume positive definiteness. `Lorentzian/DensityDerivative.lean`
then derives the actual chart-metric derivative from Levi-Civita compatibility,
and proves

\[
\partial_k\rho=\rho\sum_i\Gamma^i{}_{ik},\qquad
\operatorname{div}V=\rho^{-1}\sum_i\partial_i(\rho V^i),
\quad\rho=\sqrt{|\det g|}.
\]

`chartDensity_derivative`, `chartDensity_mul_divergence` and
`divergence_density` express coordinate directions through the native
`chartField` and `mvfderiv`. They need no orientation or global frame.
`DivergenceExamples` checks `div(∂x)=4x` for the curved conformal plane,
and independently differentiates its density to recover the same value.
Typed contracts fix the actual connection trace, regularity and local
chart hypotheses. SymPy checks a nonconstant vector field with a curved,
non-diagonal, time-dependent metric in both overall signatures.

`DifferentialForm/OneForm.lean` identifies continuous covectors with
alternating one-forms on native fibres. Its coordinate regularity theorem
constructs `smoothOneFormEquiv` between the existing smooth cotangent and
alternating-section bundles, without adding fibre norms. This supports the
[fixed-background Maxwell form API](electrodynamics.md#fixed-background-maxwell-forms).
`Interior.lean` inserts a vector in the first slot of a continuous form on
any topological real module. Its continuity proof uses no norm or finite-basis
choice; naturality holds even for singular continuous linear maps.
`InteriorDerivative.lean` proves the four-coordinate trace formula for the
exterior derivative of contraction with coordinate volume. The chart-direction
chain-rule API now also accepts vector-space-valued functions.

`Minkowski/HodgeCurrent.lean` proves all four one-form Hodge signs, a general
coordinate-volume cofactor expansion and `⋆(v♭)=ιᵥ vol` in four dimensions.
`Lorentzian/HodgeCurrent.lean` transports this identity to every actual tangent
fibre, in either signature, using only a pointwise Lorentz frame. The physical
current API then proves `dJ=(div j) vol`, so closedness is equivalent to zero
vector divergence. A directly computed Maxwell field has native vector source
`-∂x`. SymPy also tests current contraction and nonzero divergence in curved
mixed-coordinate metrics with either signature/orientation. The covariant
Maxwell sourced component bridge is now proved in `Electrodynamics/CurvedComponents`.

`Tensor/CovariantDerivative.lean` constructs the derivative of a smooth native
covariant bilinear tensor using any tangent connection. The scalar Leibniz
correction is tensorial in both input fields, so mathlib's `TensorialAt.mkHom₂`
descends it to the actual fibres independently of local extensions. It is
linear in all three slots and preserves antisymmetry. No native norm is added.
`DifferentialForm/TwoForm.lean` curries native alternating two-forms into the
existing hom bundle and proves smoothness through actual trivializations.

`Lorentzian/TwoFormDerivative.lean` applies this construction to Levi-Civita,
proves smoothness of the resulting three-covariant tensor and bundles it in
`smoothTwoFormDerivative`. The last argument is the derivative direction.
The public `twoFormCovariantComponent` puts that direction first, as in
`∇ᵢFⱼₖ`, and its formula derives both negative Christoffel terms.
`TwoFormExterior.lean` proves `dF(u,v,w) = ∇ᵤF(v,w) - ∇ᵥF(u,w) + ∇wF(u,v)`.
Torsion-freeness cancels the connection corrections; actual chart recovery
then proves equivalence with the cyclic component equation in every chart.

`TwoFormExamples.lean` proves that `dt∧dx` on the curved conformal plane has
`∇xFₜₓ = -4x` even though its coordinate coefficients are constant and `dF=0`.
The physical examples also include a nonclosed two-form with cyclic sum `1`.
Exact SymPy checks the nonlinear three-slot transition law and the cyclic
identity in a curved four-dimensional metric. The sourced Maxwell component
bridge is proved below. The controlled Newtonian limit is in the
[GR guide](general-relativity.md#newtonian-coordinate-families-and-trajectory-limits).

`TwoFormDivergence.lean` contracts the actual three-covariant derivative by
`sharp` and trace, then raises the resulting covector to a smooth tangent
section. Local smoothness is proved by evaluating on local smooth fields;
native fibres retain their existing topologies. Its component formula has the
two inverse-metric factors derived from the trace construction.

`DualDerivative.lean` derives the covariant product rule for raised covectors
directly from metric compatibility. `TwoFormRaised.lean` constructs the actual
coordinate covectors and raises them, proves their local smoothness and dual
Christoffel rule, then derives the two positive corrections for raised two-form
components. The symmetric-connection/antisymmetric-form contraction is zero.
Together with the proved density derivative this gives
`∇ᵢFⁱʲ = ρ⁻¹ ∂ᵢ(ρ Fⁱʲ)` in every smooth chart, in all Lorentz dimensions and
both signatures. No global frame, orientation or flatness is assumed.

The curved conformal area example has divergence `(-4x exp(-4x²), 0)`. The
physical electric example has divergence `-∂x`, equal to its `dH` source.
`DifferentialForm/BivectorVolume.lean` proves a metric-free four-dimensional
coordinate-volume dual derivative formula under local differentiability and
local antisymmetry. The physical layer applies this to the actual signed
chart coefficients of the excitation. `Electrodynamics/CurvedComponents.lean`
proves that its native derivative is the current form of `twoFormDivergence`.
Consequently the source equals that divergence, both Maxwell equations are
equivalent to their covariant component equations in every smooth chart, and
the source vector is orientation independent and conserved. The shared
geometry modules import no physics. See the [electrodynamics guide](electrodynamics.md#fixed-background-maxwell-forms)
for exact assumptions and the textbook convention comparison.

## Metrics from coordinate coefficients, observers and Killing fields

`Lorentzian/LorentzFrame.lean` proves the signature criterion in every
dimension: a symmetric bilinear form on `MinkowskiModel d` that is negative on
the time axis and positive definite on the space has a frame in which it is
the Minkowski form of `.timeNegative` (`Minkowski.exists_lorentzFrame`);
`exists_lorentzFrame_convention` is the statement for either convention, with
the hypotheses on `−σ.timeSign · B`. `Lorentzian/CoordinateMetric.lean`
turns a family of such forms, smooth on an open set `U` of the model, into a
`LorentzMetric` on the manifold `U` with the inclusion as its chart; its
components, its inverse and its Christoffel symbols in this chart are the
matrix formulas (`toLorentzMetric_chartComponent`, `toLorentzMetric_inverseComponent`,
`toLorentzMetric_christoffel`), and `toLorentzMetric_chartMetric` identifies the
metric in the chart at each point with the given form. `Lorentzian/SpatialForm.lean`
defines the spatial form `B(v, w) − B(u, v) B(u, w)/B(u, u)` of a timelike vector
`u`, proves that its square root is the radar distance of a light signal sent
to a neighbouring event and back, that it is positive on every vector not along
`u` when `B` has a Lorentz frame of the convention `.timeNegative`, and gives its coefficients `gᵢⱼ − g₀ᵢ g₀ⱼ/g₀₀` for
`u = e₀`. `Lorentzian/Killing.lean` defines the Killing equation, proves that the
pairing of a Killing field with the velocity of a geodesic is constant on any
convex set of parameters, and gives the red shift `N ω = const` for the
observers that move along a timelike Killing field; a co-ordinate field `∂_k` is
a Killing field where the metric does not change along it. The physical
measurements are in the [general relativity guide](general-relativity.md#observers-killing-fields-and-rotation-82-84-88-89).

## The covariant derivative of the curvature and the Einstein tensor

`Tensor/TrilinearTensoriality.lean` builds a continuous trilinear map from an
operation that is tensorial in three slots (`ContMDiffTensorialAt.mkHom₃`), and
`Tensor/TrilinearDerivative.lean` differentiates a smooth field of tangent-valued
trilinear maps for any connection on the tangent bundle, with the direction last
(`trilinearCovariantDerivative`). `Lorentzian/CurvatureDerivative.lean` applies
it to the curvature, gives the chart formula of `∇_m R^l_{ijk}`, and proves the
second Bianchi identity with the co-ordinate fields of a chart as a frame.
`Lorentzian/InertialDerivatives.lean` gives the contraction, the Ricci tensor and
the scalar curvature in a chart, with the inverse metric `dx^i(♯dx^j)` as a
function of the point, and the derivatives at the centre of an inertial chart.
`Lorentzian/Einstein.lean` defines the divergence of a covariant two-tensor, proves
the contracted identity `∇^a Ric_{ab} = ½ ∂_b R`, and defines the Einstein tensor
with its vanishing divergence. `Lorentzian/CoordinateConnection.lean` reads the
connection of a coordinate metric off the Koszul formula, and
`Lorentzian/ExponentialConformalExample.lean` is the four-dimensional regression.
The statements are in the [general relativity guide](general-relativity.md#the-derivative-of-the-curvature-the-bianchi-identities-and-the-einstein-tensor-85-92).

## Varying a coordinate metric

`Lorentzian/SignatureStability.lean` keeps the Lorentz signature of a bilinear
form whose quadratic form is close to that of a Lorentz form
(`Minkowski.exists_lorentzFrame_of_near`), and
`Lorentzian/CoordinateVariation.lean` uses it with the tube lemma to give one
interval of admissible `ε` for a variation `g + εh` with compact support
(`CoordinateMetric.eventually_isAdmissible`, `addVariation`).
`Lorentzian/CoordinateCurvature.lean` writes the Christoffel symbols, the Ricci
tensor, the scalar curvature and the density as formulas in the coefficients and
identifies them with the native quantities of a coordinate metric;
`Lorentzian/CoordinateFamily.lean` applies the formulas to the slices of a
jointly smooth family `C(ε, x)` and differentiates them in `ε`.
`Lorentzian/PalatiniAlgebra.lean` is the Palatini identity between arrays of
numbers, `Lorentzian/CoordinateFirstVariation.lean` differentiates the inverse
metric and the density of `g + εh`, and
`Lorentzian/ScalarCurvatureVariation.lean` and
`Lorentzian/CoordinateEinsteinHilbert.lean` give the pointwise and the integrated
first variation of `(R − 2Λ)√|g|`, with the native reading of the integrand and of
the Einstein tensor. `Lorentzian/InertialDerivatives.lean` gains the derivative of
the inverse metric in any chart (`mvfderiv_chartInverse_chartField`). The physical
action is in the [general relativity guide](general-relativity.md#the-first-variation-of-the-einsteinhilbert-action-93).

## Matter and the Einstein equations in co-ordinates

`Variational/RelativeIntegral.lean` differentiates a relative integral
`∫ (L(ε, x) − L(0, x)) dx` of a density that is smooth near `[−r, r] × U` and does
not depend on `ε` off a compact set (`hasDerivAt_integral_sub`).
`Lorentzian/CoordinateMatter.lean` applies it to admissible variations of a
coordinate metric and gives the Hilbert tensors of a scalar field and of a fixed
electromagnetic field. `Lorentzian/EinsteinEquation.lean` states the Einstein
equations `G + Λ g = κ T` on a Lorentz manifold, with the conservation of the
source, the trace and the trace-reversed form, and
`Lorentzian/CoordinateEinsteinEquation.lean` proves that a continuous symmetric
field that pairs to zero with every metric variation vanishes, builds native
tensors from coefficients and identifies the co-ordinate equations with the native
ones. The physics is in the [general relativity guide](general-relativity.md#matter-and-the-einstein-equations-94-95).
`Lorentzian/CoordinateConservation.lean` proves metric compatibility of the
coefficients, defines the covariant Hessian, the wave operator and the divergence
of a field of coefficients with its native reading, and computes the divergence of
the stress of a scalar field; `Lorentzian/CoordinateScalarField.lean` varies the
scalar field on a fixed metric and proves that its action is stationary exactly when
the Klein–Gordon equation holds.
`Lorentzian/CoordinatePotential.lean` varies a field of covectors on a fixed metric:
its relative action with a prescribed current is exactly quadratic in the variation,
and it is stationary exactly when `∂_a(√|g| F^{ab}) = √|g| j^b`, the native equation
`∇_a F^{ab} = j^b` of `LorentzMetric.twoFormDivergence`.
`Lorentzian/CoordinateTangent.lean` reads tangent fields on an open set of the model
space in co-ordinates: the trivialization of its tangent bundle is the identity, a
tangent field along a map is as regular as its co-ordinates, and the native velocities
of curves and families are the derivatives of the co-ordinates.

## Orthonormal frames

`Lorentzian/Tetrad.lean` treats a smooth orthonormal frame on an open set of a Lorentz
manifold: the expansion of vectors and bilinear forms in it, the rotation and
commutator coefficients, the second structure equation of Cartan in components, the
Ricci, scalar and Einstein tensors in the frame, and the change of frame. The physics is
in the [general relativity guide](general-relativity.md#orthonormal-frames-and-the-tetrad-equations-98).

## Normal geodesics and synchronous co-ordinates

`Lorentzian/NormalGeodesics.lean` proves the lemma of Gauss for a two-parameter family of
geodesics with the same metric norm of their velocity. `Lorentzian/Synchronous.lean` treats a
coordinate metric with `g_{00} = −1` and `g_{0α} = 0`: its inverse, Christoffel symbols and
time lines, and the Ricci tensor in terms of the rate `κ` of the spatial metric and the
geometry of the slices. The physics is in the
[general relativity guide](general-relativity.md#the-synchronous-reference-system-97).

## The superpotential of Landau and Lifshitz

`Lorentzian/PseudotensorAlgebra.lean` proves the identities of arrays behind the second
derivatives of a metric at a point where its first derivatives vanish, and
`Lorentzian/Pseudotensor.lean` defines the superpotential `h^{ikl}` and the pseudotensor of a
coordinate metric and proves `∂_k ∂_l h^{ikl} = 0` and `∂_l h^{ikl} = 2 |g| G^{ik}` at such a
point. `Lorentzian/PseudotensorQuadratic.lean` proves the identities of arrays behind the
expression (96.9), and `Lorentzian/PseudotensorChristoffel.lean` writes the superpotential, the
derivative of the Christoffel symbols and the pseudotensor in the Christoffel symbols at every
point. The physics is in the
[general relativity guide](general-relativity.md#the-energy-momentum-pseudotensor-96).

## Coordinate tools for exact solutions

`Lorentzian/DiagonalMetric.lean` builds a coordinate metric from diagonal coefficients and gives
its Christoffel symbols with no differentiability hypothesis. `Lorentzian/ChristoffelCertificate.lean`
certifies a table of Christoffel symbols by the lowering identity and computes the Ricci and
curvature tensors from it. `Lorentzian/CoordinateGeodesic.lean` is the geodesic equation of a
coordinate metric in its co-ordinates, `Lorentzian/CoordinateKilling.lean` the Killing equation
in components, and `Lorentzian/CoordinateFrameCriterion.lean` the Lorentz criterion for a form
in a pointwise frame. `Lorentzian/SpaceForm.lean` gives the three-dimensional spaces of constant
curvature in conformally flat charts, with their embeddings into the sphere and the hyperboloid
and the volume of the closed space. `Lorentzian/CoordinateFrame.lean` builds an orthonormal
frame of a coordinate metric from the components of its fields, with the coordinate brackets of
the fields and the Ricci tensor in given commutator functions. `Lorentzian/Static.lean` gives
the static coefficients `−N² dt² + γ` with `R₀₀ = N Δ_γ N`, and `Lorentzian/Linearized.lean` the
linearized Christoffel symbols, Ricci and Einstein tensors of `η + εh` as derivatives, with gauge
invariance and the harmonic gauge. `Potential/` is potential theory on ℝ³: the co-ordinate
Laplacian with Green's identities, the Newton kernel with the pairing `∫ K Δχ = −χ(0)`, the
maximum principle, the Newton potential with `Δφ = −ρ`, its decay and its uniqueness, the Taylor
bounds of the kernel for multipoles and its Fourier pairing. `Fourier/WaveSolution.lean` is the
Fourier solution of the wave equation. Their physics is in the
[electrodynamics guide](electrodynamics.md#static-fields-the-moving-charge-and-waves-3638-4648-50).
The physics of the Lorentzian layer is in the
[general relativity guide](general-relativity.md#the-centrally-symmetric-field-100-101) and its
sections on [isotropic cosmology](general-relativity.md#isotropic-cosmology-111-114) and
[homogeneous models](general-relativity.md#homogeneous-cosmological-models-116-117) and
[the Newtonian limit and gravitational waves](general-relativity.md#the-newtonian-limit-and-gravitational-waves-99-107-109).

## Scope and next stages

These definitions impose neither finite generation nor global Hausdorffness
on a scheme. A morphism preserves the smooth operations, not just polynomial
ones. Real residue maps are part of the local-space condition, expressed as
existence of local ring maps compatible with real constants on every open set.

General C∞ localizations, open subschemes, gluing, and the manifold-to-scheme
construction are implemented. Subsequent stages include quotients by
arbitrary ordinary ideals, the Γ–Spec adjunction, complete/fair rings,
full faithfulness of the manifold construction, and universal cotangent
modules. The Lorentz connection and curvature endpoints above are
implemented and merged into `main` through [#52](https://github.com/MGYamada/ProjectAinos/issues/52).
In particular,
`A ≅ Γ(Spec A)` and full faithfulness of Spec on all C∞-rings are not asserted.
The essential-image definition of affine schemes does not require either
incorrect assertion.

The mathematical reference is [Joyce, *Algebraic Geometry over C∞-rings*,
Definitions 2.10 and 2.13, Proposition 2.14, Definitions 4.13 and 4.16,
Lemma 4.18, Definition 4.23, and §4.6](https://arxiv.org/pdf/1001.0023).

Validation uses the required Lean build, root-import check, and transitive
axiom audit described in the [smooth algebra guide](smooth-algebra.md#proof-map-and-verification).
[Formalization notes](smooth-geometry-notes.md) record the distinctions
between these constructions and their remaining comparison theorems.
