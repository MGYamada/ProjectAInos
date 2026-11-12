# Shared Smooth Geometry: Joyce C∞ Schemes

`ProjectAInos/SmoothAlgebra/` and `ProjectAInos/SmoothGeometry/` are the
mathematical foundation shared by Mechanics, Special Relativity,
Electrodynamics, and General Relativity (research-plan topics 2–5).
Neither imports the physics or variational modules.
The implementation sequence and subsequent research stages are in the
[research plan](../README.md#shared-smooth-algebra-and-geometry).

## Correspondence with mathlib

The source review and implementation target the pinned mathlib v4.35.0,
commit `56a005855ea17e0b0958f73ec801ae140b0a1679`.

| mathlib layer | Project AInos layer | Mathematical change |
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
noninvertible composition with a nonsymmetric two-tensor. A full slot-permutation
and tensor-product API remains subsequent work in
[#52](https://github.com/MGYamada/ProjectAInos/issues/52).

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

`Lorentzian/ChartExamples.lean` addresses [#43](https://github.com/MGYamada/ProjectAInos/issues/43)
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
proof endpoints are implemented; its PR still requires review and merge.
The curvature endpoints below are implemented. Finite-segment parallel
transport and local inertial coordinates are described in the motion section.
Native form bundles, pullback, exterior differentiation, wedge, density and
oriented volume and pointwise Hodge are described below; smooth Hodge/Maxwell and the Newtonian motion limit
remain incomplete.

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

Stage C's proof endpoints are implemented and awaiting review/merge.
Typed API examples fix the chart formula/overlap hypotheses, all metric
symmetries, Ricci symmetry, conformal signature construction and curved
example conclusions. Exact experiments independently check these examples
and nonzero curvature covariance under the shear. Differential and
contracted Bianchi are explicitly deferred to 5.2.

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

Stage D's principal proof endpoints are implemented, pending review and
merge. No global frame, global chart, analytic metric, Hausdorff premise or
geodesic completeness is assumed or concluded. Stage E's principal particle-
variation endpoints are now implemented; see the [GR guide](general-relativity.md).
Curved exterior calculus/Maxwell and the Newtonian trajectory limit remain
in stages F–G.

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
and pointwise Hodge are described below. Hodge regularity/general square and the curved Maxwell component bridge remain
in #52. Maxwell action variation remains in §4.2/#44, and Einstein dynamics
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
The density divergence formula remains to be implemented with the curved
Maxwell bridge.

### Pointwise native Lorentz Hodge

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
needed for the forthcoming local regularity proof.

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
with arbitrary pullback. These are pointwise constructions and proofs.

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

The remaining Hodge work is its local coordinate formula and regularity as
an operation on smooth native sections, the general Lorentz square identity
and curved component examples. Those results are required before completing
the Maxwell component bridge, current conservation and density divergence.

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
implemented and awaiting review/merge.
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
