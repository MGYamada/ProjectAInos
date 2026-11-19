# Smooth Geometry Formalization Notes

These notes record mathematical distinctions and implementation decisions for
the common C∞ scheme foundation used by Special Relativity and General
Relativity. The construction guide is [smooth-geometry.md](smooth-geometry.md).
The current continuation preserves the existing contents of `README.md`.

## General localization differs from point localization

The existing `PointLocalization` is a quotient of the original C∞-ring. Its
projection is surjective because smooth cutoffs supply inverses locally at a
real point. This property must not be copied to arbitrary localizations:
adjoining the inverse of the coordinate on ℝ already requires new elements.

`SmoothAlgebra.Free` constructs free C∞-rings on arbitrary sets as smooth
cylinder functions with finite coordinate dependence. Equality between two
finite presentations is proved to imply equality after interpretation in
every C∞-ring, in arbitrary target universes. Testing functions on real tuples
is used for this **free ring**, not to identify arbitrary C∞-rings with their
real-valued functions. Smooth congruence quotients can retain nilpotents.

`SmoothAlgebra.GeneralLocalization` adjoins an inverse for every element of a
chosen set and imposes the original smooth operations and inverse equations.
Its universal property quantifies over C∞ morphisms. An ordinary commutative
ring localization does not by itself provide this property.

Localizing again at a surviving real point gives the same point-local ring.
`LocalizationComparison` constructs both directions using the two universal
properties. This comparison is the algebraic input to the stalk comparison
for open immersions.

## The spectrum of a localization need not be open

For a set `S`, the relevant locus is the subspace

\[
\{x\in\operatorname{Spec}_{\mathbb R}(A)\mid x(s)\ne0\text{ for all }s\in S\}.
\]

An infinite intersection of principal open sets need not be open. The
principal-open construction uses a singleton `S = {a}`; finite sets can be
handled by a product. The general subspace comparison and the principal-open
immersion therefore have separate statements.

The real-spectrum topology also makes every evaluation `x ↦ x(a)` continuous.
One proof uses the existence of a smooth real function with prescribed open
support. In particular, the point bijection for the free ring `C∞(ℝⁿ)` upgrades
to a homeomorphism with ordinary Euclidean space.

## Reusing the manifold sheaf

Mathlib already provides the smooth-function sheaf, its local stalks, maps
induced by smooth functions, and compatibility with open restriction in
`Geometry/Manifold/Sheaf/{Smooth,LocallyRingedSpace}`. These provide the
underlying ringed-space layer. The project must retain all smooth operations
on sections and prove the comparison with its constructed affine models.

The construction uses the Euclidean comparison, principal open subschemes,
and smooth coordinate charts. A manifold's local-affine property is proved
from its charts. Scheme gluing likewise constructs the glued object and its
maps from the overlap and cocycle data.

`Manifold.Germs` proves that on a finite-dimensional Hausdorff smooth
manifold, every smooth function on an open set has a global representative
near each chosen point. The proof multiplies a zero extension by a smooth
bump function equal to one near that point. It needs neither compactness
nor a global coordinate chart. For Euclidean functions it also proves that
equality in point localization is equivalent to agreement on a neighbourhood.
This is stronger than equality of the real residues at the single point.

The Euclidean comparison is now constructed on every open set: taking real
residues of a spectrum section gives a smooth function, and the inverse
assigns its local germ. The resulting maps are bijective and commute with
restriction. Thus `Manifold.euclideanIso` compares the entire
smooth locally ringed spaces, rather than just their underlying points.

`Restrict` proves that open subspaces of C∞ schemes are schemes using the
principal-localization basis. `Manifold.scheme` then proves local
affineness from smooth charts for manifolds modeled on `Fin n → ℝ`.
This includes non-Hausdorff charted manifolds: Hausdorffness was needed only
for the Euclidean cutoff argument, and is not a premise of the chartwise
scheme construction. Smooth maps induce scheme morphisms with identity and
composition laws. Full faithfulness of this functor is a separate statement.
The current manifold API is for boundaryless finite-dimensional models
`Fin n → ℝ`, with a carrier in `Type`, matching the real-valued manifold
sheaf API reused from mathlib. Higher-universe carriers and manifolds with
boundary are not covered by this comparison.

## Gluing must retain the smooth operations

Gluing only the underlying commutative-ring sheaves would leave an additional
obligation to reconstruct compatible C∞ operations. `SmoothRingCat.Limits`
instead constructs compatible families of C∞-rings and proves preservation
of their limits by the forgetful functor. `SmoothPresheaf` and `SmoothSheaf`
connect this category to mathlib's generic sheaf and open-immersion APIs.

`Gluing` applies mathlib's sheaf gluing to the full C∞-valued sheaves.
The open inclusions of the pieces transfer local stalks and real residues
to the glued object; their affine neighbourhoods prove the scheme condition.
The output includes open inclusions, joint surjectivity, the overlap
equations, descent of compatible morphisms, and uniqueness. Both the
locally ringed space and scheme constructions prove `gluedIsColimit` for
the actual gluing diagram. The cocycle data are inputs; existence of a
glued scheme is a theorem of the construction.

## G01. Recovering a scheme from a gluing needs injectivity on points

**Observation.** The universal property of `GlueData.glued` gives the descent
morphism to any scheme that receives the pieces compatibly, and joint
surjectivity of the pieces gives surjectivity on points. It does not give
injectivity: the overlaps `V (i, j)` of a gluing datum may be smaller than the
intersections of the images, and then two points over the same point of the
target stay distinct in the gluing. For the two half-lines, injectivity is the
statement that the overlap of the datum is the whole interval `-1 < x < 1`.
`CategoryTheory.GlueData.ofGlueData'` chooses its overlaps by a classical case
distinction on `i = j`, so `datum.V (false, true)` is equal to `overlap`
propositionally and not by definition; the gluing condition has to be read
through `eqToHom` (`overlapToPiece_ι`).

**Interface decision.** `OpenCover` states the criterion with injectivity or
bijectivity on points as a hypothesis, for an arbitrary jointly surjective
family of open immersions, and `GlueData.desc_isIso` specializes it. The new
modules use no `set_option backward.*`; since G02 no module does.

**Proof status.** `toLine` is proved to be an isomorphism of C∞ schemes, with
the coordinate function followed through the gluing as a section. Gluing of
morphisms out of an arbitrary scheme along an open cover, mathlib's
`Scheme.Cover.glueMorphisms`, is not proved; for the line it follows from the
isomorphism (`line_hom_ext` gives uniqueness).

## G02. The tangent space of a vector space is the space, and Lean has to be told

**Observation.** Mathlib defines `TangentSpace I x` as the model space `E`. The definition is
not reducible, so that instance search does not confuse the structures of the two, and the
identification is the named equivalence `NormedSpace.fromTangentSpace`. With the default options
Lean does not unfold such a definition when it compares implicit arguments. A term that uses the
identification silently still elaborates, for example a bilinear form on `E` given as the form of
a metric on the model space, or a `Form E k` given as a `NativeForm 𝓘(ℝ, E) E k`. A `rw` or a
`simp` lemma whose pattern passes through such a term does not: the motive is not type-correct
at the transparency that these tactics use. The same happens with `Matrix m n ℝ` used as
`m → n → ℝ`, and with instances that were found by unfolding a forgetful functor in the scheme
layer. The option `backward.isDefEq.respectTransparency false` restores the unfolding, and 195
files had set it for the whole file. 144 of them did not need it, and the option
`backward.defeqAttrib.useBackward true` was needed by none.

One instance of Mathlib is affected in the same way. The derived instance
`IsNormableSpace 𝕜 (TangentSpace I x)` is stated with the module structure of `E`, so instance
search does not find it, and `ContinuousLinearMap.flip` cannot be applied to a map between
tangent spaces.

**Interface decision.** No file sets a `backward` option or `maxHeartbeats`, and
`checks/ForbiddenOptions.lean` enforces this. Statements and definitions keep the silent
identification; no declaration changed its type, with one exception: the helper
`minkowski_hodgeVolume_normalized` names the tangent space in an implicit argument that was
inferred before. The proofs apply a lemma across the identification in term mode
(`refine (lemma).trans ?_`, `exact (a.trans b).trans (congrFun c y)`, `congrArg` with a function
whose domain is written out), state an equation for a variable of the right type before using
it, or restate the goal with `change`. These steps unify at default transparency.
`tangentSpace_isNormableSpace` states the normable instance for the module structure of the
tangent space. Marking `TangentSpace` as implicitly reducible was measured and not adopted: it
repaired 6 of the 51 failing files and goes against the reason for which Mathlib keeps the
definition irreducible. The computation of `alternatize_bivectorVolume`, 64 cases under a raised
heartbeat limit, is split into four lemmas that exclude the 40 cases with a repeated index by
hypothesis.

**Proof status.** The whole library builds with the default options. The pinned Mathlib still
sets the option for 71 declarations in 17 files of its manifold library; a later version may
make some of the term-mode steps unnecessary. [Tangent space instance](../ProjectAinos/SmoothGeometry/Manifold/TangentSpace.lean) · [Check](../checks/ForbiddenOptions.lean)

## G03. Four elaboration limits met with tangent-valued trilinear tensors

**Observation.** Four limits appeared while building the covariant derivative of the curvature
(F10).
1. Instance search does not find a norm on a threefold space of continuous linear maps
   `E →L[ℝ] E →L[ℝ] E →L[ℝ] E`, even for a normed `E`; on the twofold space it does. The bundle
   of tangent-valued trilinear maps cannot be written as `Cₛ^∞⟮I; E →L[ℝ] E →L[ℝ] E →L[ℝ] E, …⟯`.
2. A `local notation` whose body names a section variable, such as `"E" => MinkowskiModel d`,
   does not resolve that variable inside a later `variable` command. The declared variable gets
   the type `OpenPartialHomeomorph M (MinkowskiModel sorry)`, no error is reported at the
   `variable` line, and each theorem that uses it fails in its proof. In the binders of a theorem
   the same notation works.
3. A named argument `(I := I)` is parsed with the local notation `I` on its left; it has to be
   written `(«I» := I)`.
4. On spaces of continuous linear maps between tangent spaces, `simp` left `(0 : ℝ) • 0` and
   `g.ricci x - 0 • g.form x` unsimplified, as in G02. A chain of `rw` steps through the terms
   `R y (∇_{∂_a} ∂_u) (∂_v y) (∂_w y)` on the manifold of an open set `U` exceeded the heartbeat
   limit.

**Interface decision.** `Tensor.trilinearBundle` is the iterated `SmoothBundle.hom`, whose
model carries the norm of each level, as `curvatureBundle` does. A field of trilinear maps is a
function to `TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x`, and its smoothness is the predicate
`IsSmoothTrilinear`, the form in which `curvature_smooth` is stated. `variable` commands write
the model `MinkowskiModel d` out. Equalities of bilinear maps are proved after `ext`, on the
scalars, and a long rewrite is split into one `have` for each term, combined by `simp only`.

**Proof status.** Applied in F10; no option is set. [Trilinear derivative](../ProjectAinos/SmoothGeometry/Tensor/TrilinearDerivative.lean) · [Inertial derivatives](../ProjectAinos/SmoothGeometry/Lorentzian/InertialDerivatives.lean) · [Coordinate connection](../ProjectAinos/SmoothGeometry/Lorentzian/CoordinateConnection.lean)

## G04. Five elaboration limits met with matrices and bilinear forms of the model space

**Observation.** Five limits appeared while varying coordinate metrics (F11).
1. On the space `MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ`, instance search failed for
   `IsBoundedSMul`, `ContinuousAdd`, `NormSMulClass`, and for the matching of `norm_add_le`,
   `dist_eq_norm` and `zero_smul`; `ContDiff.smul` with a scalar function and a constant form
   did not elaborate, and one statement reached the heartbeat limit in `whnf`.
2. `-(M) a c` for a matrix `M` parses as `-(M a c)`, the negation of an entry, not as the entry
   of `-M`; lemmas about `(-M) a c` do not match it.
3. A matrix-valued variable introduced by `set` made later applications fail with "function
   expected".
4. A `local notation` for a term cannot be followed by a projection: `gc.coefficient` is read
   as an identifier `«gc».coefficient`.
5. `HasFDerivAt.fun_sum` and the composition lemmas leave the index set, or the function, as a
   metavariable unless they are named (`(u := Finset.univ)`, `(g := …)`), and `HasDerivAt.mul`
   gives the function as a product of functions, which `convert … using 1` matches.

**Interface decision.** Smoothness of a field of bilinear forms is proved on its values,
with `contDiff_clm_apply_iff` twice, and bounds on bilinear forms are bounds on the values of
the quadratic form (`Minkowski.abs_apply_self_le`). Statements write entry negation as
`-(M a c)`, matrices are not introduced with `set`, and a notation is parenthesized before a
projection, `(gc).coefficient`.

**Proof status.** Applied in F11; no option is set. [Signature stability](../ProjectAinos/SmoothGeometry/Lorentzian/SignatureStability.lean) · [Inverse metric and density](../ProjectAinos/SmoothGeometry/Lorentzian/CoordinateFirstVariation.lean) · [Action](../ProjectAinos/GeneralRelativity/EinsteinHilbertAction.lean)

## Lorentz metrics and the common geometric base

The smooth structure of a spacetime is independent of its Lorentz metric.
Both Minkowski space and a general Lorentz manifold pass through the same
`LorentzManifold.toScheme` construction. The metric is additional smooth
bilinear data on the actual tangent bundle. The explicit parameter
`σ : LorentzConvention` selects `(+,-,...,-)` or `(-,+,...,+)`. Symmetry and nondegeneracy are derived from this
signature condition. Pairing smooth vector fields gives a smooth function,
linking the metric to the same function algebra as the structure sheaf.

The signature field asks for a linear equivalence at each point, not a
smooth global frame. Smoothness is imposed using mathlib's topology and
charts on the bundle of bilinear maps, rather than arbitrary identifications
of each tangent fiber with the model space. This distinction allows curved
spacetimes and tangent bundles without global trivializations.

`minkowski σ d` supplies the constant form on `Fin (d+1) → ℝ`. Its smoothness,
symmetry, nondegeneracy, constant coefficients, and affine scheme comparison
are proved. `LorentzMetric.IsLocallyMinkowski` uses an actual coordinate
diffeomorphism and its manifold derivative to express local inertial
coordinates on an open neighbourhood, rather than just a pointwise normal
form. `minkowski_isLocallyMinkowski` proves this property for Minkowski space.
Negating the metric changes `σ` to `σ.opposite` and preserves this local
condition, as well as smoothness, symmetry and nondegeneracy. The underlying
C∞ scheme is definitionally unchanged. The [flat-spacetime extension](special-relativity.md)
keeps time orientation separate from spacetime orientation.
Local Minkowski coordinates are not a premise on general Lorentz manifolds.
The Lorentz Levi-Civita connection and smooth curvature tensor are now
constructed; equivalence of `IsLocallyMinkowski` with vanishing native
curvature is now proved. Both implications, coordinate flat-frame
construction and coframe-to-chart integration are implemented in stage D,
merged through [#52](https://github.com/MGYamada/ProjectAinos/issues/52).

The localization construction follows [Joyce, *Algebraic Geometry over
C∞-rings*, §2.3](https://arxiv.org/pdf/1001.0023). The requested general
localization, open gluing, and manifold comparison are now constructed.
The Γ–Spec adjunction, complete/fair rings, full faithfulness of the manifold
construction and universal cotangent modules remain separate research
stages. Curvature and the new along-curve/geodesic initial-value proof status
are recorded in the [API guide](smooth-geometry.md#gr-51-differentiation-along-curves-and-geodesic-initial-data).
The latter constructs native differentiation, proves metric preservation
and reparametrization, and derives local geodesic existence and germ
uniqueness. Parallel transport now exists uniquely on prescribed finite
regular segments, with metric preservation, subdivision, reversal and
parameter-change laws. Linear uniqueness also preserves nonzero null
velocity. Finite piecewise-path concatenation has independent matching-field
and continuous-lift proofs, and uniquely characterized endpoint transport.
Pointwise local inertial charts now follow from a quadratic correction with
prescribed Jacobian and Hessian. The inverse function theorem gives an actual
chart in the smooth maximal atlas. Analytic regularity is used only for the
polynomial correction and its local inverse; the manifold and metric remain
smooth. The chosen pointwise Lorentz equivalence determines the first
derivative, the connection transformation law makes `Γ(p) = 0`, and metric
compatibility makes `∂g(p) = 0`. No norm is added to native tangent fibres.
`IsInertialChartAt` concerns one point and admits nonzero curvature, as proved
for the conformal origin. The conformal metric is now proved not to satisfy
`IsLocallyMinkowski`, even though every point admits an inertial chart.

For the local flatness theorem, restriction to open submanifolds preserves
native curvature, and `IsLocallyMinkowski` implies zero curvature. The
coordinate equation for a parallel coframe is `∂θ = θ Γ`. Torsion-freeness
makes it closed; Poincaré's lemma on an open convex coordinate domain gives
a smooth primitive, and invertibility gives an actual smooth chart. The
transition law makes the new connection coefficients vanish on the entire
source. After shrinking to a convex target, metric compatibility propagates
a normalization at the base point to the whole chart. These conditional
integration theorems take a parallel coframe as input. A separate coordinate
construction now supplies one under an explicit zero-curvature equation.
The native curvature bridge and the application of this construction are
also proved.
The supporting linear-ODE solver now uses the Banach space of continuous
coordinate curves on `[0,1]`. If the coefficient supremum norm is less than
one, the integral equation has an invertible operator, yielding the unique
solution with smooth dependence on coefficients and initial values. These
norms belong to coordinate curve spaces, not the native tangent fibres.
Jointly smooth coordinate coefficients now lift to smooth curve-valued
families by a uniform mean-value estimate and induction on derivatives.
The radial coefficients vanish at zero displacement, so a common ball has
small coefficients and smooth invertible endpoint maps. Their inverses give
smooth radial coframes. ODE uniqueness identifies shorter-ray endpoints
with intermediate solution values, proving the radial differential equation.
A vector-valued cutoff extends native chart coefficients without changing
their germ. For coordinate coefficients satisfying zero curvature,
`ODE.FlatFrame` now proves parallelness in all directions. Writing the
defect as `Q = DP + ΓP`, Hessian symmetry and flatness give a homogeneous
radial equation. Along each ray, `t Q(t x)(u)v` solves the original transport
equation with zero initial value, so uniqueness makes it zero. Inverting
the frame yields `Dθ(u)v = θ(Γ(u)v)`. This constructs an invertible smooth
parallel coframe on a smaller ball, normalized to identity at its center.
`FlatConnection` identifies the bundled trilinear expression with the native
curvature components on every smooth chart, with basis tests giving full
coordinate flatness. `LocalFlatnessConverse` starts with an inertial chart
at the chosen point, which already fixes its center and metric normalization.
Curvature zero on a neighborhood passes to a smaller coordinate ball;
smooth extension preserves the coefficient germ. The radial coframe has
identity value at the center and integrates to a Minkowski chart. This proves
the converse, using only local data and the native tangent bundle.
Inside the resulting flat neighborhood, transport depends only on endpoint
chart identifications. This is proved for arbitrary finite piecewise regular
paths, including corners and different decompositions; it makes no global
path-independence assertion for the original manifold.
In particular, no claim that `A ≅ Γ(Spec A)` for arbitrary
C∞-rings is used in this continuation.

## Verification

The warning-free full build (`lake build --wfail ProjectAinos`), root-import
check, external API regression check, and transitive axiom audit pass.
The current motion increment's audit covers 7,309 project declarations,
including 453 in smooth algebra and 3,144 in smooth geometry,
with only `propext`, `Classical.choice`, and `Quot.sound` allowed.
The full build has 9,302 jobs. All six API checks and the installed-package
exact Lorentz experiment pass, including the motion examples.
`git diff --check` also passes. The existing `README.md` contents, including
the earlier subject-numbering changes, were preserved throughout this work.

## Code review follow-up (2026-11-11)

External API examples exposed two missing instance registrations despite
the successful full build and root-import check. Both issues are now fixed.

- `Scheme.IsOpenImmersion` now has instances for isomorphisms (including
  identities), compositions, and `Scheme.ofRestrict`. These transfer the
  existing locally ringed space instances through the scheme morphism
  wrapper. Pullbacks of open inclusions, including inclusions followed by
  isomorphisms, synthesize without local instance declarations.
- Both smooth locally ringed spaces and schemes register the constructed
  colimit as `HasMulticoequalizer`. Their public `glued` and `ι` are now
  abbreviations of mathlib's categorical gluing and inclusions. The
  concrete sheaf-based construction remains the existence proof, and
  `isoConstructed` identifies it with the categorical choice. Compatibility
  of this isomorphism with each inclusion transfers openness and joint
  surjectivity. Public descent uses `Multicoequalizer.desc` directly.

The regression file `checks/SmoothGeometryAPI.lean` exercises these APIs
under default elaborator settings and in arbitrary carrier universes.
It checks instance inference, definitional agreement with the generic
gluing, and descent through the generic multicoequalizer API at both
geometric levels. It runs in the required **Lean build** CI job.

The metric smoothness field was also checked after elaboration: it uses the
tangent bundle and the bundle of continuous linear maps, including their
bundle topology and charts. It does not accidentally use a trivial tangent
bundle.

## G05. Coordinate metrics are computed from diagonal coefficients or from a certified table

**Observation.** The Christoffel symbols of a coordinate metric contain the inverse matrix, and the Ricci tensor differentiates them. Differentiating the inverse is avoidable in two ways. For diagonal coefficients the symbols are explicit and need no differentiability, since the off-diagonal entries are the constant zero (`christoffelOf_diagonal`). For any metric, a table that satisfies the lowering identity `g_{lq} Γ^q_{ij} = ½(∂_i g_{jl} + ∂_j g_{li} − ∂_l g_{ij})` equals `christoffelOf`, because the coefficient matrix is invertible (`christoffelOf_eq_of_lowered`). The Ricci tensor then needs the table only near the point (`ricciOf_eq_ricciOfChristoffel`). A form whose time co-ordinate is null somewhere, as in Eddington–Finkelstein, fails `ofCriterion` but passes it in a pointwise frame (`ofFrameCriterion`); the frame need not depend smoothly on the point.

**Interface decision.** `ofDiagonal`, `christoffelOf_eq_of_lowered`, `ricciOfChristoffel`, `curvatureOf`, `isGeodesicOn_iff` (the geodesic equation of a coordinate metric in its co-ordinates), `vectorFieldOf`, `lieOf` with `isKillingField_iff_lieOf` (the Killing equation in components), and `ofFrameCriterion` are shared. Each file has a proved regression, among them `minkowski_eq_ofDiagonal`, a two-dimensional certified table with `Ric = g`, the straight lines of the Minkowski metric, its rotations and boosts as Killing fields, and a null form that fails `ofCriterion`.

**Proof status.** Proved and built. The general physical consumers are the Schwarzschild files of F14 (GR20, GR21). [DiagonalMetric](../ProjectAinos/SmoothGeometry/Lorentzian/DiagonalMetric.lean) · [ChristoffelCertificate](../ProjectAinos/SmoothGeometry/Lorentzian/ChristoffelCertificate.lean) · [CoordinateGeodesic](../ProjectAinos/SmoothGeometry/Lorentzian/CoordinateGeodesic.lean) · [CoordinateKilling](../ProjectAinos/SmoothGeometry/Lorentzian/CoordinateKilling.lean) · [CoordinateFrameCriterion](../ProjectAinos/SmoothGeometry/Lorentzian/CoordinateFrameCriterion.lean)

## G06. Riemannian space forms are coefficient arrays, and long rational identities need typed exponents

**Observation.** `CoordinateMetric` is Lorentzian, but `christoffelOf`, `ricciOf` and `curvatureOf` are formulas for any matrix of coefficients, so a three-dimensional Riemannian metric is a coefficient array on ℝ³ (`MinkowskiModel 2`). Positive definiteness is then `Matrix.PosDef`. Generated identities of rational functions met two elaboration limits: literal exponents in a long real expression made the elaborator time out before any tactic ran, and `field_simp` did not clear a polynomial denominator in its own normal form unless that denominator was a variable.

**Interface decision.** `SpaceForm` is shared mathematics, with no physics imports; the topology is stated by `sphereHomeomorph` and `hyperboloidHomeomorph`. Generated Lean writes exponents as `^ (n : ℕ)` and generalizes polynomial denominators to variables before `field_simp`, then substitutes them back and closes with `ring` (GR22).

**Proof status.** Proved and built. [SpaceForm](../ProjectAinos/SmoothGeometry/Lorentzian/SpaceForm.lean)

## G07. Orthonormal frames of a coordinate metric are built from their components

**Observation.** The tetrad theorems of §98 take an `OrthonormalFrame` of native vector fields. For a metric given by coefficients, the natural data are the components of the fields. Their brackets are the coordinate brackets `∂_ξ η − ∂_η ξ`. The proof avoids the chart pullback of `mlieBracket`: the Levi-Civita connection of the Minkowski coefficients is torsion free and has vanishing Christoffel symbols, so `[X, Y] = ∇_X Y − ∇_Y X` gives the coordinate bracket directly. A function on `U` differentiated along a field of components is the ordinary derivative along the components, for any normed target.

**Interface decision.** `CoordinateMetric.orthonormalFrameOf` takes components smooth on `U` with `g(ξ_a, ξ_b) = η_{ab}` and returns a frame on all of `U`; the chart is fixed by a base point. `ricci_orthonormalFrameOf` takes commutator functions `Λ_{abc}` smooth on `U` with `g(ξ_a, [ξ_b, ξ_c]) = Λ_{abc}` and gives the frame components of the Ricci tensor in `Λ` and its derivatives along the components (`ricciOfFrame`). The homogeneous models of §116 use it (GR24); it is also the frame route that the Kerr certificate made unnecessary.

**Proof status.** Proved and built. [CoordinateFrame](../ProjectAinos/SmoothGeometry/Lorentzian/CoordinateFrame.lean)
