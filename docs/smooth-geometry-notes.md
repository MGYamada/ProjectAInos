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
constructed; equivalence of `IsLocallyMinkowski` with vanishing curvature
still requires the local flat-frame/integration arguments in stage D.

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
velocity. Piecewise-path concatenation and the local inertial/flatness
constructions remain open in stage D.
In particular, no claim that `A ≅ Γ(Spec A)` for arbitrary
C∞-rings is used in this continuation.

## Verification

The warning-free full build (`lake build --wfail ProjectAInos`), root-import
check, external API regression check, and transitive axiom audit pass.
The current motion increment's audit covers 6,758 project declarations,
including 453 in smooth algebra and 2,593 in smooth geometry,
with only `propext`, `Classical.choice`, and `Quot.sound` allowed.
The full build has 9,277 jobs. All six API checks and the installed-package
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
