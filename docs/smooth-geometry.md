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

## Scope and next stages

These definitions impose neither finite generation nor global Hausdorffness
on a scheme. A morphism preserves the smooth operations, not just polynomial
ones. Real residue maps are part of the local-space condition, expressed as
existence of local ring maps compatible with real constants on every open set.

General C∞ localizations, open subschemes, gluing, and the manifold-to-scheme
construction are implemented. Subsequent stages include quotients by
arbitrary ordinary ideals, the Γ–Spec adjunction, complete/fair rings,
full faithfulness of the manifold construction, and universal cotangent
modules. Connections and curvature require their own constructions.
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
