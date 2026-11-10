# Shared Smooth Geometry: Joyce C∞ Schemes

`ProjectAInos/SmoothAlgebra/` and `ProjectAInos/SmoothGeometry/` are the
mathematical foundation shared by Mechanics and the Classical Theory of Fields
(Landau–Lifshitz). Neither imports the physics or variational modules.
The implementation sequence and subsequent research stages are in the
[research plan](../README.md#shared-smooth-algebra-and-geometry).

## Correspondence with mathlib

The source review and implementation target the pinned mathlib v4.35.0,
commit `56a005855ea17e0b0958f73ec801ae140b0a1679`.

| mathlib layer | Project AInos layer | Mathematical change |
| --- | --- | --- |
| `CommAlgCat ℝ` | `SmoothAlgebra.Category` | Morphisms preserve every smooth operation |
| `PrimeSpectrum` | `SmoothGeometry.RealSpectrum` | Points are `SmoothRingHom A ℝ` |
| `AlgebraicGeometry.StructureSheaf` | `SmoothGeometry.StructureSheaf` | Sections locally represented in C∞ point localizations |
| `Geometry.RingedSpace.SheafedSpace` | `SmoothGeometry.RingedSpace` | Smooth structure on all sections and restrictions |
| `Geometry.RingedSpace.LocallyRingedSpace` | `SmoothGeometry.LocallyRingedSpace` | Real residue fields and smooth morphisms |
| `AlgebraicGeometry.Spec` | `SmoothGeometry.Spec` | The constructed real spectrum, contravariantly |
| `AlgebraicGeometry.Scheme` | `SmoothGeometry.Scheme` | The same local-affine condition using C∞ spectra |
| `AlgebraicGeometry.AffineScheme` | `SmoothGeometry.AffineScheme` | Essential image of C∞ Spec |

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

## Scope and next stages

These definitions impose neither finite generation nor global Hausdorffness
on a scheme. A morphism preserves the smooth operations, not just polynomial
ones. Real residue maps are part of the local-space condition, expressed as
existence of local ring maps compatible with real constants on every open set.

The current localization construction is at real points. Arbitrary C∞
localizations, quotients by arbitrary ordinary ideals, open subschemes and
gluing, the Γ–Spec adjunction, complete/fair rings, the manifold embedding,
and universal cotangent modules are subsequent stages. In particular,
`A ≅ Γ(Spec A)` and full faithfulness of Spec on all C∞-rings are not asserted.
The essential-image definition of affine schemes does not require either
incorrect assertion.

The mathematical reference is [Joyce, *Algebraic Geometry over C∞-rings*,
Definitions 2.10 and 2.13, Proposition 2.14, Definitions 4.13 and 4.16,
Lemma 4.18, Definition 4.23, and §4.6](https://arxiv.org/pdf/1001.0023).

Validation uses the required Lean build, root-import check, and transitive
axiom audit described in the [smooth algebra guide](smooth-algebra.md#proof-map-and-verification).
