# Semantic review of the Yang--Mills import (PR #41)

The upstream declarations remain unchanged. The Lean kernel checks their
types and proofs; this document distinguishes **proved interfaces** from
**additional physical identifications that have not been proved** in P⊗AI.

The import is a mathematical dependency library for Project AInos. It is not
yet a construction theorem for a specific continuum Yang--Mills model.

## Proved integration bridges

1. **Finite Wilson action and law (including every public `WilsonFamily`).**
   `WilsonLawBridge.lean` defines the forgetful gauge-group map
   `YangMills.GaugeGroup.core`, proves `wilsonEnergy_eq_core`, and proves
   `wilsonLaw_eq_core`. Furthermore, `WilsonFamily.haar_eq_core` proves
   uniqueness of the normalized invariant Haar data on the same compact
   second-countable matrix group. `WilsonFamily.law_eq_core` and
   `finiteMoment_eq_core` therefore transport the actual public lattice
   moments into the normalized, gauge-invariant `YM.Wilson.law` API.

2. **Coordinate convention, linear level.**
   `SmoothGeometry/YangMillsCoordinates.lean` provides an explicit linear
   equivalence between P⊗AI time-first points and the upstream time-last
   points. It identifies the time coordinate, preserves the physical
   Minkowski square with signature `(+---)`, and preserves distinct
   insertion-point configurations. It does not yet identify the dual
   momentum action, Poincaré representation or OS/Wightman analytic
   continuation. Those require additional compatibility theorems.

3. **First derivative.**
   `Variational/YangMillsBridge.lean` identifies the project first-jet
   derivative with the upstream totalized directional Fréchet derivative.
   It does not identify higher polynomial jets or geometric jet bundles.

## Open physical integration conditions

| Review gate | Current upstream interface | Required before a stronger claim |
| --- | --- | --- |
| Phase selection | `Properties.wilson` controls `correlation none`; the Wightman boundary uses `correlation (some T.selected)` | Prove that the selected vacuum/phase arises from the same Wilson extraction, together with the needed extremality/clustering properties. `mixture`, full support and continuity alone do not suffice. |
| Correlator algebra | `Hierarchy.correlation` is an unrestricted function on tagged field insertions | Require or prove multilinearity in each fixed-degree insertion, including zero-field vanishing, before treating it as an operator-valued Schwinger hierarchy. |
| Operator degree | `Reconstructed.injective` is degreewise only, while `toLabel` maps each `Field d` into a common label space | Specify whether engineering degree is a grading or filtration; prohibit contradictory nonzero identifications, or prove that all OPE weights are representation-independent. Zero field can legitimately appear in every degree. |
| Trace identification | `centeredTrace : Field 4` is a designated field tag | Relate it to a renormalized Wilson plaquette/`tr(F²)` operator before claiming the trace two-point asymptotic is about that physical composite. `TraceTest.excludes` concerns the stated *finite* Wick profiles only. |
| Wightman spectral convention | Mathlib's `charFun` uses a Euclidean scalar-product Fourier phase | The flat spacetime signature now matches; still prove Minkowski momentum/covector identification and Poincaré-boost compatibility for that character. |
| Full QFT reconstruction | The imported OS-related file is `Hilbert/Kolmogorov.lean` only | Positive kernels are not an OS reconstruction. Separate reflection-positive Schwinger data, the Hilbert quotient and semigroup, and the Wightman field construction are required. |
| Coincident-point observables | Imported continuum limits use separated insertions | Diagonal/contact-term extensions and operator renormalization must be stated and proved separately. |

## Honest scope

- `YangMills.JointExistence` is imported as a **proposition**, not a proved
  theorem. No proof of it, no positive mass gap, no uniqueness of the
  thermodynamic/infinite-volume limit, and no exclusion of every generalized
  free theory are claimed by this PR.
- The finite Wilson-law theorem is an **actual equality of measures**, not
  merely a structural similarity. Haar uniqueness establishes that its
  canonical normalization agrees with each `WilsonFamily.haar`.
- Future import candidates (`Maxwell/Exterior`, `Maxwell/Shell`,
  `Maxwell/Wick`, `Labels/Grading`, `Mink/Poincare`, `OS/Core`, and
  `PublicView`) are **not** part of this 18-module import. Their interfaces
  should be evaluated independently with their full dependency and license
  provenance before additional PRs.

Original source: [`yang-mills-group/OpenAI-YM-20261028`](https://github.com/yang-mills-group/OpenAI-YM-20261028),
commit `3456e5e75cf8d4cd558955a5c7638fba2d68f464` (Apache-2.0).
