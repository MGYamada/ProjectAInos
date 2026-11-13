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

2. **Coordinates, affine action, and Fourier phase.**
   `Integrations/YangMillsCoordinates.lean` transports time-first points
   into the upstream time-last convention and preserves the invariant
   quadratic form, future cone, and distinct insertion points.
   `properLorentz` conjugates project transformations, including boosts,
   into the upstream proper orthochronous type. `poincare_apply` and
   `poincare_pullback_point` identify the affine action and the inverse
   argument used in the upstream test pullback.
   `fourierMomentum_pairing` identifies the Euclidean Fourier pairing with
   the `(+---)` metric pairing after lowering the physical momentum.
   `fourierMomentum_covariance` proves the inverse-action rule for that
   covector. The inverse identification preserves the forward cone.
   `spectralRepresentation_minkowski` rewrites the phase in the existing
   W0 identity at the same translation argument.

3. **First derivative.**
   `Integrations/YangMillsBridge.lean` identifies the project first-jet
   derivative with the upstream totalized directional Fréchet derivative.
   The statement concerns first derivatives.

## Additional premises on candidate hierarchies

`SemanticContracts.lean` adds project-owned contracts for the review gates.
The imported `Properties` and `JointExistence` retain their upstream meanings.

- **Selected phase (P1).** `SelectedWilsonLimit` asks for the selected phase
  on the same finite Wilson family, order of limits, and separated tests.
  Given the averaged Wilson limit, `selectedWilsonLimit_iff` proves this is
  equivalent to equality of the selected and averaged smeared moments.
  The proof uses uniqueness first at each suitable fixed volume, then along
  the volume sequence. `IntegratedProperties` requires that equality
  explicitly. A proof of the equality for a concrete candidate, or a new
  phase-selecting lattice construction, is a separate existence problem.
  Extremality and clustering require their own hypotheses and results.
- **Correlator algebra (P1).** `CorrelatorAlgebra` requires complex
  multilinearity at separated points for each fixed degree profile, in
  each phase and in the average. The canonical map `labelSum` from the
  algebraic direct sum of the degree spaces to Wightman labels must be
  bijective. This gives degreewise injectivity, a unique degree for each
  nonzero homogeneous label, and well-defined OPE weights for tuples of
  such labels. The derived correlator lemmas prove zero-insertion vanishing
  and equality for tagged tuples representing the same labels.
  `sum_not_tag` proves that a sum of nonzero fields in distinct degrees
  cannot be represented by a single tag. The graded contract therefore
  uses coverage by finite sums. It does not inherit the upstream
  `Reconstructed.covers` premise, which asks for single-tag coverage.
- **Trace identification (P2).** `TraceTest.shortDistance` constrains the
  two-point evaluation of the designated `centeredTrace : Field 4` tag.
  `TraceTest.excludes` rules out eventual exact equality near zero with each
  specified finite Wick profile. Identifying this tag with a renormalized
  plaquette or tr(F²) composite requires a choice of lattice observable and
  renormalization and a convergence theorem for that choice.

## Further mathematical work

The coordinate results concern the point action and Fourier pairing.
Transport of full Wightman representations and Euclidean-to-Minkowski
analytic continuation are separate. OS reconstruction requires
reflection-positive Schwinger data, the corresponding Hilbert quotient
and semigroup, and the Wightman field construction. Coincident-point and
contact terms require extensions of the separated-point distributions.
These steps also leave the continuum existence and mass-gap problems open.

## Honest scope

- `YangMills.JointExistence` is imported as a **proposition**, not a proved
  theorem. No proof of it, no positive mass gap, no uniqueness of the
  thermodynamic/infinite-volume limit, and no exclusion of every generalized
  free theory are claimed by this PR.
- The finite Wilson-law theorem is an **actual equality of measures**, not
  merely a structural similarity. Haar uniqueness establishes that its
  canonical normalization agrees with each `WilsonFamily.haar`.
- The statements above describe the original 18-module import. The Maxwell
  homogeneous-jet closure (`Maxwell/Exterior` with `Gauge/{Lie,Colors}`,
  `Space/{Configurations,Orthogonal}` and `Labels/Jet`) was imported afterwards
  as phase 4; [PROVENANCE.md](PROVENANCE.md) lists all 24 files.
- The remaining import candidates (`Maxwell/Shell`, `Maxwell/Wick`,
  `Labels/Grading`, `Mink/Poincare`, `OS/Core`, and `PublicView`) are **not**
  imported. Their interfaces should be evaluated independently with their full
  dependency and license provenance before additional PRs.

Original source: [`yang-mills-group/OpenAI-YM-20261028`](https://github.com/yang-mills-group/OpenAI-YM-20261028),
commit `3456e5e75cf8d4cd558955a5c7638fba2d68f464` (Apache-2.0).
