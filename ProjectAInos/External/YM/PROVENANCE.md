# Imported Wilson Yang--Mills foundations and public specifications

The Lean files in this directory originate from
[`yang-mills-group/OpenAI-YM-20261028`](https://github.com/yang-mills-group/OpenAI-YM-20261028),
at commit [`3456e5e75cf8d4cd558955a5c7638fba2d68f464`](https://github.com/yang-mills-group/OpenAI-YM-20261028/commit/3456e5e75cf8d4cd558955a5c7638fba2d68f464).

License: **Apache License 2.0**. The root `LICENSE` supplies the license text;
the root `NOTICE` preserves applicable attribution from the upstream
[`NOTICE`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/main/NOTICE).
The upstream [`THIRD_PARTY.md`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/main/THIRD_PARTY.md)
describes third-party dependencies and source adaptations. None of the
nine Mathlib-adapted modules named in that upstream `NOTICE` has been copied
into this subset. The public challenge interfaces have separate provenance,
which the root `NOTICE` records.

## Selected modules

All 24 files below are copied from the upstream source. Their proof bodies
have been preserved where Lean 4.35 permits; P⊗AI changes the module paths
and adds Lean 4.35 `module`, `public import`, and `@[expose] public section`
directives. Minor compatibility changes (explicit mathlib analytic import,
public type synonym used in a signature, updated deprecated names, explicit
namespace qualification and local lint adjustments) are tracked in the diff.
The import and visibility changes are marked at the top of every file.

| Phase | Imported modules | Scope |
| --- | --- | --- |
| 1: Analysis | `Analytic/Implicit`; `Analysis/{Symmetric,SmoothJets,Homogeneous,Nonnegative}`; `Distribution/Tests`; `Hilbert/Kolmogorov`; `Extraction/Orders` | Higher derivatives and local analytic implicit functions, Schwartz tests, positive kernels, Hilbert reconstruction, limit extraction |
| 2: Finite Wilson | `Gauge/MatrixGroup`; `Space/Index`; `Lattice/{Site,Path,Faces}`; `Wilson/{Law,Symmetry}` | Compact matrix gauge groups, discrete gauge geometry and Wilson-law invariance |
| 3: Specification | `PublicTheory`; `PublicWilson`; `ChallengeSpec` | Standalone public Yang--Mills/Wightman/Wilson specifications |
| 4: Maxwell jets | `Gauge/{Lie,Colors}`; `Space/{Configurations,Orthogonal}`; `Labels/Jet`; `Maxwell/Exterior` | Homogeneous closed curvature jets and radial-gauge potential recovery |

The Maxwell dependency closure has **11 modules**: the six files in phase 4
and the existing `Analysis/{Symmetric,SmoothJets,Homogeneous}`,
`Gauge/MatrixGroup`, and `Space/Index`. It is pinned to the same commit above.
Its Lean 4.35 changes, beyond the import/export wrapper, are:

- `Gauge/Lie`: replace redundant instance-local `haveI` with `have`; make
  `tangent_generates`' matrix coercion and `map_pow` steps explicit.
- `Gauge/Colors`: replace redundant instance-local `haveI` with `have`.
- `Space/Configurations`: replace deprecated `mem_setOf` with `mem_ofPred`.
- `Space/Orthogonal`: use `have`; prove the reflected coordinate formula
  explicitly to avoid recursive simplification of `eq_comm`.
- `Labels/Jet`: unfold `turn`, `value`, and `Tensor.diagonal` explicitly in
  `turn_value`, replacing a coercion-sensitive simplification.
- `Maxwell/Exterior`: no mathematical proof-body changes.

The original `YM` namespaces and theorem statements are retained. The
project-authored `Electrodynamics/PolynomialRadial.lean` adapts the upstream
`curl_inverse` argument to any real normed target, including ℝ. Its
`radial_upstream` theorem identifies the original color-valued formula;
`mapCoefficients_closed` and `radial_map` prove compatibility with linear
component extraction. `PolynomialBridge.lean` transports coefficient
evaluation, exterior differentiation, and the coefficient `1/(j+2)` through
an explicit continuous linear equivalence `(t,x,y,z) ↦ (z,x,y,t)`.
This is a polynomial differential-form result. It does not assert a global
potential for arbitrary closed forms or a Euclidean-to-Lorentzian dynamics
correspondence. Both nonzero degrees 0 and 1 are checked in Lean.

Each phase's dependency-closed set is included; no other modules from the
approximately 9,500-file upstream proof are imported. In particular,
`YangMills.JointExistence` is currently a **proposition**, not a theorem
proved in P⊗AI. This import does not assert mass-gap positivity.

## Post-import semantic bridges

`WilsonLawBridge.lean` adapts only the **finite** energy and probability-law
comparison from upstream [`WilsonBridge.lean`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/main/WilsonBridge.lean)
at the pinned source commit. Its `wilsonEnergy_eq_core` and
`wilsonLaw_eq_core` identify the public challenge definitions with the
already proved finite-lattice Wilson law for canonical probability Haar.
For an arbitrary public `WilsonFamily`, `WilsonFamily.haar_eq_core` derives
canonical Haar from its normalized Haar hypotheses using measure uniqueness,
and `WilsonFamily.law_eq_core` and `finiteMoment_eq_core` transfer the result
to the actual lattice moments. The remaining upstream extraction and
continuum construction are not imported.

`ProjectAInos/SmoothGeometry/YangMillsCoordinates.lean` is a project-authored
adapter between the time-first and time-last conventions. It proves
compatibility of the affine point action, future cone, and Fourier pairing.
`SemanticContracts.lean` is a project-authored extension expressing the
additional selected-limit and correlator-algebra premises.
See [SEMANTICS.md](SEMANTICS.md) for the precise statements and open conditions.

## Integration boundaries

- Original declaration namespaces (`YM`, `YM.Analysis`, `YM.Wilson`, and
  `YangMills`) are preserved for auditability and to avoid silently changing
  theorem statements.
- P⊗AI's `Variational` first-jet API is preserved. The imported jet tools
  are separate, higher-order analytic results; they are not equivalent to a
  general smooth jet-bundle theory. The project-local
  `Variational/YangMillsBridge.lean` proves that the shared first-jet
  derivative agrees with the imported directional derivative.
- P⊗AI's shared Lorentz model uses **time first**, while the imported
  public Yang--Mills spacetime uses **time last**. The point equivalence
  transports the flat affine action and Fourier covector pairing. Full
  Wightman representation transport and analytic continuation are separate
  problems.
- The upstream `YM.Gauge.Gauge` and public `YangMills.GaugeGroup` remain
  distinct types; the project now proves the concrete forgetful map and
  finite Wilson-action/law comparison for the probability Haar in each
  `WilsonFamily`, without assuming a full equivalence of representations.
- The Wilson-law results cover the stated finite-lattice setting. They do
  not establish thermodynamic-limit uniqueness or a positive mass gap.
- The original project targets Lean 4.32.0; P⊗AI targets Lean 4.35.0.
  Import path availability is not proof of elaborator compatibility. These
  modules must pass compilation and the existing CI axiom audit before merge.

## Reverification

Run from the P⊗AI repository root:

```sh
lake exe cache get
lake build --wfail ProjectAInos
lake env lean -DwarningAsError=true checks/YangMillsImportAPI.lean
lake env lean -DwarningAsError=true checks/ElectrodynamicsAPI.lean
lake env lean -DwarningAsError=true checks/AxiomAudit.lean
lake exe mk_all --check --lib ProjectAInos
```

The P⊗AI CI additionally audits transitive axioms with its existing allowlist
(`propext`, `Classical.choice`, `Quot.sound`). No additional axioms, `sorry`s,
or assumptions should be accepted to make this port compile.
