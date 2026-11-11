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

All 18 files below are copied from the upstream source. Their proof bodies
have not been intentionally altered; P⊗AI changes the module paths and adds
Lean 4.35 `module`, `public import`, and `@[expose] public section` directives.
These changes are marked at the top of every imported file.

| Phase | Imported modules | Scope |
| --- | --- | --- |
| 1: Analysis | `Analytic/Implicit`; `Analysis/{Symmetric,SmoothJets,Homogeneous,Nonnegative}`; `Distribution/Tests`; `Hilbert/Kolmogorov`; `Extraction/Orders` | Higher derivatives and local analytic implicit functions, Schwartz tests, positive kernels, Hilbert reconstruction, limit extraction |
| 2: Finite Wilson | `Gauge/MatrixGroup`; `Space/Index`; `Lattice/{Site,Path,Faces}`; `Wilson/{Law,Symmetry}` | Compact matrix gauge groups, discrete gauge geometry and Wilson-law invariance |
| 3: Specification | `PublicTheory`; `PublicWilson`; `ChallengeSpec` | Standalone public Yang--Mills/Wightman/Wilson specifications |

Each phase's dependency-closed set is included; no other modules from the
approximately 9,500-file upstream proof are imported. In particular,
`YangMills.JointExistence` is currently a **proposition**, not a theorem
proved in P⊗AI. This import does not assert mass-gap positivity.

## Integration boundaries

- Original declaration namespaces (`YM`, `YM.Analysis`, `YM.Wilson`, and
  `YangMills`) are preserved for auditability and to avoid silently changing
  theorem statements.
- P⊗AI's `Variational` first-jet API is preserved. The imported jet tools
  are separate, higher-order analytic results; they are not equivalent to a
  general smooth jet-bundle theory.
- P⊗AI's shared Lorentz model uses **time first**, while the imported
  public Yang--Mills spacetime uses **time last**. Any bridge must implement
  an explicit coordinate permutation and prove sign compatibility.
- The upstream `YM.Gauge.Gauge` and public `YangMills.GaugeGroup` remain
  distinct. No unproved equivalence between their representations is assumed.
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
lake exe mk_all --check --lib ProjectAInos
```

The P⊗AI CI additionally audits transitive axioms with its existing allowlist
(`propext`, `Classical.choice`, `Quot.sound`). No additional axioms, `sorry`s,
or assumptions should be accepted to make this port compile.
