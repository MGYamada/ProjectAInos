# Project AInos contributor instructions

## Project layout

- Use `README.md` as the research plan and subject outline.
- Put definitions and machine-checked proofs in the Lean library. Keep
  `ProjectAInos.lean` current with the library modules.
- Put symbolic and numerical Python experiments in `experiments/` as an
  independent package. Start with SymPy for exact calculations. Add SciPy
  when an experiment needs numerical solvers.
- Put documentation tooling in `docs/`.
- Keep `tex/` and `.lake/` local and Git-ignored.
- Track `docbuild/lakefile.toml`, `docbuild/lean-toolchain`, and
  `docbuild/lake-manifest.json`. Keep all other `docbuild/` contents local and
  Git-ignored.

## Verification

- Require the **Lean build** job for merges into `main`. Its checks cover Lean
  warnings, root-module imports, and transitive axiom dependencies. The
  axiom allowlist is `propext`, `Classical.choice`, and `Quot.sound`. Express
  physical premises as explicit hypotheses or predicates.
- Run short, reproducible Python checks in the separate, non-required
  **Experiments** workflow for changes to the experiment package. Run long calculations
  on demand and record the parameters, tolerances, and random seeds when
  applicable.
- Use experimental results to test examples and guide conjectures. Verify
  formal claims in Lean.
- Generate API documentation on demand using `docs/build.md`. Keep
  doc-gen4 generation separate from the required Lean job.

## Run the Python checks locally

From the repository root, use Python 3.12 or newer.

```sh
python3 -m venv experiments/.venv
experiments/.venv/bin/python -m pip install ./experiments
experiments/.venv/bin/python -m ainos_experiments.verify_identities
```
