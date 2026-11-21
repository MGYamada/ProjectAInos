# Project Ainos contributor instructions

## Project layout

- Use `README.md` as the research plan and subject outline.
- Put definitions and machine-checked proofs in the Lean library. Keep
  `ProjectAinos.lean` current with the library modules.
- Put shared mathematics in `ProjectAinos/SmoothAlgebra/`,
  `ProjectAinos/SmoothGeometry/`, `ProjectAinos/Variational/` and
  `ProjectAinos/SpecialFunctions/`. These
  directories import no physics module; `checks/CoreImports.lean` enforces it.
- Use the plans `docs/cinfty-*.md` for the targets of each textbook section
  and their ledgers, the guides `docs/<subject>.md` for the implemented
  declarations, and `docs/*-notes.md` for observations.
- Put symbolic and numerical Python experiments in `experiments/` as an
  independent package. Start with SymPy for exact calculations. Add SciPy
  when an experiment needs numerical solvers.
- Put documentation tooling in `docs/`.
- Keep `tex/` and `.lake/` local and Git-ignored.
- Track `docbuild/lakefile.toml`, `docbuild/lean-toolchain`, and
  `docbuild/lake-manifest.json`. Keep all other `docbuild/` contents local and
  Git-ignored.

## Verification

- Require the **Lean build** and **Handbook tests** jobs for merges into
  `main`. The Lean checks cover Lean warnings, root-module imports, and
  transitive axiom dependencies. The axiom allowlist is `propext`,
  `Classical.choice`, and `Quot.sound`. Express physical premises as explicit
  hypotheses or predicates.
- Lean builds run concurrently for Thermodynamics, Mechanics, and Classical
  field theory. `checks/ci.py` assigns source modules to a subject and routes
  `checks/*.lean` by their imports. Use the narrowest project imports a check
  needs. Checks that import `ProjectAinos` or span independent subjects run
  at integration. Adding a check needs no new workflow step.
- The required **Lean build** job joins the three results, checks the public
  root and shared import boundary, and audits the assembled Lean environment.
  Pull requests that change no Lean source, checks, Lake configuration,
  toolchain, manifest, or Lean workflow skip the Lean steps. Pushes to `main`
  always run them. The ruleset of `main` also requires **Detect Lean changes**
  and the three subject jobs, so these jobs run in every pull request and
  skip their steps when the Lean steps are not needed.
- Run short, reproducible Python checks in the separate, non-required
  **Experiments** workflow for changes to the experiment package. Run long calculations
  on demand and record the parameters, tolerances, and random seeds when
  applicable.
- Use experimental results to test examples and guide conjectures. Verify
  formal claims in Lean.
- Generate API documentation on demand using `docs/build.md`. Keep
  doc-gen4 generation separate from the required Lean job.

## Lean conventions

- Start each file with the copyright header of the existing files and
  `module`. Import with `public import`, and import a module that is used only
  for its tactics with `import`. Open the declarations with
  `@[expose] public section`.
- Write every binder: `autoImplicit` is off. Do not use `sorry`, `axiom`,
  `set_option maxHeartbeats` or `set_option backward.*`;
  `checks/ForbiddenOptions.lean` enforces the last two. Keep lines within
  100 characters.
- After adding a module, run `lake exe mk_all --lib ProjectAinos`.
- Pin each new public statement with a typed `example` in a `checks/*API.lean`
  file.
- Make an index type an explicit argument of a definition when its other
  arguments do not determine it, and give a generator written with nested
  `Sum.inl` and `Sum.inr` a definition with its full type. Otherwise the
  coercion to a function is searched with a metavariable in the type, and
  each application costs about a second.

## Stating theorems

- Give a proved instance for every structure, and for every theorem whose
  hypotheses are identities in a free C∞-ring. Such a hypothesis holds for
  all real values of the generators, so it can be unsatisfiable while the
  statement type-checks.
- The flow of a vector field that is smooth on all of a Banach space is
  `SmoothGeometry.NonlinearODE.flow`, with the open domain `flowDomain` and
  smooth dependence on the time and the point; the pinned Mathlib has none.
  A solution exists for all times only when `flowDomain X = univ` is proved.
  For a field that is smooth only on an open set, state the theorem for a
  given curve or solution: existence is then an explicit solution, or data.
- A free C∞-ring is the ring of smooth functions on all of `ℝⁿ`. For another
  domain use a global chart of the positions, with which the conjugate
  momenta change; an adjoined inverse whose relation is kept as an element;
  or the open-domain analytic model. A chart of the velocities changes the
  derivative that defines the momentum, so the Legendre correspondence does
  not carry over to it.
- Before recording that a statement is out of reach, check the reason against
  Mathlib. An integral whose integrand has an integrable singularity is a
  Lebesgue integral, and the change-of-variables lemmas cover it.

## Ledgers and notes

- Each plan `docs/cinfty-*.md` has one row for each textbook section. A row
  has one status, and a status is only promoted. The ledgers use *proved*,
  *proved modulo interface*, *hypothesis*, *evidence* and *informal*.
- Close a row when it is *proved*, or when its remark names the proved part
  and gives the reason why the rest is not proved.
- Promote a row to *proved* when its whole target in the dictionary is
  proved. If the proof has a restricted scope, write the scope in the row.
- When a row changes, update the count line and the list of rows closed with
  a remainder, the guide of the subject with its proof map,
  `docs/proof-development.md` and the paragraph of the subject in `README.md`.
- Record an observation that changes an interface, or corrects an earlier
  judgement, as a numbered entry in `docs/*-notes.md` with **Observation**,
  **Interface decision** and **Proof status**.

## Pull requests

- `main` requires an up-to-date branch and resolved review threads in
  addition to the two jobs. Merge `origin/main` into the branch before the
  final push. A stack of `n` pull requests costs `n − 1` further CI runs.
- Close several ledger rows in one pull request. Give the body a summary, a
  list of what is not in the pull request, and the validation commands that
  were run.
- Read the automated review before merging. If it has not finished, say so.
  Fix a valid finding first, in the pull request or in a follow-up when it is
  merged, then reply on the thread and resolve it.

## Run the Lean checks locally

From the repository root, after fetching the Mathlib cache with
`lake exe cache get`:

```sh
lake build --wfail ProjectAinos
lake exe mk_all --check --lib ProjectAinos
checks/run.sh
```

`checks/run.sh` compiles every check file with warnings as errors and prints
one verdict per file. Pass specific check files to run a subset, and set
`JOBS` to change parallelism. `checks/ci.py` also supports local subject
builds and artifact integration with Python 3.12 or newer. Give each subject
run an output archive named `<subject>.tar` in the same directory, then
pass that directory to `python3 checks/ci.py integration`.

## Run the documentation tests locally

The **Handbook tests** job needs only the Python standard library.

```sh
PYTHONPATH=docs python3 -m unittest discover -s docs/tests
```

## Run the Python checks locally

From the repository root, use Python 3.12 or newer.

```sh
python3 -m venv experiments/.venv
experiments/.venv/bin/python -m pip install ./experiments
experiments/.venv/bin/python -m ainos_experiments.verify_identities
```
