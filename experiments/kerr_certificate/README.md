# Kerr certificate generator

These scripts generate `ProjectAinos/GeneralRelativity/Kerr.lean`, the Kerr metric in the
rational Boyer–Lindquist chart `(t, r, χ = cos θ, φ)` with its certified Christoffel symbols and
the vacuum equations (Landau–Lifshitz §104).

- `gen.py` computes the Christoffel table with SymPy and writes the caches `G.pkl` and
  `entries.pkl` (ignored by Git).
- `kast.py` turns the SymPy expressions into Lean terms: exponents are written `^ (n : ℕ)`, and
  the denominators `Σ = r² + a²χ²` and `Δ = r² − 2Mr + a²` are atoms.
- `build.py` fills `template.lean` with the generated lemmas.

From the repository root:

```sh
cd experiments/kerr_certificate
../.venv/bin/python gen.py > /dev/null
../.venv/bin/python build.py ../../ProjectAinos/GeneralRelativity/Kerr.lean
```

The output is the checked-in file byte for byte. Lean checks every generated lemma; the scripts
are not trusted.
