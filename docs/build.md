# Building the Lean API Reference

The root `lean-toolchain` pins Lean. The root Lake manifest pins Mathlib and its
dependencies. The documentation workspace uses the same Lean release and
shares the root package cache. Install `elan`, a C compiler, and Python 3 for
the local preview.

## Build the library

From the repository root, fetch cached artifacts for the initial module's
Mathlib imports and build the library.

```sh
lake exe cache get Mathlib.Algebra.Module.Defs Mathlib.Topology.UniformSpace.Real
lake build ProjectAInos
```

## Set up doc-gen4

Create `docbuild/lakefile.toml` with the following contents. Git ignores the
entire `docbuild/` directory, including its manifest and generated HTML.

```toml
name = "docbuild"
reservoir = false
version = "0.1.0"
packagesDir = "../.lake/packages"

[[require]]
name = "doc-gen4"
git = "https://github.com/leanprover/doc-gen4.git"
rev = "v4.35.0"

[[require]]
name = "ProjectAInos"
path = "../"
```

From `docbuild/`, resolve the documentation dependencies and build the
reference. The source links in this local build open Lean files in VS Code.

```sh
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update doc-gen4
DOCGEN_SRC=vscode lake build ProjectAInos:docs
```

After each documentation build, run `python3 docs/brand_api.py` from the
repository root. This adds the Project AInos heading and shortcuts to the
generated homepage and sidebar.

When the root package's dependencies change, run
`MATHLIB_NO_CACHE_ON_UPDATE=1 lake update ProjectAInos` from `docbuild/` before
rebuilding. When upgrading Lean, update the Mathlib and doc-gen4 versions to
the matching release. [doc-gen4 setup for v4.35.0](https://github.com/leanprover/doc-gen4/blob/v4.35.0/README.md)

## Preview locally

From the repository root, serve the generated reference over HTTP.

```sh
python3 -m http.server --bind 127.0.0.1 --directory docbuild/.lake/build/doc 8000
```

Open [the local API reference](http://127.0.0.1:8000/) and follow the
Thermodynamics shortcut to the stability axiom and its source link.
