# Building the HTML Handbook and Lean API Reference

The root `lean-toolchain` pins Lean. The root Lake manifest pins Mathlib and its
dependencies. The documentation workspace uses the same Lean release and
shares the root package cache. Install `elan`, a C compiler, and Python 3 for
the local preview.

## Build the library

From the repository root, fetch the full Mathlib cache for the pinned dependency
revision and build the library.

```sh
lake exe cache get
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

For a standalone API preview, run `python3 docs/brand_api.py` from the
repository root to add the Project AInos heading and shortcuts. The combined
handbook build applies the branding to its bundled copy.

When the root package's dependencies change, run
`MATHLIB_NO_CACHE_ON_UPDATE=1 lake update ProjectAInos` from `docbuild/` before
rebuilding. When upgrading Lean, update the Mathlib and doc-gen4 versions to
the matching release. [doc-gen4 setup for v4.35.0](https://github.com/leanprover/doc-gen4/blob/v4.35.0/README.md)

## Build the HTML handbook

Install [Quarto](https://quarto.org/docs/download/) and make `quarto` available
on `PATH`. After building the API reference above, run this from the repository root.

```sh
python3 docs/build_handbook.py
```

The script stages the root research plan and the Markdown files in `docs/` for
Quarto. The [documentation index](README.md) becomes the home page, and the
sidebar groups the guides by subject. The output is `docbuild/handbook/`, with
the generated reference at `api/`. Handbook links to project `.lean` files open
the corresponding API module pages. The API home and sidebar link back to the
handbook, and the API's source links follow the `DOCGEN_SRC` setting used when
generating the reference. The build checks local links and anchors from the
handbook before replacing a previous build.

For Markdown edits, rerun the handbook script. For changes to Lean definitions
or docstrings, rebuild the API reference first. Quarto and doc-gen4 output stay
under the Git-ignored `docbuild/` directory.

## Preview locally

From the repository root, serve the combined site over HTTP.

```sh
python3 -m http.server --bind 127.0.0.1 --directory docbuild/handbook 8000
```

Open [the local handbook](http://127.0.0.1:8000/). Use the **Lean API** link in
the navbar or follow a module link from a guide. In the API sidebar, use
**Documentation handbook** to return to the handbook.
