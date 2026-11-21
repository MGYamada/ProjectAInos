"""Build Lean by subject and check the assembled public library."""

import argparse
import json
import os
from pathlib import Path
import subprocess
import tarfile
from tempfile import TemporaryDirectory


SUBJECTS = {
    "thermodynamics": ("Thermodynamics",),
    "mechanics": ("Mechanics", "SmoothAlgebra", "Variational"),
    "classical-fields": (
        "SpecialRelativity", "Electrodynamics", "GeneralRelativity", "SmoothGeometry",
        "SpecialFunctions", "External", "Integrations", "QuantumMechanics", "QuantumFieldTheory",
    ),
}
FAMILY_OWNERS = {family: subject for subject, families in SUBJECTS.items() for family in families}
OBJECTS = Path(".lake/build/lib/lean")
OBJECT_SUFFIXES = (".olean", ".olean.private", ".olean.server", ".ir", ".ir.sig")


def run(*args, **kwargs):
    subprocess.run(args, check=True, **kwargs)


def group_checks(modules):
    checks = sorted(Path("checks").glob("*.lean"))
    headers = json.loads(subprocess.check_output(["lean", "--deps-json", *checks]))["imports"]
    assignments = {subject: [] for subject in (*SUBJECTS, "integration")}
    for check, header in zip(checks, headers, strict=True):
        if header["errors"]:
            raise SystemExit(f"Cannot parse imports of {check}: {header['errors']}")
        imports = {imp["module"] for imp in header["result"]["imports"]}
        unknown = {name for name in imports if name.startswith("ProjectAinos.") and name not in modules}
        if unknown:
            raise SystemExit(f"Unknown project imports in {check}: {sorted(unknown)}")
        owners = {modules[name][1] for name in imports if name in modules}
        if "ProjectAinos" in imports or not owners or ("thermodynamics" in owners and len(owners) > 1):
            subject = "integration"
        else:
            # Field consumers can import small pieces of mechanics. Lake builds
            # these direct check imports and their transitive dependencies.
            subject = next(group for group in reversed(SUBJECTS) if group in owners)
        assignments[subject].append((check, imports))
    return assignments


def build_subject(subject, archive_path, owned_sources, checks, modules):
    check_imports = {modules[name][0] for _, imports in checks for name in imports if name in modules}
    targets = sorted(set(owned_sources) | check_imports)
    print(f"{subject}: {len(owned_sources)} owned modules and {len(checks)} checks", flush=True)
    run("lake", "build", "--wfail", *targets)
    if checks:
        run("checks/run.sh", *(check for check, _ in checks))

    # Each object belongs to one archive, even when another subject built it
    # as a dependency. The integration job needs no Lake trace or C output.
    with tarfile.open(archive_path, "w") as archive:
        for source in owned_sources:
            for suffix in OBJECT_SUFFIXES:
                relative = source.with_suffix(suffix)
                path = OBJECTS / relative
                if suffix == ".olean" or path.is_file():
                    archive.add(path, arcname=relative)


def check_integration(archive_dir, checks):
    run("lake", "exe", "mk_all", "--check", "--lib", "ProjectAinos")
    with TemporaryDirectory(prefix="ainos-ci-") as directory:
        objects = Path(directory)
        for subject in SUBJECTS:
            with tarfile.open(archive_dir / f"{subject}.tar") as archive:
                archive.extractall(objects, filter="data")

        lake_path = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], text=True)
        dependencies = [p for p in lake_path.strip().split(os.pathsep) if Path(p).resolve() != OBJECTS.resolve()]
        lean_path = os.pathsep.join([directory, *dependencies])
        run("lake", "env", "env", f"LEAN_PATH={lean_path}", "lean", "-DwarningAsError=true",
            "-DautoImplicit=false", "-DrelaxedAutoImplicit=false",
            "-o", objects / "ProjectAinos.olean", "ProjectAinos.lean")
        if checks:
            run("checks/run.sh", *(check for check, _ in checks),
                env={**os.environ, "CHECK_LEAN_PATH": lean_path})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("subject", choices=(*SUBJECTS, "integration"))
    parser.add_argument("artifacts", type=Path, help="output tar file, or input directory for integration")
    args = parser.parse_args()
    args.artifacts = args.artifacts.resolve()
    os.chdir(Path(__file__).resolve().parents[1])

    modules = {}
    for source in sorted(Path("ProjectAinos").rglob("*.lean")):
        family = source.relative_to("ProjectAinos").with_suffix("").parts[0]
        if family not in FAMILY_OWNERS:
            raise SystemExit(f"No CI subject owns {source}")
        modules[".".join(source.with_suffix("").parts)] = (source, FAMILY_OWNERS[family])
    checks = group_checks(modules)[args.subject]
    if args.subject == "integration":
        check_integration(args.artifacts, checks)
    else:
        sources = [source for source, group in modules.values() if group == args.subject]
        build_subject(args.subject, args.artifacts, sources, checks, modules)


if __name__ == "__main__":
    main()
