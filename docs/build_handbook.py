"""Render the Markdown handbook and bundle the existing doc-gen4 reference."""

import json
import re
import shutil
import subprocess
from html.parser import HTMLParser
from pathlib import Path
from tempfile import TemporaryDirectory
from urllib.parse import unquote, urlsplit

from brand_api import brand_api


REPOSITORY = Path(__file__).resolve().parents[1]
DOCS = REPOSITORY / "docs"
DOCBUILD = REPOSITORY / "docbuild"
API = DOCBUILD / ".lake" / "build" / "doc"
OUTPUT = DOCBUILD / "handbook"


class PageLinks(HTMLParser):
    def __init__(self, path: Path) -> None:
        super().__init__()
        self.anchors: set[str] = set()
        self.links: set[str] = set()
        self.feed(path.read_text(encoding="utf-8"))

    def handle_starttag(self, tag, attributes):
        attrs = dict(attributes)
        if attrs.get("id"):
            self.anchors.add(attrs["id"])
        if tag == "a" and attrs.get("href"):
            self.links.add(attrs["href"])


def check_handbook_links(directory: Path) -> None:
    pages = {path: PageLinks(path) for path in directory.glob("*.html")}
    broken = []
    for path, page in pages.items():
        for href in sorted(page.links):
            link = urlsplit(href)
            if link.scheme or link.netloc:
                continue
            target = (path.parent / unquote(link.path)) if link.path else path
            if target.is_dir():
                target /= "index.html"
            fragment = unquote(link.fragment)
            exists = target.is_file()
            if exists and fragment and target.suffix == ".html":
                exists = fragment in (pages.get(target) or PageLinks(target)).anchors
            if not exists:
                broken.append(f"{path.name} → {href}")
    if broken:
        raise SystemExit("Broken handbook links. Rebuild the API if needed.\n" + "\n".join(broken))


def stage_page(source: Path, destination: Path, repository_source: str) -> None:
    heading, _, body = source.read_text(encoding="utf-8").partition("\n")
    if not heading.startswith("# "):
        raise SystemExit(f"Expected a top-level title in {source}")
    metadata = {
        "title": heading[2:],
        "source-path": source.relative_to(REPOSITORY).as_posix(),
        "repository-source": repository_source,
    }
    # GitHub uses plain Mermaid fences. Quarto uses a diagram cell.
    body = re.sub(r"^```mermaid[ \t]*$", "```{mermaid}", body, flags=re.MULTILINE)
    # Display-math delimiters occupy their own lines. Inline escaped brackets
    # include literal citation labels and must retain their Markdown meaning.
    body = re.sub(r"^([ \t]*)\\[\[\]][ \t]*$", r"\1$$", body, flags=re.MULTILINE)
    front_matter = "\n".join(
        f"{key}: {json.dumps(value, ensure_ascii=False)}" for key, value in metadata.items()
    )
    destination.write_text(f"---\n{front_matter}\n---\n{body}", encoding="utf-8")


def main() -> None:
    quarto = shutil.which("quarto")
    if quarto is None:
        raise SystemExit("Install Quarto and add it to PATH. See docs/build.md.")
    if not (API / "ProjectAInos.html").is_file():
        raise SystemExit("Build ProjectAInos:docs in docbuild first. See docs/build.md.")

    revision = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=REPOSITORY, text=True
    ).strip()
    repository_source = f"https://github.com/MGYamada/ProjectAInos/blob/{revision}/"
    with TemporaryDirectory(prefix="handbook-", dir=DOCBUILD) as temporary:
        staging = Path(temporary)
        for name in ("_quarto.yml", "links.lua"):
            shutil.copy2(DOCS / "handbook" / name, staging / name)
        stage_page(REPOSITORY / "README.md", staging / "research-plan.qmd", repository_source)
        for source in sorted(DOCS.glob("*.md")):
            name = "index" if source.name == "README.md" else source.stem
            stage_page(source, staging / f"{name}.qmd", repository_source)

        subprocess.run([quarto, "render"], cwd=staging, check=True)
        generated = staging / "_site"
        shutil.copytree(API, generated / "api", ignore=shutil.ignore_patterns(".DS_Store"))
        brand_api(generated / "api", handbook=True)
        check_handbook_links(generated)
        if OUTPUT.exists():
            OUTPUT.rename(staging / "previous")
        try:
            generated.rename(OUTPUT)
        except OSError:
            previous = staging / "previous"
            if previous.exists():
                previous.rename(OUTPUT)
            raise
    print(f"Handbook built in {OUTPUT}")


if __name__ == "__main__":
    main()
