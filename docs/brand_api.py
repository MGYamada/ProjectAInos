"""Add project navigation to the doc-gen4 v4.35.0 HTML output."""

from pathlib import Path
from stat import S_IMODE
from tempfile import NamedTemporaryFile


def replace_once(html: str, anchor: str, replacement: str) -> str:
    if replacement in html:
        return html
    if html.count(anchor) != 1:
        raise SystemExit(f"Expected one doc-gen4 HTML anchor: {anchor}")
    return html.replace(anchor, replacement, 1)


def brand_api(directory: Path, *, handbook: bool = False) -> None:
    project = '<a href="./ProjectAInos.html">Project API</a>'
    thermo = '<a href="./ProjectAInos/Thermodynamics/Basic.html">Thermodynamics</a>'
    homepage = (
        "<h1>Project AInos</h1>"
        "<p>Lean 4 API reference for the formalization of theoretical physics.</p>"
        f"<ul><li>{project}</li><li>{thermo} — adiabatic stability (A6)</li></ul>"
    )
    general_heading = "<h3>General documentation</h3>"
    navigation = (
        '<h3><a href="./">Project AInos</a></h3>'
        f'<div class="nav_link">{project}</div>'
        f'<div class="nav_link">{thermo}</div>'
        + general_heading
    )

    index = directory / "index.html"
    sidebar = directory / "navbar.html"
    original_index = index.read_text(encoding="utf-8")
    original_sidebar = sidebar.read_text(encoding="utf-8")
    branded_index = replace_once(
        original_index, "<title>Index</title>", "<title>Project AInos | Lean API Reference</title>"
    )
    branded_index = replace_once(
        branded_index, "<h1>Welcome to the documentation page </h1>", homepage
    )
    branded_sidebar = replace_once(original_sidebar, general_heading, navigation)
    if handbook:
        handbook_home = '<p><a href="../index.html">Documentation handbook</a></p>'
        handbook_nav = (
            '<div class="nav_link"><a href="../index.html" target="_top">'
            'Documentation handbook</a></div>'
        )
        branded_index = replace_once(
            branded_index, homepage, homepage + handbook_home
        )
        branded_sidebar = replace_once(branded_sidebar, navigation, handbook_nav + navigation)

    for path, original, branded in (
        (index, original_index, branded_index),
        (sidebar, original_sidebar, branded_sidebar),
    ):
        if branded != original:
            with NamedTemporaryFile(
                mode="w", encoding="utf-8", dir=directory, delete=False
            ) as output:
                output.write(branded)
            temporary = Path(output.name)
            temporary.chmod(S_IMODE(path.stat().st_mode))
            temporary.replace(path)


if __name__ == "__main__":
    repository = Path(__file__).resolve().parents[1]
    brand_api(repository / "docbuild" / ".lake" / "build" / "doc")
