"""Fast tests for handbook staging and local links."""

import json
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch

import build_handbook


class StagePageTests(unittest.TestCase):
    def test_metadata_and_markdown_transformations(self):
        with TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "docs" / "sample.md"
            source.parent.mkdir()
            destination = root / "sample.qmd"
            repository_source = "https://example.test/repository/"
            source.write_text(
                '# A "quoted" title — λ\n\n'
                'Inline \\[citation\\] and `\\[inline\\]`.\n\n'
                '```mermaid\nflowchart LR\n  A --> B\n```\n\n'
                '  \\[\n  x = y\n  \\]\n\n'
                '```python\nprint("unchanged")\n```\n',
                encoding="utf-8",
            )
            with patch.object(build_handbook, "REPOSITORY", root):
                build_handbook.stage_page(source, destination, repository_source)

            _, metadata, markdown = destination.read_text(encoding="utf-8").split("---\n", 2)
            self.assertEqual(
                {key: json.loads(value) for key, value in
                 (line.split(": ", 1) for line in metadata.splitlines())},
                {
                    "title": 'A "quoted" title — λ',
                    "source-path": "docs/sample.md",
                    "repository-source": repository_source,
                },
            )
            self.assertEqual(
                markdown,
                '\nInline \\[citation\\] and `\\[inline\\]`.\n\n'
                '```{mermaid}\nflowchart LR\n  A --> B\n```\n\n'
                '  $$\n  x = y\n  $$\n\n'
                '```python\nprint("unchanged")\n```\n',
            )


class HandbookLinksTests(unittest.TestCase):
    def setUp(self):
        temporary = TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)

    def write(self, name, html):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(html, encoding="utf-8")

    def test_local_fragments_and_bundled_api(self):
        self.write("index.html", """
            <h1 id="top">Top</h1>
            <a href="#top">Within this page</a>
            <a href="chapter.html#part%20one">Chapter fragment</a>
            <a href="api/">API index</a>
            <a href="api/ProjectAInos.html#theorem">API theorem</a>
            <a href="https://example.test/missing#fragment">External</a>
            <a href="//example.test/missing">External without scheme</a>
            <a href="mailto:editor@example.test">Email</a>
        """)
        self.write("chapter.html", '<h2 id="part one">Section</h2>')
        self.write("api/index.html", "<h1>API</h1>")
        self.write("api/ProjectAInos.html", '<div id="theorem">Theorem</div>')
        build_handbook.check_handbook_links(self.root)

    def test_missing_pages_and_fragments_report_origin_and_target(self):
        self.write("index.html", """
            <a href="missing.html">Missing page</a>
            <a href="#missing">Missing in-page fragment</a>
            <a href="api/ProjectAInos.html#missing">Missing API fragment</a>
        """)
        self.write("api/ProjectAInos.html", '<div id="present">Theorem</div>')
        with self.assertRaises(SystemExit) as failure:
            build_handbook.check_handbook_links(self.root)

        for link in ("missing.html", "#missing", "api/ProjectAInos.html#missing"):
            with self.subTest(link=link):
                self.assertIn(f"index.html → {link}", str(failure.exception))


if __name__ == "__main__":
    unittest.main()
