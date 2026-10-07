"""tools/cite/: the three old commands still mean what they meant (P10(a)).

`cite_check`, `spec_cite_check` and `docs_check` are entry points of one
module; this fixture tree holds one finding of each kind from each of them and
asserts the finding set through the OLD command names, so folding the rule sets
into one module cannot change what counts as a finding.
"""
import contextlib
import io
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

TOOLS = Path(__file__).resolve().parents[1] / "tools"
sys.path.insert(0, str(TOOLS))
import cite  # noqa: E402
import cite_check  # noqa: E402
import docs_check  # noqa: E402
import spec_cite_check  # noqa: E402
from cite import docs, names, paths  # noqa: E402


class EntryPoints(unittest.TestCase):
    def test_each_old_name_is_its_rule_sets_main(self):
        self.assertIs(cite_check.main, paths.main)
        self.assertIs(spec_cite_check.main, names.main)
        self.assertIs(docs_check.main, docs.main)

    def test_each_old_command_still_runs_and_cite_dispatches_to_them(self):
        for old, ruleset in (("cite_check", "paths"), ("spec_cite_check", "names"),
                             ("docs_check", "docs")):
            direct = subprocess.run([sys.executable, str(TOOLS / f"{old}.py"), "--help"],
                                    capture_output=True, text=True)
            self.assertEqual(direct.returncode, 0, direct.stderr)
            via = subprocess.run([sys.executable, "-m", "cite", ruleset, "--help"],
                                 cwd=TOOLS, capture_output=True, text=True)
            self.assertEqual(via.returncode, 0, via.stderr)
            self.assertEqual(direct.stdout.split("\n", 1)[1], via.stdout.split("\n", 1)[1])
        self.assertEqual(cite.main([]), 2)


class FixtureFindings(unittest.TestCase):
    def test_paths_one_finding_of_each_raised_kind(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            sources = {
                "books/a-book.lisp": "; see `books/never.lisp'\n; and `books/folded.lisp'\n",
                "books/real.lisp": "(in-package \"ACL2\")\n",
                "specs/s.md": "`books/gone-ann.lisp` never existed here.\n",
            }
            for name, text in sources.items():
                (root / name).parent.mkdir(parents=True, exist_ok=True)
                (root / name).write_text(text)
            saved = paths.ROOT
            paths.ROOT = root
            try:
                found = paths.scan(set(sources), {"books/folded.lisp"}, list(sources))
            finally:
                paths.ROOT = saved
        self.assertEqual(
            sorted((f.token, f.klass, f.tier) for f in found),
            [("books/folded.lisp", "drift", "load-bearing"),
             ("books/gone-ann.lisp", "annotated", "spec"),
             ("books/never.lisp", "phantom", "load-bearing")])
        self.assertEqual(paths.verdict(True, [f for f in found if f.tier == "load-bearing"], []), 1)
        self.assertEqual(paths.verdict(False, [1], []), 0)

    def test_names_undefined_and_unused_through_the_old_module(self):
        doc = ("specs/x.md", "`fn-a-gone` `fn-a-live` `fn-a-*` `fn-a` `fn-a-v1`\n")
        listing = {"exemptions": {"fn-b-unused": "prose"}}
        result = spec_cite_check.check({"fn-a-live"}, [doc], listing)
        self.assertEqual(result.unlisted, {"fn-a-gone": ["specs/x.md:1"]})
        self.assertEqual(result.unused, ["exemption fn-b-unused: no longer cited"])
        self.assertEqual((result.resolved, result.ruled),
                         (1, {"template": 1, "short": 1, "tag": 1}))
        self.assertFalse(result.ok)

    def test_docs_inventory_kinds_and_the_retired_fn_config_line(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "docs").mkdir()
            doc = root / "docs" / "d.md"
            doc.write_text(
                "```\n"
                "fn operator /etc/fn/fn.toml health\n"
                "fn operator CONFIG VERB WHATEVER\n"
                "fn operator CONFIG store inspect  # docs-check: skip (kept as written)\n"
                "fn --config /etc/fn/fn.toml run\n"
                "refused operator bad-thing\n"
                "```\n", encoding="utf-8")
            saved = docs.ROOT, docs.DOCS, docs.ARTICLES
            docs.ROOT, docs.DOCS, docs.ARTICLES = root, [doc], []
            try:
                found = docs.inventory()
            finally:
                docs.ROOT, docs.DOCS, docs.ARTICLES = saved
        self.assertEqual(
            [(kind, number, argv is None) for kind, _rel, number, _line, argv, _why in found],
            [("operator", 2, False), ("operator", 3, True), ("skip", 4, True),
             ("bin/fn", 5, False), ("reply", 6, True)])


if __name__ == "__main__":
    unittest.main()
