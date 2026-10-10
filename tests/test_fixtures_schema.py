#!/usr/bin/env python3
"""tools/fixtures.py refuses a store fixture built under another store schema
by name, before an image opens a copy (OVER-WINDOW-FIXTURE-SCHEMA: syn100k-2k
predated the 2026-09-29 schema change and surfaced as a refused open inside a
native run)."""
import argparse
import contextlib
import io
import json
import shutil
import tempfile
import unittest
import unittest.mock
from pathlib import Path

from tools import fixtures

ROOT = Path(__file__).resolve().parent.parent


class SchemaDigestTests(unittest.TestCase):
    def setUp(self):
        self.tree = Path(tempfile.mkdtemp(prefix="fn-schema-tree-"))
        self.addCleanup(shutil.rmtree, self.tree, True)
        (self.tree / "books").mkdir()
        self.book = self.tree / fixtures.GENESIS_BOOK
        shutil.copy2(ROOT / fixtures.GENESIS_BOOK, self.book)

    def test_the_digest_follows_the_schema_text_and_nothing_else(self):
        here = fixtures.schema_digest(self.tree)
        self.assertEqual(here, fixtures.schema_digest(ROOT))
        self.assertRegex(here, r"^[0-9a-f]{64}$")
        text = self.book.read_text()
        # A comment is not the schema: the digest stays.
        self.book.write_text(text + "\n; a comment after the forms\n")
        self.assertEqual(fixtures.schema_digest(self.tree), here)
        # One more field in the schema text is another schema.
        self.book.write_text(text.replace(";digest=fn-digest;", ";digest=fn-digest;extra=1;"))
        self.assertNotEqual(fixtures.schema_digest(self.tree), here)

    def test_a_book_without_the_constant_refuses_by_name(self):
        self.book.write_text("(in-package \"ACL2\")\n")
        with self.assertRaises(SystemExit) as raised:
            fixtures.schema_digest(self.tree)
        self.assertIn(fixtures.SCHEMA_CONSTANT, str(raised.exception))


class SchemaRefusalTests(unittest.TestCase):
    NAME = "syn100k-2k"

    def setUp(self):
        self.root = Path(tempfile.mkdtemp(prefix="fn-fixtures-schema-"))
        self.addCleanup(shutil.rmtree, self.root, True)
        self.where = self.root / self.NAME
        (self.where / "store").mkdir(parents=True)
        (self.where / "store" / "x").write_text("x")
        self.tree = fixtures.schema_digest()

    def built(self, **record):
        (self.where / "FIXTURE.json").write_text(json.dumps(dict(name=self.NAME, rev="r1", **record)))
        fixtures.write_sums(self.where)

    def path(self):
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = fixtures.main(["path", self.NAME, "--root", str(self.root)])
        return code, out.getvalue(), err.getvalue()

    def test_the_same_schema_passes_and_path_prints_the_directory(self):
        self.built(schema_digest=self.tree)
        self.assertIsNone(fixtures.schema_refusal(self.where, self.tree))
        code, out, _ = self.path()
        self.assertEqual((code, out.strip()), (0, str(self.where)))

    def test_another_schema_refuses_by_name(self):
        self.built(schema_digest="0" * 64)
        refusal = fixtures.schema_refusal(self.where, self.tree)
        self.assertTrue(refusal.startswith("schema-digest: syn100k-2k"), refusal)
        self.assertIn(self.tree[:16], refusal)
        code, out, err = self.path()
        self.assertEqual((code, out), (1, ""))
        self.assertIn("schema-digest", err)

    def test_a_fixture_from_before_the_record_refuses_as_unrecorded(self):
        self.built()
        refusal = fixtures.schema_refusal(self.where, self.tree)
        self.assertTrue(refusal.startswith("schema-unrecorded: syn100k-2k"), refusal)
        (self.where / "FIXTURE.json").unlink()
        self.assertTrue(fixtures.schema_refusal(self.where, self.tree).startswith("schema-unrecorded"))

    def test_a_static_fixture_holds_no_store_and_is_not_asked(self):
        static = self.root / "usenet-20news-19997"
        static.mkdir()
        self.assertTrue(fixtures.BY_NAME["usenet-20news-19997"].static)
        self.assertIsNone(fixtures.schema_refusal(static, self.tree))

    def test_check_prints_the_tree_schema_and_fails_on_a_stale_fixture(self):
        self.built(schema_digest="0" * 64)
        only = fixtures.Fixture(self.NAME, recipe=lambda c: None)
        out = io.StringIO()
        with unittest.mock.patch.object(fixtures, "REGISTRY", [only]), \
                unittest.mock.patch.object(fixtures, "RETIRED", {}), \
                contextlib.redirect_stdout(out):
            code = fixtures.main(["check", "--root", str(self.root)])
        self.assertEqual(code, 1)
        self.assertIn("schema " + self.tree, out.getvalue())
        self.assertIn("schema-digest: syn100k-2k", out.getvalue())


class RebuildRecordsTheSchemaTests(unittest.TestCase):
    def test_a_rebuild_writes_the_tree_schema_into_fixture_json_and_the_manifest(self):
        root = Path(tempfile.mkdtemp(prefix="fn-fixtures-root-"))
        self.addCleanup(shutil.rmtree, root, True)

        def recipe(ctx):
            ctx.dest.mkdir(parents=True)
            (ctx.dest / "store").mkdir()
            (ctx.dest / "store" / "x").write_text("x")
        fixture = fixtures.Fixture("schema-probe", recipe=recipe)
        args = argparse.Namespace(root=str(root), work=str(root / ".work"),
                                  image=str(root / "no-image"), rev="r2")
        name, verdict = fixtures.rebuild_one(fixture, args, None)
        self.assertTrue(verdict.startswith("rebuilt"), verdict)
        record = json.loads((root / name / "FIXTURE.json").read_text())
        row = json.loads((root / "MANIFEST.json").read_text())["fixtures"][name]
        self.assertEqual(record["schema_digest"], fixtures.schema_digest())
        self.assertEqual(row["schema_digest"], record["schema_digest"])
        self.assertIsNone(fixtures.schema_refusal(root / name, fixtures.schema_digest()))


if __name__ == "__main__":
    unittest.main()
