#!/usr/bin/env python3
"""Fixed-original and scope checks for the five C mutation fences."""
from __future__ import annotations

import json
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import csnapshot_mutation_fences_rewrite as rewrite
import lisp_rewrite as lr


class MutationFenceRewrite(unittest.TestCase):
    def test_five_scoped_edits_recover_fixed_originals(self):
        fixture = json.loads(rewrite.FIXTURE.read_text())
        count = 0
        for relative, raw in rewrite.SPECS.items():
            specs = (raw,) if isinstance(raw[0], str) else raw
            source = (ROOT / relative).read_text()
            self.assertEqual(rewrite.digest(source), fixture[relative]["after_sha256"])
            original = rewrite.splice(source, specs, False)
            self.assertEqual(rewrite.digest(original), fixture[relative]["before_sha256"])
            count += len(specs)
        self.assertEqual(count, 5)

    def test_closing_remains_open_for_active_sealer(self):
        parsed = lr.parse(ROOT / "books/c-snapshot-state.lisp")
        matches = lr.match("(defun fn2-csnapshot-source-closed-p ?*body)", parsed.forms)
        self.assertEqual(len(matches), 1)
        body = parsed.text[matches[0].start:matches[0].end].lower()
        for phase in ("held", "adopting", "adopted"):
            self.assertIn(f"*fn2-csnapshot-phase-{phase}*", body)
        self.assertNotIn("*fn2-csnapshot-phase-closing*", body)

    def test_source_builder_guard_stays_exact_held(self):
        source = (ROOT / "books/event-build.lisp").read_text()
        self.assertIn("*fn2-csnapshot-phase-held*", source)
        self.assertNotIn("fn2-csnapshot-source-closed-p", source)

    def test_unexpected_original_rejected(self):
        relative = "books/machines-c-groups.lisp"
        raw = rewrite.SPECS[relative]
        source = (ROOT / relative).read_text()
        changed = source.replace("fn2-csnapshot-source-closed-p", "fn2-csnapshot-ownerp", 1)
        with self.assertRaises(ValueError):
            rewrite.splice(changed, (raw,), False)


if __name__ == "__main__":
    unittest.main()
