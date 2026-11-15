"""Source-only controls for HELD compaction selection; no ACL2/runtime claim."""
import sys
import unittest
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
from lisp_source import forms, read_sexp


def trees(path):
    return [read_sexp(s) for s in forms((ROOT / path).read_text())]


def definition(path, name):
    return next(t for t in trees(path) if isinstance(t, list)
                and t[:2] == ["defun", name])


def nodes(t):
    if isinstance(t, list):
        yield t
        for c in t:
            yield from nodes(c)


def calls(t, name):
    return [n for n in nodes(t) if n and n[0] == name]


SOURCE = "books/checkpoint-compaction-source.lisp"
STATE = "books/checkpoint-compaction-state.lisp"
OLD = "books/checkpoint-metadata-source.lisp"


class CompactionSource(unittest.TestCase):
    def test_canonical_held_membership_is_shared(self):
        old = definition(OLD, "fn2-checkpoint-source-step")
        new = definition(SOURCE, "fn2-checkpoint-compaction-source-tuple")
        for p in ("fn2-checkpoint-source-overlayp", "fn2-checkpoint-source-runp"):
            self.assertEqual(len(calls(old, p)), 1)
            self.assertEqual(len(calls(new, p)), 1)
        ov = definition(OLD, "fn2-checkpoint-source-overlayp")
        self.assertTrue(calls(ov, "fn2-overlays-count"))
        self.assertTrue(calls(ov, "fn2-checkpoint-source-retire-overlayp"))
        retire = definition(OLD, "fn2-checkpoint-source-retire-overlayp")
        self.assertIn("*fn2-overlay-phase-frozen*", repr(retire))
        self.assertNotIn("*fn2-overlay-phase-private*", repr(retire))

    def test_begin_requires_actual_build_and_candidate(self):
        t = definition(STATE, "fn2-checkpoint-compaction-begin")
        for p in ("fn2-checkpoint-build-ownerp", "fn2-checkpoint-builder-ownerp"):
            self.assertEqual(len(calls(t, p)), 1)
        self.assertIn("*fn2-checkpoint-build-phase-await-roots*", repr(t))
        self.assertTrue(calls(t, "fn2-checkpoint-build-candidate"))

    def test_each_source_scan_retains_cut_and_geometry(self):
        t = definition(STATE, "fn2-checkpoint-compaction-ownerp")
        self.assertTrue(calls(t, "fn2-checkpoint-compaction-cut-ownerp"))
        self.assertTrue(calls(t, "fn2-checkpoint-builder-ownerp"))
        self.assertIn("*fn2-checkpoint-build-phase-await-roots*", repr(t))
        cut = definition(STATE, "fn2-checkpoint-compaction-cut-ownerp")
        for p in ("fn2-checkpoint-build-ownerp", "fn2-checkpoint-builder-claimp",
                  "fn2-overlays-rows", "fn2-run-installed-rows"):
            self.assertTrue(calls(cut, p))
        step = definition(SOURCE, "fn2-checkpoint-compaction-source-step")
        self.assertTrue(calls(step, "fn2-checkpoint-compaction-ownerp"))

    def test_no_source_count_truncation_or_recursive_scan(self):
        t = definition(SOURCE, "fn2-checkpoint-compaction-source-step")
        self.assertFalse(calls(t, "fn2-checkpoint-compaction-source-step"))
        self.assertFalse(calls(t, "min"))
        self.assertNotIn("*fn2-read-sources*", repr(t))
        self.assertNotIn("*fn2-idc-run-budget*", repr(t))
        self.assertTrue(calls(t, "fn2-overlays-rows"))
        self.assertTrue(calls(t, "fn2-run-installed-rows"))

    def test_zero_budget_precedes_every_state_write(self):
        t = definition(SOURCE, "fn2-checkpoint-compaction-source-step")
        bindings = t[-1][1]
        self.assertEqual(bindings[0][0][0], "unless")
        self.assertEqual(bindings[0][0][1], ["posp", "budget"])
        self.assertIn(":yield", bindings[0][1])

    def test_scanner_suspends_in_seek_not_ready(self):
        t = definition(SOURCE, "fn2-checkpoint-compaction-source-step")
        self.assertIn("*fn2-checkpoint-compaction-phase-seek*", repr(t))
        self.assertNotIn(":ready", repr(t))
        self.assertNotIn("complete", t[2])
        self.assertEqual(len(calls(t, "fn2-checkpoint-compaction-source-tuple")), 1)

    def test_selector_has_no_io_decode_or_hash_twin(self):
        for t in trees(SOURCE):
            for n in nodes(t):
                if n and isinstance(n[0], str):
                    self.assertFalse(n[0].startswith(("fn2-block-", "fn2-issue-", "fn2-b3-", "fn2-format-run-")))

    def test_key_lease_is_separate_canonical_page_bound(self):
        text = (ROOT / "books/checkpoint-working-geometry.lisp").read_text()
        self.assertIn("*fn2-checkpoint-compaction-key-window*", text)
        self.assertIn("(+ 1 *fn2-checkpoint-source-read-window*)", text)
        self.assertIn("(+ 1 *fn2-checkpoint-compaction-key-window*)", text)
        self.assertNotIn('include-book "runs-served"', text)
        state = (ROOT / STATE).read_text()
        self.assertIn("(assert-event (<= *fn2-run-layout-max-key-octets* *fn2-format-page-size*))", state)
        self.assertIn("(assert-event (<= *fn2-run-layout-max-entry-bytes* *fn2-format-page-size*))", state)

class CompactionMerge(unittest.TestCase):
    def step(self):
        return definition("books/checkpoint-compaction-merge.lisp", "fn2-checkpoint-compaction-merge-step")

    def test_real_decoders_and_shared_comparator(self):
        t = self.step()
        for p in ("fn2-ov-locate", "fn2-ov-entry", "fn2-run-scan-step",
                  "fn2-run-layout-compare", "fn2-checkpoint-source-beforep"):
            self.assertTrue(calls(t, p), p)
        for n in nodes(t):
            if n and isinstance(n[0], str):
                self.assertFalse(n[0].startswith(("fn2-block-", "fn2-issue-", "fn2-b3-", "fn2-format-run-")))
        self.assertIn(":need-read", repr(t))

    def test_copy_reads_and_writes_fit_grant(self):
        t = self.step()
        copy = calls(t, "fn2-run-entry-rehome-step")
        self.assertEqual(len(copy), 1)
        self.assertEqual(copy[0][-3], ["floor", "budget", "2"])
        self.assertIn(["<=", "2", "budget"], list(nodes(t)))
        # A raw-budget mutation is rejected by this exact source condition.
        bad = list(copy[0]); bad[-3] = "budget"
        self.assertNotEqual(bad[-3], ["floor", "budget", "2"])

    def test_lower_is_strict_without_key_successor_twin(self):
        t = self.step()
        self.assertIn(["eq", "lower-order", ":eq"], list(nodes(t)))
        self.assertIn(["eq", "lower-order", ":gt"], list(nodes(t)))
        self.assertFalse(calls(t, "fn2-range-successor"))
        self.assertFalse(calls(t, "fn2-run-build-add"))

    def test_actual_identity_gate_is_shared_with_old_rebuild(self):
        t = self.step()
        self.assertEqual(len(calls(t, "fn2-checkpoint-source-run-headerp")), 2)
        self.assertIn("reading-header", repr(t))
        old = definition("books/checkpoint-metadata.lisp", "fn2-checkpoint-metadata-run-step")
        self.assertEqual(len(calls(old, "fn2-checkpoint-source-run-headerp")), 1)
        h = definition(OLD, "fn2-checkpoint-source-run-headerp")
        for p in ("fn2-run-readerp", "fn2-run-installed-wire-run", "fn2-run-installed-schema"):
            self.assertTrue(calls(h, p))
        self.assertIn("*fn2-format-page-header-field-history*", repr(h))
        self.assertIn("*fn2-format-page-header-field-incarnation*", repr(h))

    def test_source_view_frozen_until_copy_done(self):
        t = self.step()
        self.assertIn("*fn2-checkpoint-compaction-phase-copy*", repr(t))
        self.assertIn("*fn2-checkpoint-compaction-phase-park*", repr(t))
        self.assertNotIn("*fn2-checkpoint-compaction-phase-sources*", repr(t))
        self.assertFalse(calls(t, "fn2-checkpoint-compaction-source-step"))

    def test_retained_windows_are_bound_to_actual_declared_slots(self):
        t = definition("books/checkpoint-compaction-workspaces.lisp", "fn2-checkpoint-compaction-windowsp")
        for p in ("fn2-checkpoint-windows-generation", "fn2-checkpoint-windows-slot",
                  "fn2-checkpoint-compaction-key-disjoint-p", "fn2-pool-workspace-code"):
            self.assertTrue(calls(t, p))
        self.assertIn("*fn2-checkpoint-compaction-key-window*", repr(t))
        step = self.step()
        for p in ("fn2-checkpoint-source-ebase", "fn2-checkpoint-manifest-ebase", "fn2-checkpoint-source-rbase",
                  "fn2-b-checkpoint-source-cursor-from-rows"):
            self.assertTrue(calls(step, p))


class CompactionPark(unittest.TestCase):
    def test_borrowed_park_has_real_cut_and_pending_gate(self):
        t = definition("books/checkpoint-compaction-park.lisp", "fn2-checkpoint-compaction-park-source")
        for p in ("fn2-checkpoint-compaction-ownerp", "fn2-checkpoint-compaction-windowsp",
                  "fn2-checkpoint-source-reader-attachedp", "fn2-checkpoint-source-reader-windowsp"):
            self.assertTrue(calls(t, p))
        self.assertIn(["equal", ["fn2-run-loads-pending", "c", "fn2-run-loads"], "0"], list(nodes(t)))
        self.assertIn("*fn2-checkpoint-compaction-phase-park*", repr(t))
        self.assertEqual(len(calls(t, "fn2-run-load-park-source-mutations")), 1)
        self.assertFalse(calls(t, "fn2-pool-release"))
        self.assertFalse(calls(t, "fn2-run-load-admission-begin"))
        self.assertIn("*fn2-checkpoint-compaction-phase-sources*", repr(t))

    def test_shared_recipe_preserves_borrow_mode_and_windows(self):
        trees0 = trees("books/run-physical-release.lisp")
        macro = next(t for t in trees0 if isinstance(t,list) and t[:2] == ["defmacro", "fn2-run-load-park-source-mutations"])
        self.assertTrue(calls(macro, "fn2-checkpoint-summary-release"))
        self.assertNotIn("['windows',", repr(macro))
        self.assertNotIn("['lease-mode',", repr(macro))
        self.assertFalse(calls(macro, "fn2-pool-release"))
        self.assertFalse(calls(macro, "fn2-pool-reset"))


class CompactionOutput(unittest.TestCase):
    def test_winner_bind_preserves_actual_typed_retention(self):
        t = definition("books/checkpoint-compaction-output.lisp", "fn2-checkpoint-compaction-selected-bind")
        self.assertTrue(calls(t, "fn2-checkpoint-compaction-source-tuple"))
        self.assertIn("*fn2-checkpoint-compaction-phase-selected*", repr(t))
        self.assertIn("*fn2-checkpoint-compaction-phase-retention*", repr(t))
        self.assertIn(["retention-stage", "0"], list(nodes(t)))
        self.assertNotIn(["retention-stage", "1"], list(nodes(t)))
        self.assertFalse(calls(t, "fn2-run-build-add"))

    def test_append_calls_same_checked_entry_path(self):
        t = definition("books/checkpoint-compaction-output.lisp", "fn2-checkpoint-compaction-append-step")
        self.assertEqual(len(calls(t, "fn2-checkpoint-metadata-entry-step")), 1)
        self.assertIn(["equal", ["fn2-checkpoint-metadata-retention-stage", "0", "fn2-checkpoint-metadata"], "1"], list(nodes(t)))
        self.assertIn("*fn2-checkpoint-compaction-phase-lower-copy*", repr(t))
        self.assertIn(["eq", "code", ":ok"], list(nodes(t)))
        self.assertFalse(calls(t, "fn2-pool-reset"))

    def test_lower_window_changes_only_after_append(self):
        t = definition("books/checkpoint-compaction-output.lisp", "fn2-checkpoint-compaction-lower-step")
        self.assertIn("*fn2-checkpoint-compaction-phase-lower-copy*", repr(t))
        self.assertIn(["equal", ["fn2-checkpoint-metadata-held", "0", "fn2-checkpoint-metadata"], "0"], list(nodes(t)))
        self.assertEqual(calls(t, "fn2-run-entry-rehome-step")[0][-3], ["floor", "budget", "2"])
        self.assertIn(["lower-round", ["+", "1", ["fn2-checkpoint-compaction-lower-round", "0", "fn2-checkpoint-compaction"]]], list(nodes(t)))
        self.assertIn(["best", "0"], list(nodes(t)))
        self.assertIn(["has-lower", "1"], list(nodes(t)))

    def test_schema_builder_is_one_dense_rank_after_inventory(self):
        t = definition("books/checkpoint-compaction-schema.lisp", "fn2-checkpoint-compaction-schema-begin")
        self.assertTrue(calls(t, "fn2-checkpoint-predecessor-ready-p"))
        self.assertTrue(calls(t, "fn2-run-build-start"))
        self.assertIn(["rank", ["+", "1", ["fn2-checkpoint-compaction-output-rank", "0", "fn2-checkpoint-compaction"]]], list(nodes(t)))
        self.assertFalse(calls(t, "fn2-checkpoint-source-set-rank"))
        self.assertIn(["schema-open", "1"], list(nodes(t)))


class CompactionEmpty(unittest.TestCase):
    def step(self):
        return definition("books/checkpoint-compaction-empty.lisp", "fn2-checkpoint-compaction-empty-step")

    def test_empty_root_uses_real_full_ref_reader(self):
        t = self.step()
        for p in ("fn2-run-cursor-start-installed", "fn2-run-scan-step", "fn2-checkpoint-source-run-headerp"):
            self.assertEqual(len(calls(t,p)),1)
        self.assertIn("reading-header", repr(t))
        self.assertIn("*fn2-run-cursor-phase-end*", repr(t))
        self.assertIn(["posp", ["fn2-checkpoint-compaction-empty-headers", "0", "fn2-checkpoint-compaction"]], list(nodes(t)))
        self.assertFalse(calls(t, "fn2-run-build-start"))
        self.assertFalse(calls(t, "fn2-run-build-add"))

    def test_nonempty_result_cannot_retry_past_rejected_entry(self):
        t = self.step()
        self.assertIn([["when", ["eq", "code", ":entry"]], ["fn2-checkpoint-compaction-merge-fail", ":source-count"]], list(nodes(t)))
        fs = trees("books/checkpoint-compaction-merge.lisp")
        macro = next(x for x in fs if isinstance(x,list) and x[:2] == ["defmacro","fn2-checkpoint-compaction-merge-fail"])
        self.assertIn("*fn2-checkpoint-compaction-phase-uncertain*", repr(macro))

    def test_empty_overlay_checks_actual_index_and_source_owner(self):
        t = self.step()
        self.assertTrue(calls(t, "fn2-ov-okp"))
        self.assertTrue(calls(t, "fn2-layout-range-code"))
        for p in ("fn2-overlays-slot", "fn2-overlays-gen", "fn2-overlays-fill", "fn2-overlays-okind", "fn2-overlays-oslot", "fn2-overlays-ogen"):
            self.assertTrue(calls(t,p))

    def test_empty_lifecycle_never_manufactures_an_output_rank(self):
        t = self.step()
        self.assertFalse(calls(t, "fn2-checkpoint-compaction-set-output-rank"))
        self.assertIn("*fn2-checkpoint-compaction-phase-empty-end*", repr(t))
        park = definition("books/checkpoint-compaction-park.lisp", "fn2-checkpoint-compaction-park-source")
        self.assertIn("*fn2-checkpoint-compaction-phase-schema*", repr(park))
        self.assertIn("fn2-checkpoint-compaction-schema-open", repr(park))


class CompactionReader(unittest.TestCase):
    def test_exact_cursor_proof_is_shared_with_old_source_reader(self):
        p = "books/checkpoint-source-loader.lisp"
        old = definition(p, "fn2-checkpoint-source-reader-sourcep")
        new = definition("books/checkpoint-compaction-reader.lisp", "fn2-checkpoint-compaction-reader-sourcep")
        self.assertEqual(len(calls(old,"fn2-checkpoint-source-cursorp")),1)
        self.assertEqual(len(calls(new,"fn2-checkpoint-source-cursorp")),1)
        helper = definition(p,"fn2-checkpoint-source-cursorp")
        for column in ("source-row","catalog-tag","schema","run","priority","okind","oslot","ogen"):
            self.assertTrue(calls(helper,"fn2-run-cursors-"+column))
        self.assertIn("*fn2-run-cursor-phase-miss*", repr(helper))
        self.assertIn("*fn2-run-installed-state-live*", repr(helper))
        self.assertTrue(calls(old,"fn2-checkpoint-source-selectedp"))
        self.assertTrue(calls(new,"fn2-checkpoint-compaction-current-source-p"))

    def test_bound_step_delegates_same_actual_engine(self):
        t = definition("books/checkpoint-compaction-reader.lisp", "fn2-checkpoint-compaction-reader-step")
        self.assertEqual(len(calls(t,"fn2-run-load-bind")),1)
        self.assertEqual(len(calls(t,"fn2-run-load-step")),1)
        self.assertFalse(calls(t,"fn2-block-read-children"))
        self.assertFalse(calls(t,"fn2-run-load-issue"))
        self.assertTrue(calls(t,"fn2-checkpoint-compaction-reader-sourcep"))

    def test_physical_issue_is_explicit_and_does_not_mutate_compaction(self):
        t = definition("books/checkpoint-compaction-reader.lisp", "fn2-checkpoint-compaction-reader-issue")
        self.assertEqual(len(calls(t,"fn2-run-load-issue")),1)
        self.assertFalse(calls(t,"fn2-checkpoint-compaction-put"))
        self.assertTrue(calls(t,"fn2-checkpoint-compaction-reader-sourcep"))
        self.assertIn(["posp","budget"],list(nodes(t)))
        self.assertNotIn("complete", t[2])


if __name__ == "__main__":
    unittest.main()
