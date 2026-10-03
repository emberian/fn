"""tools/native_program_check.py: the tree passes, and each mutation fails.

The mutations are applied to the host source TEXT handed to `check()`; no
file is changed.  Each one is a drift the check exists to catch.
"""
from pathlib import Path
import unittest

from tests.campaign import native_cuts
from tools import native_program_check as npc

ROOT = Path(__file__).resolve().parent.parent


def mutate(text: str, old: str, new: str, within: str | None = None) -> str:
    """Replace OLD by NEW once, inside the defun WITHIN when given."""
    if within is None:
        assert text.count(old) == 1, old
        return text.replace(old, new)
    body = native_cuts.host_function(text, within)
    assert body.count(old) == 1, (within, old)
    return text.replace(body, body.replace(old, new))


class NativeProgramCheckTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.host = (ROOT / npc.HOST).read_text()

    def verdicts(self, report):
        return {r.program: r.verdict for r in report.programs}

    def assert_fails(self, host, program, needle=None):
        report = npc.check(host_text=host)
        self.assertFalse(report.ok)
        result = next(r for r in report.programs if r.program == program)
        self.assertEqual(result.verdict, "FAIL")
        if needle is not None:
            self.assertTrue(any(needle in m for m in result.mismatches), result.mismatches)
        return report

    def test_current_tree_passes_every_program_in_the_cut_table(self):
        # The per-file programs (P-FRONTIER, P-RECORD, P-RECOVER, P-MARKER)
        # went with format 8 (lane log-recovery-2, PKT-838); the byte-program
        # programs the host still runs are the finish and the staging sweep.
        # The log route's are LogRouteArmTests' below.
        report = npc.check()
        named = {c.program for c in native_cuts.ALL_CUTS} | {
            c.follows for c in native_cuts.ALL_CUTS if c.follows}
        self.assertEqual(set(self.verdicts(report)), named & set(npc.PROGRAM_HOSTS))
        self.assertEqual(set(self.verdicts(report)),
                         {"fn-bs-finish-program", "fn-bs-recover-stage-cleanup-program"})
        self.assertTrue(report.ok, npc.render(report))
        for r in report.programs:
            self.assertEqual(r.matched, r.model_steps, r.program)
            self.assertGreater(r.model_steps, 0)

    def test_swapped_cuts_fail(self):
        body = native_cuts.host_function(self.host, "fnn-finish")
        swapped = (body.replace("(fnn-at store :finish-consumed)", "(fnn-at store :SWAP)")
                   .replace("(fnn-at store :finish-durable)", "(fnn-at store :finish-consumed)")
                   .replace("(fnn-at store :SWAP)", "(fnn-at store :finish-durable)"))
        self.assertNotEqual(swapped, body)
        self.assert_fails(self.host.replace(body, swapped), "fn-bs-finish-program")

    def test_deleted_cut_fails(self):
        host = mutate(self.host, "(handler-case (fnn-at store :finish-durable)",
                      "(handler-case (progn)", within="fnn-finish")
        self.assert_fails(host, "fn-bs-finish-program")

    def test_declared_model_cut_off_its_program_fails(self):
        # frontier-reserved is a declared post cut (fn-lg-reserve-program's),
        # not fn-bs-finish-program's.
        host = mutate(self.host, "(handler-case (fnn-at store :finish-consumed)",
                      "(fnn-at store :frontier-reserved)\n  (handler-case (fnn-at store :finish-consumed)",
                      within="fnn-finish")
        self.assert_fails(host, "fn-bs-finish-program", "frontier-reserved")

    def test_a_sweep_before_the_programs_steps_fails(self):
        host = mutate(self.host, "(handler-case (fnn-at store :finish-consumed)",
                      "(fnn-sweep-staging store)\n  (handler-case (fnn-at store :finish-consumed)",
                      within="fnn-finish")
        self.assert_fails(host, "fn-bs-finish-program", "sequel")

    def test_a_cut_before_the_unlink_fails(self):
        body = native_cuts.host_function(self.host, "fnn-sweep-staging")
        moved = body.replace(
            "                  (fnn-unlink (fnn-join (fnn-staging store) name))\n", "").replace(
            "                  (fnn-at store :recovery-stage-unlinked))",
            "                  (fnn-at store :recovery-stage-unlinked)\n"
            "                  (fnn-unlink (fnn-join (fnn-staging store) name)))")
        self.assertNotEqual(moved, body)
        self.assert_fails(self.host.replace(body, moved), "fn-bs-recover-stage-cleanup-program")


class UnbalancedFormTests(unittest.TestCase):
    """PKT-345: an unbalanced form is located, never a bare StopIteration."""

    def test_parse_at_names_the_file_and_the_forms_first_line(self):
        text = npc.Text('(defun ok (x) x)\n\n(defun broken (x)\n  (let ((y x))\n    y)\n', [(0, "host/x.lisp")])
        offset = text.index("(defun broken")
        with self.assertRaises(npc.Unbalanced) as raised:
            npc.parse_at(text, offset)
        self.assertEqual(str(raised.exception),
                         "unbalanced: host/x.lisp:6, form starting at host/x.lisp:3 never closes")
        self.assertEqual(npc.parse_at(text, 0), ["defun", "ok", ["x"], "x"])
        self.assertEqual(npc.parse_at(npc.Text('(f ")" "(")', []), 0), ["f", ")", "("])

    def test_a_joined_text_reports_the_book_the_form_is_in(self):
        joined = npc.Text("(a)\n(b)\n" + "\n" + "(c\n(d)\n", [(0, "books/one.lisp"), (9, "books/two.lisp")])
        with self.assertRaises(npc.Unbalanced) as raised:
            npc.parse_at(joined, joined.index("(c"))
        self.assertIn("form starting at books/two.lisp:1", str(raised.exception))

    def test_a_stray_close_is_located(self):
        with self.assertRaises(npc.Unbalanced) as raised:
            npc.parse_at(npc.Text("\n) x", [(0, "f.lisp")]), 0)
        self.assertIn("f.lisp:1: a close parenthesis with no open form", str(raised.exception))

    def test_check_reports_an_unbalanced_host_defun(self):
        host = (ROOT / npc.HOST).read_text()
        # rep-wave-d-3's case: the defun loses its last close parenthesis.
        start = host.index("\n(defun fnn-state-checkpoint-plan ") + 1
        end = host.index("\n(defun ", start)
        body = host[start:end].rstrip()
        self.assertTrue(body.endswith(")"))
        broken = npc.Text(host[:start] + body[:-1] + "\n" + host[end:], [(0, npc.HOST)])
        self.assertEqual(npc.balance(npc.Text(host, [(0, npc.HOST)])), [])
        problems = npc.balance(broken)
        self.assertEqual(len(problems), 1, problems)
        line = host.count("\n", 0, start) + 1
        self.assertIn("form starting at {}:{} never closes".format(npc.HOST, line), problems[0])
        self.assertIn("a form opens at column 0 inside it at {}:".format(npc.HOST), problems[0])

    def test_balance_mode_exit_codes(self):
        import subprocess, sys, tempfile
        with tempfile.TemporaryDirectory() as temporary:
            good = Path(temporary) / "good.lisp"
            bad = Path(temporary) / "bad.lisp"
            good.write_text('(defun a (x) "(" x) ; )\n#| ( |#\n(b #\\( |c(| ")")\n')
            bad.write_text("(defun a (x)\n  x\n(defun b (y) y)\n")
            ok = subprocess.run([sys.executable, str(ROOT / "tools" / "native_program_check.py"),
                                 "--balance", str(good)], capture_output=True, text=True, timeout=60)
            self.assertEqual(ok.returncode, 0, ok.stdout)
            no = subprocess.run([sys.executable, str(ROOT / "tools" / "native_program_check.py"),
                                 "--balance", str(good), str(bad)], capture_output=True, text=True, timeout=60)
            self.assertEqual(no.returncode, 1)
            self.assertIn("form starting at {}:1 never closes".format(bad), no.stdout)
            self.assertIn("column 0 inside it at {}:3".format(bad), no.stdout)


class LogRouteArmTests(unittest.TestCase):
    """Lane log-2: each record-log arm against books/store-log-route-programs.lisp
    and the log's own programs; every mutation below is a process-death cut
    that no model program has, or a step out of the programs' order."""

    @classmethod
    def setUpClass(cls):
        cls.host = (ROOT / npc.HOST).read_text()

    def test_the_tree_passes(self):
        self.assertEqual(native_cuts.verify_log_route_arms(self.host), [])

    def test_an_unmodelled_cut_in_the_reservation_fails(self):
        host = mutate(self.host, "(fnn-at store :frontier-reserved)",
                      "(fnn-at store :frontier-reserved)\n    (fnn-at store :frontier-extra)",
                      within="fnn-log-reserve")
        problems = native_cuts.verify_log_route_arms(host)
        self.assertTrue(any("fnn-log-reserve" in p for p in problems), problems)

    def test_the_record_place_before_the_barrier_fails(self):
        body = native_cuts.host_function(self.host, "fnn-log-publish")
        moved = body.replace("  (unless *fnn-log-batch*\n    (fnn-log-commit-open-batch store))\n", "")
        moved = moved.replace("(fnn-at store :record-completing)",
                              "(fnn-at store :record-completing)\n  (unless *fnn-log-batch* (fnn-log-commit-open-batch store))")
        self.assertNotEqual(moved, body)
        problems = native_cuts.verify_log_route_arms(self.host.replace(body, moved))
        self.assertTrue(any("fnn-log-publish" in p for p in problems), problems)

    def test_a_missing_recovery_barrier_fails(self):
        host = mutate(self.host, "        (lambda () (fnn-fsync-dir (fnn-store-root store)))\n", "",
                      within="fnn-store-recovery-barriers")
        problems = native_cuts.verify_log_route_arms(host)
        self.assertTrue(any("fnn-recover-log" in p for p in problems), problems)


class LogProgramListingTests(unittest.TestCase):
    """Lane byte-model (row Q3b): native_program_check lists the log programs
    the host runs (fnn-log-append, fnn-log-fence, fnn-log-recover and the
    segment's extension fnn-log-ensure-extent) with their cuts, and a cut
    removed or reordered fails the listing."""

    @classmethod
    def setUpClass(cls):
        cls.host = (ROOT / npc.HOST).read_text()

    def test_the_tree_lists_the_four_log_programs_with_their_cuts(self):
        listing = native_cuts.log_program_cut_map(self.host)
        self.assertEqual([(p, h) for p, h, _ in listing],
                         [("fn-lg-append-program", "fnn-log-append"),
                          ("fn-lg-fence-program", "fnn-log-fence"),
                          ("fn-lg-recover-program", "fnn-log-recover"),
                          ("fn-lg-extend-program", "fnn-log-ensure-extent")])
        self.assertEqual([c for _, _, c in listing],
                         [("log-written",), ("log-fenced",),
                          ("log-truncated", "log-recovered"),
                          ("log-extended", "log-extent-fenced")])

    def test_a_missing_append_cut_fails(self):
        host = mutate(self.host, "  (fnn-log-at :log-written))", "  nil)",
                      within="fnn-log-append")
        with self.assertRaises(AssertionError) as caught:
            native_cuts.log_program_cut_map(host)
        self.assertIn("fnn-log-append", str(caught.exception))

    def test_an_extension_fenced_before_its_write_fails(self):
        body = native_cuts.host_function(self.host, "fnn-log-ensure-extent")
        moved = body.replace("        (fnn-log-preallocate (fnn-log-fd log) next extent)\n"
                             "        (fnn-log-at :log-extended)\n"
                             "        (fnn-log-fdatasync (fnn-log-fd log))\n",
                             "        (fnn-log-fdatasync (fnn-log-fd log))\n"
                             "        (fnn-log-preallocate (fnn-log-fd log) next extent)\n"
                             "        (fnn-log-at :log-extended)\n")
        self.assertNotEqual(moved, body)
        with self.assertRaises(AssertionError) as caught:
            native_cuts.log_program_cut_map(self.host.replace(body, moved))
        self.assertIn("fnn-log-ensure-extent", str(caught.exception))


class LogCutInventoryTests(unittest.TestCase):
    """Drive the standalone script over source mutations, without editing files."""

    @classmethod
    def setUpClass(cls):
        cls.host = (ROOT / npc.HOST).read_text()
        cls.book_path = "books/store-log-segments.lisp"
        cls.book = (ROOT / cls.book_path).read_text()

    def standalone(self, replacements):
        import json
        import subprocess
        import sys
        # The child runs the real __main__, including its exit status. Only
        # read_text is substituted; globbing and the parser still see the tree.
        script = '''
import json, runpy, sys
from pathlib import Path
replacements = json.load(sys.stdin)
read_text = Path.read_text
def read(path, *args, **kwargs):
    key = str(path.relative_to(Path.cwd())) if path.is_absolute() else str(path)
    return replacements[key] if key in replacements else read_text(path, *args, **kwargs)
Path.read_text = read
sys.argv = ['tools/native_program_check.py']
runpy.run_path(sys.argv[0], run_name='__main__')
'''
        return subprocess.run([sys.executable, "-c", script], cwd=ROOT,
                              input=json.dumps(replacements), text=True,
                              capture_output=True, timeout=60)

    def assert_inventory_failure(self, replacements, diagnostic):
        result = self.standalone(replacements)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("log cut inventory: FAIL", result.stdout)
        self.assertIn(diagnostic, result.stdout)

    def test_unknown_cut_in_previously_unlisted_helper_fails(self):
        path = "host/native/checkpoint.lisp"
        source = (ROOT / path).read_text()
        self.assert_inventory_failure({path: source +
            '\n(defun fnn-unlisted-helper () (fnn-log-at :surprise-cut))\n'},
            "surprise-cut")

    def test_undeclared_segment_name_fails(self):
        # Host and model agree on the new name; its declaration does not.
        self.assert_inventory_failure({
            npc.HOST: self.host.replace('(fnn-log-at :rotate-created)',
                                        '(fnn-log-at :rotate-unknown)'),
            self.book_path: self.book.replace('"rotate-created"', '"rotate-unknown"')},
            "rotate-unknown")

    def test_declared_model_only_orphan_fails(self):
        # Supply the model cut and declaration, but no host site.
        host = self.host.replace('"log-extent-fenced"))',
                                 '"log-extent-fenced" "log-orphan"))')
        path = "books/store-log-extend.lisp"
        book = (ROOT / path).read_text()
        self.assert_inventory_failure({npc.HOST: host,
            path: book.replace('(list :cut "log-extent-fenced")',
                               '(list :cut "log-extent-fenced") (list :cut "log-orphan")')},
            "log-orphan")

    def test_reordered_segment_steps_fail(self):
        body = native_cuts.host_function(self.host, "fnn-log-prepare-spare")
        moved = body.replace(":rotate-created", ":SWAP").replace(
            ":rotate-fenced", ":rotate-created").replace(":SWAP", ":rotate-fenced")
        self.assert_inventory_failure({npc.HOST: self.host.replace(body, moved)},
                                      "fnn-log-prepare-spare")

    def test_dynamic_point_fails(self):
        self.assert_inventory_failure({npc.HOST: self.host +
            '\n(defun fnn-unlisted-helper (point) (fnn-log-at point))\n'},
            "dynamic")

    def test_comments_and_strings_are_not_sites(self):
        host = mutate(self.host, "(fnn-log-at :log-written)",
                      '(progn "(fnn-log-at :string-cut)" ; (fnn-log-at :comment-cut)\n'
                      '    #| (fnn-log-at :block-comment-cut) |#\n'
                      '    (fnn-log-at :log-written))', within="fnn-log-append")
        result = self.standalone({npc.HOST: host + '''
; (fnn-log-at :comment-cut)
#| (fnn-log-at :block-comment-cut) |#
(defun fnn-document-log-cuts () "(fnn-log-at :string-cut)" nil)
'''})
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("log cut inventory: PASS (13 cuts; 7 segment cuts)", result.stdout)


if __name__ == "__main__":
    unittest.main()
