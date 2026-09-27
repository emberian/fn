"""tools/bridge_image.py identity and the bridge's shared pool slot; no ACL2 runs."""

import os
from pathlib import Path
import subprocess
import sys
import tempfile
import textwrap
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from tools import bridge_image, run_store  # noqa: E402


class ClosureTests(unittest.TestCase):
    def test_the_store_closure_reaches_every_boot_file(self):
        names = {str(path.relative_to(ROOT)) for path in
                 bridge_image.closure(bridge_image.STORE_FORMS)}
        for expected in ("books/replay.lisp", "books/records-concrete.lisp",
                         "host/store-host.lisp", "host/config-host.lisp",
                         # reached only through store-node-host's include
                         "books/store-reclaim.lisp"):
            self.assertIn(expected, names)

    def test_references_follow_include_and_ld_and_skip_system_books(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "a.lisp"
            source.write_text(textwrap.dedent('''
                (include-book "b")
                (include-book "std/lists/top" :dir :system)
                ; (include-book "commented-out")
                #| (include-book "block-commented") |#
                (ld "c.lisp" :ld-error-action :error)
            '''))
            found = {path.name for path in bridge_image._references(source)}
        self.assertEqual(found, {"b.lisp", "c.lisp"})

    def test_a_changed_closure_file_changes_the_digest(self):
        environment = run_store.acl2_environment()
        try:
            before = bridge_image.digest("store", environment)
        except FileNotFoundError:
            self.skipTest("waiver-ok: no ACL2 launcher to fingerprint on this machine")
        real = bridge_image._sha256
        target = (ROOT / "books" / "replay.lisp").resolve()
        with mock.patch.object(bridge_image, "_sha256",
                               lambda path: "changed" if path == target else real(path)):
            after = bridge_image.digest("store", environment)
        self.assertNotEqual(before, after)
        self.assertEqual(before, bridge_image.digest("store", environment))

    def test_the_owner_image_extends_the_store_boot(self):
        self.assertEqual(bridge_image.OWNER_FORMS[:len(bridge_image.STORE_FORMS)],
                         bridge_image.STORE_FORMS)


CHILD = textwrap.dedent('''
    import sys, time
    sys.path.insert(0, {root!r})
    from tools import run_store
    started = time.monotonic()
    run_store._acquire_slot("child")
    print("waited %.2f" % (time.monotonic() - started))
    run_store._release_slot()
''')


class LoadBudgetTests(unittest.TestCase):
    """A boot load form's budget is 3x its last measured time, never a fixed
    20 s (dev-health packet 5)."""

    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.path = Path(temp.name) / "times.json"
        self.form = '(ld "host/checkpoint-host.lisp"' + bridge_image.LD

    def test_only_loads_are_load_forms(self):
        self.assertTrue(bridge_image.is_load_form(self.form))
        self.assertTrue(bridge_image.is_load_form('(include-book "books/replay")'))
        self.assertFalse(bridge_image.is_load_form("(set-check-invariant-risk t)"))
        self.assertFalse(bridge_image.is_load_form("(fn-store-reset state)"))

    def test_an_unmeasured_load_gets_the_refutation_bound(self):
        self.assertEqual(bridge_image.load_budget(self.form, self.path),
                         bridge_image.LOAD_FIRST_SECONDS)

    def test_a_measured_load_gets_three_times_its_time(self):
        with mock.patch.object(bridge_image, "_load_per_cpu", return_value=0.5):
            bridge_image.record_load(self.form, 25.4, self.path)
            self.assertAlmostEqual(bridge_image.load_budget(self.form, self.path), 76.2)
            bridge_image.record_load(self.form, 2.0, self.path)
            self.assertEqual(bridge_image.load_budget(self.form, self.path),
                             bridge_image.LOAD_FLOOR_SECONDS)

    def test_a_busier_machine_scales_the_budget(self):
        with mock.patch.object(bridge_image, "_load_per_cpu", return_value=0.5):
            bridge_image.record_load(self.form, 10.0, self.path)
        with mock.patch.object(bridge_image, "_load_per_cpu", return_value=2.0):
            self.assertAlmostEqual(bridge_image.load_budget(self.form, self.path), 60.0)

    def test_the_boot_times_each_load_and_records_it(self):
        store = run_store.Acl2Store.__new__(run_store.Acl2Store)
        seen = []
        store.call = lambda form, timeout=None: seen.append((form, timeout)) or b"ok"
        with mock.patch.object(bridge_image, "LOAD_TIMES", self.path):
            store.boot_call(self.form)
            store.boot_call("(set-check-invariant-risk t)")
            self.assertEqual(seen[0], (self.form, bridge_image.LOAD_FIRST_SECONDS))
            self.assertEqual(seen[1], ("(set-check-invariant-risk t)", None))
            self.assertIn(self.form, bridge_image._read_load_times(self.path))
            store.boot_call(self.form)
            self.assertEqual(seen[2], (self.form, bridge_image.LOAD_FLOOR_SECONDS))


class SlotTests(unittest.TestCase):
    """The bridge takes a pool slot; a child of a holder shares it."""

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="fn-bridge-slots-")
        self.environment = mock.patch.dict(os.environ, {
            "FN_ACL2_SLOT_DIR": self.temp.name, "FN_ACL2_SLOTS": "1"})
        self.environment.start()
        os.environ.pop(run_store.SLOT_HOLDER_VARIABLE, None)

    def tearDown(self):
        os.environ.pop(run_store.SLOT_HOLDER_VARIABLE, None)
        self.environment.stop()
        self.temp.cleanup()

    def child(self, timeout):
        return subprocess.run([sys.executable, "-c", CHILD.format(root=str(ROOT))],
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                              env=os.environ.copy(), timeout=timeout)

    def test_a_child_of_the_holder_shares_the_only_slot(self):
        run_store._acquire_slot("parent")
        try:
            self.assertEqual(os.environ[run_store.SLOT_HOLDER_VARIABLE], str(os.getpid()))
            result = self.child(timeout=30)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertLess(float(result.stdout.split()[1]), 5.0)
        finally:
            run_store._release_slot()
        self.assertNotIn(run_store.SLOT_HOLDER_VARIABLE, os.environ)

    def test_an_unrelated_process_waits_for_the_held_slot(self):
        run_store._acquire_slot("parent")
        try:
            # Without the holder's pid in its environment the child is a
            # stranger to the pool: it must wait, and the one slot is taken.
            del os.environ[run_store.SLOT_HOLDER_VARIABLE]
            with self.assertRaises(subprocess.TimeoutExpired):
                self.child(timeout=3)
            os.environ[run_store.SLOT_HOLDER_VARIABLE] = str(os.getpid())
        finally:
            run_store._release_slot()

    def test_nested_bridges_in_one_process_hold_one_slot(self):
        run_store._acquire_slot("first")
        run_store._acquire_slot("second")
        run_store._release_slot()
        # Still held: a stranger waits.
        del os.environ[run_store.SLOT_HOLDER_VARIABLE]
        with self.assertRaises(subprocess.TimeoutExpired):
            self.child(timeout=3)
        os.environ[run_store.SLOT_HOLDER_VARIABLE] = str(os.getpid())
        run_store._release_slot()
        result = self.child(timeout=30)
        self.assertEqual(result.returncode, 0, result.stderr)


if __name__ == "__main__":
    unittest.main()
