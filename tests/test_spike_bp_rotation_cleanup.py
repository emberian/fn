"""spike/storage (D28): BP journal rotation cleanup on the native image.

The N16 test (tests/test_bp_node_native.py
test_rotation_killed_at_each_cut_keeps_held_rows) keeps every old
generation as evidence.  On the spike, fnn-bps-open removes what the durable
selection no longer names (host/native/spike-storage.lisp block E): older
generation directories, killed rotations' empty unselected directories and
staged selection files.  This test is that contract: after each cut and each
reopen the held rows are recovered, and after a completed rotation only the
selected generation remains.  Run it alone:
  python3 -m unittest tests.test_spike_bp_rotation_cleanup.SpikeRotationCleanup.test_rotation_cleanup
"""
import unittest

from tests.test_bp_node_native import NativeBpNodeTests


class SpikeRotationCleanup(NativeBpNodeTests):
    def generations(self):
        journal = self.receiver_journal
        return sorted(p.name for p in journal.iterdir()
                      if p.is_dir() and p.name.startswith("lifecycle"))

    def strays(self):
        return sorted(p.name for p in self.receiver_journal.iterdir()
                      if p.name.startswith(".bp-generation-"))

    def test_rotation_cleanup(self):
        receiver, port = self.start_node(True, once=False)
        sent = self.send_transit(port, self.unrouted_transit_bundle(), "r1")
        self.assertEqual(sent.returncode, 0, sent.stderr)
        self.wait_for_output(
            receiver, b"BP node progress waiting reason=route", timeout=120)
        self.stop_process(receiver)
        journal = self.receiver_journal
        self.assertEqual(self.recovered_held(), 1)
        selection = journal / "bp-generation.fnb"
        for cut in ("directory", "stage"):
            self.rotate_receiver(cut)
            self.assertFalse(selection.exists(), cut)
            # The reopen removes the killed rotation's empty directory and
            # its staged selection file, and keeps the held row.
            self.assertEqual(self.recovered_held(), 1, cut)
            self.assertEqual(self.generations(), ["lifecycle"], cut)
            self.assertEqual(self.strays(), [], cut)
        self.rotate_receiver("replace")
        self.assertTrue(selection.exists())
        # The reopen reads the new selection and retires generation 0.
        self.assertEqual(self.recovered_held(), 1)
        gens = self.generations()
        self.assertEqual(len(gens), 1, gens)
        self.assertTrue(gens[0].startswith("lifecycle-g"), gens)
        code, out, err = self.rotate_receiver()
        self.assertEqual(code, 0, (out, err))
        self.assertEqual(self.recovered_held(), 1)
        self.assertEqual(len(self.generations()), 1, self.generations())
        # New work lands in the selected generation and survives a rotation.
        receiver, port = self.start_node(True, once=False)
        second = self.send_transit(port, self.conflicting_transit_bundle_free(), "r2")
        self.assertEqual(second.returncode, 0, second.stderr)
        self.wait_for_output(
            receiver, b"BP node progress waiting reason=route", timeout=120)
        self.stop_process(receiver)
        self.assertEqual(self.recovered_held(), 2)
        code, out, err = self.rotate_receiver()
        self.assertEqual(code, 0, (out, err))
        self.assertEqual(self.recovered_held(), 2)
        self.assertEqual(len(self.generations()), 1, self.generations())


if __name__ == "__main__":
    unittest.main()
