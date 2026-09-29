"""The store's lineage through the log's rotation heads (row A10, lane
store-lineage, PRF-979; books/store-log-lineage.lisp, specs/storage.md
"Lineage").

Every log segment K >= 2 opens with a ROTATION ENTRY chained from the
closed segment's last trailer; a checkpoint's F row names (K, G) with G the
head's trailer, and the open refuses by name a checkpoint whose (K, G) is
not this log's (`fn-lgl-open`: foreign-lineage, segment-head-damaged,
segment-misnamed).  A restored backup that took records of its own is a
fork: its next rotation heads its segment K from another trailer, so its
checkpoint never opens this copy's log, and this copy's never opens its --
with or without records after the checkpoint.  Before the head the open's
three decisions were identical for the two (an empty suffix compared
nothing): the gap of the 2026-09-29 review.

What the mechanism decides is ancestry through the log's own commitment,
not freshness: a complete restore of every local file is an old legitimate
state and opens.  A copy that did not diverge is the same history and opens
under the same (K, G) -- every existing checkpoint test's restart.

The rotation's cut `rotate-headed` (the head written after the rename,
before the fence) is exercised with the other rotation cuts by
tests/test_native_checkpoint_auto.py, tests/test_native_log_compaction.py
and tests/test_native_capacity_vector.py.
"""

import shutil
import unittest

from tests import test_native_state_checkpoint as scp
from tests.native_harness import EXIT_OK, Node


class StoreLineageTests(scp.StateCheckpointFixture):

    def fork(self):
        """This store's files copied to a second node (a restored backup):
        the same genesis record, the same log, the same keys."""
        other = Node(self, self.image, listener=True, control=True)
        other.image = self.image
        shutil.copytree(self.store, other.store_path, symlinks=True, dirs_exist_ok=True)
        return other

    def current(self):
        return (self.node, self.root, self.store, self.config, self.port, self.control)

    def become(self, other):
        self.node, self.root, self.store, self.config, self.port, self.control = (
            other, other.root, other.store_path, other.config, other.port, other.control)

    def restore(self, saved):
        self.node, self.root, self.store, self.config, self.port, self.control = saved

    def diverged_copies(self):
        """Init, one article, the copy; the copy takes two articles of its own
        and checkpoints (K = 2, three records, no suffix); this store takes
        two of its own and checkpoints likewise.  Answers the copy's checkpoint
        file and this store's."""
        created = self.op("init", "--profile", "development", "fn.test")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        self.ids = ["<lineage-a-{}@example.invalid>".format(n) for n in range(4)]
        self.post(self.ids[:1])
        saved = self.current()
        self.fork_node = self.fork()
        self.become(self.fork_node)
        try:
            self.post(["<lineage-b-{}@example.invalid>".format(n) for n in range(2)])
            made = self.checkpoint()
            self.assertEqual(made.returncode, EXIT_OK, made.stderr.decode())
            self.assertEqual(self.open_line(), "open=checkpoint:3 suffix=0")
            theirs = self.path().read_bytes()
        finally:
            self.restore(saved)
        self.post(self.ids[1:3])
        self.keep_log()
        made = self.checkpoint()
        self.assertEqual(made.returncode, EXIT_OK, made.stderr.decode())
        self.assertEqual(self.open_line(), "open=checkpoint:3 suffix=0")
        mine = self.path().read_bytes()
        self.assertNotEqual(theirs, mine)
        return theirs, mine

    def assert_foreign_lineage(self, theirs, mine, open_line):
        self.path().write_bytes(theirs)
        status = self.op("status")
        self.assertNotEqual(status.returncode, EXIT_OK, status.stdout.decode())
        self.assertIn(b"open refused reason=foreign-lineage", status.stderr)
        # Refused, not damaged, not uncertain: nothing was written or dropped.
        self.assertNotIn(b"uncertain", status.stderr)
        self.path().write_bytes(mine)
        self.assertEqual(self.open_line(), open_line)

    def test_a_diverged_copy_checkpoint_with_an_empty_suffix_is_refused_by_name(self):
        """G1: the same store identity, the same count, an empty suffix: the
        copy's checkpoint names segment 2 with the copy's head trailer; this
        log's segment 2 is headed from this store's records."""
        theirs, mine = self.diverged_copies()
        self.assert_foreign_lineage(theirs, mine, "open=checkpoint:3 suffix=0")

    def test_a_diverged_copy_checkpoint_over_a_suffix_is_refused_by_name(self):
        """The same with a record after this store's checkpoint: the head
        decides before any suffix record is read."""
        theirs, mine = self.diverged_copies()
        self.post(self.ids[3:])
        self.assertEqual(self.open_line(), "open=checkpoint:3 suffix=1")
        self.assert_foreign_lineage(theirs, mine, "open=checkpoint:3 suffix=1")

    def test_this_checkpoint_against_the_copy_log_is_refused_by_name(self):
        """The other direction: this store's checkpoint put in the diverged
        copy's place is refused there by the copy's head."""
        theirs, mine = self.diverged_copies()
        saved = self.current()
        self.become(self.fork_node)
        try:
            self.assertEqual(self.path().read_bytes(), theirs)
            self.assert_foreign_lineage(mine, theirs, "open=checkpoint:3 suffix=0")
        finally:
            self.restore(saved)


if __name__ == "__main__":
    unittest.main()
