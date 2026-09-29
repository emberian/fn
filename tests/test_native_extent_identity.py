"""The extent reader decides IDENTITY, not self-consistency (lane
extent-identity, 2026-09-29; PRF-994; row A11 of COMPLETE-BEFORE-6.6.0.md;
GPT-6's warranty-quality-proof-engineering.md section 2).

Before this lane host/native/extent.lisp fnn-extent-entry ignored the
descriptor's expected trailer and asked ACL2 whether the entry it had just
read matched the trailer it had just read: a different, well-formed,
same-sized entry at the extent's offset was ACCEPTED.  Now the descriptor
carries the entry's commitment (books/payload-extent.lisp
fn-arx-attach-trailers) and ACL2's verdict (books/payload-extent-read.lisp
fn-arx-entry-verdict-buffer) decides every read against it: :trailer when
the trailer recorded after the prefix is not the descriptor's, :digest when
the prefix's digest is not its trailer.  The host refuses each by name
(arena-extent-trailer, arena-extent-digest) as a store fault: the owner
stops with the fault class and nothing is served from the substituted read.

The family (stronger than random damage: every substituted object is well
formed), each on a running node whose extents come from the open's replay,
substituted IN PLACE in the log segment (the held descriptor reads the same
inode; a rename would leave the old file readable and change nothing):

* a different valid same-sized entry / a wrong offset: two equal-sized
  entries of the same store swapped;
* an entry from another store: an equal-sized entry of another store
  written over the extent's entry;
* a wrong expected trailer: another entry's trailer written over the
  entry's recorded trailer (prefix intact);
* the prefix damaged in place under its own trailer (the case the old check
  caught): arena-extent-digest, distinct by name;
* a stale cache entry: the entry read BEFORE the substitution is served
  from the cache under its identity (file, offset, length, trailer) and
  still equals the baseline, and the same read with the cache off is
  refused -- a hit is the verified read of that identity, never a re-read;
  the cache's key is asserted at the source (a hit compares all four).

Runs on the developer image (FN_NATIVE_DEVELOPER_HOST) and, where the
runner names it, the production image (FN_NATIVE_HOST): nothing here is
developer-only but the cache-off selector, which is skipped without it.
"""
import os
import re
import unittest

from tests.campaign import native_cuts
from tests import test_native_operator_verbs as verbs
from tests.native_harness import EXIT_FAULT, EXIT_OK, ROOT, Node, native_image

IMAGE = native_image("FN_NATIVE_DEVELOPER_HOST")
PRODUCTION = native_image("FN_NATIVE_HOST")
SEGMENT = os.path.join("journal", "000001.log")
UNIT = 4096
MAGIC = b"FNLG"
HEADER = 10
TRAILER = 32
# The owner's fault line names the ACL2 entry that was reading (e.g.
# fn-owner-chunk-span) before the realizer's refusal name.
FAULT = re.compile(rb"owner core/store fault; process stopped: [^\n]*?(arena-extent-[a-z]+):")


def entries(data):
    """The entries of a segment: (start, prefix_length) per unit-aligned
    FNLG entry (the header's u32 length at offset 6, big-endian; the
    protected prefix is the header and the body, the trailer follows)."""
    found = []
    for q in range(0, len(data), UNIT):
        if data[q:q + 4] == MAGIC:
            body = int.from_bytes(data[q + 6:q + 10], "big")
            found.append((q, HEADER + body))
    return found


class ExtentIdentitySourceTests(unittest.TestCase):
    def test_the_realizer_decides_against_the_descriptor_and_keys_its_cache_by_identity(self):
        host = (ROOT / "host" / "native" / "extent.lisp").read_text(encoding="ascii")
        entry = native_cuts.host_function(host, "fnn-extent-entry")
        self.assertNotIn("(ignore trailer)", entry)
        # A hit agrees with the whole descriptor identity.
        for field in ("(eql (first e) file)", "(eql (second e) eoff)",
                      "(eql (third e) elen)", "(eql (fourth e) trailer)"):
            self.assertIn(field, entry)
        # The verdict is ACL2's, against the descriptor's trailer; every
        # refusal is by name.
        verdict = native_cuts.host_function(host, "fnn-extent-entry-verdict")
        self.assertIn("'fn-arx-entry-verdict-buffer trailer", verdict)
        for name in ("arena-extent-trailer", "arena-extent-digest", "arena-extent-verdict"):
            self.assertIn(name, entry)
        # The file id names a durable incarnation.
        register = native_cuts.host_function(host, "fnn-extent-register")
        self.assertIn("sb-posix:stat-ino", register)
        # The reseat reads a frame that has no descriptor yet through the
        # fresh read, and fills the buffer with prefix AND trailer.
        owner = (ROOT / "host" / "native" / "owner.lisp").read_text(encoding="ascii")
        release = native_cuts.host_function(owner, "fnn-owner-release-extents")
        self.assertIn("(fnn-extent-entry-fresh new-id eoff elen)", release)
        self.assertNotIn("(fnn-extent-entry new-id eoff elen 0)", release)
        # The open and the commit attach the commitment to every place.
        io = (ROOT / "host" / "native" / "io.lisp").read_text(encoding="ascii")
        self.assertIn("'fn-arx-attach-trailers-buffer", io)
        self.assertIn("'fn-arx-attach-trailers\n", io)


class ExtentIdentityFixture(verbs.NativeOperatorVerbFixture):
    image = IMAGE
    listener = True
    post_many = verbs.NativeOperatorCapacityTests.post_many

    def setUp(self):
        if not self.image.is_file():
            self.skipTest("{} is required".format(self.image))
        super().setUp()
        self.node.image = self.image

    def segment(self):
        return self.store / SEGMENT

    def init_and_post(self, node=None, prefix="xi", count=4):
        """A development store with COUNT equal-sized articles (equal-length
        Message-IDs, the same subject and body), restarted so every payload
        is an extent of the open's replay.  The ids and the entries."""
        node = node or self.node
        created = node.operator("init", "--profile", "development", "fn.test")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        node.start()
        ids = ["<{}-{}@example.invalid>".format(prefix, n) for n in range(count)]
        with node.session(timeout=120) as client:
            for message_id in ids:
                first, final = client.post(verbs.article(message_id, subject="identity"))
                self.assertTrue(first.startswith(b"340"), first)
                self.assertEqual(final.rstrip(b"\r\n"), b"240 article received OK")
        node.stop()
        data = (node.store_path / SEGMENT).read_bytes()
        found = entries(data)
        self.assertEqual(len(found), count, found)
        self.assertEqual(len({n for _, n in found}), 1, "the entries are not equal-sized")
        return ids, found

    def read(self, client, message_id):
        try:
            return client.article(message_id)
        except (OSError, EOFError, AssertionError, ValueError):
            # A refused read stops the owner: the connection closes.
            return None

    def substitute(self, edit):
        """EDIT the segment's bytes in place (the same inode the owner holds)."""
        path = self.segment()
        data = bytearray(path.read_bytes())
        edit(data)
        with open(path, "r+b") as f:
            f.seek(0)
            f.write(bytes(data))
            f.flush()
            os.fsync(f.fileno())

    def refused_by_name(self, owner, name):
        """The owner stopped with the fault class and named NAME; the
        refusal is refused, not uncertain and not absent."""
        self.node.exited(EXIT_FAULT, timeout=60, process=owner)
        text = owner.stderr.since(0)
        match = FAULT.search(text)
        self.assertIsNotNone(match, text[-1200:])
        self.assertEqual(match.group(1), name.encode("ascii"), text[-1200:])
        self.assertNotIn(b"outcome uncertain", text)

    def warm_then_substitute_then_read(self, edit, cached, cold, env=None):
        """Read CACHED (its entry verified and cached), substitute, read
        CACHED again (the cache hit under its identity) and then COLD.  The
        baseline of CACHED, what the second read of CACHED served, what the
        cold read served, and the owner."""
        owner = self.node.start(env=env)
        with self.node.session(timeout=60) as client:
            baseline = client.article(cached)
            self.assertIsNotNone(baseline)
            self.substitute(edit)
            again = self.read(client, cached)
            cold_read = self.read(client, cold)
        return baseline, again, cold_read, owner


class ExtentIdentityTests(ExtentIdentityFixture):
    def swap(self, a, b, n):
        def edit(data):
            whole = n + TRAILER
            data[a:a + whole], data[b:b + whole] = data[b:b + whole], data[a:a + whole]
        return edit

    def test_a_different_valid_same_sized_entry_at_the_offset_is_refused_by_name(self):
        # Two equal-sized, individually valid entries of the same store
        # swapped: each is a well-formed entry at a wrong offset whose
        # recorded trailer is not the descriptor's.
        ids, found = self.init_and_post()
        (a, n), (b, _) = found[2], found[3]
        baseline, again, cold, owner = self.warm_then_substitute_then_read(
            self.swap(a, b, n), cached=ids[0], cold=ids[2])
        self.assertEqual(again, baseline)
        self.assertIsNone(cold)
        self.refused_by_name(owner, "arena-extent-trailer")

    def test_an_entry_of_another_store_at_the_offset_is_refused_by_name(self):
        other = Node(self, self.image, root=self.root / "other", name="other", listener=True,
                     control=True)
        other.image = self.image
        _ids, theirs = self.init_and_post(node=other, prefix="xo")
        foreign = (other.store_path / SEGMENT).read_bytes()
        ids, found = self.init_and_post()
        (a, n) = found[2]
        (fa, fn) = theirs[2]
        self.assertEqual(n, fn)

        def edit(data):
            data[a:a + n + TRAILER] = foreign[fa:fa + fn + TRAILER]
        baseline, again, cold, owner = self.warm_then_substitute_then_read(
            edit, cached=ids[0], cold=ids[2])
        self.assertEqual(again, baseline)
        self.assertIsNone(cold)
        self.refused_by_name(owner, "arena-extent-trailer")

    def test_a_wrong_recorded_trailer_under_an_intact_prefix_is_refused_by_name(self):
        # The prefix is the extent's; the trailer recorded after it is
        # another entry's (well formed, a real digest): the descriptor's
        # expected trailer is not what the file records.
        ids, found = self.init_and_post()
        (a, n), (b, _) = found[2], found[3]

        def edit(data):
            data[a + n:a + n + TRAILER] = data[b + n:b + n + TRAILER]
        baseline, again, cold, owner = self.warm_then_substitute_then_read(
            edit, cached=ids[0], cold=ids[2])
        self.assertEqual(again, baseline)
        self.assertIsNone(cold)
        self.refused_by_name(owner, "arena-extent-trailer")

    def test_a_prefix_damaged_under_its_own_trailer_is_refused_by_a_distinct_name(self):
        ids, found = self.init_and_post()
        (a, n) = found[2]

        def edit(data):
            data[a + n - 1] ^= 1
        baseline, again, cold, owner = self.warm_then_substitute_then_read(
            edit, cached=ids[0], cold=ids[2])
        self.assertEqual(again, baseline)
        self.assertIsNone(cold)
        self.refused_by_name(owner, "arena-extent-digest")

    def test_a_cached_entry_serves_under_its_identity_and_the_cache_off_arm_refuses(self):
        # The stale-cache case: after the substitution the entry read before
        # it is still served (a hit under (file, offset, length, trailer):
        # the verified read of that identity) and equals the baseline; the
        # cache-off arm of the developer image re-reads and is refused.
        if self.image != IMAGE:
            self.skipTest("the cache-off selector is developer-only")
        ids, found = self.init_and_post()
        (a, n), (b, _) = found[0], found[1]
        baseline, again, cold, owner = self.warm_then_substitute_then_read(
            self.swap(a, b, n), cached=ids[0], cold=ids[1],
            env={"FN_NATIVE_EXTENT_CACHE_TEST_OFF": "1"})
        self.assertIsNone(again)
        self.refused_by_name(owner, "arena-extent-trailer")
        # And with the cache on: the same substitution, the cached read
        # served from the verified entry.
        self.node = Node(self, self.image, root=self.root / "on", name="on", listener=True,
                         control=True)
        self.node.image = self.image
        self.root, self.store = self.node.root, self.node.store_path
        ids, found = self.init_and_post()
        (a, n), (b, _) = found[0], found[1]
        baseline, again, cold, owner = self.warm_then_substitute_then_read(
            self.swap(a, b, n), cached=ids[0], cold=ids[1])
        self.assertEqual(again, baseline)
        self.assertIsNone(cold)
        self.refused_by_name(owner, "arena-extent-trailer")


class ExtentIdentityProductionTests(ExtentIdentityTests):
    image = PRODUCTION

    def test_a_cached_entry_serves_under_its_identity_and_the_cache_off_arm_refuses(self):
        self.skipTest("the cache-off selector is developer-only")


if __name__ == "__main__":
    unittest.main()
