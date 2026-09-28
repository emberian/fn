"""The decision journal never keeps a torn line (lane health-truth-journal,
2026-09-28; PKT-872, PRF-360, HST-030, SCN-192).

Lane fitness's full-disk run (planning/evidence/fitness-2026-09-28.md, f2-full)
left a decision journal whose writer hit ENOSPC part-way through an entry and
then appended the next entry after the torn octets: `store ROOT journal' read
`malformed-at-18416' for that store forever.  The writer's rule is now ACL2's
(books/owner-time-journal-writer.lisp): a failed append is truncated back to
the last whole entry, the next entry written after a lost one carries a mark
line, which the replay reads as a gap naming the first sequence number
missing, and each run's start cuts a torn tail left by a death mid-append.

The developer selector FN_NATIVE_TEST_JOURNAL_FAIL_FILE makes every journal
append write half its octets and fail while the named file exists (the
f2-full shape without filling a filesystem).  The cases:

  * appends fail for a stretch while POSTs keep being accepted; afterwards
    the journal holds only whole entries and the mark, `store ROOT journal'
    exits 1 with `status=whole replay=gap-at-N', N one past the last entry
    before the mark, never malformed;
  * a torn tail (half an entry, as a process that died mid-append leaves it)
    is cut when the next run opens the journal, which then replays to
    agreement.
"""
import os
from pathlib import Path
import re
import select
import signal
import socket
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
DEVELOPER = Path(os.environ.get("FN_NATIVE_DEVELOPER_HOST", ROOT / "build" / "fn-host-developer"))
MARK = [0, 6, 0, 0, 0, 0, 0]


def environment():
    env = dict(os.environ)
    env["ACL2_CUSTOMIZATION"] = "NONE"
    env.pop("ACL2_SYSTEM_BOOKS", None)
    env.pop("FN_HOST", None)
    return env


def executable(path):
    return path.is_file() and os.access(path, os.X_OK)


def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


class JournalWriterSourceTests(unittest.TestCase):
    """Every writer decision is ACL2's; the host performs the I/O."""

    def test_the_writer_and_the_open_call_acl2(self):
        io = (ROOT / "host" / "native" / "io.lisp").read_text()
        write = io[io.index("(defun fnn-journal-write "):io.index("(defun fnn-log-write-item ")]
        for call in ("'fn-otm-jw-drop", "'fn-otm-jw-plan", "'fn-otm-jw-after",
                     "'fn-otm-jw-truncated", "'fn-otm-jw-closed-line", "sb-posix:ftruncate"):
            self.assertIn(call, write)
        item = io[io.index("(defun fnn-log-write-item "):io.index("(defun fnn-log-writer-loop")]
        self.assertIn("(fnn-journal-write octets (eq destination :journal-gap))", item)
        offer = io[io.index("(defun fnn-log-offer "):io.index("(defun fnn-log-sink-snapshot")]
        self.assertIn(":journal-gap", offer)
        self.assertIn("(setq *fnn-journal-dropped* t)", offer)
        owner = (ROOT / "host" / "native" / "owner.lisp").read_text()
        opening = owner[owner.index("(defun fnn-owner-journal-open "):owner.index("(defun fnn-owner-journal-close")]
        self.assertIn("'fn-otm-jw-init", opening)
        self.assertIn("'fn-otm-jw-open-step", opening)
        self.assertIn("'fn-otm-jw-open-first", opening)
        self.assertIn("'fn-otm-jw-cut-line", opening)
        # the writer state is set before the run's start entry is offered
        self.assertLess(opening.index("(setq *fnn-journal-w*"),
                        opening.index("'fn-otm-start-line"))


@unittest.skipUnless(executable(DEVELOPER), "no developer image at %s" % DEVELOPER)
class JournalWriterNativeTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="fn-journal-torn-")
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.store = self.root / "store"
        self.control = self.root / "control.sock"
        self.config = self.root / "fn.toml"
        self.fail_file = self.root / "journal-fail"
        self.port = free_port()
        self.config.write_text(
            '[store]\npath = "{}"\n'
            '[listener]\nhost = "127.0.0.1"\nport = {}\n'
            '[control]\npath = "{}"\n'.format(self.store, self.port, self.control),
            encoding="ascii")
        init = self.operator("init", "--max-article-octets", "1048576", "fn.test")
        self.assertEqual(init.returncode, 0, init.stderr.decode())
        self.log = open(self.root / "owner.stderr", "wb")
        self.addCleanup(self.log.close)
        self.addCleanup(lambda: self.fail_file.unlink() if self.fail_file.exists() else None)
        self.journal = self.store / "decisions" / "decisions.fnj"
        self.posted = 0

    def operator(self, *words, timeout=60):
        return subprocess.run(
            [str(DEVELOPER), "--fn", "operator", str(self.config), *words],
            cwd=ROOT, env=environment(), stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, timeout=timeout, check=False)

    def start_owner(self):
        env = environment()
        env["FN_NATIVE_TEST_JOURNAL_FAIL_FILE"] = str(self.fail_file)
        process = subprocess.Popen(
            [str(DEVELOPER), "--fn", "operator", str(self.config), "run"],
            cwd=ROOT, env=env, stdout=subprocess.PIPE, stderr=self.log, bufsize=0)
        self.addCleanup(self.stop_owner, process)
        for _ in range(4):
            self.assertTrue(select.select([process.stdout], [], [], 180)[0],
                            "the owner did not become ready")
            line = process.stdout.readline()
            if line.startswith(b"LISTENING "):
                return process
            self.assertIsNone(process.poll(), "the owner exited before listening")
        self.fail("the owner's readiness output was malformed")

    def stop_owner(self, process):
        if process.poll() is None:
            process.send_signal(signal.SIGTERM)
            try:
                process.wait(timeout=60)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait(timeout=10)
        if process.stdout and not process.stdout.closed:
            process.stdout.close()

    def post(self, count):
        conn = socket.create_connection(("127.0.0.1", self.port), timeout=120)
        with conn:
            stream = conn.makefile("rwb")
            self.assertTrue(stream.readline().startswith(b"200"))
            for _ in range(count):
                self.posted += 1
                msgid = b"jt-%d@example.invalid" % self.posted
                stream.write(b"POST\r\n")
                stream.flush()
                line = stream.readline()
                self.assertTrue(line.startswith(b"340"), line)
                stream.write(b"From: author@example.invalid\r\nNewsgroups: fn.test\r\n"
                             b"Subject: journal\r\nMessage-ID: <" + msgid + b">\r\n\r\n"
                             b"body\r\n.\r\n")
                stream.flush()
                line = stream.readline()
                self.assertTrue(line.startswith(b"240"), (msgid, line))
                stream.write(b"GROUP fn.test\r\n")
                stream.flush()
                self.assertTrue(stream.readline().startswith(b"211"))
            stream.write(b"QUIT\r\n")
            stream.flush()

    def replay(self):
        result = subprocess.run([str(DEVELOPER), "--fn", "store", str(self.store), "journal"],
                                cwd=ROOT, env=environment(), stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE, timeout=120, check=False)
        print("store journal: rc=%d %r" % (result.returncode, result.stdout))
        return result

    def entries(self):
        data = self.journal.read_bytes()
        self.assertTrue(data.endswith(b"\n"), data[-80:])
        lines = data.split(b"\n")[:-1]
        entries = [[int(x) for x in line.split(b" ")] for line in lines]
        self.assertTrue(all(len(e) == 7 for e in entries), "a journal line is not a whole entry")
        return entries

    def test_failed_appends_leave_whole_entries_and_a_named_gap(self):
        owner = self.start_owner()
        self.post(3)
        self.fail_file.write_bytes(b"")
        # The owner keeps serving while every journal append fails.
        self.post(4)
        self.fail_file.unlink()
        self.post(3)
        self.stop_owner(owner)
        self.assertEqual(owner.returncode, 0)
        entries = self.entries()
        self.assertIn(MARK, entries)
        at = entries.index(MARK)
        before = entries[at - 1]
        self.assertNotEqual(before[1], 0, "no entry of this run before the mark")
        replay = self.replay()
        self.assertEqual(replay.returncode, 1, replay.stderr)
        self.assertIn(b" status=whole", replay.stdout)
        self.assertIn(b" replay=gap-at-%d" % (before[0] + 1), replay.stdout)
        self.assertNotIn(b"malformed", replay.stdout)

    def test_a_torn_tail_is_cut_when_the_next_run_opens_the_journal(self):
        owner = self.start_owner()
        self.post(2)
        self.stop_owner(owner)
        self.assertEqual(owner.returncode, 0)
        whole = self.journal.read_bytes()
        # Half an entry, as a process that died mid-append leaves it.
        with open(self.journal, "ab") as journal:
            journal.write(b"12 1 45")
        torn = self.replay()
        self.assertIn(b" status=torn", torn.stdout)
        owner = self.start_owner()
        self.post(2)
        self.stop_owner(owner)
        self.assertEqual(owner.returncode, 0)
        data = self.journal.read_bytes()
        self.assertTrue(data.startswith(whole), "the cut removed a whole entry")
        self.assertEqual(data[len(whole):len(whole) + 2], b"0 ", "the next run did not start after the cut")
        self.entries()
        log = (self.root / "owner.stderr").read_bytes()
        self.assertIn(b"decision journal: the previous run's torn last entry (7 octets) was cut", log)
        replay = self.replay()
        self.assertEqual(replay.returncode, 0, (replay.stdout, replay.stderr))
        self.assertIn(b" status=whole", replay.stdout)
        self.assertIn(b" segments=2", replay.stdout)
        self.assertIn(b" replay=agrees", replay.stdout)


if __name__ == "__main__":
    unittest.main()
