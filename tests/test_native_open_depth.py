"""PKT-876: a registered fixture store opens at the deployed control stack.

A node's every thread, the main one included, runs on the control stack the
installed launcher passes (books/heap-reservation.lisp fn-heap-stack-kib,
1,024 KiB), and since lane open-depth so does every native test: the image's
own launcher carries the same figure (tools/build_native_host.sh).  At that
stack a full-replay open of syn100k-2k (100,000 retained articles) died in
30,527 frames of fn-retain-obligation-ids, one of the per-article walks under
the node recognizer the open runs (fn-cnode-statep from fn-sco-cpr-finish;
lane thread-stacks).  Here each named fixture is copied, rebound to this
filesystem, and opened by the owner (`operator CONFIG run`):

* by full replay (the fixture has no checkpoint): the owner LISTENs, a
  connection is greeted and answers DATE, and the owner stops cleanly with
  no stack exhaustion;
* on a second copy, from a checkpoint `operator CONFIG store checkpoint'
  writes first, the open line naming it: the same.

Each open's seconds to LISTENING are printed (`OPEN-DEPTH NAME MODE
seconds=S`).  The fixtures live on hbox (tools/fixtures.py): set
FN_OPEN_DEPTH_FIXTURES to their directory (/tank/fn/scratch/fixtures) and
FN_OPEN_DEPTH_NAMES to a comma (or colon) list (default syn100k-2k; syn1m-2k needs an
80G scope, its init reservation is 57,158 MB).  FN_OPEN_DEPTH_CHECKPOINT_STACK_KB
writes the checkpoint at another stack (with FN_TEST_CONTROL_STACK_REASON),
to ask whether an image that cannot full-replay-open can open a checkpoint.
Skips, naming the variable, without them.

PKT-877 (lane serve-depth): after the open, every command of defprotocol's
table (books/protocol-table.lisp, one row per command) is issued against the
open store over one connection -- LIST and its variants, GROUP, LISTGROUP,
OVER/XOVER, HDR/XHDR, XPAT, NEWNEWS, NEWGROUPS, ARTICLE/HEAD/BODY/STAT,
LAST/NEXT, POST, IHAVE/CHECK/TAKETHIS, AUTHINFO, STARTTLS, XREDEEM,
XFNCATCHUP, CAPABILITIES, HELP, MODE, DATE, an unrecognized command, QUIT --
with the group's whole range where a command takes one.  A death does not
hide the next one: when the owner stops, the command, its exit and the
owner's last frames are recorded, the owner is reopened and the list goes
on; the test fails at the end naming every command that killed it.  Each
command prints `OPEN-DEPTH NAME MODE SERVED <command> <first reply line>
lines=N seconds=S`.  FN_OPEN_DEPTH_SERVED=0 serves DATE only;
FN_OPEN_DEPTH_ONLY=PREFIX/PREFIX (`_' for a space: GROUP/HDR_:fn-verified) serves
only the commands starting with one (a measurement, not the table's coverage).
"""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import time
import unittest

from tests.native_harness import Node, executable, native_image

IMAGE = native_image("FN_NATIVE_HOST")


FIXTURES = os.environ.get("FN_OPEN_DEPTH_FIXTURES")
NAMES = [n for n in os.environ.get("FN_OPEN_DEPTH_NAMES", "syn100k-2k").replace(":", ",").split(",") if n]
OPEN_SECONDS = 3600
SERVED = os.environ.get("FN_OPEN_DEPTH_SERVED", "1") != "0"
CONTROL = SERVED and os.environ.get("FN_OPEN_DEPTH_CONTROL", "1") != "0"
# Every report the running owner renders on its control thread.
CONTROL_REPORTS = [["status"], ["health"], ["pins"], ["obligations"], ["peer", "list"],
                   ["account", "list"], ["account", "access", "show"], ["consumer", "show"],
                   ["show"]]
# The store verbs an operator runs with no owner (host/native/io.lisp's store dispatch).
# `store export' holds every record as an octet list: at 1,000,000 it exhausts a
# 32 GB heap (lane serve-depth's finding, not the stack), so it runs on the
# fixtures named here.
EXPORT_NAMES = os.environ.get("FN_OPEN_DEPTH_EXPORT", "syn100k-2k").replace(":", ",").split(",")
OFFLINE_VERBS = [["status"], ["digest"], ["journal"], ["retention"], ["compression"], ["config"],
                 ["inspect", "<0000s99999@example.invalid>"]]
# The reply codes after which a multi-line block follows (RFC 3977 3.1.1),
# and 211 only for LISTGROUP.
MULTI = {b"100", b"101", b"215", b"220", b"221", b"222", b"224", b"225", b"230", b"231",
         b"291"}  # 291: XFNCATCHUP's batch, a dot-terminated block (books/peer-catchup-serve.lisp)


def served_commands(group, low, high, msgid):
    """(command, whether it takes a POST body) for every row of the table."""
    whole = "{}-{}".format(low, high) if high else "{}-".format(low)
    high = high or low
    epoch = "19700101 000000 GMT"
    return [
        ("CAPABILITIES", None), ("HELP", None), ("MODE READER", None), ("DATE", None),
        ("LIST", None), ("LIST ACTIVE", None), ("LIST ACTIVE {}".format(group), None),
        ("LIST ACTIVE *", None), ("LIST NEWSGROUPS", None), ("LIST COUNTS", None),
        ("LIST COUNTS {}".format(group), None), ("LIST ACTIVE.TIMES", None),
        ("LIST OVERVIEW.FMT", None), ("LIST HEADERS", None), ("LIST HEADERS MSGID", None),
        ("LIST HEADERS RANGE", None), ("LIST SUBSCRIPTIONS", None), ("LIST MOTD", None),
        ("LIST DISTRIB.PATS", None), ("LIST DISTRIBUTIONS", None),
        ("NEWGROUPS {}".format(epoch), None),
        ("GROUP {}".format(group), None), ("LISTGROUP {}".format(group), None),
        ("LISTGROUP {} {}".format(group, whole), None),
        ("LISTGROUP {} {}-".format(group, low), None),
        ("OVER {}".format(whole), None), ("OVER {}-".format(low), None),
        ("XOVER {}".format(whole), None), ("OVER {}".format(msgid), None),
        ("HDR Subject {}".format(whole), None), ("HDR Message-ID {}-".format(low), None),
        ("HDR :bytes {}".format(whole), None), ("HDR :lines {}".format(whole), None),
        ("HDR Xref {}".format(whole), None), ("HDR :fn-verified {}".format(whole), None),
        # :fn-verified over the whole range: the catalog and one pass over the
        # verdict list (lane scale-reads, books/served-catalog.lisp
        # fn-nntp-verdict-hdr-response-cat); it was quadratic, over 30 minutes
        # at 100,000 (lane serve-depth).
        ("HDR :fn-control {}".format(whole), None),
        ("HDR :fn-enrollment {}".format(whole), None), ("HDR Subject {}".format(msgid), None),
        ("XHDR Subject {}".format(whole), None), ("XHDR Message-ID {}".format(msgid), None),
        ("XPAT Subject {} *".format(whole), None), ("XPAT Message-ID {} *".format(whole), None),
        ("NEWNEWS * {}".format(epoch), None), ("NEWNEWS {} {}".format(group, epoch), None),
        ("GROUP {}".format(group), None),
        ("STAT", None), ("NEXT", None), ("LAST", None),
        ("ARTICLE {}".format(high), None), ("HEAD {}".format(low), None),
        ("BODY {}".format(high), None), ("STAT {}".format(high), None),
        ("ARTICLE {}".format(msgid), None), ("HEAD {}".format(msgid), None),
        ("BODY {}".format(msgid), None), ("STAT {}".format(msgid), None),
        ("XFNCATCHUP * {} {} 1000".format("0" * 16, "0" * 64), None),
        ("XREDEEM code", None), ("AUTHINFO USER nobody", None), ("STARTTLS", None),
        ("CHECK {}".format(msgid), None), ("IHAVE {}".format(msgid), None),
        ("TAKETHIS <serve-depth-takethis@fn.invalid>", None),
        ("POST", group), ("GROUP {}".format(group), None), ("LISTGROUP {}".format(group), None),
        ("XSERVEDEPTHUNKNOWN", None), ("QUIT", None),
    ]


def dying_frames(text):
    """The distinct fn functions of a death's backtrace, innermost first, and
    the fault line: what the owner printed since it started."""
    text = text.decode("utf-8", "replace")
    names = []
    for word in text.replace("(", " ").replace(")", " ").split():
        word = word.upper()
        if word.startswith("ACL2::FN-"):
            word = word[len("ACL2::"):]
        if word.startswith("FN-") and word not in names and len(names) < 8:
            names.append(word)
    faults = [l.strip() for l in text.splitlines() if "exhausted" in l or l.startswith("fault")]
    return names + faults[-1:]


def post_body(group):
    return ("From: serve-depth <serve-depth@fn.invalid>\r\nNewsgroups: {}\r\n"
            "Subject: serve-depth after the whole-range reads\r\n"
            "Message-ID: <serve-depth-{}@fn.invalid>\r\n\r\nbody\r\n.\r\n").format(
                group, os.getpid()).encode("ascii")


def stack_env(kib):
    return {"SBCL_USER_ARGS": "--control-stack-size {}KB".format(kib)} if kib else None


class OpenDepthTests(unittest.TestCase):
    def setUp(self):
        if not executable(IMAGE):
            self.skipTest("needs the production image {}".format(IMAGE))
        if not FIXTURES or not Path(FIXTURES).is_dir():
            self.skipTest("FN_OPEN_DEPTH_FIXTURES names no directory (hbox: /tank/fn/scratch/fixtures)")
        self.work = Path(tempfile.mkdtemp(prefix="fn-open-depth-", dir=os.environ.get("FN_OPEN_DEPTH_WORK")))
        self.addCleanup(shutil.rmtree, self.work, True)

    def prepare(self, name):
        source = Path(FIXTURES) / name / "store"
        if not source.is_dir():
            self.skipTest("no fixture store {}".format(source))
        node = Node(self, IMAGE, root=self.work / name, name=name)
        shutil.copytree(source, node.store_path, symlinks=True)
        lock = node.store_path / "writer.lock"
        if not lock.exists():
            lock.touch(mode=0o600)
        rebound = node.store("rebind-filesystem", timeout=600)
        self.assertEqual(rebound.returncode, 0, rebound.stderr)
        return node

    def start_owner(self, node):
        """Start the owner; answer (process, seconds to LISTENING, OWNER-OPEN line)."""
        started = time.monotonic()
        owner = node.start(timeout=OPEN_SECONDS, limit=64 << 20)
        opened = [l for l in owner.stderr.since(0).decode("utf-8", "replace").splitlines()
                  if l.startswith("OWNER-OPEN")]
        return owner, time.monotonic() - started, (opened[-1] if opened else "")

    def stop_owner(self, node, owner):
        # At 1,000,000 an owner still rendering the reports the control
        # client gave up on (status, obligations: uncertain after 10 s)
        # took over 600 s to stop (native-sd5).
        status = node.stop(expect=None, process=owner, grace=OPEN_SECONDS)
        if self.deaths:
            return
        text = owner.stderr.since(0).decode("utf-8", "replace")
        self.assertNotIn("Control stack exhausted", text)
        self.assertEqual(status, 0, text[-3000:])

    def open_and_serve(self, name, mode, node):
        self.deaths = []
        # Commands the live owner answered with no reply line: a closed
        # connection (other than QUIT's), a read error or timeout, or a first
        # line that is not a three-digit reply.  Before 2026-10-03 (sweep
        # S133) only owner deaths were asserted, so a command that never
        # answered at depth passed.
        self.drops = []
        owner, listening, opened = self.start_owner(node)
        self.state = {"owner": owner}
        print("OPEN-DEPTH {} {} seconds={:.1f} {}".format(
            name, mode, listening, opened or "(no OWNER-OPEN line)"), flush=True)
        try:
            if SERVED:
                self.serve_every_command(name, mode, node)
                if CONTROL:
                    self.control_reports(name, mode, node)
                self.assertEqual([(t, e) for t, e, _ in self.deaths], [],
                                 "commands or reports that stopped the owner at {} ({})".format(
                                     name, mode))
                self.assertEqual(self.drops, [],
                                 "commands the live owner did not answer at {} ({})".format(
                                     name, mode))
            else:
                with node.session(timeout=600, greeting=None) as client:
                    self.assertTrue(client.greeting.startswith(b"20"))
                    reply = client.command("DATE")
                    print("OPEN-DEPTH {} {} {}".format(name, mode, reply.strip().decode("ascii")),
                          flush=True)
                    self.assertTrue(reply.startswith(b"111 "), reply)
            return opened
        finally:
            self.stop_owner(node, self.state["owner"])

    def serve_every_command(self, name, mode, node):
        """Every command of the table against the open store; reopen after a death."""
        deaths = self.deaths
        state = self.state

        def connect():
            client = node.session(timeout=1800, greeting=None)
            self.assertTrue(client.greeting.startswith(b"20"), client.greeting)
            return client

        def exchange(client, text, body):
            lines = 0
            try:
                first = client.command(text)
                code = first[:3]
                if body is not None and code == b"340":
                    client.send(post_body(body))
                    first = client.line()
                    code = first[:3]
                if code in MULTI or (code == b"211" and text.startswith("LISTGROUP")):
                    while client.line() != b".\r\n":
                        lines += 1
            except EOFError:
                return None, lines
            return first, lines

        client = connect()
        group = os.environ.get("FN_OPEN_DEPTH_GROUP", "fn.test")

        def run(text, body):
            nonlocal client
            started = time.monotonic()
            try:
                first, lines = exchange(client, text, body)
            except OSError as e:
                first, lines = None, 0
                print("OPEN-DEPTH {} {} SERVED {} connection error {}".format(name, mode, text, e),
                      flush=True)
            seconds = time.monotonic() - started
            if first is not None and not first[:3].isdigit():
                self.drops.append((text, "not a reply: {!r}".format(first[:40])))
            if first is not None:
                print("OPEN-DEPTH {} {} SERVED {} {} lines={} seconds={:.1f}".format(
                    name, mode, text, first.strip().decode("utf-8", "replace")[:80], lines,
                    seconds), flush=True)
                return first
            proc = state["owner"]
            try:
                proc.wait(5 if text == "QUIT" else 60)
            except subprocess.TimeoutExpired:
                pass
            client.close(quit=False)
            if proc.poll() is None:
                # The connection closed and the owner lives: QUIT's own close,
                # or a drop, which is recorded.  Reconnect either way.
                if text != "QUIT":
                    self.drops.append((text, "closed with no reply, owner alive"))
                print("OPEN-DEPTH {} {} SERVED {} (closed) seconds={:.1f}".format(
                    name, mode, text, seconds), flush=True)
            else:
                frames = dying_frames(proc.stderr.since(0))
                deaths.append((text, proc.returncode, frames))
                print("OPEN-DEPTH {} {} SERVED {} OWNER-DIED exit={} seconds={:.1f} {}".format(
                    name, mode, text, proc.returncode, seconds, " | ".join(frames)), flush=True)
                state["owner"], _, _ = self.start_owner(node)
            client = connect()
            if text != "QUIT":
                exchange(client, "GROUP {}".format(group), None)
            return None

        # The group with the most articles, when LIST ACTIVE answers: the one
        # whose whole range is deepest.
        best = None
        try:
            head = client.command("LIST ACTIVE")
            while head.startswith(b"215"):
                line = client.line()
                if line == b".\r\n":
                    break
                words = line.split()
                if len(words) >= 3 and words[1].isdigit() and words[2].isdigit():
                    depth = int(words[1]) - int(words[2])
                    if best is None or depth > best[0]:
                        best = (depth, words[0].decode("ascii"))
        except EOFError:
            pass
        if best is not None:
            group = best[1]
        else:
            run("LIST ACTIVE", None)
        low, high = 1, None
        first = run("GROUP {}".format(group), None)
        if first and first.startswith(b"211"):
            low, high = int(first.split()[2]), int(first.split()[3])
        msgid = "<serve-depth-none@fn.invalid>"
        first = run("HEAD {}".format(high if high else low), None)
        if first and first.startswith(b"221") and len(first.split()) > 2:
            msgid = first.split()[2].decode("ascii")
        self.msgid = msgid
        print("OPEN-DEPTH {} {} group={} low={} high={} msgid={}".format(
            name, mode, group, low, high, msgid), flush=True)
        only = [w.replace("_", " ") for w in os.environ.get("FN_OPEN_DEPTH_ONLY", "").split("/") if w]
        for text, body in served_commands(group, low, high, msgid):
            if only and not any(text.startswith(w) for w in only):
                continue
            if run(text, body) is not None and text == "QUIT":
                break
        client.close(quit=False)

    def control_reports(self, name, mode, node):
        """Every live report the control thread renders, against the open store.

        The owner renders them on the control socket's thread (1,024 KiB like
        every other): status and health stopped it at 20,000 and 60,000
        articles (lane health-truth).  A death is recorded and the owner
        reopened, as for a served command."""
        for words in CONTROL_REPORTS:
            started = time.monotonic()
            done = node.operator(*words, timeout=OPEN_SECONDS)
            seconds = time.monotonic() - started
            proc = self.state["owner"]
            text = (done.stdout + done.stderr).decode("utf-8", "replace")
            try:
                proc.wait(2)
            except subprocess.TimeoutExpired:
                pass
            if proc.poll() is not None or "Control stack exhausted" in text:
                frames = dying_frames(proc.stderr.since(0))
                self.deaths.append((" ".join(words), proc.returncode, frames))
                print("OPEN-DEPTH {} {} CONTROL {} OWNER-DIED exit={} seconds={:.1f} {} | {}".format(
                    name, mode, " ".join(words), proc.returncode, seconds, " | ".join(frames),
                    text.strip()[-200:]), flush=True)
                node.stop(expect=None, process=proc, grace=600)
                self.state["owner"], _, _ = self.start_owner(node)
                continue
            print("OPEN-DEPTH {} {} CONTROL {} exit={} bytes={} seconds={:.1f} {}".format(
                name, mode, " ".join(words), done.returncode, len(done.stdout), seconds,
                text.strip().splitlines()[-1][:100] if text.strip() else ""), flush=True)

    def offline_store_verbs(self, name, node):
        """The store verbs, with no owner, over the whole store."""
        failures = []
        export = [["export", str(node.root / "export")]] if name in EXPORT_NAMES else []
        for words in OFFLINE_VERBS + export:
            started = time.monotonic()
            done = node.store(*words, timeout=OPEN_SECONDS)
            text = (done.stdout + done.stderr).decode("utf-8", "replace")
            print("OPEN-DEPTH {} STORE {} exit={} bytes={} seconds={:.1f} {}".format(
                name, " ".join(words[:1]), done.returncode, len(done.stdout),
                time.monotonic() - started,
                text.strip().splitlines()[-1][:100] if text.strip() else ""), flush=True)
            if done.returncode != 0 or "Control stack exhausted" in text:
                failures.append((words[0], done.returncode, text.strip()[-300:]))
        shutil.rmtree(node.root / "export", ignore_errors=True)
        self.assertEqual(failures, [], "store verbs that failed at {}".format(name))

    def test_full_replay_open_at_the_deployed_stack(self):
        for name in NAMES:
            with self.subTest(fixture=name):
                node = self.prepare(name)
                line = self.open_and_serve(name, "full-replay", node)
                if CONTROL:
                    self.offline_store_verbs(name, node)
                self.assertIn("open=full-replay", line)

    def test_checkpoint_open_at_the_deployed_stack(self):
        kib = os.environ.get("FN_OPEN_DEPTH_CHECKPOINT_STACK_KB")
        if kib:
            self.assertTrue(os.environ.get("FN_TEST_CONTROL_STACK_REASON"),
                            "FN_OPEN_DEPTH_CHECKPOINT_STACK_KB needs FN_TEST_CONTROL_STACK_REASON")
        for name in NAMES:
            with self.subTest(fixture=name):
                node = self.prepare(name)
                started = time.monotonic()
                made = node.operator("store", "checkpoint", env=stack_env(kib),
                                     timeout=OPEN_SECONDS)
                print("OPEN-DEPTH {} store-checkpoint stack={} seconds={:.1f} exit={} {}".format(
                    name, kib or "launcher", time.monotonic() - started, made.returncode,
                    made.stdout.decode("utf-8", "replace").strip()[-200:]), flush=True)
                self.assertEqual(made.returncode, 0, made.stderr[-3000:])
                line = self.open_and_serve(name, "checkpoint", node)
                self.assertIn("open=checkpoint:", line)

if __name__ == "__main__":
    unittest.main()
