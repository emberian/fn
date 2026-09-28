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
lines=N seconds=S`.  FN_OPEN_DEPTH_SERVED=0 serves DATE only.
"""
import os
from pathlib import Path
import select
import shutil
import socket
import subprocess
import tempfile
import time
import unittest

from tests import test_native_operator_verbs as verbs


FIXTURES = os.environ.get("FN_OPEN_DEPTH_FIXTURES")
NAMES = [n for n in os.environ.get("FN_OPEN_DEPTH_NAMES", "syn100k-2k").replace(":", ",").split(",") if n]
OPEN_SECONDS = 3600
SERVED = os.environ.get("FN_OPEN_DEPTH_SERVED", "1") != "0"
# The reply codes after which a multi-line block follows (RFC 3977 3.1.1),
# and 211 only for LISTGROUP.
MULTI = {b"100", b"101", b"215", b"220", b"221", b"222", b"224", b"225", b"230", b"231"}


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
        ("XFNCATCHUP * {} 0 {}".format(whole, whole), None),
        ("XREDEEM code", None), ("AUTHINFO USER nobody", None), ("STARTTLS", None),
        ("CHECK {}".format(msgid), None), ("IHAVE {}".format(msgid), None),
        ("TAKETHIS <serve-depth-takethis@fn.invalid>", None),
        ("POST", group), ("GROUP {}".format(group), None), ("LISTGROUP {}".format(group), None),
        ("XSERVEDEPTHUNKNOWN", None), ("QUIT", None),
    ]


def post_body(group):
    return ("From: serve-depth <serve-depth@fn.invalid>\r\nNewsgroups: {}\r\n"
            "Subject: serve-depth after the whole-range reads\r\n"
            "Message-ID: <serve-depth-{}@fn.invalid>\r\n\r\nbody\r\n.\r\n").format(
                group, os.getpid()).encode("ascii")


def env_at(kib):
    env = verbs.environment()
    if kib:
        env["SBCL_USER_ARGS"] = "--control-stack-size {}KB".format(kib)
    return env


class OpenDepthTests(unittest.TestCase):
    def setUp(self):
        if not verbs.executable(verbs.IMAGE):
            self.skipTest("needs the production image {}".format(verbs.IMAGE))
        if not FIXTURES or not Path(FIXTURES).is_dir():
            self.skipTest("FN_OPEN_DEPTH_FIXTURES names no directory (hbox: /tank/fn/scratch/fixtures)")
        self.work = Path(tempfile.mkdtemp(prefix="fn-open-depth-", dir=os.environ.get("FN_OPEN_DEPTH_WORK")))
        self.addCleanup(shutil.rmtree, self.work, True)

    def prepare(self, name):
        source = Path(FIXTURES) / name / "store"
        if not source.is_dir():
            self.skipTest("no fixture store {}".format(source))
        root = self.work / name
        store = root / "store"
        shutil.copytree(source, store, symlinks=True)
        lock = store / "writer.lock"
        if not lock.exists():
            lock.touch(mode=0o600)
        rebound = subprocess.run([str(verbs.IMAGE), "--fn", "store", str(store), "rebind-filesystem"],
                                 env=verbs.environment(), stdout=subprocess.PIPE,
                                 stderr=subprocess.PIPE, timeout=600)
        self.assertEqual(rebound.returncode, 0, rebound.stderr)
        port = verbs.free_port()
        config = root / "fn.toml"
        config.write_text('[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
                          '[control]\npath = "{}"\n'.format(store, port, root / "control.sock"),
                          encoding="ascii")
        return root, config, port

    def start_owner(self, name, mode, root, config, err_path):
        """Start the owner; answer (process, seconds to LISTENING, OWNER-OPEN line)."""
        err = open(err_path, "ab")
        self.addCleanup(err.close)
        started = time.monotonic()
        owner = subprocess.Popen([str(verbs.IMAGE), "--fn", "operator", str(config), "run"],
                                 env=verbs.environment(), stdout=subprocess.PIPE, stderr=err)
        while True:
            ready = select.select([owner.stdout], [], [], OPEN_SECONDS)[0]
            if not ready:
                owner.kill()
                self.fail("no LISTENING in {} s".format(OPEN_SECONDS))
            line = owner.stdout.readline()
            if not line:
                owner.wait(60)
                self.fail("{} {}: the owner stopped at open (exit {}): {}".format(
                    name, mode, owner.returncode,
                    err_path.read_bytes()[-3000:].decode("utf-8", "replace")))
            if line.startswith(b"LISTENING"):
                break
        opened = [l for l in err_path.read_text("utf-8", "replace").splitlines()
                  if l.startswith("OWNER-OPEN")]
        return owner, time.monotonic() - started, (opened[-1] if opened else "")

    def stop_owner(self, owner, err_path):
        if owner.poll() is None:
            owner.terminate()
            owner.wait(600)
        if self.deaths:
            return
        text = err_path.read_text("utf-8", "replace")
        self.assertNotIn("Control stack exhausted", text)
        self.assertEqual(owner.returncode, 0, text[-3000:])

    def open_and_serve(self, name, mode, root, config, port):
        err_path = root / "owner-{}.err".format(mode)
        self.deaths = []
        owner, listening, opened = self.start_owner(name, mode, root, config, err_path)
        self.state = {"owner": owner}
        print("OPEN-DEPTH {} {} seconds={:.1f} {}".format(
            name, mode, listening, opened or "(no OWNER-OPEN line)"), flush=True)
        try:
            if SERVED:
                self.serve_every_command(name, mode, root, config, port, err_path)
            else:
                with socket.create_connection(("127.0.0.1", port), timeout=600) as conn:
                    f = conn.makefile("rwb")
                    self.assertTrue(f.readline().startswith(b"20"))
                    f.write(b"DATE\r\n")
                    f.flush()
                    reply = f.readline()
                    print("OPEN-DEPTH {} {} {}".format(name, mode, reply.strip().decode("ascii")),
                          flush=True)
                    self.assertTrue(reply.startswith(b"111 "), reply)
            return opened
        finally:
            self.stop_owner(self.state["owner"], err_path)

    def serve_every_command(self, name, mode, root, config, port, err_path):
        """Every command of the table against the open store; reopen after a death."""
        deaths = self.deaths
        state = self.state

        def connect():
            c = socket.create_connection(("127.0.0.1", port), timeout=1800)
            h = c.makefile("rwb")
            greeting = h.readline()
            self.assertTrue(greeting.startswith(b"20"), greeting)
            return c, h

        def exchange(h, text, body):
            h.write(text.encode("ascii") + b"\r\n")
            h.flush()
            first = h.readline()
            if not first:
                return None, 0
            code = first[:3]
            lines = 0
            if body is not None and code == b"340":
                h.write(post_body(body))
                h.flush()
                first = h.readline()
                if not first:
                    return None, 0
                code = first[:3]
            if code in MULTI or (code == b"211" and text.startswith("LISTGROUP")):
                while True:
                    line = h.readline()
                    if not line:
                        return None, lines
                    if line == b".\r\n":
                        break
                    lines += 1
            return first, lines

        conn, f = connect()
        group = os.environ.get("FN_OPEN_DEPTH_GROUP", "fn.test")

        def run(text, body):
            nonlocal conn, f
            started = time.monotonic()
            try:
                first, lines = exchange(f, text, body)
            except OSError as e:
                first, lines = None, 0
                print("OPEN-DEPTH {} {} SERVED {} connection error {}".format(name, mode, text, e),
                      flush=True)
            seconds = time.monotonic() - started
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
            conn.close()
            if proc.poll() is None:
                # The connection closed and the owner lives (QUIT): reconnect.
                print("OPEN-DEPTH {} {} SERVED {} (closed) seconds={:.1f}".format(
                    name, mode, text, seconds), flush=True)
            else:
                tail = err_path.read_bytes()[-6000:].decode("utf-8", "replace")
                frames = [l.strip() for l in tail.splitlines()
                          if "FN-" in l.upper() or "exhausted" in l][-8:]
                deaths.append((text, proc.returncode, frames))
                print("OPEN-DEPTH {} {} SERVED {} OWNER-DIED exit={} seconds={:.1f} {}".format(
                    name, mode, text, proc.returncode, seconds, " | ".join(frames)), flush=True)
                state["owner"], _, _ = self.start_owner(name, mode + "-reopen", root, config,
                                                        err_path)
            conn, f = connect()
            if text != "QUIT":
                exchange(f, "GROUP {}".format(group), None)
            return None

        # The group with the most articles, when LIST ACTIVE answers: the one
        # whose whole range is deepest.
        f.write(b"LIST ACTIVE\r\n")
        f.flush()
        head = f.readline()
        best = None
        while head.startswith(b"215"):
            line = f.readline()
            if not line or line == b".\r\n":
                break
            words = line.split()
            if len(words) >= 3 and words[1].isdigit() and words[2].isdigit():
                depth = int(words[1]) - int(words[2])
                if best is None or depth > best[0]:
                    best = (depth, words[0].decode("ascii"))
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
        print("OPEN-DEPTH {} {} group={} low={} high={} msgid={}".format(
            name, mode, group, low, high, msgid), flush=True)
        for text, body in served_commands(group, low, high, msgid):
            if run(text, body) is not None and text == "QUIT":
                break
        conn.close()
        self.assertEqual([(t, e) for t, e, _ in deaths], [], "commands that stopped the owner at {} ({}): {}".format(
            name, mode, "; ".join("{} (exit {})".format(t, e) for t, e, _ in deaths)))

    def test_full_replay_open_at_the_deployed_stack(self):
        for name in NAMES:
            with self.subTest(fixture=name):
                root, config, port = self.prepare(name)
                line = self.open_and_serve(name, "full-replay", root, config, port)
                self.assertIn("open=full-replay", line)

    def test_checkpoint_open_at_the_deployed_stack(self):
        kib = os.environ.get("FN_OPEN_DEPTH_CHECKPOINT_STACK_KB")
        if kib:
            self.assertTrue(os.environ.get("FN_TEST_CONTROL_STACK_REASON"),
                            "FN_OPEN_DEPTH_CHECKPOINT_STACK_KB needs FN_TEST_CONTROL_STACK_REASON")
        for name in NAMES:
            with self.subTest(fixture=name):
                root, config, port = self.prepare(name)
                started = time.monotonic()
                made = subprocess.run([str(verbs.IMAGE), "--fn", "operator", str(config), "store",
                                       "checkpoint"], env=env_at(kib), stdout=subprocess.PIPE,
                                      stderr=subprocess.PIPE, timeout=OPEN_SECONDS)
                print("OPEN-DEPTH {} store-checkpoint stack={} seconds={:.1f} exit={} {}".format(
                    name, kib or "launcher", time.monotonic() - started, made.returncode,
                    made.stdout.decode("utf-8", "replace").strip()[-200:]), flush=True)
                self.assertEqual(made.returncode, 0, made.stderr[-3000:])
                line = self.open_and_serve(name, "checkpoint", root, config, port)
                self.assertIn("open=checkpoint:", line)

if __name__ == "__main__":
    unittest.main()
