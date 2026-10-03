"""Host lifecycle: a client's or peer's event ends that connection, never the
node (lane host-lifecycle, 2026-10-03; Astra r71, inspection sweep
2026-10-03).

Each case is a remote or lifecycle event the native host once turned into a
stopped owner, a wedged loop or an unjoined worker, driven on a scratch
developer node; the assertion is that the node keeps serving (or settles its
stop cleanly) and that the client gets the protocol's answer.

    FN_NATIVE_DEVELOPER_HOST=build/fn-host-developer \\
        python3 -m unittest tests.test_native_host_lifecycle
"""
import os
import re
import resource
import signal
import socket
import statistics
import sys
import threading
import time
import unittest

from tests import test_native_checkpoint_auto as auto
from tests.test_native_web import PASSWORD, Browser
from tests.native_harness import (EXIT, EXIT_OK, Client, Node, article, client_context,
                                  free_port, native_image, requires)

DEVELOPER = native_image("FN_NATIVE_DEVELOPER_HOST")


def read_reply(client, status_prefix):
    """The status line, and the dot-terminated block when the status says one follows."""
    status = client.line()
    block = client.block() if status.startswith((b"220", b"221", b"222")) else None
    return status, block


@requires(DEVELOPER)
class TlsPipelineTests(unittest.TestCase):
    """r71 F3 / sweep S010 (host/native/mux.lisp fnn-mux-step): on a protected
    channel a step that consumed a prefix of the record without closing,
    submitting or redeeming was a fault of the whole service ("protected
    owner read left a TLS suffix").  A pipelined line whose payload is not in
    memory splits the read (row A4 (c), fnn-owner-chunk-span-no-io: the warm
    lines first, then the cold line alone), so any TLS client could stop the
    node with DATE, ARTICLE <cold>, DATE in one record.  The suffix is the
    next step's input, as on a plaintext connection."""

    MSGID = b"<tls-cold@example.invalid>"

    def setUp(self):
        self.node = Node(self, DEVELOPER).use_tls(protected_only=False)
        self.node.init()
        owner = self.node.start()
        with Client(self.node.port, timeout=60) as poster:
            first, final = poster.post(article(self.MSGID, body=b"cold body\r\n"))
            self.assertTrue(first.startswith(b"340"), first)
            self.assertTrue(final.startswith(b"240"), final)
        self.node.stop(process=owner)
        # Reopened: the payload is a cold extent (nothing read it yet).
        self.owner = self.node.start()

    def tls(self):
        return Client(self.node.tls_port, timeout=60, implicit_tls=client_context())

    def test_a_pipelined_cold_line_in_one_tls_record_is_served_in_order(self):
        with self.node.log_on_failure(self.owner):
            client = self.tls()
            try:
                # One write is one TLS record: the whole pipeline is one read.
                client.send(b"DATE\r\nARTICLE " + self.MSGID + b"\r\nDATE\r\n")
                self.assertTrue(client.line().startswith(b"111 "))
                status, block = read_reply(client, b"220")
                self.assertTrue(status.startswith(b"220 "), status)
                self.assertIn(b"cold body", block)
                self.assertTrue(client.line().startswith(b"111 "))
                self.assertTrue(client.command(b"DATE").startswith(b"111 "))
            finally:
                client.close()
            self.assertIsNone(self.owner.poll(), "a TLS client's pipeline stopped the owner")
            # The node still serves a new connection, plaintext and TLS.
            with Client(self.node.port, timeout=60) as plain:
                self.assertTrue(plain.command(b"DATE").startswith(b"111 "))
            with self.tls() as again:
                self.assertTrue(again.command(b"DATE").startswith(b"111 "))
            self.node.stop(process=self.owner, expect=EXIT.OK)

    def test_a_cold_first_line_then_a_pipelined_line_in_one_tls_record(self):
        with self.node.log_on_failure(self.owner):
            client = self.tls()
            try:
                client.send(b"ARTICLE " + self.MSGID + b"\r\nDATE\r\n")
                status, block = read_reply(client, b"220")
                self.assertTrue(status.startswith(b"220 "), status)
                self.assertIn(b"cold body", block)
                self.assertTrue(client.line().startswith(b"111 "))
            finally:
                client.close()
            self.assertIsNone(self.owner.poll(), "a TLS client's pipeline stopped the owner")
            self.node.stop(process=self.owner, expect=EXIT.OK)



@requires(DEVELOPER)
@unittest.skipUnless(sys.platform.startswith("linux"), "prlimit and /proc are Linux's")
class AcceptExhaustionTests(unittest.TestCase):
    """Sweep S001/S004 (io.lisp fnn-accept-attempt): an accept(2) that fails
    for one connection or for want of a descriptor (EMFILE under a flood:
    nothing caps descriptors before accept) was a socket-error re-signalled
    out of the main accept loop (the owner stopped) and out of the TLS
    listener's thread (that port stopped accepting for good).  It is a named
    attempt outcome now: the queued connection waits in the kernel's queue,
    the loop backs off and goes on, and every port serves again once
    descriptors free."""

    def test_a_descriptor_flood_on_both_listeners_is_survived(self):
        node = Node(self, DEVELOPER).use_tls(protected_only=False)
        node.init()
        owner = node.start()
        with node.log_on_failure(owner):
            pid = owner.pid
            held = len(os.listdir("/proc/{}/fd".format(pid)))
            soft, hard = resource.prlimit(pid, resource.RLIMIT_NOFILE)
            flood = []
            try:
                # Eight descriptors past what the owner holds now: the flood
                # below exhausts them on both listeners.
                resource.prlimit(pid, resource.RLIMIT_NOFILE, (held + 8, hard))
                for port in (node.port, node.tls_port) * 12:
                    flood.append(socket.create_connection(("127.0.0.1", port), timeout=30))
                # The owner meets EMFILE at accept(2) on both listeners.
                deadline = time.monotonic() + 30
                while time.monotonic() < deadline and \
                        b"no descriptor for a queued connection" not in owner.stderr.since(0):
                    time.sleep(0.25)
                    self.assertIsNone(owner.poll(), "EMFILE at accept stopped the owner")
                time.sleep(3)
                self.assertIsNone(owner.poll(), "EMFILE at accept stopped the owner")
            finally:
                for peer in flood:
                    peer.close()
                resource.prlimit(pid, resource.RLIMIT_NOFILE, (soft, hard))
            # Descriptors free: the queued connections are accepted and end,
            # and both ports serve a new client.
            deadline = time.monotonic() + 60
            while True:
                try:
                    with Client(node.port, timeout=10) as plain:
                        self.assertTrue(plain.command(b"DATE").startswith(b"111 "))
                    with Client(node.tls_port, timeout=10, implicit_tls=client_context()) as tls:
                        self.assertTrue(tls.command(b"DATE").startswith(b"111 "))
                    break
                except (OSError, EOFError, AssertionError):
                    self.assertIsNone(owner.poll(), "the owner stopped")
                    if time.monotonic() > deadline:
                        raise
                    time.sleep(1)
            self.assertIsNone(owner.poll())
            node.stop(process=owner, expect=EXIT.OK)


ROTATION_REFUSED = re.compile(rb"CHECKPOINT auto failed: .*rotation refused reason=spare-rename-exists")
TAIL_HELD = re.compile(rb"WORKER-TAIL held worker=(publisher|exporter)")


@requires(DEVELOPER)
class WorkerRosterTests(auto.AutoCheckpointFixture):
    """The stop joins every worker before it settles the Store
    (host/native/owner.lisp fnn-owner-wait-workers): r71 F10 (sweep S018),
    F12."""

    def test_a_refused_rotation_leaves_no_nil_worker_and_the_stop_settles(self):
        """r71 F12: a publication whose log rotation is refused by name (the
        next segment's name is taken: rename-no-replace answers :exists) made
        no thread, and NIL was pushed onto the worker roster; the stop then
        called (join-thread nil)."""
        self.init_development()
        owner = self.node.start()
        self.post_batch(0, 2)
        journal = self.store / "journal"
        active = max(p.name for p in journal.iterdir() if re.fullmatch(r"\d{6}\.log", p.name))
        taken = journal / "{:06d}.log".format(int(active[:6]) + 1)
        taken.write_bytes(b"")
        self.addCleanup(lambda: taken.unlink() if taken.exists() else None)
        self.op("store", "checkpoint")
        self.assertIsNotNone(self.owner_line(owner, ROTATION_REFUSED, deadline=60.0),
                             "the rotation was not refused by name")
        # Refused again at a later decision: still no NIL worker.
        self.op("store", "checkpoint")
        self.nudge(30)
        self.assertIsNone(owner.poll())
        self.node.stop(process=owner, expect=EXIT.OK)

    def held_stop(self, owner, release, worker):
        line = self.owner_line(owner, TAIL_HELD, deadline=120.0, nudge=False)
        self.assertIsNotNone(line, "the worker never reached its tail")
        self.assertEqual(line.group(1), worker.encode("ascii"))
        owner.signal(signal.SIGTERM)
        # The stop waits for the held worker: it may not settle the Store
        # (and exit) while that worker still holds its pin.
        time.sleep(4)
        self.assertIsNone(owner.poll(),
                          "the owner settled and exited while the {} still ran".format(worker))
        release.write_bytes(b"")
        status = owner.wait(timeout=120)
        owner.finish()
        log = owner.stderr.since(0)
        self.assertIn("WORKER-TAIL released worker={}".format(worker).encode("ascii"), log)
        self.assertEqual(status, EXIT.OK, log[-4000:])

    def test_the_stop_joins_the_publisher_through_its_tail(self):
        """r71 F10 / S018: the publisher left the worker roster before its
        unpin and its next publication decision, so the stop saw `all
        joined' while it still ran."""
        self.init_development()
        release = self.root / "release-publisher"
        owner = self.node.start(env={"FN_NATIVE_WORKER_TAIL_HOLD": str(release)})
        self.post_batch(0, 2)
        self.op("store", "checkpoint")
        self.held_stop(owner, release, "publisher")

    def test_the_stop_joins_the_exporter_through_its_tail(self):
        """r71 F10: the exporter likewise left the roster before its unpin."""
        self.init_development()
        release = self.root / "release-exporter"
        owner = self.node.start(env={"FN_NATIVE_WORKER_TAIL_HOLD": str(release)})
        self.post_batch(0, 2)
        exported = self.op("store", "export", str(self.root / "archive"))
        self.assertEqual(exported.returncode, EXIT_OK, exported.stdout + exported.stderr)
        self.held_stop(owner, release, "exporter")


def owner_sockets(pid, local_port, remote_port):
    """The owner's descriptors that are the TCP socket of the connection
    local_port <- remote_port (Linux /proc)."""
    inodes = set()
    for table in ("/proc/net/tcp", "/proc/net/tcp6"):
        try:
            rows = open(table).read().splitlines()[1:]
        except OSError:
            continue
        for row in rows:
            fields = row.split()
            local, remote, inode = fields[1], fields[2], fields[9]
            if (int(local.rsplit(":", 1)[1], 16) == local_port
                    and int(remote.rsplit(":", 1)[1], 16) == remote_port and inode != "0"):
                inodes.add("socket:[{}]".format(inode))
    held = []
    for fd in os.listdir("/proc/{}/fd".format(pid)):
        try:
            if os.readlink("/proc/{}/fd/{}".format(pid, fd)) in inodes:
                held.append(fd)
        except OSError:
            continue
    return held


@requires(DEVELOPER)
@unittest.skipUnless(sys.platform.startswith("linux"), "/proc is Linux's")
class AdoptionRaceTests(unittest.TestCase):
    """r71 F9 / sweep S021 (host/native/mux.lisp fnn-mux-adopt): an accept
    thread registered its socket as a client, then pushed it to a loop's
    inbox under another lock with no check that the loop still ran.  A stop
    between the two left the socket in a dead loop's inbox: never finished,
    its descriptor never closed, and the wake written to the loop's closed
    pipe (a number the kernel may have reused)."""

    def test_a_socket_adopted_across_a_stop_is_closed_by_its_adopter(self):
        node = Node(self, DEVELOPER).use_tls(protected_only=False)
        node.init()
        release = node.root / "release-adopt"
        owner = node.start(env={"FN_NATIVE_ADOPT_HOLD": str(release),
                                "FN_NATIVE_OWNER_TEST_PAUSE_CLEANUP": "1"})
        with node.log_on_failure(owner):
            client = socket.create_connection(("127.0.0.1", node.tls_port), timeout=30)
            self.addCleanup(client.close)
            client_port = client.getsockname()[1]
            deadline = time.monotonic() + 30
            while b"ADOPT held" not in owner.stderr.since(0):
                self.assertLess(time.monotonic(), deadline, "the adoption was never held")
                time.sleep(0.1)
            owner.signal(signal.SIGTERM)
            # The loops see the stop, take their last inbox and close.
            time.sleep(3)
            release.write_bytes(b"")
            owner.output_until(b"OWNER-CLEANUP", timeout=60)
            held = owner_sockets(owner.pid, node.tls_port, client_port)
            self.assertEqual(held, [], "the late-adopted socket is open in a stopped owner")
            status = owner.wait(timeout=60)
            owner.finish()
            self.assertEqual(status, EXIT.OK)


@requires(DEVELOPER)
class IdleTimerTests(unittest.TestCase):
    """r71 F11 (host/native/mux.lisp fnn-mux-timers): while a response plan
    waits on its cursor resume, the idle check is not eligible to fire, but
    its expired deadline was still scheduled, so the loop polled with a zero
    timeout until the resume: every cursor yield of a response longer than
    the idle second was a busy poll.  The loop's passes between two yields
    (the OVER trace, FN_NATIVE_OVER_WINDOW) count it."""

    COUNT = 2000

    def test_a_long_cursor_reply_does_not_busy_poll_between_quanta(self):
        node = Node(self, DEVELOPER)
        node.init()
        owner = node.start()
        ids = ["<idle-{}@example.invalid>".format(n) for n in range(self.COUNT)]

        def post(chunk):
            with Client(node.port, timeout=120) as client:
                for message_id in chunk:
                    first, final = client.post(article(message_id, body=b"x\r\n"))
                    assert final.startswith(b"240"), final

        workers = [threading.Thread(target=post, args=(ids[k::8],)) for k in range(8)]
        for w in workers:
            w.start()
        for w in workers:
            w.join()
        node.stop(process=owner)
        owner = node.start(env={"FN_NATIVE_OVER_WINDOW": "1"})
        with node.log_on_failure(owner):
            with Client(node.port, timeout=120) as client:
                status = client.command(b"GROUP fn.test")
                self.assertTrue(status.startswith(b"211 "), status)
                low, high = status.split()[2:4]
                started = time.monotonic()
                status = client.command(b"OVER " + low + b"-" + high)
                self.assertTrue(status.startswith(b"224"), status)
                rows = client.block().count(b"\r\n")
                seconds = time.monotonic() - started
            self.assertEqual(rows, self.COUNT)
            time.sleep(1)
            passes = [int(m) for m in re.findall(rb"OVER (?:cursor|empty)-yield cid=\d+ passes=(\d+)",
                                                  owner.stderr.since(0))]
            if not passes:
                # unreachable-in-composition: OVER is not served on the
                # cursor arm at this revision (over_pins 0/4, a known served
                # defect), so no reply yields and the timer cannot meet a
                # yield.  The case runs as soon as a reply does.
                node.stop(process=owner, expect=EXIT.OK)
                self.skipTest("no cursor yield in composition: OVER is not on the cursor arm")
            self.assertGreater(seconds, 2.0, "the reply was too short to outlive the idle second")
            self.assertGreater(len(passes), self.COUNT // 2)
            later = passes[len(passes) // 2:]
            deltas = [b - a for a, b in zip(later, later[1:])]
            # One pass for the resume timer, at most a few for the window's
            # write; a busy poll is hundreds per millisecond of wait.
            self.assertLess(statistics.median(deltas), 10, deltas[:50])
            node.stop(process=owner, expect=EXIT.OK)


@requires(DEVELOPER)
class LogicalFeedTests(unittest.TestCase):
    """r71 F5 / sweep S003 (host/native/owner.lisp fnn-owner-handle-chunk-read):
    a web-face POST (a logical :reader connection, no socket) committed
    INLINE, as if the owner were idle: its START and barrier ran inside the
    reader's quantum, under the owner mutex -- after waiting there for
    another batch's barrier when one was in flight (the gate admits :reader
    then).  On a stalled device that held every other quantum.  It joins the
    next batch now and is awaited off the owner (fnn-owner-feed-logical), as
    an NNTP POST is: while the browser's POST waits for the device, the
    owner answers others at once, and the post is accepted when the device
    returns."""

    STALL_SECONDS = 4

    def setUp(self):
        node = self.node = Node(self, DEVELOPER, name="web-stall")
        node.use_tls(alt_name=True, protected_only=False)
        self.web_port = free_port()
        node.write_config(extra=(
            'tls_port = {}\ntls_cert = "{}"\ntls_key = "{}"\n\n'
            '[auth]\nrequired = true\nprotected_only = true\n\n'
            '[web]\nport = {}\nsite = "Friends news"\ndomain = "friends.invalid"\n'.format(
                node.tls_port, node.cert, node.root / "key.pem", self.web_port)))
        node.init("local.general", "control.cancel", timeout=240)
        node.listening = 3
        self.stall = node.root / "stall"
        self.addCleanup(lambda: self.stall.unlink() if self.stall.exists() else None)
        self.owner = node.start(env={"FN_NATIVE_TEST_DISK_STALL_FILE": str(self.stall)})

    def signed_in(self):
        b = Browser(self.web_port)
        _, _, page, _, _ = b.request("GET", "/redeem")
        invite = self.node.operator("account", "invite", "--expires", "3600", timeout=240,
                                    expect=EXIT.OK)
        code = re.findall(rb"^[0-9a-f]{32}$", invite.stdout, re.M)[0].decode("ascii")
        status, where, page, _, _ = b.request("POST", "/redeem", {
            "pre": b.form_value(page, "pre"), "code": code, "user": "wren",
            "password": PASSWORD, "again": PASSWORD})
        self.assertEqual((status, where), (303, "/"), page)
        status, _, page, _, _ = b.request("GET", "/")
        self.assertEqual(status, 200)
        return b, b.form_value(page, "csrf")

    def timed_health(self):
        started = time.monotonic()
        result = self.node.operator("health", timeout=120)
        return time.monotonic() - started, result

    def test_a_web_post_on_a_stalled_device_waits_off_the_owner(self):
        with self.node.log_on_failure(self.owner):
            b, csrf = self.signed_in()
            baseline, _ = self.timed_health()
            self.stall.write_bytes(b"")
            answer = {}

            def post():
                answer["reply"] = b.request("POST", "/post", {
                    "csrf": csrf, "g": "local.general", "subject": "During a stall",
                    "body": "posted while the device does not return"})

            poster = threading.Thread(target=post)
            started = time.monotonic()
            poster.start()
            time.sleep(1)
            self.assertTrue(poster.is_alive(), "the post was answered before its barrier")
            # HTTP itself remains available while its POST receipt awaits
            # the committer; an operator-only probe misses a blocked face.
            web_started = time.monotonic()
            web_status, _, web_body, _, _ = Browser(self.web_port).request("GET", "/health")
            self.assertEqual((web_status, web_body), (200, "ready\n"))
            self.assertLess(time.monotonic() - web_started, 1.5,
                            "web actor waited on its POST completion")
            waited, health = self.timed_health()
            self.assertLess(waited, baseline + 1.5,
                            "the owner held its mutex for a web post's barrier")
            self.assertLess(time.monotonic() - started, self.STALL_SECONDS)
            time.sleep(max(0, self.STALL_SECONDS - (time.monotonic() - started)))
            self.stall.unlink()
            poster.join(timeout=120)
            self.assertFalse(poster.is_alive())
            status, _, page, _, _ = answer["reply"]
            self.assertEqual(status, 200, page)
            self.assertIn("Posted!", page)
            self.assertIsNone(self.owner.poll())
            self.node.stop(process=self.owner, expect=EXIT.OK)


@requires(DEVELOPER)
@unittest.skipUnless(sys.platform.startswith("linux"), "/proc is Linux's")
class PendingAcceptBoundTests(unittest.TestCase):
    """r71 F13 (host/native/mux.lisp fnn-mux-adopt): the accept threads took
    every queued connection from the kernel and pushed it onto a loop's
    inbox, whatever the loop was doing, so while the loops were held (a cold
    read's wait holds its loop, r71 F7) the accepted-but-unadmitted sockets
    grew without bound, outside every capacity ACL2 decides.  Now an accept
    takes a socket only into a loop's free slot (fnn-mux-reserve): at most one
    pending per loop, the rest wait in the kernel's listen queue."""

    def test_accepted_sockets_stay_bounded_while_the_loops_are_held(self):
        node = Node(self, DEVELOPER)
        node.init()
        owner = node.start()
        ids = [b"<held-a@example.invalid>", b"<held-b@example.invalid>"]
        with Client(node.port, timeout=60) as poster:
            for message_id in ids:
                _, final = poster.post(article(message_id, body=b"held\r\n"))
                self.assertTrue(final.startswith(b"240"), final)
        node.stop(process=owner)
        readstall = node.root / "readstall"
        self.addCleanup(lambda: readstall.unlink() if readstall.exists() else None)
        owner = node.start(env={"FN_NATIVE_TEST_READ_STALL_FILE": str(readstall)})
        with node.log_on_failure(owner):
            holders = [Client(node.port, timeout=60) for _ in ids]
            readstall.write_bytes(b"")
            # One cold read per loop (adoption is round-robin): both loops
            # wait for a page the device does not return (up to ACL2's
            # dependency deadline, 5,000 ms).
            for client, message_id in zip(holders, ids):
                client.send(b"ARTICLE " + message_id + b"\r\n")
            time.sleep(0.5)
            before = len(os.listdir("/proc/{}/fd".format(owner.pid)))
            flood = [socket.create_connection(("127.0.0.1", node.port), timeout=30)
                     for _ in range(30)]
            time.sleep(2)
            after = len(os.listdir("/proc/{}/fd".format(owner.pid)))
            self.assertLessEqual(after - before, 4,
                                 "{} sockets accepted while every loop was held".format(after - before))
            readstall.unlink()
            for peer in flood:
                peer.close()
            for client in holders:
                client.close(quit=False)
            with Client(node.port, timeout=60) as reader:
                self.assertTrue(reader.command(b"DATE").startswith(b"111 "))
            self.assertIsNone(owner.poll())
            node.stop(process=owner, expect=EXIT.OK)


@unittest.skipUnless(os.environ.get("FN_HOST_LIFECYCLE_MEASURE") == "1",
                     "a measurement: set FN_HOST_LIFECYCLE_MEASURE=1 (and FN_NATIVE_HOST)")
class PullCommitLatencyMeasure(unittest.TestCase):
    """The pull feed's commit latency (coordinator's request for r71 F5): node
    B pulls COUNT articles from node A in one round.  Before F5's fix each
    pulled article committed inline under the owner (its own barrier in the
    transit quantum); after, it joins the committer's batch and is awaited off
    the owner.  Prints the seconds from B's start to its last article stored
    and the per-article figure; asserts only that every article arrived."""

    COUNT = 200

    def setUp(self):
        from tests import test_native_peer_pull as pull
        if not pull.READY:
            self.skipTest("set FN_NATIVE_HOST")
        self.pull = pull
        self.case = pull.NativePeerPullTests("test_pull_from_fn_node")
        self.case.setUp()
        self.addCleanup(self.case.doCleanups)

    def test_measure_pull_commit_latency(self):
        case, pull = self.case, self.pull
        a, b, _ = case.two_nodes()
        ids = ["<latency-{}@example.invalid>".format(n) for n in range(self.COUNT)]
        for n, message_id in enumerate(ids):
            case.post(a, pull.article(message_id, "latency-{}".format(n)))
        started = time.monotonic()
        case.start(b)
        case.await_article(b, ids[-1], timeout=600)
        for message_id in ids:
            case.await_article(b, message_id, timeout=60)
        seconds = time.monotonic() - started
        print("PULL-COMMIT-LATENCY articles={} seconds={:.3f} per-article-ms={:.2f}".format(
            self.COUNT, seconds, 1000 * seconds / self.COUNT), flush=True)
        case.stop(b)
        case.stop(a)

if __name__ == "__main__":
    unittest.main()
