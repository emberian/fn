"""Native outage/restart evidence for the durable BP lifecycle service."""

import shutil
import time
import unittest

from tests.native_harness import (
    EXIT, ROOT, AcceptThenClosePeer, environment, native_image, refused_port, requires, run,
    scratch, start)

# specs/host.md "BP run classes" (books/bp-run-class.lisp, PRF-131): a
# connection lost after it existed is EXIT.INTERRUPTED (connection-local:
# the job stays and is re-offered; no recovery); a connect that never
# produced a socket is EXIT.NOT_CONNECTED; EXIT.UNCERTAIN stays the fence
# (a publication whose outcome is unknown).
LOST, NOT_CONNECTED = EXIT.INTERRUPTED, EXIT.NOT_CONNECTED
IMAGE = native_image("FN_NATIVE_BP_HOST")


def output(process):
    """What PROCESS wrote so far, stdout then stderr, as text."""
    return (process.stdout.since(0) + process.stderr.since(0)).decode("utf-8", "replace")


@requires(IMAGE)
class NativeBpServiceTests(unittest.TestCase):
    image = IMAGE

    def setUp(self):
        self.tmp = scratch(self, "fn-bp-service-")
        self.journal = self.tmp / "journal"
        self.adu = self.tmp / "adu"
        self.adu.write_bytes(b"hello lifecycle")
        # The outage: the peer accepts the connection and closes it before
        # any transfer completes, so every transfer here is :uncertain.
        self.peer = AcceptThenClosePeer()
        self.addCleanup(self.peer.close)

    def invoke(self, *args, env=None):
        return run([self.image, "--fn", "bp-service", *args], env=environment(env),
                        timeout=30, text=True)

    def run_outage(self, adu=None, env=None):
        return self.invoke(
            "run", "127.0.0.1", self.peer.port, adu or self.adu, self.journal,
            "dtn://fn-a/", "dtn://fn-b/", "work-1", "attempt-1", "0",
            env=env,
        )

    def records(self):
        return sorted((self.journal / "lifecycle").glob("*.fnb"))

    def resume(self, env=None):
        return self.invoke("resume", self.journal, "dtn://fn-a/", env=env)

    def test_outage_restart_duplicate_and_conflict(self):
        first = self.run_outage()
        self.assertEqual(first.returncode, LOST, first.stderr)
        self.assertIn("BP queue accepted", first.stdout)
        self.assertIn("BP forwarding retained reason=uncertain", first.stdout)
        self.assertEqual(len(self.records()), 3)  # queued, attempting, requeued
        self.assertGreater(self.peer.accepted, 0, "the outage must follow a connection")

        frontier = (self.journal / "sequence" / "frontier.fnb").read_bytes()
        domain = (self.journal / "clock-domain.fnb").read_bytes()
        resumed = self.resume()
        self.assertEqual(resumed.returncode, LOST, resumed.stderr)
        self.assertIn("BP queue recovered jobs=1", resumed.stdout)
        self.assertEqual(len(self.records()), 5)
        self.assertEqual((self.journal / "clock-domain.fnb").read_bytes(), domain)

        duplicate = self.run_outage()
        self.assertEqual(duplicate.returncode, LOST, duplicate.stderr)
        self.assertIn("status=duplicate", duplicate.stdout)
        self.assertEqual(
            (self.journal / "sequence" / "frontier.fnb").read_bytes(), frontier,
            "an idempotent enqueue must reuse its durable object binding",
        )

        contrary = self.tmp / "contrary"
        contrary.write_bytes(b"contrary bytes")
        conflict = self.run_outage(contrary)
        self.assertEqual(conflict.returncode, LOST, conflict.stderr)
        self.assertIn("BP queue refused reason=enqueue-conflict", conflict.stdout)

    def test_connect_without_socket_is_failed_and_requeued(self):
        # specs/bp-node-machine.md: a connect that never produced a socket
        # reads :failed (no octet left; ACL2 requeues the job); specs/host.md
        # "BP run classes": the run is :not-connected, exit 7.
        reservation, port = refused_port()
        self.addCleanup(reservation.close)
        first = self.invoke(
            "run", "127.0.0.1", port, self.adu, self.journal,
            "dtn://fn-a/", "dtn://fn-b/", "work-1", "attempt-1", "0",
        )
        self.assertEqual(first.returncode, NOT_CONNECTED, first.stderr)
        self.assertIn("BP queue accepted", first.stdout)
        self.assertNotIn("reason=uncertain", first.stdout)
        self.assertEqual(len(self.records()), 3)  # queued, attempting, requeued

        resumed = self.resume()
        self.assertEqual(resumed.returncode, NOT_CONNECTED, resumed.stderr)
        self.assertIn("BP queue recovered jobs=1", resumed.stdout)
        self.assertNotIn("reason=uncertain", resumed.stdout)
        self.assertEqual(self.peer.accepted, 0)

    def test_wall_jump_after_interrupted_contact_retains_anchored_work(self):
        first = self.invoke(
            "run", "127.0.0.1", self.peer.port, self.adu, self.journal,
            "dtn://fn-a/", "dtn://fn-b/", "work-expiry", "attempt-expiry",
            "0", "3600000", "2", "32", "1048576", "0", "0",
        )
        self.assertEqual(first.returncode, LOST, first.stderr)
        self.assertIn("BP queue accepted", first.stdout)
        before = tuple((p.name, p.read_bytes()) for p in self.records())

        resumed = self.invoke(
            "resume", self.journal, "dtn://fn-a/", "3600000", "2", "32",
            "1048576", "3600001", "0",
        )
        self.assertEqual(resumed.returncode, LOST, resumed.stderr)
        self.assertIn("BP queue recovered jobs=1", resumed.stdout)
        self.assertNotIn("release", resumed.stdout.lower())
        self.assertNotIn("status=expired", resumed.stdout)
        after = tuple((p.name, p.read_bytes()) for p in self.records())
        self.assertGreater(len(after), len(before))

    def test_monotonic_age_expires_interrupted_work(self):
        first = self.invoke(
            "run", "127.0.0.1", self.peer.port, self.adu, self.journal,
            "dtn://fn-a/", "dtn://fn-b/", "work-aged", "attempt-aged",
            "0", "1500", "2", "32", "1048576", "0", "0",
        )
        self.assertEqual(first.returncode, LOST, first.stderr)
        self.assertIn("BP queue accepted", first.stdout)
        before = tuple((p.name, p.read_bytes()) for p in self.records())
        time.sleep(1.7)

        resumed = self.invoke(
            "resume", self.journal, "dtn://fn-a/", "1500", "2", "32",
            "1048576", "0", "0",
        )
        self.assertEqual(resumed.returncode, EXIT.OK, resumed.stderr)
        self.assertIn("BP queue recovered jobs=1", resumed.stdout)
        self.assertIn("status=expired", resumed.stdout)
        self.assertNotIn("release", resumed.stdout.lower())
        after = tuple((p.name, p.read_bytes()) for p in self.records())
        self.assertGreater(len(after), len(before))
        self.assertEqual(after[:len(before)], before)

    def test_corrupt_clock_domain_fences_before_replay(self):
        first = self.run_outage()
        self.assertEqual(first.returncode, LOST, first.stderr)
        domain = self.journal / "clock-domain.fnb"
        saved = domain.read_bytes()
        self.assertGreater(len(saved), 36)
        before = tuple((p.name, p.read_bytes()) for p in self.records())
        replacement = saved[:-1] + bytes([saved[-1] ^ 1])
        domain.write_bytes(replacement)

        resumed = self.resume()
        self.assertEqual(resumed.returncode, EXIT.UNCERTAIN, resumed.stderr)
        self.assertIn("clock domain", resumed.stderr.lower())
        self.assertEqual(
            tuple((p.name, p.read_bytes()) for p in self.records()), before,
            "a boot-domain mismatch must fence before replay or clock effects",
        )

    def test_legacy_durable_records_without_clock_domain_fence(self):
        first = self.run_outage()
        self.assertEqual(first.returncode, LOST, first.stderr)
        (self.journal / "clock-domain.fnb").unlink()
        before = tuple((p.name, p.read_bytes()) for p in self.records())

        resumed = self.resume()
        self.assertEqual(resumed.returncode, EXIT.UNCERTAIN, resumed.stderr)
        self.assertIn("clock domain", resumed.stderr.lower())
        self.assertEqual(tuple((p.name, p.read_bytes()) for p in self.records()), before)

    def test_visible_clock_domain_after_barrier_error_recovers_without_work(self):
        injected = {"FN_BP_CLOCK_DOMAIN_TEST_FAIL": "namespace"}
        cut = self.run_outage(env=injected)
        self.assertEqual(cut.returncode, EXIT.UNCERTAIN, cut.stderr)
        self.assertIn("clock domain", cut.stderr.lower())
        domain = self.journal / "clock-domain.fnb"
        visible = domain.read_bytes()
        self.assertGreater(len(visible), 36)
        self.assertEqual(self.records(), [])

        recovered = self.resume()
        self.assertEqual(recovered.returncode, EXIT.OK, recovered.stderr)
        self.assertIn("BP queue recovered jobs=0", recovered.stdout)
        self.assertEqual(domain.read_bytes(), visible)
        self.assertEqual(self.records(), [])

    def test_shared_spool_owner_precedes_lifecycle_mutation(self):
        owner = start(
            [self.image, "--fn", "tcpcl", "listen", "0", "1", self.journal, "dtn://fn-a/",
             "-", "4", "1024", "1048576", "-", "-"], cwd=ROOT, env=environment())
        try:
            line = owner.next_line(60)
            self.assertIn(b"TCPCL LISTENING", line)
            refused = self.run_outage()
            self.assertEqual(refused.returncode, EXIT.REFUSED, refused.stderr)
            self.assertIn("spool is already owned", refused.stderr)
            self.assertFalse((self.journal / "sequence").exists())
            self.assertFalse((self.journal / "lifecycle").exists())
            self.assertIsNone(owner.poll())
        finally:
            owner.kill()
            owner.wait(timeout=10)
            owner.finish()

    def test_visible_final_never_converts_failed_authority_barrier_to_durable(self):
        injected_env = {"FN_IMMUTABLE_PUBLISH_TEST_FAIL": "namespace"}
        cut = self.run_outage(env=injected_env)
        self.assertEqual(cut.returncode, EXIT.UNCERTAIN, cut.stderr)
        self.assertIn("BP queue uncertain reason=persistence", cut.stdout)
        self.assertNotIn("BP queue accepted", cut.stdout)
        self.assertEqual(
            len(self.records()), 1,
            "the uncertain persist must fence before attempting/forwarding records",
        )

        recovered = self.resume()
        self.assertEqual(recovered.returncode, LOST, recovered.stderr)
        self.assertIn("BP queue recovered jobs=1", recovered.stdout)
        self.assertNotIn("restart fenced", recovered.stderr)

    def test_cleanup_barrier_failure_does_not_retract_durable_record(self):
        injected_env = {"FN_IMMUTABLE_PUBLISH_TEST_FAIL": "cleanup"}
        cut = self.run_outage(env=injected_env)
        self.assertEqual(cut.returncode, LOST, cut.stderr)
        self.assertIn("BP queue accepted", cut.stdout)
        self.assertNotIn("BP queue uncertain reason=persistence", cut.stdout)
        self.assertEqual(len(self.records()), 3)

        recovered = self.resume()
        self.assertEqual(recovered.returncode, LOST, recovered.stderr)
        self.assertIn("BP queue recovered jobs=1", recovered.stdout)
        self.assertNotIn("restart fenced", recovered.stderr)

    def test_prelink_publication_failure_is_refused(self):
        injected_env = {"FN_IMMUTABLE_PUBLISH_TEST_FAIL": "stage"}
        refused = self.run_outage(env=injected_env)
        self.assertEqual(refused.returncode, EXIT.REFUSED, refused.stderr)
        self.assertIn("BP queue refused reason=persistence-refused", refused.stdout)
        self.assertNotIn("BP queue uncertain", refused.stdout)
        self.assertEqual(len(self.records()), 0)

    def test_send_core_fault_remains_exit_four(self):
        fault_env = {"FN_BP_SERVICE_TEST_SEND_FAULT": "1"}
        result = self.run_outage(env=fault_env)
        self.assertEqual(result.returncode, EXIT.FAULT, result.stderr)
        self.assertIn("injected send core fault", result.stderr)
        self.assertNotIn("BP forwarding retained reason=uncertain", result.stdout)
        self.assertEqual(
            len(self.records()), 2,
            "a core fault must stop before a requeued transport record",
        )

    def test_recovery_rejects_corrupt_name_gap_and_token_binding(self):
        mutations = ("corrupt-name", "gap", "token-mismatch")
        for mutation in mutations:
            with self.subTest(mutation=mutation):
                shutil.rmtree(self.journal, ignore_errors=True)
                first = self.run_outage()
                self.assertEqual(first.returncode, LOST, first.stderr)
                records = self.records()
                self.assertEqual(len(records), 3)

                if mutation == "corrupt-name":
                    records[1].rename(records[1].with_suffix(".fnB"))
                    expected = "ACL2 rejected lifecycle namespace"
                elif mutation == "gap":
                    records[1].unlink()
                    expected = "ACL2 rejected lifecycle namespace"
                else:
                    records[0].write_bytes(records[1].read_bytes())
                    expected = "do not bind decoded record tokens"

                resumed = self.resume()
                self.assertEqual(resumed.returncode, EXIT.UNCERTAIN, resumed.stderr)
                self.assertIn(expected, resumed.stderr)
                self.assertNotIn("BP queue recovered", resumed.stdout)

    def test_append_uses_recovered_frontier_without_namespace_rescan(self):
        injected_env = {"FN_BP_SERVICE_TEST_FAIL_SECOND_LIFECYCLE_ENUMERATION": "1"}
        first = self.run_outage(env=injected_env)
        self.assertEqual(first.returncode, LOST, first.stderr)
        self.assertIn("BP queue accepted", first.stdout)
        self.assertEqual(len(self.records()), 3)
        self.assertNotIn("enumerated after recovery", first.stderr)

    def test_hidden_stage_is_bounded_recovery_evidence(self):
        first = self.run_outage()
        self.assertEqual(first.returncode, LOST, first.stderr)
        stage = self.journal / "lifecycle" / ".interrupted-stage"
        stage.write_bytes(b"uncommitted evidence")

        resumed = self.resume()
        self.assertEqual(resumed.returncode, LOST, resumed.stderr)
        self.assertIn("BP queue recovered jobs=1", resumed.stdout)
        self.assertTrue(stage.exists(), "recovery must retain hidden stage evidence")

    def test_namespace_bound_is_applied_during_directory_enumeration(self):
        lifecycle = self.journal / "lifecycle"
        lifecycle.mkdir(parents=True)
        # Mixed FNBS admits legacy, received, and delivery-result budgets.
        for number in range(3 * 4096 + 16 + 1):
            (lifecycle / f".stage-{number:04d}").touch()

        resumed = self.resume()
        self.assertEqual(resumed.returncode, EXIT.UNCERTAIN, resumed.stderr)
        self.assertIn("lifecycle namespace exceeds its bound", resumed.stderr)
        self.assertNotIn("BP queue recovered", resumed.stdout)

    def test_transport_uncertain_dominates_refused_article(self):
        malformed = self.tmp / "malformed.bundle"
        malformed.write_bytes(b"not a BPv7 bundle")
        listener = start(
            [self.image, "--fn", "bp", "receive", "0", "1", self.tmp / "bp-journal",
             "dtn://fn-b/", "-", "3600000", "2", "32", "1048576", self.adu,
             "dtn://fn-a/", "-", "0"], cwd=ROOT, env=environment())
        self.addCleanup(listener.stop, 10)
        port = int(listener.announcement(b"BP LISTENING ", timeout=15).rsplit(b" ", 1)[1])
        sender = start(
            [self.image, "--fn", "tcpcl", "send", "127.0.0.1", port, malformed,
             self.tmp / "peer-journal", "dtn://fn-a/", "-", "4", "1024", "1048576", "1",
             "-"], cwd=ROOT, env=environment({"FN_TCPCL_TEST_PAUSE_AFTER_STAGE_DATA": "1"}))
        self.addCleanup(sender.stop, 10)
        deadline = time.time() + 20
        while time.time() < deadline:
            refused = "BP refused xfer=" in output(listener)
            held_ack = "TCPCL TEST STAGE-DATA " in output(sender)
            if refused and held_ack:
                break
            if sender.poll() is not None:
                break
            time.sleep(0.02)
        self.assertIn(
            "BP refused xfer=", output(listener),
            "the mixed-outcome cut requires a reachable refused article",
        )
        self.assertIn(
            "TCPCL TEST STAGE-DATA ", output(sender),
            "the peer must still hold the reply's final ACK",
        )
        listener.wait(timeout=30)
        listener.finish()
        sender.kill()
        sender.wait(timeout=10)

        text = output(listener)
        self.assertIn("BP summary accepted=0 refused=1 uncertain=0", text)
        self.assertIn("TCPCL passive uncertain", text)
        self.assertEqual(listener.returncode, LOST, text)

    def test_v3_contact_is_refused_without_msg_reject(self):
        # REP-016 / PRF-977 (PKT-650): ION's passive-side run sent a whole
        # TCPCLv3 contact header; fn answered its v4 header and SESS_TERM
        # Version mismatch, then parsed the rest of the v3 header as v4
        # messages and sent MSG_REJECT 06 01 00.  RFC 9174 section 4.3:
        # send the header and IMMEDIATELY terminate.
        import socket
        listener = start(
            [self.image, "--fn", "bp", "receive", "0", "1", self.tmp / "bp-journal",
             "dtn://fn-b/", "-", "3600000", "2", "32", "1048576", self.adu,
             "dtn://fn-a/", "-", "0"], cwd=ROOT, env=environment())
        self.addCleanup(listener.stop, 10)
        port = int(listener.announcement(b"BP LISTENING ", timeout=15).rsplit(b" ", 1)[1])
        v3 = b"dtn!\x03\x00" + b"\x00\x0f" + b"\x09" + b"ipn:150.0"
        reply = b""
        with socket.create_connection(("127.0.0.1", port), timeout=10) as conn:
            conn.sendall(v3)
            deadline = time.time() + 10
            while time.time() < deadline:
                chunk = conn.recv(4096)
                if not chunk:
                    break
                reply += chunk
            else:
                self.fail(f"the passive side kept the connection open: {reply!r}")
        # Its own v4 header (CAN_TLS clear), SESS_TERM flags 0 reason 2, EOF.
        self.assertEqual(reply, b"dtn!\x04\x00" + b"\x05\x00\x02", output(listener))
        self.assertNotIn(b"\x06", reply[6:], "no MSG_REJECT after the SESS_TERM")

    def test_inbound_offer_on_the_outbound_session_is_refused_not_spooled(self):
        # Inspection sweep 2026-10-03 S024.  The hop fn contacts offers fn a
        # bundle of its own on fn's outbound session.  That session takes no
        # inbound custody: fn answers XFER_REFUSE No Resources (2, the
        # sender keeps it and retries) and never the final XFER_ACK, writes
        # no spool file into the FNBS journal root, and its own transfer's
        # outcome is still what the hop answered for it.  Before, the offer
        # was ACKed into JOURNAL/bp-service-1.bundle, never admitted, and the
        # next session's xfer 1 renamed over it; and an inbound refusal on
        # an outbound session overwrote that session's outcome.
        peer = OfferingTcpclPeer(b"dtn://fn-b/", b"inbound custody offered")
        self.addCleanup(peer.close)
        result = self.invoke(
            "run", "127.0.0.1", peer.port, self.adu, self.journal,
            "dtn://fn-a/", "dtn://fn-b/", "work-1", "attempt-1", "0")
        peer.thread.join(timeout=30)
        text = result.stdout + result.stderr
        self.assertIsNone(peer.error, text)
        self.assertIn((3, 2, 1), peer.received, "XFER_REFUSE No Resources for xfer 1: " + text)
        self.assertFalse([m for m in peer.received if m[0] == 2 and m[2] == 1 and m[1] & 1],
                         "no final XFER_ACK for the refused offer")
        self.assertTrue(peer.got_bundle, "fn's own transfer reached the hop: " + text)
        self.assertEqual(sorted(p.name for p in self.journal.glob("*.bundle")), [], text)
        self.assertNotIn("status=refused", text)
        self.assertIn("status=sent", text)


class OfferingTcpclPeer:
    """A TCPCLv4 hop (RFC 9174) that, once the session is up, offers fn one
    bundle of its own (xfer 1) and acknowledges fn's transfers whole; it
    records every message fn sends as (type, first field, transfer id)."""

    def __init__(self, node_id, offer):
        import socket
        import threading
        self.node_id, self.offer = node_id, offer
        self.received, self.got_bundle, self.error = [], False, None
        self.server = socket.socket()
        self.server.bind(("127.0.0.1", 0))
        self.server.listen(1)
        self.server.settimeout(30)
        self.port = self.server.getsockname()[1]
        self.thread = threading.Thread(target=self.serve, daemon=True)
        self.thread.start()

    def close(self):
        self.server.close()

    def serve(self):
        try:
            conn, _ = self.server.accept()
            with conn:
                conn.settimeout(20)
                self.talk(conn)
        except Exception as e:  # recorded for the test to report
            self.error = repr(e)

    @staticmethod
    def exact(conn, n):
        data = b""
        while len(data) < n:
            chunk = conn.recv(n - len(data))
            if not chunk:
                raise EOFError("fn closed after %d of %d octets" % (len(data), n))
            data += chunk
        return data

    def talk(self, conn):
        u = lambda b: int.from_bytes(b, "big")
        conn.sendall(b"dtn!\x04\x00")
        self.exact(conn, 6)
        body = (b"\x00\x3c" + (1 << 16).to_bytes(8, "big") + (1 << 20).to_bytes(8, "big")
                + len(self.node_id).to_bytes(2, "big") + self.node_id + b"\x00\x00\x00\x00")
        conn.sendall(b"\x07" + body)
        offered = False
        while True:
            kind = self.exact(conn, 1)[0]
            if kind == 7:  # SESS_INIT
                self.exact(conn, 2 + 8 + 8)
                self.exact(conn, u(self.exact(conn, 2)))
                self.exact(conn, u(self.exact(conn, 4)))
                self.received.append((7, 0, 0))
                if not offered:
                    offered = True
                    conn.sendall(b"\x01\x03" + (1).to_bytes(8, "big") + b"\x00\x00\x00\x00"
                                 + len(self.offer).to_bytes(8, "big") + self.offer)
            elif kind == 1:  # XFER_SEGMENT
                flags = self.exact(conn, 1)[0]
                xfer = u(self.exact(conn, 8))
                if flags & 2:
                    self.exact(conn, u(self.exact(conn, 4)))
                n = u(self.exact(conn, 8))
                self.exact(conn, n)
                self.received.append((1, flags, xfer))
                if flags & 1:
                    self.got_bundle = True
                    conn.sendall(b"\x02" + bytes([flags | 1]) + xfer.to_bytes(8, "big")
                                 + n.to_bytes(8, "big"))
            elif kind == 2:  # XFER_ACK
                flags = self.exact(conn, 1)[0]
                xfer = u(self.exact(conn, 8))
                self.exact(conn, 8)
                self.received.append((2, flags, xfer))
            elif kind == 3:  # XFER_REFUSE
                reason = self.exact(conn, 1)[0]
                self.received.append((3, reason, u(self.exact(conn, 8))))
            elif kind == 4:  # KEEPALIVE
                self.received.append((4, 0, 0))
            elif kind == 5:  # SESS_TERM
                flags, reason = self.exact(conn, 2)
                self.received.append((5, flags, reason))
                if not flags & 1:
                    conn.sendall(b"\x05\x01" + bytes([reason]))
                return
            elif kind == 6:  # MSG_REJECT
                self.received.append((6,) + tuple(self.exact(conn, 2)))
            else:
                raise ValueError("unknown TCPCL message type %d" % kind)


if __name__ == "__main__":
    unittest.main()
