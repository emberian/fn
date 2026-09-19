"""Process-kill recovery checks for the real BP receiver path.

Each child enters ``receive_bpa_request`` with an ACL2-backed Store.  A
test-only wrapper reports a point only after the named durable predecessor has
returned, then blocks until the parent kills the child process group.  These
are process-death/cache-retention tests, not power-loss evidence.
"""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import select
import signal
import subprocess
import sys
import tempfile
import time
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from tools import run_bp_ingress, run_bp_receive, run_store, workflow_journal


def _pause(ready_fd: int, control_fd: int, point: str) -> None:
    os.write(ready_fd, ("READY {}\n".format(point)).encode("ascii"))
    os.read(control_fd, 1)


def _child_main(args: argparse.Namespace) -> None:
    """Run the actual receiver and stop at one test-only postcondition hook."""
    request = Path(args.request).read_bytes()
    original_stage = run_bp_receive._stage
    original_store = run_bp_receive.run_bp_ingress._publish_accepted
    original_intent = run_bp_receive.ReceiptJournal.prepare_receipt
    original_decision = run_bp_receive.ReceiptJournal.commit_receipt
    original_delete = run_bp_receive._delete_after_decision
    original_receipt = run_bp_receive.ReceiptJournal.receipt_adu

    def hook_fnbi(*values, **keywords):
        result = original_stage(*values, **keywords)
        _pause(args.ready_fd, args.control_fd, args.point)
        return result

    def hook_store(*values, **keywords):
        result = original_store(*values, **keywords)
        _pause(args.ready_fd, args.control_fd, args.point)
        return result

    def hook_intent(*values, **keywords):
        _pause(args.ready_fd, args.control_fd, args.point)
        return original_intent(*values, **keywords)

    def hook_decision(*values, **keywords):
        _pause(args.ready_fd, args.control_fd, args.point)
        return original_decision(*values, **keywords)

    def hook_delete(*values, **keywords):
        _pause(args.ready_fd, args.control_fd, args.point)
        return original_delete(*values, **keywords)

    def capture_receipt(*values, **keywords):
        receipt = original_receipt(*values, **keywords)
        if args.point == "decision":
            Path(args.receipts).parent.joinpath("before-kill.receipt").write_bytes(receipt)
        return receipt

    hooks = {
        "fnbi": (run_bp_receive, "_stage", hook_fnbi),
        "store": (run_bp_receive.run_bp_ingress, "_publish_accepted", hook_store),
        "context": (run_bp_receive.ReceiptJournal, "prepare_receipt", hook_intent),
        "intent": (run_bp_receive.ReceiptJournal, "commit_receipt", hook_decision),
        "decision": (run_bp_receive, "_delete_after_decision", hook_delete),
    }
    target, name, hook = hooks[args.point]
    original_hook = getattr(target, name)
    setattr(target, name, hook)
    run_bp_receive.ReceiptJournal.receipt_adu = capture_receipt
    try:
        run_bp_receive.receive_bpa_request(
            store_root=Path(args.store), inbox_root=Path(args.inbox),
            receipt_root=Path(args.receipts), bid=args.bid,
            source_eid="dtn://sender.lab", inventory=lambda: [args.bid],
            download=lambda bid: request,
            delete=lambda bid: Path(args.deleted_marker).write_text(bid, encoding="ascii"),
        )
    finally:
        setattr(target, name, original_hook)
        run_bp_receive.ReceiptJournal.receipt_adu = original_receipt


class ReceiverProcessCrashTests(unittest.TestCase):
    @staticmethod
    def _article(name: str) -> bytes:
        return (f"Message-ID: <{name}@fn.example>\r\nNewsgroups: fn.letters\r\n\r\n"
                f"body for {name}\r\n").encode("ascii")

    def _request(self, name: str) -> bytes:
        article = self._article(name)
        bridge = run_bp_ingress.Acl2BpIngress()
        try:
            bridge.call('(include-book "books/bp-adu")')
            msgid = bridge.extract_message_id(article)
            _, subject, _ = run_store.metadata(msgid, article)

            def text(value: bytes) -> str:
                return "(fn-store-octets->string '" + bridge.literal(value) + ")"

            fields = [f"work:{name}".encode(), subject, b"dtn://sender.lab",
                      b"dtn://fn.lab/inbox", b"bp-lab-policy-v0", b"origin:1",
                      b"wire-auth", b"terms:1"]
            form = "(fn-bpa-encode (fn-bpa-make-request " + " ".join(
                text(value) for value in fields) + " '" + bridge.literal(article) + "))"
            return run_store.acl2_octets(bridge.call(form))
        finally:
            bridge.close()

    @staticmethod
    def _kill_group(child: subprocess.Popen[bytes]) -> None:
        """Kill the dedicated group, then reap the helper.

        The helper can exit while its ACL2 subprocess still owns the group, so
        the group is always killed, not only when the leader is still live.
        """
        try:
            os.killpg(child.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        except PermissionError:
            child.kill()
        try:
            child.wait(timeout=10)
        except subprocess.TimeoutExpired:
            child.kill()
            child.wait(timeout=10)

    def _kill_at(self, root: Path, request: bytes, point: str, bid: str) -> Path:
        request_path = root / "request.adu"
        request_path.write_bytes(request)
        ready_read, ready_write = os.pipe()
        control_read, control_write = os.pipe()
        marker = root / "bpa-delete-called"
        command = [
            sys.executable, "tests/test_bp_receive_process_crash.py", "--child",
            "--point", point, "--store", str(root / "store"),
            "--inbox", str(root / "inbox"), "--receipts", str(root / "receipts"),
            "--request", str(request_path), "--bid", bid,
            "--deleted-marker", str(marker), "--ready-fd", str(ready_write),
            "--control-fd", str(control_read),
        ]
        child = subprocess.Popen(command, cwd=ROOT, stdin=subprocess.DEVNULL,
                                 stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                 pass_fds=(ready_write, control_read),
                                 start_new_session=True)
        os.close(ready_write)
        os.close(control_read)
        line = b""
        try:
            deadline = time.monotonic() + 45
            while time.monotonic() < deadline:
                ready, _, _ = select.select([ready_read], [], [], 0.1)
                if ready:
                    line = os.read(ready_read, 128)
                    break
                if child.poll() is not None:
                    break
            expected = ("READY {}\n".format(point)).encode("ascii")
            if line != expected:
                self._kill_group(child)
                stderr = child.stderr.read().decode("utf-8", "replace")
                self.fail("child did not reach {}: line={!r} stderr={}".format(
                    point, line, stderr))
        finally:
            self._kill_group(child)
            os.close(ready_read)
            os.close(control_write)
            child.stdout.close()
            child.stderr.close()
        self.assertEqual(child.returncode, -signal.SIGKILL)
        self.assertFalse(marker.exists(), "BPA deletion ran before the kill point")
        return marker

    def _counts(self, store_root: Path, name: str, present=True) -> tuple[int, int, int]:
        store, bridge, records = run_bp_ingress.open_live_bp_store(store_root, False)
        try:
            self.assertEqual(bridge.lookup(f"<{name}@fn.example>".encode("ascii")),
                             self._article(name) if present else b"")
            return len(records), bridge.article_count(), bridge.pin_count()
        finally:
            bridge.close()
            store.close()

    def _retry(self, root: Path, inventory: dict[str, bytes], bid: str,
               *, pending_outcome: str | None = None):
        deleted: list[str] = []

        def delete(found: str) -> None:
            deleted.append(found)
            inventory.pop(found)

        result = run_bp_receive.receive_bpa_request(
            store_root=root / "store", inbox_root=root / "inbox",
            receipt_root=root / "receipts", bid=bid,
            source_eid="dtn://sender.lab", inventory=lambda: list(inventory),
            download=lambda found: inventory[found], delete=delete,
            pending_outcome=pending_outcome,
        )
        return result, deleted

    def test_process_death_at_receiver_durable_boundaries_recovers_once(self) -> None:
        outcomes = {"fnbi": "accepted", "store": "accepted", "context": "duplicate",
                    "intent": "duplicate", "decision": "duplicate"}
        for point, expected in outcomes.items():
            with self.subTest(point=point), tempfile.TemporaryDirectory(
                    prefix="fn-bp-receiver-process-") as temporary:
                root = Path(temporary)
                run_store.Store(root / "store", True).initialize()
                bid = "bid-" + point
                request = self._request(point)
                self._kill_at(root, request, point, bid)

                staged = list((root / "inbox" / "inbound").glob("*.bp"))
                self.assertEqual(len(staged), 1)
                staged_bid, _staged_identity, staged_request = workflow_journal.decode_inbound(
                    staged[0].read_bytes())
                self.assertEqual((staged_bid, staged_request), (bid, request))
                self.assertEqual(self._counts(root / "store", point, point != "fnbi"),
                                 (0, 0, 0) if point == "fnbi" else (1, 1, 1))

                inventory = {bid: request}
                if point == "intent":
                    with self.assertRaises(run_bp_receive.BpReceiveError):
                        self._retry(root, inventory, bid)
                result, deleted = self._retry(
                    root, inventory, bid,
                    pending_outcome="committed" if point == "intent" else None)
                self.assertEqual(result.outcome, expected)
                self.assertEqual(deleted, [bid])
                self.assertEqual(self._counts(root / "store", point), (1, 1, 1))
                if point == "decision":
                    self.assertEqual(result.receipt_adu, (root / "before-kill.receipt").read_bytes())

                # A fresh BPA BID carrying the exact ADU must not charge a
                # second article/pin and must regenerate the committed receipt.
                retry_bid = bid + "-again"
                inventory[retry_bid] = request
                repeated, repeated_delete = self._retry(root, inventory, retry_bid)
                self.assertEqual(repeated.outcome, "duplicate")
                self.assertEqual(repeated_delete, [retry_bid])
                self.assertEqual(repeated.receipt_adu, result.receipt_adu)
                self.assertEqual(self._counts(root / "store", point), (1, 1, 1))


def _parse_child() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--child", action="store_true")
    parser.add_argument("--point")
    parser.add_argument("--store")
    parser.add_argument("--inbox")
    parser.add_argument("--receipts")
    parser.add_argument("--request")
    parser.add_argument("--bid")
    parser.add_argument("--deleted-marker")
    parser.add_argument("--ready-fd", type=int)
    parser.add_argument("--control-fd", type=int)
    return parser.parse_args()


if __name__ == "__main__":
    child_args = _parse_child()
    if child_args.child:
        _child_main(child_args)
    else:
        unittest.main()
