#!/usr/bin/env python3
"""One addressed crosspost under changing group and consume rights."""
import argparse
import importlib.util
import os
from pathlib import Path
import time

SPEC = importlib.util.spec_from_file_location(
    "cursor_restart", Path(__file__).with_name("native-consumer-cursor-restart.py"))
cursor_test = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(cursor_test)
fixture = cursor_test.fixture


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--directory", required=True, type=Path)
    directory = parser.parse_args().directory.resolve()
    directory.mkdir(parents=True, exist_ok=False)
    image = directory / "node.img"
    control = Path(f"/tmp/fn2-membership-{os.getpid()}-{time.time_ns()}.sock")
    principal = "crosspost-reader"
    consumer = "1"
    mid = "<native-membership@example.invalid>"
    first, second = "local.test", "local.other"

    def run(label, *args, expected=0):
        return fixture.run_fn(directory, label, *args, "--control-sock", control, expected=expected)

    def stream(label, verb, *args, expected=0):
        return run(label, "stream", verb, "--as", principal, *args, expected=expected)

    def grant(label, right, *scope):
        reply = run(label, "grant", "set", principal, right, *scope)
        assert reply["outcome"] == "accepted", reply

    fixture.initialize(directory, image, startup_args=("--group", first, "--group", second))
    node = fixture.restart.Node(directory, image, "serve", "membership", control_sock=control,
                                env=fixture.environment())
    try:
        node.marker(b"LISTENING-LOCAL ")
        assert run("principal", "principal", "create", principal)["outcome"] == "accepted"
        grant("consume", "consume")
        grant("append-first", "append", first)
        grant("append-second", "append", second)
        grant("read-second", "read", second)
        view = stream("register", "register", "--consumer", consumer, "--start", "history")

        _, lines = fixture.restart.article(mid.encode("ascii"), 8)
        article = fixture.restart.wire(lines).replace(
            b"Newsgroups: local.test\r\n", b"Newsgroups: local.test,local.other\r\n", 1)
        path = directory / "crosspost.article"
        path.write_bytes(article)
        receipt = stream("append", "append", "--file", path, "--op", 71)
        assert receipt["outcome"] == "accepted" and receipt["evidence"] == "committed", receipt
        assert receipt["message_id"] == mid and receipt["position"] > 0, receipt
        pairs = bytes.fromhex(receipt["numbers"]).split()
        assert pairs == [b"local.test:1", b"local.other:1"], receipt

        occurrence = (mid, "--domain", receipt["domain"], "--position", receipt["position"])

        def check(label, cursor, visible):
            page = stream(f"{label}-read", "read", "--cursor", cursor)
            status = stream(f"{label}-status", "status", "--consumer", consumer)
            assert status["outcome"] == "accepted" and status["position"] == 0, status
            if visible:
                cursor_test.check_page(page, receipt, article, more=False)
                assert status["frontier"] == receipt["position"] and status["gap"] == receipt["position"], status
                fixture.exact_fetch(stream(f"{label}-fetch", "fetch", *occurrence), article)
            else:
                assert page["outcome"] == "accepted" and page["items"] == [], page
                assert page["count"] == 0 and page["next"] == 0 and not page["more"], page
                assert status["frontier"] == status["gap"] == 0, status
                refused = stream(f"{label}-fetch", "fetch", *occurrence, expected=1)
                assert refused == {"outcome": "refused", "reason": "unavailable"}, refused

        def change_view(label, group, *options):
            nonlocal view
            grant(f"{label}-change-read", "read", group, *options)
            stale = stream(f"{label}-stale", "read", "--cursor", view["cursor"], expected=1)
            assert stale == {"outcome": "refused", "reason": "rebase-required"}, stale
            view = stream(f"{label}-rebase", "rebase", "--consumer", consumer, "--start", "history")
            assert view["outcome"] == "accepted" and view["position"] == 0, view

        check("second-only", view["cursor"], True)
        node.kill()
    finally:
        node.close()

    # Reuse the issued cursor before granting read on the primary group.
    # The sole readable membership at this cut is the stored ordinal row.
    node = fixture.restart.Node(directory, image, "serve", "membership-reopen",
                                control_sock=control, env=fixture.environment())
    try:
        node.marker(b"LISTENING-LOCAL ")
        check("reopened-second-only", view["cursor"], True)
        change_view("both", first)
        check("both", view["cursor"], True)
        change_view("first-only", second, "--revoke")
        check("first-only", view["cursor"], True)
        change_view("neither", first, "--revoke")
        check("neither", view["cursor"], False)
        change_view("second-restored", second)
        check("second-restored", view["cursor"], True)
        grant("consume-revoked", "consume", "--revoke")
        denied = stream("fetch-no-consume", "fetch", *occurrence, expected=1)
        assert denied == {"outcome": "refused", "reason": "access"}, denied
        node.kill()
    finally:
        node.close()
    print("NATIVE MULTI-GROUP MEMBERSHIP PASS: one occurrence and coherent PAGE, FETCH and STATUS")


if __name__ == "__main__":
    main()
