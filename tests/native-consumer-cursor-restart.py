#!/usr/bin/env python3
"""Exercise public FNCT paging, durable ACK and redelivery across SIGKILL."""
import argparse
from concurrent.futures import ThreadPoolExecutor, TimeoutError
import importlib.util
import json
import os
from pathlib import Path
import time

SPEC = importlib.util.spec_from_file_location(
    "append_restart", Path(__file__).with_name("native-append-fetch-restart.py"))
fixture = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(fixture)


def check_page(page, receipt, article, more):
    assert page["outcome"] == "accepted" and page["count"] == 1, page
    assert page["next"] == receipt["position"] and page["more"] is more, page
    item, = page["items"]
    for key in ("message_id", "domain", "position"):
        assert item[key] == receipt[key], (item, receipt)
    assert item["type"] == "record" and item["octets"] == len(article), item
    assert bytes.fromhex(item["article_hex"]) == article, item


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--directory", type=Path, required=True)
    args = parser.parse_args()
    directory = args.directory.resolve()
    directory.mkdir(parents=True, exist_ok=False)
    image = directory / "node.img"
    control = Path(f"/tmp/fn2-cursor-{os.getpid()}-{time.time_ns()}.sock")
    principal = "cursor-reader"
    consumer = "1"
    other = "cursor-other"

    def run(label, *args, expected=0):
        return fixture.run_fn(directory, label, *args, "--control-sock", control, expected=expected)

    def stream(label, verb, *args, actor=principal, expected=0):
        return run(label, "stream", verb, "--as", actor, *args, expected=expected)

    def grant(label, actor, right, *scope):
        reply = run(label, "grant", "set", actor, right, *scope)
        assert reply["outcome"] == "accepted", reply

    articles = []
    appended = []
    processes = []
    fixture.initialize(directory, image, startup_args=("--group", "local.other"))
    node = fixture.restart.Node(directory, image, "serve", "before-ack", control_sock=control,
                                env=fixture.environment())
    try:
        node.marker(b"LISTENING-LOCAL ")
        for actor in (principal, other):
            created = run(f"create-{actor}", "principal", "create", actor)
            assert created["outcome"] == "accepted", created
            grant(f"consume-{actor}", actor, "consume")
        for right in ("append", "read"):
            grant(f"grant-{right}", principal, right, "local.test")
            grant(f"grant-other-{right}", other, right, "local.other")

        for verb, options in (("status", ()), ("read", ()), ("wait", ()), ("ack", (0,))):
            missing = stream(f"missing-{verb}", verb, *options, "--consumer", consumer, expected=1)
            assert missing == {"outcome": "refused", "reason": "unknown-consumer"}, missing
        registered = stream("register", "register", "--consumer", consumer, "--start", "history")
        assert registered["outcome"] == "accepted", registered
        position = stream("status-registered", "status", "--consumer", consumer)
        assert position["outcome"] == "accepted" and position["position"] == registered["position"], position
        unrelated = stream("other-status-before-register", "status", "--consumer", consumer,
                           actor=other, expected=1)
        assert unrelated == {"outcome": "refused", "reason": "unknown-consumer"}, unrelated
        other_registered = stream("other-register-same-consumer", "register", "--consumer", consumer,
                                  "--start", "history", actor=other)
        assert other_registered["outcome"] == "accepted", other_registered
        assert other_registered["position"] == registered["position"], other_registered
        assert other_registered["cursor"] != registered["cursor"], other_registered
        for index in range(2):
            message_id = f"<native-cursor-{index}@example.invalid>"
            _, lines = fixture.restart.article(message_id.encode("ascii"), 3 + index)
            article = fixture.restart.wire(lines)
            path = directory / f"submitted-{index}.article"
            path.write_bytes(article)
            receipt = stream(f"append-{index}", "append", "--file", path, "--op", 81 + index)
            assert receipt["outcome"] == "accepted" and receipt["evidence"] == "committed", receipt
            assert receipt["message_id"] == message_id, receipt
            articles.append(article)
            appended.append(receipt)
        assert registered["position"] < appended[0]["position"] < appended[1]["position"], appended
        other_status = stream("other-status-after-reader-appends", "status", "--consumer", consumer,
                              actor=other)
        assert other_status["outcome"] == "accepted" and other_status["frontier"] == 0, other_status
        other_empty = stream("other-read-after-reader-appends", "read", "--cursor",
                             other_registered["cursor"], actor=other)
        assert other_empty["outcome"] == "accepted" and other_empty["items"] == [], other_empty
        other_message_id = "<native-cursor-other@example.invalid>"
        _, lines = fixture.restart.article(other_message_id.encode("ascii"), 4)
        other_article = fixture.restart.wire(lines).replace(b"Newsgroups: local.test\r\n",
                                                          b"Newsgroups: local.other\r\n", 1)
        other_path = directory / "submitted-other.article"
        other_path.write_bytes(other_article)
        other_receipt = stream("other-append", "append", "--file", other_path, "--op", 84, actor=other)
        assert other_receipt["outcome"] == "accepted" and other_receipt["evidence"] == "committed", other_receipt
        assert other_receipt["message_id"] == other_message_id, other_receipt
        assert appended[1]["position"] < other_receipt["position"], other_receipt
        other_page = stream("other-read", "read", "--cursor", other_registered["cursor"], actor=other)
        check_page(other_page, other_receipt, other_article, more=False)
        denied_fetch = stream("cross-principal-fetch", "fetch", appended[0]["message_id"],
                              "--domain", appended[0]["domain"], "--position", appended[0]["position"],
                              actor=other, expected=1)
        assert denied_fetch == {"outcome": "refused", "reason": "unavailable"}, denied_fetch
        first = stream("read-first", "read", "--cursor", registered["cursor"], "--max-items", 1)
        check_page(first, appended[0], articles[0], more=True)
        second = stream("read-continuation", "read", "--cursor", first["cursor"], "--max-items", 1)
        check_page(second, appended[1], articles[1], more=False)
        waited = stream("wait-continuation", "wait", "--cursor", first["cursor"], "--seconds", 5)
        assert waited == second, (waited, second)
        empty = stream("wait-at-tail", "wait", "--cursor", second["cursor"], "--seconds", 1)
        assert empty["outcome"] == "accepted" and empty["items"] == [], empty
        assert empty["cursor"] == second["cursor"] and not empty["more"], empty

        before = stream("status-before-ack", "status", "--consumer", consumer)
        assert before["outcome"] == "accepted" and before["position"] == registered["position"], before
        denied = stream("foreign-ack", "ack", first["next"], "--cursor", first["cursor"],
                        actor=other, expected=1)
        assert denied["outcome"] == "refused" and denied["reason"] == "scope", denied
        ahead = stream("ahead-ack", "ack", second["next"] + 1, "--cursor", second["cursor"], expected=1)
        assert ahead["outcome"] == "refused" and ahead["reason"] == "beyond-frontier", ahead
        ack = stream("ack-first", "ack", first["next"], "--cursor", first["cursor"])
        assert ack["outcome"] == "accepted", ack
        assert (ack["domain"], ack["position"]) == (appended[0]["domain"], first["next"]), ack

        node.kill()
        processes.append(dict(phase="accepted-ack", pid=node.node_pid, exit=node.proc.returncode,
                              position=ack["position"], unacknowledged=second["next"]))
    finally:
        node.close()
    report = directory / "processes.json"
    report.write_text(json.dumps(processes, indent=2) + "\n")

    node = fixture.restart.Node(directory, image, "serve", "after-ack", control_sock=control,
                                env=fixture.environment())
    try:
        node.marker(b"LISTENING-LOCAL ")
        assert node.node_pid != processes[0]["pid"], node.node_pid
        status = stream("status-after-restart", "status", "--consumer", consumer)
        assert status["outcome"] == "accepted" and status["domain"] == ack["domain"], status
        assert status["position"] == first["next"] and status["frontier"] == second["next"], status
        assert status["gap"] == second["next"] - first["next"], status
        other_status = stream("other-status-after-restart", "status", "--consumer", consumer, actor=other)
        assert other_status["outcome"] == "accepted", other_status
        assert other_status["position"] == other_registered["position"] < status["position"], other_status
        assert other_status["frontier"] == other_receipt["position"], other_status
        other_redelivery = stream("other-read-from-persisted", "read", "--consumer", consumer, actor=other)
        check_page(other_redelivery, other_receipt, other_article, more=False)
        assert other_redelivery == other_page, (other_redelivery, other_page)

        def check_stale(label, old):
            for verb, extra in (("read", ()), ("wait", ("--seconds", 0)), ("ack", (old["position"],))):
                denied = stream(f"{label}-{verb}", verb, *extra, "--cursor",
                                old["cursor"], actor=other, expected=1)
                assert denied == {"outcome": "refused", "reason": "rebase-required"}, denied
            advance = stream(f"{label}-advancing-ack", "ack", other_receipt["position"],
                             "--cursor", old["cursor"], actor=other, expected=1)
            assert advance == {"outcome": "refused", "reason": "rebase-required"}, advance

        grant("revoke-other-page-read", other, "read", "local.other", "--revoke")
        check_stale("stale-after-revoke", other_registered)
        denied_view = stream("register-view-without-read", "register", "--consumer", "2",
                             "--start", "history", actor=other)
        assert denied_view["outcome"] == "accepted", denied_view
        for verb, extra in (("read", ()), ("wait", ("--seconds", 0))):
            filtered = stream(f"{verb}-new-view-without-read", verb, "--cursor",
                              denied_view["cursor"], "--max-items", 1, *extra, actor=other)
            assert filtered["outcome"] == "accepted" and filtered["items"] == [], filtered
            assert filtered["count"] == 0 and not filtered["more"], filtered
            assert filtered["cursor"] == denied_view["cursor"], filtered
            assert filtered["next"] == denied_view["position"], filtered
        grant("restore-other-page-read", other, "read", "local.other")
        check_stale("stale-after-restore", other_registered)
        check_stale("revoked-view-after-restore", denied_view)
        repeated_registration = stream("register-stale-id-again", "register", "--consumer", consumer,
                                       "--start", "history", actor=other)
        assert repeated_registration == other_registered, repeated_registration
        retained = stream("status-after-stale-ack-proposals", "status", "--consumer", consumer, actor=other)
        assert retained["outcome"] == "accepted" and retained["position"] == other_registered["position"], retained
        restored_view = stream("register-restored-read-view", "register", "--consumer", "3",
                               "--start", "history", actor=other)
        assert restored_view["outcome"] == "accepted", restored_view
        visible = stream("read-with-current-restored-view", "read", "--cursor",
                         restored_view["cursor"], actor=other)
        check_page(visible, other_receipt, other_article, more=False)

        # Omitting --cursor makes the public CLI ask the fresh node for POSITION.
        redelivery = stream("read-from-persisted", "read", "--consumer", consumer, "--max-items", 1)
        check_page(redelivery, appended[1], articles[1], more=False)
        assert redelivery == second, (redelivery, second)
        repeated = stream("repeat-first-ack", "ack", first["next"], "--cursor", first["cursor"])
        assert repeated == ack, (repeated, ack)
        stale = stream("stale-ack", "ack", registered["position"], "--cursor",
                       registered["cursor"], expected=1)
        assert stale["outcome"] == "refused" and stale["reason"] == "behind", stale
        assert stream("status-after-controls", "status", "--consumer", consumer) == status

        message_id = "<native-cursor-wake@example.invalid>"
        _, lines = fixture.restart.article(message_id.encode("ascii"), 5)
        article = fixture.restart.wire(lines)
        path = directory / "submitted-wake.article"
        path.write_bytes(article)
        # This public check observes a pending client and a later item reply.
        # sim-layer-e checks the internal parked phase and linked edge.
        with ThreadPoolExecutor(max_workers=1) as clients:
            waiting = clients.submit(stream, "wait-for-append", "wait", "--cursor",
                                     second["cursor"], "--seconds", 30)
            try:
                early = waiting.result(timeout=0.75)
            except TimeoutError:
                pass
            else:
                raise AssertionError(("WAIT returned before APPEND", early))
            receipt = stream("append-wake", "append", "--file", path, "--op", 83)
            assert receipt["outcome"] == "accepted" and receipt["evidence"] == "committed", receipt
            assert receipt["message_id"] == message_id and receipt["position"] > second["next"], receipt
            woken = waiting.result(timeout=20)
            check_page(woken, receipt, article, more=False)
        occurrence = (other_receipt["message_id"], "--domain", other_receipt["domain"],
                      "--position", other_receipt["position"])
        readable = stream("fetch-with-read-grant", "fetch", *occurrence, actor=other)
        fixture.exact_fetch(readable, other_article)
        grant("revoke-other-read", other, "read", "local.other", "--revoke")
        revoked = stream("fetch-after-read-revocation", "fetch", *occurrence, actor=other, expected=1)
        assert revoked == denied_fetch, (revoked, denied_fetch)
        grant("restore-other-read", other, "read", "local.other")
        restored = stream("fetch-with-restored-read-grant", "fetch", *occurrence, actor=other)
        fixture.exact_fetch(restored, other_article)
        node.kill()
        processes.append(dict(phase="redelivery", pid=node.node_pid, exit=node.proc.returncode,
                              position=status["position"], redelivered=redelivery["next"]))
    finally:
        node.close()
    report.write_text(json.dumps(processes, indent=2) + "\n")

    # A second persisted image with the same credentials and consumer exposes
    # only the physical history difference. Try the exact cursor from image 1.
    foreign_image = directory / "foreign.img"
    foreign_dir = directory / "foreign"
    foreign_dir.mkdir()
    foreign_env = dict(fixture.environment(), FN2_HISTORY_ID="714")
    fixture.initialize(foreign_dir, foreign_image, env=foreign_env)
    node = fixture.restart.Node(foreign_dir, foreign_image, "serve", "foreign", control_sock=control,
                                env=foreign_env)
    try:
        node.marker(b"LISTENING-LOCAL ")
        for actor in (principal, other):
            created = run(f"foreign-create-{actor}", "principal", "create", actor)
            assert created["outcome"] == "accepted", created
            grant(f"foreign-consume-{actor}", actor, "consume")
        foreign_reg = stream("foreign-register", "register", "--consumer", consumer, "--start", "history")
        assert foreign_reg["outcome"] == "accepted", foreign_reg
        assert foreign_reg["position"] == registered["position"], foreign_reg
        before = stream("foreign-status-before", "status", "--consumer", consumer)
        for verb in ("read", "wait", "ack"):
            options = ["--cursor", registered["cursor"]]
            if verb == "ack":
                # Equal in both stores: only scope can cause this ACK refusal.
                options.insert(0, registered["position"])
            denied = stream(f"foreign-history-{verb}", verb, *options, expected=1)
            assert denied["outcome"] == "refused" and denied["reason"] == "scope", denied
        local_page = stream("foreign-local-read", "read", "--cursor", foreign_reg["cursor"])
        assert local_page["outcome"] == "accepted" and local_page["items"] == [], local_page
        assert stream("foreign-status-after", "status", "--consumer", consumer) == before
        node.kill()
    finally:
        node.close()

    print("NATIVE CONSUMER CURSOR RESTART PASS: independent ACK positions, redelivery, and foreign scope")


if __name__ == "__main__":
    main()
