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
    assert item["text"].encode("ascii") == article, item


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--directory", type=Path, required=True)
    args = parser.parse_args()
    directory = args.directory.resolve()
    directory.mkdir(parents=True, exist_ok=False)
    image = directory / "node.img"
    control = Path(f"/tmp/fn2-cursor-{os.getpid()}-{time.time_ns()}.sock")
    principal = "cursor-reader"
    consumer = "inbox1"

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
    fixture.initialize(directory, image)
    node = fixture.restart.Node(directory, image, "serve", "before-ack", control_sock=control,
                                env=fixture.environment())
    try:
        node.marker(b"LISTENING-LOCAL ")
        for actor in (principal, "cursor-other"):
            created = run(f"create-{actor}", "principal", "create", actor)
            assert created["outcome"] == "accepted", created
            grant(f"consume-{actor}", actor, "consume")
        for right in ("append", "read"):
            grant(f"grant-{right}", principal, right, "local.test")

        registered = stream("register", "register", "--consumer", consumer, "--start", "history")
        assert registered["outcome"] == "accepted", registered
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
                        actor="cursor-other", expected=1)
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
        for actor in (principal, "cursor-other"):
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

    print("NATIVE CONSUMER CURSOR RESTART PASS: durable ACK, redelivery, and foreign scope")


if __name__ == "__main__":
    main()
