#!/usr/bin/env python3
"""Real owner-local FNCT APPEND, owned process death, fresh-process exact FETCH.

Requires the current qualified node-profile/native-b3-evidence and a named
runtime allocation. This is process-death visibility, not power-loss proof.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import importlib.util
import json
import os
import signal
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("boundaries", ROOT / "tests/native-image-boundaries.py")
boundary = importlib.util.module_from_spec(spec)
spec.loader.exec_module(boundary)
restart = boundary.restart


def environment():
    """One explicit origin for this isolated image and both fresh processes."""
    env = boundary.environment()
    env.update(FN2_ORIGIN_LINEAGE="711", FN2_ORIGIN_DOMAIN="712",
               FN2_ORIGIN_INCARNATION="1", FN2_HISTORY_ID="713",
               FN2_HISTORY_INCARNATION="1")
    return env


def run_fn(directory, label, *args, expected=0):
    result = subprocess.run([str(ROOT / "fn"), *map(str, args), "--json"], cwd=ROOT,
                            env=environment(), capture_output=True, timeout=90)
    (directory / f"{label}.stdout").write_bytes(result.stdout)
    (directory / f"{label}.stderr").write_bytes(result.stderr)
    assert result.returncode == expected, (label, result.returncode, result.stderr)
    return json.loads(result.stdout)


def exact_fetch(reply, expected):
    assert reply["outcome"] == "accepted", reply
    actual = bytes.fromhex(reply["article_hex"])
    assert reply["octets"] == len(actual) and actual == expected, "FETCH changed article octets"
    return actual


def checked_status(reply, accepted_articles, registered_position, previous=None):
    """Check observed consumer state against actual committed APPEND receipts."""
    assert reply["outcome"] == "accepted", reply
    fields = {key: reply[key] for key in ("domain", "position", "frontier", "gap")}
    assert fields["position"] == registered_position, reply
    assert all(fields["domain"] == article["domain"] and
               fields["frontier"] >= article["position"] for article in accepted_articles), reply
    if previous is not None:
        assert fields == previous, (fields, previous)
    return fields


def append_file(directory, label, control, principal, operation, path, expected=0):
    return run_fn(directory, label, "stream", "append", "--as", principal, "--file", path,
                  "--op", str(operation), "--control-sock", control, expected=expected)


def retry_controls(directory, phase, control, principal, submission, original):
    mid, article, path = submission
    assert append_file(directory, f"{phase}-same", control, principal, 71, path) == original
    # Change body octets alone, then name a different, previously unseen MID.
    for name, changed in (("body", crossing_article(mid, body_variant=1)),
                          ("identity", crossing_article("<retry-other@example.invalid>"))):
        assert changed != article
        candidate = directory / f"{phase}-{name}.article"
        candidate.write_bytes(changed)
        refused = append_file(directory, f"{phase}-{name}", control, principal, 71,
                              candidate, expected=1)
        assert (refused["outcome"], refused["reason"]) == ("refused", "operation-reused"), refused


def check_retry_occurrences(directory, phase, control, principal, registered, accepted):
    reply = run_fn(directory, f"{phase}-items", "stream", "read", "--as", principal,
                   "--consumer", "inbox1", "--cursor", registered["cursor"],
                   "--max-items", 3, "--max-octets", 4096, "--control-sock", control)
    assert reply["outcome"] == "accepted" and not reply["more"], reply
    actual = [(item["message_id"], item["position"]) for item in reply["items"]]
    assert actual == [(item["message_id"], item["position"]) for item in accepted], reply


def crossing_article(mid, body_variant=0):
    """A valid, exact 6 KiB article crossing the transport's 4 KiB window."""
    _, lines = restart.article(mid.encode("ascii"), 100)
    # Vary every body window, not just the Message-ID in the first unit.
    # A reused extent from the other article must change the exact FETCH bytes.
    assert body_variant in (0, 1)
    if body_variant:
        mapping = bytes.maketrans(b"0123456789", b"abcdefghij")
        lines = lines[:5] + [line.translate(mapping) for line in lines[5:]]
    article = restart.wire(lines)
    # Keep the varied body (including a dot-leading line), and shorten only
    # its tail. End on CRLF without adding an NNTP dot terminator to FNCT data.
    assert len(article) >= 6144 and len(restart.wire(lines[:5])) < 6142
    article = article[:6142].rstrip(b"\r\n")
    return article.ljust(6142, b"x") + b"\r\n"



def initialize(directory, image, seconds=600, startup_args=()):
    """Bound initialization and clean up only this recorded launch session."""
    command = [str(ROOT / "fn"), "init", str(image), "--size-mb", "32", "--group", "local.test", *startup_args]
    with (directory / "init.log").open("wb") as log:
        process = subprocess.Popen(command, cwd=ROOT, env=environment(), stdout=log,
                                   stderr=subprocess.STDOUT, start_new_session=True)
        pidfile = directory / "init.launcher.pid"
        pidfile.write_text(f"{process.pid}\n")
        try:
            result = process.wait(timeout=seconds)
        except subprocess.TimeoutExpired:
            # fn init waits for tools/acl2, which waits for the actual runtime.
            # Killing only the direct Python child leaves those descendants.
            assert int(pidfile.read_text()) == process.pid
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            process.wait(timeout=30)
            raise
        if result:
            raise subprocess.CalledProcessError(result, command)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--directory", type=Path, required=True)
    parser.add_argument("--durable-retry", action="store_true",
                        help="also require concurrent same-key acceptance, changed-request refusal, and replay after revoking append")
    args = parser.parse_args()
    directory = args.directory.resolve()
    directory.mkdir(parents=True, exist_ok=False)
    image = directory / "node.img"
    control = Path(f"/tmp/fn2-append-fetch-{os.getpid()}-{time.time_ns()}.sock")
    principal = "crash-reader"
    submissions = []
    for index in range(2):
        mid = f"<native-append-fetch-{index}@example.invalid>"
        article = crossing_article(mid, body_variant=index)
        article_path = directory / f"submitted-{index}.article"
        article_path.write_bytes(article)
        submissions.append((mid, article, article_path))
    initialize(directory, image)
    receipts = []
    node = restart.Node(directory, image, "serve", "append", control_sock=control,
                        env=environment())
    try:
        node.marker(b"LISTENING-LOCAL ")
        created = run_fn(directory, "principal", "principal", "create", principal, "--control-sock", control)
        assert created["outcome"] == "accepted", created
        for right in ("append", "read"):
            grant = run_fn(directory, f"grant-{right}", "grant", "set", principal, right,
                           "local.test", "--control-sock", control)
            assert grant["outcome"] == "accepted", grant
        consume = run_fn(directory, "grant-consume", "grant", "set", principal, "consume",
                         "--control-sock", control)
        assert consume["outcome"] == "accepted", consume
        registered = run_fn(directory, "register", "stream", "register", "--as", principal,
                            "--consumer", "inbox1", "--start", "history", "--control-sock", control)
        assert registered["outcome"] == "accepted", registered
        accepted_articles = []
        for index, (mid, article, article_path) in enumerate(submissions):
            if args.durable_retry and index == 0:
                # Distinct CLI processes and control connections race the same first insert.
                with ThreadPoolExecutor(max_workers=2) as clients:
                    replies = [clients.submit(append_file, directory, f"race-{side}", control,
                                              principal, 71, article_path) for side in range(2)]
                    accepted, other = [reply.result() for reply in replies]
                assert accepted == other, (accepted, other)
            else:
                accepted = append_file(directory, f"accepted-{index}", control, principal,
                                       71 + index, article_path)
            assert accepted["outcome"] == "accepted" and accepted["evidence"] == "committed", accepted
            assert accepted["message_id"] == mid and accepted["position"] > 0, accepted
            accepted_articles.append(accepted)
        assert len({(a["domain"], a["position"]) for a in accepted_articles}) == len(submissions)
        status_before = checked_status(
            run_fn(directory, "status-before", "stream", "status", "--as", principal,
                   "--consumer", "inbox1", "--control-sock", control),
            accepted_articles, registered["position"])
        if args.durable_retry:
            retry_controls(directory, "before-restart", control, principal, submissions[0], accepted_articles[0])
            checked_status(run_fn(directory, "status-after-retries", "stream", "status", "--as", principal,
                                  "--consumer", "inbox1", "--control-sock", control),
                           accepted_articles, registered["position"], status_before)
            check_retry_occurrences(directory, "before-restart", control, principal, registered, accepted_articles)
            revoked = run_fn(directory, "revoke-append", "grant", "set", principal, "append",
                             "local.test", "--revoke", "--control-sock", control)
            assert revoked["outcome"] == "accepted" and not revoked["enabled"], revoked
        # Both actual socket replies have reached this parent before SIGKILL.
        node.kill()
        receipts.append(dict(phase="accepted", node_pid=node.node_pid, exit=node.proc.returncode,
                             article_octets=[len(article) for _, article, _ in submissions],
                             cut="SIGKILL after parent received both accepted committed APPEND replies"))
    finally:
        node.close()
    (directory / "processes.json").write_text(json.dumps(receipts, indent=2) + "\n")
    node = restart.Node(directory, image, "serve", "fetch", control_sock=control,
                        env=environment())
    try:
        node.marker(b"LISTENING-LOCAL ")
        checked_status(
            run_fn(directory, "status-after", "stream", "status", "--as", principal,
                   "--consumer", "inbox1", "--control-sock", control),
            accepted_articles, registered["position"], status_before)
        if args.durable_retry:
            retry_controls(directory, "reopened", control, principal, submissions[0], accepted_articles[0])
            check_retry_occurrences(directory, "reopened", control, principal, registered, accepted_articles)
            fresh_path = directory / "reopened-identity.article"
            denied = append_file(directory, "reopened-new-operation", control, principal, 74, fresh_path, expected=1)
            assert denied["outcome"] == "refused" and denied["reason"] in ("access", "refused"), denied
            checked_status(run_fn(directory, "status-after-reopened-retries", "stream", "status", "--as",
                                  principal, "--consumer", "inbox1", "--control-sock", control),
                           accepted_articles, registered["position"], status_before)
        for index, ((mid, article, _), accepted) in enumerate(zip(submissions, accepted_articles)):
            fetched = run_fn(directory, f"fetched-{index}", "stream", "fetch", mid, "--as", principal,
                             "--domain", accepted["domain"], "--position", accepted["position"],
                             "--control-sock", control)
            (directory / f"fetched-{index}.article").write_bytes(exact_fetch(fetched, article))
        # Same occurrence with a different Message-ID must not disclose bytes.
        # Use the other real committed identity, not merely an unknown name.
        accepted = accepted_articles[1]
        denied = run_fn(directory, "wrong-mid", "stream", "fetch", submissions[0][0],
                        "--as", principal, "--domain", accepted["domain"],
                        "--position", accepted["position"], "--control-sock", control, expected=1)
        assert denied["outcome"] == "refused" and "article_hex" not in denied, denied
        node.kill()
        receipts.append(dict(phase="fetched", node_pid=node.node_pid, exit=node.proc.returncode,
                             cut="SIGKILL after exact FETCH and wrong-identity refusal"))
    finally:
        node.close()
    (directory / "processes.json").write_text(json.dumps(receipts, indent=2) + "\n")
    if args.durable_retry:
        print("NATIVE DURABLE APPEND RETRY PASS: original reply after revocation and fresh process; changed requests refused")
    print("NATIVE APPEND/FETCH RESTART PASS: actual local socket, independent fresh process, two exact 6144-byte articles")


if __name__ == "__main__":
    main()
