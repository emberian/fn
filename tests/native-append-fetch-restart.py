#!/usr/bin/env python3
"""Recover FNCT APPENDs through FETCH and NNTP ARTICLE/HEAD after process death.

Requires the current qualified node-profile/native-b3-evidence and a named
runtime allocation. This is process-death visibility, not power-loss proof.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
from contextlib import ExitStack
import importlib.util
import json
import os
import signal
from pathlib import Path
import subprocess
import threading
import time

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("boundaries", ROOT / "tests/native-image-boundaries.py")
boundary = importlib.util.module_from_spec(spec)
spec.loader.exec_module(boundary)
restart = boundary.restart
client_spec = importlib.util.spec_from_file_location("fn_admin", ROOT / "tools/fn_admin.py")
client = importlib.util.module_from_spec(client_spec)
client_spec.loader.exec_module(client)


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
    assert accepted_articles, "STATUS requires a committed APPEND receipt"
    frontier = max(article["position"] for article in accepted_articles)
    assert fields["position"] == registered_position, reply
    assert all(fields["domain"] == article["domain"] for article in accepted_articles), reply
    assert fields["frontier"] == frontier, reply
    assert fields["gap"] == max(0, frontier - registered_position), reply
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


def race_appends(directory, label, control, principal, operation, candidates):
    """Overlap two bound, real FNCT requests without assuming server step order."""
    with ExitStack() as stack:
        sessions = [stack.enter_context(client.ControlSession(str(control), timeout=90))
                    for _ in candidates]
        for session in sessions:
            bound = session.bind_as(principal)
            assert bound and bound["outcome"] == "accepted", bound
        frames = [client.build_cns_request("append", op=operation, article=article)
                  for _, article, _ in candidates]
        # Both requests have entered their sockets before either can complete
        # the frame. This forces wire overlap, not an ACL2 scheduler cut.
        for session, frame in zip(sessions, frames):
            session.sock.sendall(frame[:-32])
        start = threading.Barrier(len(sessions))

        def finish(side, session, frame):
            start.wait(timeout=30)
            session.sock.sendall(frame[-32:])
            reply = client.decode_cns_reply("append", session._recv_frame(mutating=True))
            reply["op"] = operation
            (directory / f"{label}-{side}.stdout").write_text(json.dumps(reply) + "\n")
            return reply

        with ThreadPoolExecutor(max_workers=len(sessions)) as callers:
            futures = [callers.submit(finish, side, session, frame)
                       for side, (session, frame) in enumerate(zip(sessions, frames))]
            return [future.result() for future in futures]


def check_retry_occurrences(directory, phase, control, principal, registered, accepted):
    expected = [(item["message_id"], item["position"]) for item in accepted]
    actual = []
    cursor, position = registered["cursor"], registered["position"]
    # Every continuation must advance. The accepted frontier also bounds a
    # stalled or spurious pagination result even when a page has no items.
    page = 0
    while True:
        reply = run_fn(directory, f"{phase}-items-{page}", "stream", "read", "--as", principal,
                       "--consumer", "inbox1", "--cursor", cursor,
                       "--max-items", 3, "--max-octets", 4096, "--control-sock", control)
        assert reply["outcome"] == "accepted", reply
        actual.extend((item["message_id"], item["position"]) for item in reply["items"])
        assert actual == expected[:len(actual)], (actual, expected, reply)
        if not reply["more"]:
            assert actual == expected, (actual, expected, reply)
            return
        assert cursor != reply["cursor"] and position < reply["next"] <= expected[-1][1], reply
        cursor, position = reply["cursor"], reply["next"]
        page += 1


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



def initialize(directory, image, seconds=600, startup_args=(), env=None):
    """Bound initialization and clean up only this recorded launch session."""
    command = [str(ROOT / "fn"), "init", str(image), "--size-mb", "32", "--group", "local.test", *startup_args]
    with (directory / "init.log").open("wb") as log:
        process = subprocess.Popen(command, cwd=ROOT, env=env if env is not None else environment(), stdout=log,
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
                        help="also require same-key races, changed-request refusal, and replay after revoking append")
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
        reader = run_fn(directory, "grant-nntp-reader", "grant", "set", "anonymous", "read",
                        "local.test", "--control-sock", control)
        assert reader["outcome"] == "accepted", reader
        consume = run_fn(directory, "grant-consume", "grant", "set", principal, "consume",
                         "--control-sock", control)
        assert consume["outcome"] == "accepted", consume
        registered = run_fn(directory, "register", "stream", "register", "--as", principal,
                            "--consumer", "inbox1", "--start", "history", "--control-sock", control)
        assert registered["outcome"] == "accepted", registered
        accepted_articles = []
        for index, submission in enumerate(submissions):
            mid, article, article_path = submission
            operation = 71 + index
            if args.durable_retry and index == 0:
                accepted, other = race_appends(directory, "same-key", control, principal, operation,
                                               [submission, submission])
                assert accepted == other, (accepted, other)
            elif args.durable_retry:
                alternate_mid = "<native-append-fetch-alternate@example.invalid>"
                alternate = crossing_article(alternate_mid)
                alternate_path = directory / "submitted-alternate.article"
                alternate_path.write_bytes(alternate)
                candidates = [submission, (alternate_mid, alternate, alternate_path)]
                replies = race_appends(directory, "different-mid", control, principal, operation, candidates)
                winners = [side for side, reply in enumerate(replies) if reply["outcome"] == "accepted"]
                assert len(winners) == 1, replies
                winner = winners[0]
                accepted, loser = replies[winner], replies[1 - winner]
                assert (loser["outcome"], loser["reason"]) == ("refused", "operation-reused"), replies
                submissions[index] = candidates[winner]
                mid = submissions[index][0]
                losing_submission = candidates[1 - winner]
            else:
                accepted = append_file(directory, f"accepted-{index}", control, principal,
                                       operation, article_path)
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
        cut = "SIGKILL after both committed APPEND receipts"
        if args.durable_retry:
            cut += " and the accepted APPEND revocation"
        receipts.append(dict(phase="accepted", node_pid=node.node_pid, exit=node.proc.returncode,
                             article_octets=[len(article) for _, article, _ in submissions],
                             append_receipts=accepted_articles, cut=cut))
    finally:
        node.close()
    (directory / "processes.json").write_text(json.dumps(receipts, indent=2) + "\n")
    node = restart.Node(directory, image, "serve", "fetch", control_sock=control,
                        env=environment())
    try:
        port = int(node.marker(b"LISTENING ").split()[1])
        node.marker(b"LISTENING-LOCAL ")
        checked_status(
            run_fn(directory, "status-after", "stream", "status", "--as", principal,
                   "--consumer", "inbox1", "--control-sock", control),
            accepted_articles, registered["position"], status_before)
        if args.durable_retry:
            retry_controls(directory, "reopened", control, principal, submissions[0], accepted_articles[0])
            winner = append_file(directory, "reopened-different-mid-winner", control, principal, 72,
                                 submissions[1][2])
            assert winner == accepted_articles[1], (winner, accepted_articles[1])
            loser = append_file(directory, "reopened-different-mid-loser", control, principal, 72,
                                losing_submission[2], expected=1)
            assert (loser["outcome"], loser["reason"]) == ("refused", "operation-reused"), loser
            fresh_path = directory / "reopened-identity.article"
            denied = append_file(directory, "reopened-new-operation", control, principal, 74, fresh_path, expected=1)
            assert (denied["outcome"], denied["reason"]) == ("refused", "refused"), denied
            check_retry_occurrences(directory, "reopened", control, principal, registered, accepted_articles)
            checked_status(run_fn(directory, "status-after-reopened-retries", "stream", "status", "--as",
                                  principal, "--consumer", "inbox1", "--control-sock", control),
                           accepted_articles, registered["position"], status_before)
        for index, ((mid, article, _), accepted) in enumerate(zip(submissions, accepted_articles)):
            # Cross each position with the other real Message-ID, then change
            # only the ID and require this same position to yield its bytes.
            other_mid = submissions[1 - index][0]
            denied = run_fn(directory, f"wrong-mid-{index}", "stream", "fetch", other_mid,
                            "--as", principal, "--domain", accepted["domain"],
                            "--position", accepted["position"], "--control-sock", control, expected=1)
            assert denied == {"outcome": "refused", "reason": "unavailable"}, denied
            fetched = run_fn(directory, f"fetched-{index}", "stream", "fetch", mid, "--as", principal,
                             "--domain", accepted["domain"], "--position", accepted["position"],
                             "--control-sock", control)
            (directory / f"fetched-{index}.article").write_bytes(exact_fetch(fetched, article))
        # Use the original FNCT submissions as the NNTP wire expectations.
        # read_back checks GROUP, ARTICLE and HEAD, including Xref and dot stuffing.
        articles = []
        for mid, article, _ in submissions:
            lines = article.removesuffix(b"\r\n").split(b"\r\n")
            articles.append((mid.encode("ascii"), lines[:lines.index(b"")], lines))
        (directory / "nntp-after.wire").write_bytes(restart.read_back(port, articles))
        # A fresh registration moves the durable tail without adding an addr
        # entry. Keep this write after the restart readbacks so it cannot
        # mask a missing APPEND fence at the first process-death cut.
        later = run_fn(directory, "register-later", "stream", "register", "--as", principal,
                       "--consumer", "inbox2", "--start", "history", "--control-sock", control)
        assert later["outcome"] == "accepted" and later["position"] == 0, later
        checked_status(
            run_fn(directory, "status-after-later", "stream", "status", "--as", principal,
                   "--consumer", "inbox1", "--control-sock", control),
            accepted_articles, registered["position"], status_before)
        node.kill()
        receipts.append(dict(phase="fetched", node_pid=node.node_pid, exit=node.proc.returncode,
                             cut="SIGKILL after exact FETCH, wrong-identity refusal and NNTP readback"))
    finally:
        node.close()
    (directory / "processes.json").write_text(json.dumps(receipts, indent=2) + "\n")
    if args.durable_retry:
        print("NATIVE DURABLE APPEND RETRY PASS: same-key races had one occurrence each; original receipts replayed after restart and revocation")
    print("NATIVE APPEND/FETCH RESTART PASS: two 6144-byte articles recovered by FNCT and NNTP")


if __name__ == "__main__":
    main()
