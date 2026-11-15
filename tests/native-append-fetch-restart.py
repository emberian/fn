#!/usr/bin/env python3
"""Real owner-local FNCT APPEND, owned process death, fresh-process exact FETCH.

Requires the current qualified node-profile/native-b3-evidence and a named
runtime allocation. This is process-death visibility, not power-loss proof.
"""
import argparse
import importlib.util
import json
import os
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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--directory", type=Path, required=True)
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
    subprocess.run([str(ROOT / "fn"), "init", str(image), "--size-mb", "32", "--group", "local.test"],
                   cwd=ROOT, env=environment(), check=True, timeout=600)
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
        accepted_articles = []
        for index, (mid, article, article_path) in enumerate(submissions):
            accepted = run_fn(directory, f"accepted-{index}", "stream", "append", "--as", principal,
                              "--file", article_path, "--op", str(71 + index), "--control-sock", control)
            assert accepted["outcome"] == "accepted" and accepted["evidence"] == "committed", accepted
            assert accepted["message_id"] == mid and accepted["position"] > 0, accepted
            accepted_articles.append(accepted)
        assert len({(a["domain"], a["position"]) for a in accepted_articles}) == len(submissions)
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
    print("NATIVE APPEND/FETCH RESTART PASS: actual local socket, independent fresh process, two exact 6144-byte articles")


if __name__ == "__main__":
    main()
