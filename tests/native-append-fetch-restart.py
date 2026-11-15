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


def run_fn(directory, label, *args, expected=0):
    result = subprocess.run([str(ROOT / "fn"), *map(str, args), "--json"], cwd=ROOT,
                            env=boundary.environment(), capture_output=True, timeout=90)
    (directory / f"{label}.stdout").write_bytes(result.stdout)
    (directory / f"{label}.stderr").write_bytes(result.stderr)
    assert result.returncode == expected, (label, result.returncode, result.stderr)
    return json.loads(result.stdout)


def exact_fetch(reply, expected):
    assert reply["outcome"] == "accepted", reply
    actual = bytes.fromhex(reply["article_hex"])
    assert reply["octets"] == len(actual) and actual == expected, "FETCH changed article octets"
    return actual


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--directory", type=Path, required=True)
    args = parser.parse_args()
    directory = args.directory.resolve()
    directory.mkdir(parents=True, exist_ok=False)
    image = directory / "node.img"
    control = Path(f"/tmp/fn2-append-fetch-{os.getpid()}-{time.time_ns()}.sock")
    principal = "crash-reader"
    mid = "<native-append-fetch@example.invalid>"
    _, lines = restart.article(mid.encode("ascii"), 100)
    article = restart.wire(lines)
    article_path = directory / "submitted.article"
    article_path.write_bytes(article)
    subprocess.run([str(ROOT / "fn"), "init", str(image), "--size-mb", "32", "--group", "local.test"],
                   cwd=ROOT, env=boundary.environment(), check=True, timeout=600)
    receipts = []
    node = restart.Node(directory, image, "serve", "append", control_sock=control,
                        env=boundary.environment())
    try:
        node.marker(b"LISTENING-LOCAL ")
        created = run_fn(directory, "principal", "principal", "create", principal, "--control-sock", control)
        assert created["outcome"] == "accepted", created
        for right in ("append", "read"):
            grant = run_fn(directory, f"grant-{right}", "grant", "set", principal, right,
                           "local.test", "--control-sock", control)
            assert grant["outcome"] == "accepted", grant
        accepted = run_fn(directory, "accepted", "stream", "append", "--as", principal,
                          "--file", article_path, "--op", "71", "--control-sock", control)
        assert accepted["outcome"] == "accepted" and accepted["evidence"] == "committed", accepted
        assert accepted["message_id"] == mid and accepted["position"] > 0, accepted
        # The actual socket reply has reached this parent before SIGKILL.
        node.kill()
        receipts.append(dict(phase="accepted", node_pid=node.node_pid, exit=node.proc.returncode,
                             cut="SIGKILL after parent received accepted committed APPEND reply"))
    finally:
        node.close()
    (directory / "processes.json").write_text(json.dumps(receipts, indent=2) + "\n")
    node = restart.Node(directory, image, "serve", "fetch", control_sock=control,
                        env=boundary.environment())
    try:
        node.marker(b"LISTENING-LOCAL ")
        fetched = run_fn(directory, "fetched", "stream", "fetch", mid, "--as", principal,
                         "--domain", accepted["domain"], "--position", accepted["position"],
                         "--control-sock", control)
        (directory / "fetched.article").write_bytes(exact_fetch(fetched, article))
        # Same occurrence with a different Message-ID must not disclose bytes.
        denied = run_fn(directory, "wrong-mid", "stream", "fetch", "<wrong@example.invalid>",
                        "--as", principal, "--domain", accepted["domain"],
                        "--position", accepted["position"], "--control-sock", control, expected=1)
        assert denied["outcome"] == "refused" and "article_hex" not in denied, denied
        node.kill()
        receipts.append(dict(phase="fetched", node_pid=node.node_pid, exit=node.proc.returncode,
                             cut="SIGKILL after exact FETCH and wrong-identity refusal"))
    finally:
        node.close()
    (directory / "processes.json").write_text(json.dumps(receipts, indent=2) + "\n")
    print("NATIVE APPEND/FETCH RESTART PASS: actual local socket, independent fresh process, exact article bytes")


if __name__ == "__main__":
    main()
