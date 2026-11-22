#!/usr/bin/env python3
"""Default-profile 96 KiB refusal, subsequent acceptance and fresh-process FETCH.

This does NOT establish accepted >64 KiB articles or upload-window recycling.
Run separately from the fast native gates, only with qualified current node
books and a named runtime allocation. The default article limit stays unchanged.
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import time

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("native_append_fetch", ROOT / "tests/native-append-fetch-restart.py")
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)


def large_article(mid, marker):
    """Exact 96 KiB; distinct valid lines across every 4 KiB/64 KiB boundary."""
    assert marker in (b"first", b"other")
    header = (b"From: a@example.invalid\r\nSubject: large refusal\r\n"
              b"Newsgroups: local.test\r\nMessage-ID: " + mid.encode("ascii") + b"\r\n\r\n")
    size = 96 * 1024
    body = bytearray()
    for number in range(2000):
        body.extend(b"." + marker + f" {number:06d} ".encode() + b"0123456789" * 6 + b"\r\n")
    assert len(header) + len(body) > size
    result = (header + body)[:size - 2].rstrip(b"\r\n")
    return result.ljust(size - 2, b"x") + b"\r\n"


def grant_append_fetch(directory, principal, control):
    # FETCH requires consume admission as well as a read grant on the stream.
    for right, scope in (("append", ("local.test",)), ("read", ("local.test",)), ("consume", ())):
        grant = base.run_fn(directory, f"grant-{right}", "grant", "set", principal, right,
                            *scope, "--control-sock", control)
        assert grant["outcome"] == "accepted", grant


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--directory", type=Path, required=True)
    args = parser.parse_args()
    directory = args.directory.resolve()
    directory.mkdir(parents=True, exist_ok=False)
    image = directory / "node.img"
    control = Path(f"/tmp/fn2-large-refusal-{os.getpid()}-{time.time_ns()}.sock")
    principal = "large-refusal-reader"
    base.initialize(directory, image)
    receipts = []
    node = base.restart.Node(directory, image, "serve", "refuse", control_sock=control, env=base.environment())
    mid = "<after-large-refusal@example.invalid>"
    accepted_bytes = base.crossing_article(mid, body_variant=1)
    try:
        node.marker(b"LISTENING-LOCAL ")
        created = base.run_fn(directory, "principal", "principal", "create", principal, "--control-sock", control)
        assert created["outcome"] == "accepted", created
        grant_append_fetch(directory, principal, control)
        for index, marker in enumerate((b"first", b"other")):
            article = large_article(f"<large-refused-{index}@example.invalid>", marker)
            path = directory / f"refused-{index}.article"
            path.write_bytes(article)
            refused = base.run_fn(directory, f"refused-{index}", "stream", "append", "--as", principal,
                                  "--file", path, "--op", str(81 + index), "--control-sock", control, expected=1)
            assert refused["outcome"] == "refused" and refused.get("evidence") != "committed", refused
        path = directory / "accepted.article"
        path.write_bytes(accepted_bytes)
        accepted = base.run_fn(directory, "accepted", "stream", "append", "--as", principal,
                               "--file", path, "--op", "83", "--control-sock", control)
        assert accepted["outcome"] == "accepted" and accepted["evidence"] == "committed", accepted
        assert accepted["message_id"] == mid and accepted["position"] > 0, accepted
        node.kill()  # Both refusals and the subsequent committed reply were received.
        receipts.append(dict(phase="refused-then-accepted", node_pid=node.node_pid,
                             exit=node.proc.returncode, refused_octets=[98304, 98304], accepted_octets=6144))
    finally:
        node.close()
    (directory / "processes.json").write_text(json.dumps(receipts, indent=2) + "\n")
    node = base.restart.Node(directory, image, "serve", "fetch", control_sock=control, env=base.environment())
    try:
        node.marker(b"LISTENING-LOCAL ")
        fetched = base.run_fn(directory, "fetched", "stream", "fetch", mid, "--as", principal,
                             "--domain", accepted["domain"], "--position", accepted["position"],
                             "--control-sock", control)
        (directory / "fetched.article").write_bytes(base.exact_fetch(fetched, accepted_bytes))
        node.kill()
        receipts.append(dict(phase="recovered", node_pid=node.node_pid, exit=node.proc.returncode))
    finally:
        node.close()
    (directory / "processes.json").write_text(json.dumps(receipts, indent=2) + "\n")
    print("NATIVE LARGE REFUSAL PASS: two 96 KiB refusals, subsequent 6144-byte committed article recovered exactly")


if __name__ == "__main__":
    main()
