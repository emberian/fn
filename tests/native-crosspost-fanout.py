#!/usr/bin/env python3
"""Exercise singleton and full seven-group APPEND on the native storage profile."""
import argparse
import importlib.util
import os
from pathlib import Path
import time

SPEC = importlib.util.spec_from_file_location(
    "append_restart", Path(__file__).with_name("native-append-fetch-restart.py"))
fixture = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(fixture)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--directory", type=Path, required=True)
    directory = parser.parse_args().directory.resolve()
    directory.mkdir(parents=True, exist_ok=False)
    groups = ["local.test", *(f"local.g{i}" for i in range(2, 8))]
    image = directory / "node.img"
    control = Path(f"/tmp/fn2-fanout-{os.getpid()}-{time.time_ns()}.sock")
    fixture.initialize(directory, image, startup_args=[
        arg for group in groups for arg in ("--group", group)])
    genesis_names = [g.encode("ascii") for g in groups]
    genesis = fixture.read_genesis(image, genesis_names)
    xrefs = {}
    articles = []

    def run(label, *args):
        return fixture.run_fn(directory, label, *args, "--control-sock", control)

    node = fixture.restart.Node(directory, image, "serve", "write", control_sock=control,
                                env=fixture.environment())
    try:
        node.marker(b"LISTENING-LOCAL ")
        for group in groups:
            grant = run(f"read-{group}", "grant", "set", "anonymous", "read", group)
            assert grant["outcome"] == "accepted", grant
        for op, label, destinations in [(71, "singleton", groups[:1]), (72, "seven-groups", groups)]:
            mid = f"<{label}@example.invalid>".encode("ascii")
            head, whole = fixture.restart.article(mid, 2)
            newsgroups = b"Newsgroups: " + ",".join(destinations).encode("ascii")
            assert head.count(b"Newsgroups: local.test") == whole.count(b"Newsgroups: local.test") == 1
            head[head.index(b"Newsgroups: local.test")] = newsgroups
            whole[whole.index(b"Newsgroups: local.test")] = newsgroups
            path = directory / f"{label}.article"
            path.write_bytes(fixture.restart.wire(whole))
            result = run(label, "stream", "append", "--file", path, "--op", op)
            expected = b"".join(b" " + g.encode("ascii") + b":" +
                                (b"2" if articles and g == groups[0] else b"1") for g in destinations)
            assert result["outcome"] == "accepted" and result["evidence"] == "committed", result
            assert result["message_id"] == mid.decode("ascii") and result["position"] > 2, result
            assert bytes.fromhex(result["numbers"]) == expected, result
            xrefs[mid] = expected
            articles.append((mid, head, whole))
        node.kill()
    finally:
        node.close()

    node = fixture.restart.Node(directory, image, "serve", "reopen", control_sock=control,
                                env=fixture.environment())
    try:
        port = int(node.marker(b"LISTENING ").split()[1])
        node.marker(b"LISTENING-LOCAL ")
        assert fixture.read_genesis(image, genesis_names) == genesis
        for group in groups:
            wire = fixture.restart.read_back(port, articles if group == groups[0] else articles[1:],
                                             group=group, xrefs=xrefs)
            (directory / f"recovered-{group}.wire").write_bytes(wire)
    finally:
        node.close()
    print("NATIVE FANOUT PASS: singleton and seven-group APPEND recovered in every destination")


if __name__ == "__main__":
    main()
