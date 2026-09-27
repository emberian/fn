#!/usr/bin/env python3
"""Owner-mutex cost of `operator post` and of the feed flush, one image.

    python3 tools/owner_post_measure.py IMAGE [--posts N] [--peer]

Initialises a scratch store (group fn.test), starts `operator run` with
FN_OWNER_MEASURE=1 (host/native/owner.lisp fnn-owner-measured), optionally
adds an outbound feed peer (a sink on 127.0.0.1:9, so every post journals
feed intent and resolution frames), makes N sequential `operator post`
requests, stops the owner with SIGTERM and prints the owner's
`fn-owner-measure` lines with per-post figures:

    label  holds  held-us  max-us  bytes  per-post-bytes  per-post-us

`control` is every owner-mutex hold made inside a control request (the
operator posts, and the one `peer add` when --peer); `feed-flush` is the
flush's own cost, nested inside a hold.  Run it on an otherwise idle box;
SBCL's allocation counter is process-wide.  A measurement, not a test: it
decides nothing and exits non-zero only when the owner or a post fails.
"""
from __future__ import annotations

import argparse
import os
import select
import signal
import socket
import subprocess
import sys
import tempfile
from pathlib import Path


def free_port() -> int:
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


def environment() -> dict:
    env = dict(os.environ)
    env["ACL2_CUSTOMIZATION"] = "NONE"
    for name in ("ACL2_SYSTEM_BOOKS", "FN_HOST", "FN_NATIVE_CONTROL_FAULT",
                 "FN_NATIVE_CONTROL_TEST_STOP"):
        env.pop(name, None)
    return env


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("image")
    parser.add_argument("--posts", type=int, default=50)
    parser.add_argument("--peer", action="store_true")
    args = parser.parse_args()
    image = str(Path(args.image).resolve())
    with tempfile.TemporaryDirectory(prefix="fn-post-measure-") as scratch:
        root = Path(scratch)
        config = root / "fn.toml"
        config.write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
            '[control]\npath = "{}"\n'.format(root / "store", free_port(),
                                               root / "control.sock"),
            encoding="ascii")

        def operator(*words, env=None):
            return subprocess.run([image, "--fn", "operator", str(config), *words],
                                  env=env or environment(), stdout=subprocess.PIPE,
                                  stderr=subprocess.PIPE, timeout=300, check=False)

        init = operator("init", "fn.test")
        if init.returncode != 0:
            sys.stderr.write(init.stderr.decode("utf-8", "replace"))
            return 1
        env = environment()
        env["FN_OWNER_MEASURE"] = "1"
        err_path = root / "owner.err"
        with open(err_path, "wb") as err:
            owner = subprocess.Popen([image, "--fn", "operator", str(config), "run"],
                                     env=env, stdout=subprocess.PIPE, stderr=err)
        try:
            ready = False
            for _ in range(4):
                if not select.select([owner.stdout], [], [], 180)[0]:
                    break
                if owner.stdout.readline().startswith(b"LISTENING "):
                    ready = True
                    break
            if not ready:
                sys.stderr.write("owner did not become ready\n")
                return 1
            if args.peer:
                added = operator("peer", "add", "sink", "sink.example", "127.0.0.1",
                                 "9", "-", "fn.*", "127.0.0.1", "true")
                if added.returncode != 0:
                    sys.stderr.write(added.stderr.decode("utf-8", "replace"))
                    return 1
            for index in range(args.posts):
                message_id = "<measure-{}@example.invalid>".format(index)
                payload = root / "post.eml"
                payload.write_bytes(
                    b"From: author@example.invalid\r\nNewsgroups: fn.test\r\n"
                    b"Subject: measure\r\nDate: Mon, 21 Sep 2026 09:00:00 +0000\r\n"
                    b"Message-ID: " + message_id.encode("ascii") +
                    b"\r\n\r\n" + b"x" * 2000 + b"\r\n")
                posted = operator("post", "--message-id", message_id,
                                  "--payload", str(payload), "--group", "fn.test")
                if posted.returncode != 0:
                    sys.stderr.write("post {} failed: {}\n".format(
                        index, posted.stderr.decode("utf-8", "replace")))
                    return 1
            owner.send_signal(signal.SIGTERM)
            code = owner.wait(timeout=120)
        finally:
            if owner.poll() is None:
                owner.kill()
                owner.wait(timeout=10)
        lines = [line for line in err_path.read_text("utf-8", "replace").splitlines()
                 if line.startswith("fn-owner-measure ")]
        print("owner exit {}; {} posts; peer {}".format(code, args.posts, args.peer))
        for line in lines:
            words = line.split()
            fields = dict(word.split("=", 1) for word in words[2:])
            print("{} {} per-post-bytes={} per-post-us={}".format(
                words[1], " ".join(words[2:]),
                int(fields["bytes"]) // max(args.posts, 1),
                int(fields["held-us"]) // max(args.posts, 1)))
        return 0 if code == 0 and lines else 1


if __name__ == "__main__":
    sys.exit(main())
