#!/usr/bin/env python3
"""A real image, fresh SBCL processes, and SIGKILL immediately after POST's 240.

Run after qualifying current books/node-profile and books/native-b3-evidence.
Keeps image and logs under build/.
The control is exact GROUP, ARTICLE and HEAD wire bytes on two fresh opens,
including dot transparency and an article longer than one payload extent.
"""
import argparse
import os
from pathlib import Path
import selectors
import signal
import socket
import subprocess
import time

from harness.launcher import require_launcher_sigkill

ROOT = Path(__file__).resolve().parents[1]
PAYLOAD_EXTENT_BYTES = 64 * 1024
ARTICLE_MAX = 96 * 1024


class Node:
    def __init__(self, directory, image, mode, label, control_sock=None, env=None, startup_args=()):
        self.log = (directory / f"{label}.log").open("wb")
        self.pidfile = directory / f"{label}.node.pid"
        self.node_pid = None
        self.pending = b""
        cmd = ["timeout", "600", str(ROOT / "fn"), mode, str(image)]
        if control_sock is not None:
            cmd.extend(["--control-sock", str(control_sock)])
        cmd.extend(startup_args)
        self.proc = subprocess.Popen(
            cmd, cwd=ROOT,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, start_new_session=True,
            env=env,
        )
        self.launcher_pidfile = directory / f"{label}.launcher.pid"
        self.launcher_pidfile.write_text(f"{self.proc.pid}\n")
        self.selector = selectors.DefaultSelector()
        self.selector.register(self.proc.stdout, selectors.EVENT_READ)

    def marker(self, prefix, seconds=480):
        deadline = time.monotonic() + seconds
        while time.monotonic() < deadline:
            while b"\n" in self.pending:
                line, self.pending = self.pending.split(b"\n", 1)
                if line.startswith(b"NODE-PID "):
                    self.node_pid = int(line.split()[1])
                    self.pidfile.write_text(f"{self.node_pid}\n")
                if line.startswith(prefix):
                    return line
                if line.startswith(b"REFUSED "):
                    raise AssertionError(line.decode(errors="replace"))
            events = self.selector.select(min(1, max(0, deadline - time.monotonic())))
            if events:
                chunk = os.read(self.proc.stdout.fileno(), 65536)
                if not chunk:
                    break
                self.log.write(chunk)
                self.log.flush()
                self.pending += chunk
        raise AssertionError(f"no {prefix!r}; see {self.log.name}")

    def kill(self):
        # This is the runtime PID printed by this child, persisted before use.
        # The tools/acl2 launcher is a different process.
        assert self.node_pid and int(self.pidfile.read_text()) == self.node_pid
        os.kill(self.node_pid, signal.SIGKILL)
        require_launcher_sigkill(self.proc)

    def close(self):
        if self.proc.poll() is None:
            if self.node_pid:
                try:
                    os.kill(self.node_pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                try:
                    self.proc.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    pass
            if self.proc.poll() is None:
                # Popen created this dedicated session. Before NODE-PID there
                # may still be an ACL2 child holding the output pipe open.
                # Stop only our recorded launcher's group, never by name.
                assert int(self.launcher_pidfile.read_text()) == self.proc.pid
                try:
                    os.killpg(self.proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                self.proc.wait(timeout=10)
        # Preserve bytes already available without letting an inherited writer
        # turn failure cleanup into an unbounded pipe read.
        os.set_blocking(self.proc.stdout.fileno(), False)
        self.log.write(self.proc.stdout.read() or b"")
        self.log.flush()
        self.selector.close()
        self.proc.stdout.close()
        self.log.close()


def article(mid, n):
    head = [b"From: a@example.invalid", b"Subject: hello", b"Newsgroups: local.test",
            b"Message-ID: " + mid]
    body = [(b"." if i == 7 else b"") + f"line {i} ".encode() +
            b"0123456789012345678901234567890123456789012345678901"
            for i in range(n, 0, -1)]
    return head, head + [b""] + body


def wire(lines):
    return b"".join(line + b"\r\n" for line in lines)


def stuffed(lines):
    return [(b"." + line if line.startswith(b".") else line) for line in lines]


def connect(port):
    sock = socket.create_connection(("127.0.0.1", port), timeout=30)
    stream = sock.makefile("rb")
    assert stream.readline() == b"200 fn-nntp experimental server ready\r\n"
    return sock, stream


def multiline(stream):
    lines = []
    while True:
        line = stream.readline()
        assert line, "EOF within multiline reply"
        lines.append(line)
        if line == b".\r\n":
            return b"".join(lines)


def read_back(port, articles, group="local.test", xrefs=None):
    group = group.encode("ascii")
    sock, stream = connect(port)
    try:
        sock.sendall(b"GROUP " + group + b"\r\n")
        count = str(len(articles)).encode()
        expected_group = b"211 " + count + b" 1 " + count + b" " + group + b"\r\n"
        assert stream.readline() == expected_group
        transcript = bytearray()
        for number, (mid, head, whole) in enumerate(articles, 1):
            pairs = xrefs[mid] if xrefs is not None else b" " + group + b":" + str(number).encode()
            assert group + b":" + str(number).encode() in pairs.split(), (group, number, pairs)
            xref = b"Xref: fn2.invalid" + pairs
            for verb, code, suffix, lines in ((b"ARTICLE", b"220", b"article follows", whole),
                                              (b"HEAD", b"221", b"headers follow", head)):
                sock.sendall(verb + f" {number}\r\n".encode())
                status = stream.readline()
                assert status == code + f" {number} ".encode() + mid + b" " + suffix + b"\r\n", status
                actual = multiline(stream)
                expected = wire([xref] + stuffed(lines) + [b"."])
                assert actual == expected, (verb, number, len(actual), len(expected))
                transcript.extend(status + actual)
        return bytes(transcript)
    finally:
        stream.close()
        sock.close()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--directory", type=Path)
    args = parser.parse_args()
    directory = args.directory or ROOT / "build" / f"image-restart-{time.time_ns()}"
    directory.mkdir(parents=True, exist_ok=False)
    image = directory / "node.img"
    env = dict(os.environ, FN2_ARTICLE_MAX=str(ARTICLE_MAX))
    node = Node(directory, image, "init", "init", env=env)
    try:
        node.marker(b"INITIALIZED")
        assert node.proc.wait(timeout=30) == 0
    finally:
        node.close()
    articles = []
    for mid, n in ((b"<small@example.invalid>", 100), (b"<big@example.invalid>", 1100)):
        head, whole = article(mid, n)
        articles.append((mid, head, whole))
    assert len(wire(articles[0][2])) < PAYLOAD_EXTENT_BYTES
    assert PAYLOAD_EXTENT_BYTES < len(wire(articles[1][2])) <= ARTICLE_MAX
    ctl_sock = Path(f"/tmp/fn2-nir-{os.getpid()}-{time.time_ns()}.sock")
    node = Node(directory, image, "serve", "post", control_sock=ctl_sock, env=env)
    try:
        port = int(node.marker(b"LISTENING ").split()[1])
        node.marker(b"LISTENING-LOCAL ")
        sock, stream = connect(port)
        try:
            # Control: before granting anonymous append on local.test, POST is refused.
            sock.sendall(b"POST\r\n")
            assert stream.readline() == b"340 send article to be posted\r\n"
            sock.sendall(wire(stuffed(articles[0][2]) + [b"."]))
            denied = stream.readline()
            assert denied.startswith(b"441 "), denied
            grant_rc = subprocess.call(
                [str(ROOT / "fn"), "grant", "set", "anonymous", "append", "local.test",
                 "--control-sock", str(ctl_sock)],
                cwd=ROOT, timeout=90,
            )
            assert grant_rc == 0, grant_rc
            for mid, _, whole in articles:
                sock.sendall(b"POST\r\n")
                assert stream.readline() == b"340 send article to be posted\r\n"
                sock.sendall(wire(stuffed(whole) + [b"."]))
                reply = stream.readline()
                assert reply == b"240 article received OK\r\n", (mid, reply)
            node.kill()  # no QUIT, drain, or cooperative shutdown after 240
        finally:
            stream.close()
            sock.close()
    finally:
        node.close()
        for p in (ctl_sock, Path(f"{ctl_sock}.groups")):
            if p.exists():
                p.unlink()
    previous = None
    for label in ("restart-1", "restart-2"):
        node = Node(directory, image, "serve", label, env=env)
        try:
            port = int(node.marker(b"LISTENING ").split()[1])
            actual = read_back(port, articles)
            (directory / f"{label}.wire").write_bytes(actual)
            if previous is not None:
                assert actual == previous
            previous = actual
            node.kill()
        finally:
            node.close()
    print(f"NATIVE IMAGE RESTART PASS: SIGKILL after 240; two fresh opens; exact GROUP/ARTICLE/HEAD; {directory}")


if __name__ == "__main__":
    main()
