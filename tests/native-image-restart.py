#!/usr/bin/env python3
"""A real image, fresh SBCL processes, and SIGKILL immediately after POST's 240.

Run after certifying books/node-profile.lisp. Keeps image and logs under build/.
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

ROOT = Path(__file__).resolve().parents[1]


class Node:
    def __init__(self, directory, image, mode, label):
        self.log = (directory / f"{label}.log").open("wb")
        self.pidfile = directory / f"{label}.node.pid"
        self.node_pid = None
        self.pending = b""
        self.proc = subprocess.Popen(
            ["timeout", "600", str(ROOT / "fn"), mode, str(image)], cwd=ROOT,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, start_new_session=True,
        )
        (directory / f"{label}.launcher.pid").write_text(f"{self.proc.pid}\n")
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
        rc = self.proc.wait(timeout=30)
        assert rc != 0, rc

    def close(self):
        if self.proc.poll() is None and self.node_pid:
            try:
                os.kill(self.node_pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            self.proc.wait(timeout=30)
        # Preserve runtime diagnostics emitted after the ready marker.
        # The child is reaped above, so draining this pipe cannot await it.
        self.log.write(self.proc.stdout.read())
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


def read_back(port, articles):
    sock, stream = connect(port)
    try:
        sock.sendall(b"GROUP local.test\r\n")
        assert stream.readline() == b"211 2 1 2 local.test\r\n"
        transcript = bytearray()
        for number, (mid, head, whole) in enumerate(articles, 1):
            xref = f"Xref: fn2.invalid local.test:{number}".encode()
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
    node = Node(directory, image, "init", "init")
    try:
        node.marker(b"INITIALIZED")
        assert node.proc.wait(timeout=30) == 0
    finally:
        node.close()
    articles = []
    for mid, n in ((b"<small@example.invalid>", 100), (b"<big@example.invalid>", 250)):
        head, whole = article(mid, n)
        articles.append((mid, head, whole))
    assert len(wire(articles[0][2])) < 12288 < len(wire(articles[1][2]))
    node = Node(directory, image, "serve", "post")
    try:
        port = int(node.marker(b"LISTENING ").split()[1])
        sock, stream = connect(port)
        try:
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
    previous = None
    for label in ("restart-1", "restart-2"):
        node = Node(directory, image, "serve", label)
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
