#!/usr/bin/env python3
"""Fake host: the transit half of specs/peering.md 1.1, for the gate's tests.

No book and no host file on this tree serves `IHAVE`, `CHECK` or `TAKETHIS`
yet, so tools/twonode_gate.py's feed scenario would never run its own code
against anything.  This is the stand-in that makes the gate's logic testable:
it puts a line filter in front of `tests/deploy_gate_fake/tools/run_reader.py`
which answers the transit commands and hands every other line through
unchanged, so the reader half is the deploy gate's fake, not a second copy.

Its replies are this file's, not ACL2's.  A green feed scenario against this
server says the gate drives a transit surface correctly; it says nothing
whatever about fn, and the day a real one lands the gate talks to that instead
(the gate detects the surface from the live `IHAVE` reply, never from a file
name).
"""
import argparse
import os
import socket
import sys
import threading

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import run_reader as base            # the deploy gate's fake reader


class PeerServer(base.Server):
    """The base fake reader, advertising the transit commands it now answers."""

    def __init__(self, root, allow_post, path_identity):
        base.Server.__init__(self, root, allow_post)
        self.path_identity = path_identity

    def capabilities(self):
        return base.Server.capabilities(self) + ["IHAVE", "STREAMING"]

    def holds(self, msgid):
        return any(a["msgid"] == msgid for a in base.load(self.root)["articles"])


class Transit:
    """A readline filter: the transit commands never reach the reader loop."""

    def __init__(self, server, sock, reader):
        self.server = server
        self.sock = sock
        self.reader = reader

    def send(self, text):
        self.sock.sendall(text.encode() + b"\r\n")

    def body(self):
        """Collect one article block, dot-unstuffed (RFC 3977 section 3.1.1)."""
        lines = []
        while True:
            one = self.reader.readline()
            if not one:
                return None
            one = one.rstrip(b"\r\n")
            if one == b".":
                return b"\r\n".join(lines) + b"\r\n"
            lines.append(one[1:] if one.startswith(b"..") else one)

    def take(self, msgid):
        """Read the offered article and decide: 235 accepted, 437 refused."""
        body = self.body()
        if body is None:
            return None
        headers = body.split(b"\r\n\r\n")[0]
        path = b""
        groups = []
        for header in headers.split(b"\r\n"):
            if header.lower().startswith(b"path:"):
                path = header.split(b":", 1)[1].strip()
            if header.lower().startswith(b"newsgroups:"):
                groups = [g.strip() for g in
                          header.split(b":", 1)[1].decode().split(",") if g.strip()]
        # RFC 5537 section 3.5: an agent whose own path-identity is already in
        # the Path has relayed this article before and must not take it again.
        if self.server.path_identity.encode() in path:
            return "437 article rejected: my own path-identity is already in Path"
        if not self.server.commit(msgid, groups, body):
            return "437 article rejected: duplicate"
        return "235 article transferred ok"

    def readline(self):
        while True:
            line = self.reader.readline()
            if not line:
                return b""
            words = line.strip().split()
            command = words[0].upper() if words else b""
            argument = words[1].decode() if len(words) > 1 else ""
            if command == b"MODE" and argument.upper() == "STREAM":
                self.send("203 streaming permitted")
            elif command == b"IHAVE":
                if not argument.startswith("<"):
                    self.send("501 command syntax error")
                elif self.server.holds(argument):
                    self.send("435 article not wanted")
                else:
                    self.send("335 send it; end with <CR-LF>.<CR-LF>")
                    reply = self.take(argument)
                    if reply is None:
                        return b""
                    self.send(reply)
            elif command == b"CHECK":
                self.send(("438 {} already have it" if self.server.holds(argument)
                           else "238 {} send it").format(argument))
            elif command == b"TAKETHIS":
                reply = self.take(argument)
                if reply is None:
                    return b""
                self.send("439 {} rejected".format(argument)
                          if reply.startswith("437") else
                          "239 {} transferred ok".format(argument))
            else:
                return line


class Wrapped:
    """The socket the base reader loop is given: its `makefile` is filtered."""

    def __init__(self, sock, server):
        self.sock = sock
        self.server = server

    def makefile(self, *args, **kwargs):
        return Transit(self.server, self.sock, self.sock.makefile(*args, **kwargs))

    def sendall(self, data):
        return self.sock.sendall(data)

    def close(self):
        return self.sock.close()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--store", required=True)
    parser.add_argument("--port", type=int, default=0)
    parser.add_argument("--post", action="store_true")
    parser.add_argument("--path-identity", default="peer.example.invalid")
    args = parser.parse_args()
    server = PeerServer(args.store, args.post, args.path_identity)
    listener = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    listener.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    listener.bind(("127.0.0.1", args.port))
    listener.listen(8)
    print("LISTENING {} generation=0".format(listener.getsockname()[1]), flush=True)
    while True:
        client, _ = listener.accept()
        threading.Thread(
            target=lambda c=client: (base.serve(server, Wrapped(c, server)), c.close()),
            daemon=True).start()


if __name__ == "__main__":
    sys.exit(main())
