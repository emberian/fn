#!/usr/bin/env python3
"""One NNTP connection, driven by hand so every status line is kept.

This is the socket half that `tools/node_probe.py` and `tools/fn_client.py`
share.  It frames CRLF lines, reads multi-line blocks with the dot-stuffing
undone, performs the RFC 4642 STARTTLS upgrade against a supplied context and
sends RFC 4643 AUTHINFO USER/PASS.  It holds no policy: it does not decide
whether a protected channel is required, whether a status line is a refusal,
or whether an absent reply is uncertain.  Those are the caller's, because the
probe asserts the node's policy and the client obeys it, and the two want
different answers from the same octets.

In particular `login` sends the password to whatever answers 381.  A caller
that must not reveal it on an unprotected connection checks `tls` first; that
is what `fn_client` does before it ever calls this.
"""
from __future__ import annotations

import socket
import ssl


class Disconnected(RuntimeError):
    pass


class Session:
    """One NNTP connection, driven by hand so every status line is kept."""

    def __init__(self, host: str, port: int, timeout: float):
        self.host, self.port = host, port
        self.sock = socket.create_connection((host, port), timeout=timeout)
        self.sock.settimeout(timeout)
        self.buf = b""
        self.tls = None
        self.greeting = self.line()

    def line(self) -> str:
        while b"\r\n" not in self.buf:
            chunk = self.sock.recv(4096)
            if not chunk:
                raise Disconnected("the node closed the connection")
            self.buf += chunk
        out, self.buf = self.buf.split(b"\r\n", 1)
        return out.decode("utf-8", "replace")

    def send(self, text: str) -> None:
        self.sock.sendall(text.encode("utf-8") + b"\r\n")

    def block(self) -> list[str]:
        lines = []
        while True:
            one = self.line()
            if one == ".":
                return lines
            lines.append(one[1:] if one.startswith("..") else one)

    def cmd(self, text: str, multiline: bool = False) -> tuple[str, list[str]]:
        self.send(text)
        status = self.line()
        body = self.block() if (multiline and status[:1] in "123") else []
        return status, body

    def starttls(self, context: ssl.SSLContext) -> str:
        status = self.cmd("STARTTLS")[0]
        if not status.startswith("382"):
            return status
        if self.buf:
            # RFC 4642 section 2.2.1: the TLS layer starts with the first
            # octet after the 382's CRLF; anything already buffered is a
            # pipelined leak the node must not have produced.
            raise Disconnected("octets followed the 382 before the handshake")
        self.sock = context.wrap_socket(self.sock, server_hostname=self.host)
        self.tls = {"version": self.sock.version(), "cipher": self.sock.cipher()[0]}
        return status

    def login(self, user: str, password: str) -> str:
        status = self.cmd("AUTHINFO USER " + user)[0]
        if status.startswith("381"):
            status = self.cmd("AUTHINFO PASS " + password)[0]
        return status

    def close(self) -> None:
        try:
            self.cmd("QUIT")
        except (OSError, Disconnected):
            pass
        self.sock.close()
