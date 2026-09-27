"""An unbuffered socket stream whose write sends every octet.

`sock.makefile("rwb", buffering=0)` returns a `socket.SocketIO` whose
`write` is ONE `send`: on a socket with a timeout (every
`socket.create_connection(..., timeout=T)`) the kernel takes what fits in
its send buffer and `write` returns that count.  A client that ignores the
count sends a prefix of a multi-MiB article, and the server waits for the
rest forever (lane input-loop, 2026-09-27: every large-POST figure taken
with such a client is suspect; planning/evidence/input-loop-2-2026-09-27.md).

`whole_stream(sock)` is the same stream with `write` = `sendall`: it
returns only when every octet is in the kernel, and returns len(data).
Reads are unchanged (unbuffered, so the stream never holds octets the
test has not read).  Test and measurement clients use it instead of
`makefile("rwb", buffering=0)`; tests/test_wire_stream.py checks both the
behaviour and that no client in tools/ or tests/ builds the partial one.
"""

import socket


class WholeStream(socket.SocketIO):
    """`socket.SocketIO` whose `write` sends all of `data` (or raises)."""

    def write(self, data):
        self._checkClosed()
        self._checkWritable()
        with memoryview(data) as view:
            self._sock.sendall(view)
            return view.nbytes


def whole_stream(sock, mode="rwb"):
    """The unbuffered binary stream over SOCK (a socket or SSLSocket)
    whose writes are whole.  Closing it releases the socket as
    `makefile` does."""
    if not set(mode) <= {"r", "w", "b"}:
        raise ValueError("invalid mode %r" % (mode,))
    rawmode = ("r" if "r" in mode or "w" not in mode else "") + ("w" if "w" in mode else "")
    stream = WholeStream(sock, rawmode)
    sock._io_refs += 1
    return stream
