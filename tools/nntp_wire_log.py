#!/usr/bin/env python3
"""A loopback NNTP relay that records every line both ways, for client findings.

    python3 tools/nntp_wire_log.py LISTEN_PORT TARGET_PORT LOG

Lines are logged as `C: ...` (client to node) and `S: ...`; an AUTHINFO PASS
argument is replaced by `[password]`.  Test tool only: loopback, plain NNTP.
"""
import socket
import sys
import threading
import time

listen, target, path = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
lock = threading.Lock()
out = open(path, "a", buffering=1, encoding="utf-8")


def pump(src, dst, tag, conn):
    pending = b""
    try:
        while True:
            chunk = src.recv(65536)
            if not chunk:
                break
            dst.sendall(chunk)
            pending += chunk
            while b"\r\n" in pending:
                line, pending = pending.split(b"\r\n", 1)
                text = line.decode("utf-8", "replace")
                if tag == "C" and text.upper().startswith("AUTHINFO PASS"):
                    text = "AUTHINFO PASS [password]"
                with lock:
                    out.write("%.3f %d %s: %s\n" % (time.time(), conn, tag, text[:300]))
    except OSError:
        pass
    finally:
        try:
            dst.shutdown(socket.SHUT_WR)
        except OSError:
            pass


server = socket.socket()
server.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
server.bind(("127.0.0.1", listen))
server.listen(8)
number = 0
while True:
    client, _ = server.accept()
    number += 1
    upstream = socket.create_connection(("127.0.0.1", target))
    with lock:
        out.write("%.3f %d --- connection\n" % (time.time(), number))
    threading.Thread(target=pump, args=(client, upstream, "C", number), daemon=True).start()
    threading.Thread(target=pump, args=(upstream, client, "S", number), daemon=True).start()
