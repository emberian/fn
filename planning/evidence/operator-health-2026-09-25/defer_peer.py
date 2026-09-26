#!/usr/bin/env python3
"""A loopback NNTP peer that defers every offer (RFC 3977 6.3.2: 436).

Test tool for the stranded-transfer health case: the node's outbound feed
backs off after each 436 and drops the entry at its retry bound.  It decides
nothing for fn; it only answers."""
import socket
import sys
import threading

def serve(conn):
    f = conn.makefile("rwb")
    f.write(b"200 defer-peer ready\r\n"); f.flush()
    for line in f:
        word = line.split(b" ", 1)[0].strip().upper()
        print(line.rstrip().decode("latin-1"), flush=True)
        if word == b"QUIT":
            f.write(b"205 bye\r\n"); f.flush(); break
        if word == b"IHAVE":
            f.write(b"436 try later\r\n")
        elif word == b"CHECK":
            f.write(b"431 " + line.split(b" ", 1)[1].strip() + b"\r\n")
        elif word == b"MODE":
            f.write(b"203 streaming ok\r\n")
        elif word == b"CAPABILITIES":
            f.write(b"101 capabilities\r\nVERSION 2\r\nIHAVE\r\n.\r\n")
        else:
            f.write(b"500 unknown\r\n")
        f.flush()
    conn.close()

s = socket.socket(); s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
s.bind(("127.0.0.1", int(sys.argv[1]))); s.listen(4)
while True:
    c, _ = s.accept()
    threading.Thread(target=serve, args=(c,), daemon=True).start()
