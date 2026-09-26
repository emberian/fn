#!/usr/bin/env python3
"""Fake host: an NNTP-shaped server over the fake store, for the gate's tests.

It exists so tests/test_deploy_gate.py drives the real tools/deploy_gate.py
through its whole sequence -- port parsing, the transcript, a reader held live
across another connection's POST, the SIGKILL cut, the restart and the reread
-- with no ACL2 and no ssh.  Its replies are this file's, not ACL2's, and it
is evidence of nothing but the gate's own logic.  The one property it does
copy from tools/run_reader.py is that a connection pins the article list it
saw when it opened.
"""
import argparse
import base64
import json
import os
import socket
import sys
import threading

CRLF = b"\r\n"


def load(root):
    with open(os.path.join(root, "store.json")) as handle:
        return json.load(handle)


class Server:
    greeting = "201 fn-nntp experimental reader ready"

    def __init__(self, root, allow_post):
        self.root = root
        self.allow_post = allow_post
        self.lock = threading.Lock()

    def snapshot(self):
        with self.lock:
            return load(self.root)

    def commit(self, msgid, groups, payload):
        with self.lock:
            state = load(self.root)
            if any(a["msgid"] == msgid for a in state["articles"]):
                return False
            state["articles"].append(
                {"msgid": msgid, "groups": groups,
                 "payload": base64.b64encode(payload).decode()})
            tmp = os.path.join(self.root, "store.json.tmp")
            with open(tmp, "w") as handle:
                json.dump(state, handle)
            os.replace(tmp, os.path.join(self.root, "store.json"))
            return True

    def capabilities(self):
        caps = ["VERSION 2", "READER", "OVER MSGID", "LIST ACTIVE NEWSGROUPS OVERVIEW.FMT"]
        if self.allow_post:
            caps.append("POST")
        return caps


def in_group(state, group):
    return [a for a in state["articles"] if group in a["groups"]]


def article_lines(article):
    body = base64.b64decode(article["payload"])
    return body.replace(b"\r\n", b"\n").rstrip(b"\n").split(b"\n")


def serve(server, sock):
    state = server.snapshot()          # the snapshot this connection pinned
    current = None
    reader = sock.makefile("rb")
    send = lambda text: sock.sendall(text if isinstance(text, bytes) else text.encode())
    send(server.greeting + "\r\n")
    while True:
        line = reader.readline()
        if not line:
            return
        words = line.strip().split()
        if not words:
            send("500 syntax error\r\n")
            continue
        command = words[0].upper()
        if command == b"QUIT":
            send("205 closing\r\n")
            return
        if command == b"CAPABILITIES":
            send("101 capabilities\r\n" + "".join(
                c + "\r\n" for c in server.capabilities()) + ".\r\n")
        elif command == b"LIST":
            body = "".join("{} {} 1 {}\r\n".format(g, len(in_group(state, g)),
                                                   "y" if server.allow_post else "n")
                           for g in state["groups"])
            send("215 list follows\r\n" + body + ".\r\n")
        elif command == b"GROUP" and len(words) == 2:
            group = words[1].decode()
            if group not in state["groups"]:
                send("411 no such group\r\n")
                continue
            current = group
            items = in_group(state, group)
            send("211 {} {} {} {}\r\n".format(len(items), 1 if items else 0,
                                              len(items), group))
        elif command in (b"ARTICLE", b"HEAD", b"OVER") and len(words) == 2:
            selector = words[1].decode()
            items = in_group(state, current) if current else state["articles"]
            found = None
            if selector.startswith("<"):
                found = next((a for a in state["articles"] if a["msgid"] == selector), None)
            elif selector.isdigit() and 1 <= int(selector) <= len(items):
                found = items[int(selector) - 1]
            if found is None:
                send("430 no such article\r\n")
                continue
            lines = article_lines(found)
            if command == b"ARTICLE":
                send("220 1 {} article\r\n".format(found["msgid"]))
            elif command == b"HEAD":
                send("221 1 {} head\r\n".format(found["msgid"]))
                lines = lines[:lines.index(b"")] if b"" in lines else lines
            else:
                send("224 overview\r\n")
                lines = ["1\t{}\t\t\t{}".format(found["msgid"], found["msgid"]).encode()]
            send(b"".join(one + CRLF for one in lines) + b".\r\n")
        elif command == b"POST":
            if not server.allow_post:
                send("440 posting not permitted\r\n")
                continue
            send("340 send it\r\n")
            body = b""
            while not body.endswith(b"\r\n.\r\n"):
                chunk = reader.readline()
                if not chunk:
                    return
                body += chunk
            body = body[: -len(b".\r\n")]
            msgid = None
            groups = []
            for header in body.split(b"\r\n\r\n")[0].split(b"\r\n"):
                if header.lower().startswith(b"message-id:"):
                    msgid = header.split(b":", 1)[1].strip().decode()
                if header.lower().startswith(b"newsgroups:"):
                    groups = [g.strip() for g in
                              header.split(b":", 1)[1].decode().split(",") if g.strip()]
            if msgid is None:
                send("441 no Message-ID\r\n")
                continue
            send("240 article received\r\n" if server.commit(msgid, groups, body)
                 else "441 duplicate\r\n")
        else:
            send("500 unknown command\r\n")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--store", required=True)
    parser.add_argument("--port", type=int, default=0)
    parser.add_argument("--post", action="store_true")
    parser.add_argument("--once", action="store_true")
    args = parser.parse_args()
    server = Server(args.store, args.post)
    listener = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    listener.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    listener.bind(("127.0.0.1", args.port))
    listener.listen(8)
    print("LISTENING {} generation=0".format(listener.getsockname()[1]), flush=True)
    while True:
        client, _ = listener.accept()
        threading.Thread(target=lambda c=client: (serve(server, c), c.close()),
                         daemon=True).start()


if __name__ == "__main__":
    sys.exit(main())
