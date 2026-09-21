#!/usr/bin/env python3
"""A stand-in INN, so tools/inn_lab.py's own logic is testable with no INN.

Every reply here is this file's.  It says nothing about InterNetNews and
nothing about fn: it exists so the lab's sequencing, its port scheme, its
configuration writing, its skip accounting and its evidence rendering are
exercised by tests/test_inn_lab.py on a laptop with no news server, no ssh and
no ACL2.  The real lab talks to the real INN the same way -- by asking a live
socket -- so nothing here is on the path of a real run.

The behaviours it does copy from INN, because the lab asserts them:

* ``IHAVE`` answers ``335`` then ``235``, a second offer of the same
  Message-ID answers ``435`` from a history that survives a restart, and an
  article whose ``Path`` names a site in the ``ME`` entry's exclusion
  sub-field answers ``437`` (innd/art.c's ``ME.Exclusions``).
* ``CHECK`` answers ``238`` for an unknown Message-ID and ``438`` for a known
  one; ``MODE STREAM`` answers ``203``.
* ``innfeed`` opens one connection to the port named in ``innfeed.conf``,
  sends ``MODE STREAM`` and then an offer, and logs whatever comes back.
"""
import json
import os
import re
import signal
import socket
import sys
import threading
import time

CRLF = b"\r\n"


def prefix() -> str:
    """The install root: two directories up from this script's bin/."""
    return os.environ.get("FAKE_INN_PREFIX") or os.path.dirname(
        os.path.dirname(os.path.abspath(__file__)))


def path(*parts) -> str:
    return os.path.join(prefix(), *parts)


def spool() -> dict:
    try:
        with open(path("db", "spool.json")) as handle:
            return json.load(handle)
    except Exception:
        return {"articles": {}, "history": []}


def save(state: dict):
    tmp = path("db", "spool.json.tmp")
    with open(tmp, "w") as handle:
        json.dump(state, handle)
    os.replace(tmp, path("db", "spool.json"))


def exclusions() -> list:
    """The ME entry's exclusion sub-field, as innd reads it."""
    try:
        with open(path("etc", "newsfeeds")) as handle:
            for line in handle:
                if line.startswith("ME/"):
                    return [one for one in
                            line.split(":", 1)[0][len("ME/"):].split(",") if one]
    except Exception:
        pass
    return []


def peer_port() -> int:
    try:
        with open(path("etc", "innfeed.conf")) as handle:
            match = re.search(r"port-number:\s*(\d+)", handle.read())
            return int(match.group(1)) if match else 0
    except Exception:
        return 0


class Session:
    """One NNTP connection, transit side or reader side."""

    def __init__(self, sock, reader: bool):
        self.sock = sock
        self.reader = reader
        self.file = sock.makefile("rb")
        self.lock = threading.Lock()

    def send(self, text):
        self.sock.sendall(text.encode() + CRLF)

    def block(self):
        lines = []
        while True:
            one = self.file.readline()
            if not one:
                return None
            one = one.rstrip(b"\r\n").decode("utf-8", "replace")
            if one == ".":
                return lines
            lines.append(one[1:] if one.startswith("..") else one)

    def run(self):
        self.send("200 inn.fake.test fake InterNetNews ready ({})".format(
            "reader" if self.reader else "transit mode"))
        while True:
            raw = self.file.readline()
            if not raw:
                return
            line = raw.rstrip(b"\r\n").decode("utf-8", "replace")
            word = line.split()[0].upper() if line.split() else ""
            rest = line.split()[1] if len(line.split()) > 1 else ""
            if word == "QUIT":
                self.send("205 goodbye")
                return
            if word == "CAPABILITIES":
                self.send("101 Capability list:")
                for one in (["VERSION 2", "IMPLEMENTATION fake-inn", "READER",
                             "OVER", "LIST ACTIVE"] if self.reader else
                            ["VERSION 2", "IMPLEMENTATION fake-inn", "IHAVE",
                             "STREAMING"]):
                    self.send(one)
                self.send(".")
            elif word == "MODE" and rest.upper() == "STREAM" and not self.reader:
                self.send("203 Streaming permitted")
            elif word == "LIST":
                self.send("215 Newsgroups in form \"group high low flags\"")
                for group in sorted(self.groups()):
                    self.send("{} 0000000001 0000000001 y".format(group))
                self.send(".")
            elif word == "GROUP":
                self.send("211 1 1 1 {}".format(rest) if rest in self.groups()
                          else "411 no such group")
            elif word == "ARTICLE":
                self.article(rest)
            elif word == "IHAVE" and not self.reader:
                self.ihave(rest)
            elif word == "CHECK" and not self.reader:
                state = spool()
                self.send("438 {} Duplicate".format(rest)
                          if rest in state["history"]
                          else "238 {} Send it".format(rest))
            else:
                self.send("500 command not recognized")

    @staticmethod
    def groups():
        try:
            with open(path("db", "active")) as handle:
                return [line.split()[0] for line in handle if line.strip()]
        except Exception:
            return []

    def article(self, msgid):
        state = spool()
        if msgid not in state["articles"]:
            self.send("430 no such article")
            return
        self.send("220 0 {} article".format(msgid))
        for one in state["articles"][msgid]:
            self.send("." + one if one.startswith(".") else one)
        self.send(".")

    def ihave(self, msgid):
        state = spool()
        if msgid in state["history"]:
            self.send("435 Duplicate")
            return
        self.send("335 Send it")
        lines = self.block()
        if lines is None:
            return
        hops = []
        for one in lines:
            if one.lower().startswith("path:"):
                hops = one.split(":", 1)[1].strip().split("!")
            if one == "":
                break
        bad = [site for site in exclusions() if site in hops]
        state["history"].append(msgid)
        if bad:
            save(state)
            self.send("437 Unwanted site {} in path".format(bad[0]))
            return
        state["articles"][msgid] = lines
        save(state)
        self.send("235 Article transferred OK")


def serve(port: int, reader: bool, pidfile: str):
    listener = socket.socket()
    listener.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    listener.bind(("127.0.0.1", port))
    listener.listen(8)
    with open(pidfile, "w") as handle:
        handle.write(str(os.getpid()))
    while True:
        sock, _ = listener.accept()
        threading.Thread(target=lambda s=sock: Session(s, reader).run(),
                         daemon=True).start()


def innd(argv):
    os.makedirs(path("db"), exist_ok=True)
    os.makedirs(path("run"), exist_ok=True)
    if not os.path.exists(path("db", "spool.json")):
        save({"articles": {}, "history": []})
    port = 11119
    try:
        with open(path("etc", "inn.conf")) as handle:
            match = re.search(r"^port:\s*(\d+)", handle.read(), re.M)
            port = int(match.group(1)) if match else port
    except Exception:
        pass
    with open(path("log", "news.notice"), "a") as handle:
        handle.write("fake innd starting on port {}\n".format(port))
    serve(port, False, path("run", "innd.pid"))
    return 0


def nnrpd(argv):
    port = int(argv[argv.index("-p") + 1]) if "-p" in argv else 11120
    # Real nnrpd -D writes run/nnrpd-<port>.pid on any port but 119, and
    # run/nnrpd.pid on 119.  This fake wrote run/nnrpd.pid whatever the port,
    # so the lab's `cat $P/run/nnrpd-<port>.pid` read nothing and the pid
    # parse raised -- the setUpClass error of 2026-09-20.  The box is the
    # authority: planning/evidence/inn-lab-f4e8272-2026-09-20.md step 38 is
    # `NNRPD-UP pid=629447` out of `cat $P/run/nnrpd-11120.pid`.
    name = "nnrpd.pid" if port == 119 else "nnrpd-{}.pid".format(port)
    serve(port, True, path("run", name))
    return 0


def ctlinnd(argv):
    words = [one for one in argv if not one.startswith("-")]
    # -t <seconds> is a timeout, not a command word.
    if "-t" in argv:
        seconds = argv[argv.index("-t") + 1]
        words = [one for one in words if one != seconds]
    action = words[0] if words else ""
    try:
        with open(path("run", "innd.pid")) as handle:
            pid = int(handle.read().strip())
        os.kill(pid, 0)
        alive = True
    except Exception:
        pid, alive = 0, False
    if action == "mode":
        if not alive:
            print("ctlinnd: no innd.pid file; did server die?")
            return 1
        print("Server running")
        print("Allowing remote connections")
        return 0
    if not alive:
        print("ctlinnd: cannot send \"{}\" command".format(action))
        return 1
    if action == "newgroup":
        group = words[1]
        existing = Session.groups()
        if group not in existing:
            with open(path("db", "active"), "a") as handle:
                handle.write("{} 0000000000 0000000001 y\n".format(group))
        print("Ok")
        return 0
    if action == "flush":
        innfeed([])
        print("Ok")
        return 0
    if action == "shutdown":
        os.kill(pid, signal.SIGTERM)
        print("Ok")
        return 0
    if action == "reload":
        print("Ok")
        return 0
    print("Ok")
    return 0


def innfeed(argv):
    """One connection to the peer named in innfeed.conf, and what it answered."""
    port = peer_port()
    log = open(path("log", "innfeed.log"), "a")
    state = spool()
    msgid = next(iter(state["articles"]), "<nothing@example.invalid>")
    stamp = time.strftime("%Y-%m-%d %H:%M:%S")
    try:
        sock = socket.create_connection(("127.0.0.1", port), timeout=10)
        conn = sock.makefile("rb")
        greeting = conn.readline().decode("utf-8", "replace").strip()
        log.write("{} innfeed: fn:0 connected: {}\n".format(stamp, greeting))
        sock.sendall(b"MODE STREAM\r\n")
        mode = conn.readline().decode("utf-8", "replace").strip()
        log.write("{} innfeed: fn:0 MODE STREAM -> {}\n".format(stamp, mode))
        verb = "CHECK" if mode.startswith("203") else "IHAVE"
        sock.sendall("{} {}\r\n".format(verb, msgid).encode())
        answer = conn.readline().decode("utf-8", "replace").strip()
        log.write("{} innfeed: fn:0 {} -> {}\n".format(stamp, verb, answer))
        if not answer[:3] in ("238", "335"):
            log.write("{} innfeed: fn:0 cxnsleep response unknown: {}\n".format(
                stamp, answer))
        sock.close()
    except Exception as error:
        log.write("{} innfeed: fn:0 {}: {}\n".format(
            stamp, type(error).__name__, error))
    log.close()
    with open(path("log", "innfeed.status"), "w") as handle:
        handle.write("innfeed from fake INN\n\nPeer fn\n  offered 1\n  accepted 0\n"
                     "  refused 0\n  deferred 0\n")
    return 0


def innconfval(argv):
    print("INN 2.7.4 (fake stand-in, tests/inn_lab_fake)")
    return 0


def inncheck(argv):
    return 0


def makedbz(argv):
    base = argv[argv.index("-f") + 1] if "-f" in argv else path("db", "history")
    for extension in (".n.dir", ".n.hash", ".n.index"):
        open(base + extension, "w").close()
    return 0


def grephistory(argv):
    state = spool()
    msgid = argv[0] if argv else ""
    if msgid in state["history"]:
        print("{}\t~\t-".format(msgid))
        return 0
    print("Not found.")
    return 1


ROLES = {"innd": innd, "nnrpd": nnrpd, "ctlinnd": ctlinnd, "innfeed": innfeed,
         "innconfval": innconfval, "inncheck": inncheck, "makedbz": makedbz,
         "grephistory": grephistory}


def main(role: str, argv) -> int:
    os.makedirs(path("log"), exist_ok=True)
    os.makedirs(path("run"), exist_ok=True)
    return ROLES[role](list(argv))


if __name__ == "__main__":
    sys.exit(main(sys.argv[1], sys.argv[2:]))
