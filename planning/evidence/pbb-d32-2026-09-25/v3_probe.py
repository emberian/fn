"""pbb-d32 native probe: a served POST with a supplied Path (D32 recipe v3),
resent, through the buffer twin on the developer image.

    FN_NATIVE_DEVELOPER_HOST=... python3 v3_probe.py

One owner over a fresh store.  POST 1: tin's shape (`Path: not-for-mail'
first, a supplied Message-ID, no Date) -> 240.  POST 2: the same octets
again -> the duplicate line (D25 over the v3 source: the record does not
open with the agent's Path line, so fn-pbb-source-index takes the v3 arm
and the compare reads the two pieces in place).  POST 3: the same source
with another supplied Path -> the conflict line.  POST 4: the same source
without a Path -> the conflict line.  Prints one line per POST and exits 0
only when all four replies are the expected ones.
"""
import os, select, socket, subprocess, sys, tempfile
from pathlib import Path

ROOT = Path(os.environ.get("FN_NATIVE_SOURCE_ROOT", Path(__file__).resolve().parent))
IMAGE = Path(os.environ["FN_NATIVE_DEVELOPER_HOST"])


def environment():
    env = dict(os.environ)
    env["ACL2_CUSTOMIZATION"] = "NONE"
    env.pop("ACL2_SYSTEM_BOOKS", None)
    env.pop("FN_HOST", None)
    return env


def article(path, msgid=b"<pbb-d32-v3@example.invalid>"):
    head = b""
    if path is not None:
        head += b"Path: " + path + b"\r\n"
    return (head +
            b"From: poster@example.invalid\r\n"
            b"Newsgroups: fn.test\r\n"
            b"Subject: pbb-d32 v3 probe\r\n"
            b"Message-ID: " + msgid + b"\r\n\r\n"
            b"Hello, news.\r\n")


def post(port, octets):
    with socket.create_connection(("127.0.0.1", port), timeout=30) as client:
        stream = client.makefile("rwb", buffering=0)
        assert stream.readline().startswith(b"200 ")
        stream.write(b"POST\r\n")
        assert stream.readline().startswith(b"340 ")
        stream.write(octets + b".\r\n")
        reply = stream.readline()
        stream.write(b"QUIT\r\n")
        stream.readline()
    return reply


def main():
    temporary = tempfile.TemporaryDirectory(prefix="fn-pbb-d32-v3-")
    store = Path(temporary.name) / "store"
    init = subprocess.run([str(IMAGE), "--fn", "store", str(store), "init", "fn.test"],
                          cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                          env=environment(), timeout=180, check=False)
    if init.returncode != 0:
        print("store init failed:", init.stderr.decode()); return 2
    process = subprocess.Popen([str(IMAGE), "--fn", "owner", "run", str(store), "0", "0", "8"],
                               cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                               env=environment())
    try:
        assert select.select([process.stdout], [], [], 180)[0], "no port"
        line = process.stdout.readline()
        assert line.startswith(b"LISTENING "), (line, process.stderr.read())
        port = int(line.split()[1])
        cases = [
            ("v3 first post (Path: not-for-mail)", article(b"not-for-mail"), b"240 "),
            ("v3 resend, same octets", article(b"not-for-mail"), b"already stored here"),
            ("v3 resend, another Path", article(b"example.org!not-for-mail"), b"441 "),
            ("resend without a Path", article(None), b"441 "),
        ]
        ok = True
        replies = []
        for label, octets, expect in cases:
            reply = post(port, octets)
            replies.append(reply)
            good = expect in reply
            ok = ok and good
            print(("PASS " if good else "FAIL ") + label + " -> " + reply.decode("ascii", "replace").rstrip())
        # The duplicate and conflict lines must differ from each other.
        if replies[1] == replies[2] or replies[2] != replies[3]:
            print("FAIL the duplicate line and the conflict lines do not separate as expected")
            ok = False
        process.terminate()
        try:
            process.wait(timeout=30)
        except subprocess.TimeoutExpired:
            process.kill()
        # The owner is the one process that holds the store; inspect after it exits.
        inspected = subprocess.run([str(IMAGE), "--fn", "store", str(store), "inspect",
                                    "<pbb-d32-v3@example.invalid>"], cwd=ROOT,
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                   env=environment(), timeout=180, check=False)
        text = inspected.stdout.decode("ascii", "replace")
        first = text.split("\n", 1)[0]
        print("stored record opens with:", first.rstrip())
        for want in ("Injection-Info:", "Path: "):
            if want not in text:
                print("FAIL the stored record lacks", want); ok = False
        pathline = [l for l in text.split("\n") if l.startswith("Path: ")]
        print("stored Path line:", pathline[0].rstrip() if pathline else "(none)")
        if pathline and not pathline[0].rstrip().endswith("!not-for-mail"):
            print("FAIL the stored Path does not keep the supplied tail"); ok = False
        if first.startswith("Path: "):
            print("FAIL the stored record opens with a Path line: not a v3 record"); ok = False
        return 0 if ok else 1
    finally:
        if process.poll() is None:
            process.kill()
        temporary.cleanup()


if __name__ == "__main__":
    sys.exit(main())
