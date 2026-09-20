"""Drive a real legacy newsreader (slrn) against tools/run_reader.py.

slrn 1.0.3a is an NNTP reader from the RFC 977/2980 era: it speaks XOVER and
XHDR, reads LIST ACTIVE to build a newsrc and LIST NEWSGROUPS for
descriptions, and it does not require any RFC 3977 capability.  This probe
starts the reader, runs slrn in its non-interactive `--create' mode with the
NNTP dialogue written to a debug log, and checks that log: what the client
actually sent, and that fn answered every one of them without an error code.

This is interoperability evidence for one client at one version, not an RFC
conformance audit.  Run it directly; it needs slrn on PATH.
"""
import json
import os
import platform
import re
import select
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def start_reader():
    proc = subprocess.Popen(
        [sys.executable, "tools/run_reader.py", "--port", "0"],
        cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    deadline = time.monotonic() + 120
    while time.monotonic() < deadline:
        ready, _, _ = select.select([proc.stdout], [], [], 0.2)
        if ready:
            line = proc.stdout.readline()
            if line.startswith(b"LISTENING "):
                return proc, int(line.split()[1])
        if proc.poll() is not None:
            break
    proc.kill()
    raise RuntimeError("reader did not listen")


def main():
    if shutil.which("slrn") is None:
        raise SystemExit("slrn is not on PATH")
    version = subprocess.run(["slrn", "--version"], capture_output=True,
                             text=True).stdout.splitlines()[0]
    reader, port = start_reader()
    try:
        with tempfile.TemporaryDirectory() as work:
            work = Path(work)
            debug = work / "slrn.debug"
            environment = dict(os.environ, HOME=str(work), TERM="dumb",
                               SLRNHOME=str(work))
            # --create asks the server for the group list and writes a
            # newsrc; -d then asks for the descriptions (LIST NEWSGROUPS).
            # slrn opens a curses screen afterwards, so it is given no stdin
            # and a deadline; the evidence is the dialogue it wrote first.
            command = ["slrn", "--nntp", "-h", "127.0.0.1", "-p", str(port),
                       "-f", str(work / "newsrc"), "--create", "-d", "-k",
                       "--debug", str(debug)]
            try:
                subprocess.run(command, cwd=work, env=environment,
                               stdin=subprocess.DEVNULL,
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                               timeout=60)
            except subprocess.TimeoutExpired:
                pass
            dialogue = debug.read_text(errors="replace") if debug.exists() else ""
    finally:
        reader.terminate()
        try:
            reader.wait(timeout=10)
        except subprocess.TimeoutExpired:
            reader.kill()
        reader.stdout.close()
        reader.stderr.close()

    if not dialogue:
        raise SystemExit("slrn wrote no NNTP dialogue; nothing to check")
    sent = [line.split(":", 1)[1].strip()
            for line in dialogue.splitlines() if line.startswith(">")]
    received = [line.split(":", 1)[1].strip()
                for line in dialogue.splitlines() if line.startswith("<")]
    # slrn's debug log marks each direction; fall back to the raw lines when
    # the build uses a different marker.
    if not sent:
        sent = [line for line in dialogue.splitlines()
                if re.match(r"^(LIST|MODE|GROUP|XOVER|XHDR|QUIT|HEAD|BODY"
                            r"|ARTICLE|STAT|DATE|CAPABILITIES)\b", line)]
    if not received:
        received = [line for line in dialogue.splitlines()
                    if re.match(r"^[1-5][0-9][0-9][ \t]", line)]
    codes = sorted({line[:3] for line in received if line[:3].isdigit()})
    refused = [line for line in received if line[:1] in ("4", "5")]
    result = {"status": "passed" if not refused else "failed",
              "client": version, "python": platform.python_version(),
              "sent": sent, "codes": codes, "refused": refused}
    print(json.dumps(result, indent=2, sort_keys=True))
    if refused:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
