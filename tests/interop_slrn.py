"""Drive a real legacy newsreader (slrn) against tools/run_reader.py.

slrn 1.0.3a is an NNTP reader from the RFC 977/2980 era.  Measured against
fn on 2026-09-20 it sends, unprompted and in this order: MODE READER, XOVER,
XHDR Path, LIST OVERVIEW.FMT, LIST, LIST SUBSCRIPTIONS, QUIT.  Three of those
are RFC 2980 commands that did not exist in fn before this lane.

This probe starts the reader, runs slrn under a pty in its `--create' mode
(it needs a terminal it can clear, and it refuses `-d' together with
`--create'), and checks the NNTP dialogue slrn itself wrote with --debug:
which commands it sent, that fn understood every one of them (no 500 and no
501), and that the newsrc slrn built from LIST carries the served group.

A 4xx here is not a failure: slrn probes XOVER and XHDR before selecting a
group, and 412 is the correct answer.  500 or 501 would mean fn did not
understand what a real client sent, which is the thing being tested.

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
            newsrc = work / "newsrc"
            environment = dict(os.environ, HOME=str(work), TERM="xterm")
            # script(1) gives slrn the pty it insists on; --create asks the
            # server for the group list and writes the newsrc.  slrn then
            # opens its full-screen group list and waits, so it is given no
            # stdin and a deadline: the evidence is the dialogue above.
            command = ["script", "-q", "/dev/null",
                       "slrn", "--nntp", "-h", "127.0.0.1", "-p", str(port),
                       "-f", str(newsrc), "--create", "-k",
                       "--debug", str(debug)]
            try:
                subprocess.run(command, cwd=work, env=environment,
                               stdin=subprocess.DEVNULL,
                               stdout=subprocess.DEVNULL,
                               stderr=subprocess.DEVNULL, timeout=60)
            except subprocess.TimeoutExpired:
                pass
            dialogue = debug.read_text(errors="replace") if debug.exists() else ""
            groups = (newsrc.read_text(errors="replace").split()
                      if newsrc.exists() else [])
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
    # slrn's --debug log marks a sent line with ">" and a received one with
    # "<"; it writes a bare ">" for the CRLF of each command.
    sent = sorted({line[1:] for line in dialogue.splitlines()
                   if line.startswith(">") and len(line) > 1})
    received = [line[1:] for line in dialogue.splitlines()
                if line.startswith("<")]
    codes = sorted({line[:3] for line in received if line[:3].isdigit()})
    unknown = [line for line in received if line[:3] in ("500", "501")]
    served = [g.rstrip("!:") for g in groups]
    result = {"client": version, "python": platform.python_version(),
              "sent": sent, "codes": codes, "newsrc": served,
              "unknown_or_malformed": unknown,
              "status": "passed" if not unknown and served else "failed"}
    print(json.dumps(result, indent=2, sort_keys=True))
    if unknown or not served:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
