#!/usr/bin/env python3
"""Put one commit on a farm box, serve real clients from it, kill it, recover it.

`make certify` establishes what the books prove.  This establishes nothing of
the kind and is the other half of the story: the tree at a named commit,
unpacked on a machine that is not the laptop, serving a real socket, driven by
an independent client, SIGKILLed in the middle of a session, reopened through
the real recovery path, and reread.  Every command is recorded with its exit
code, the first line it printed and its wall time; the evidence file ends with
the list of what was *not* exercised and why, because a gate that silently
skips a phase is worse than no gate.

    python3 tools/deploy_gate.py dev --host persvati
    python3 tools/deploy_gate.py HEAD --host persvati --evidence planning/evidence/x.md

The three outcomes stay distinct in the recorded exit codes (D13): an accepted
post exits 0, a refused lookup exits 1, an uncertain publication exits 3.  The
gate asserts that distinctness rather than assuming it.

Certificates come from the host's own last gate of the tree
(``~/fn-gates/<tree>-<rev>/books``) when one is there, because a certificate
is content-keyed (``ACL2_BOOK_HASH_ALISTP=NIL``, see docs/proofs.md); when it
is not, the gate certifies on the host with 16 jobs.  Certificates copied from
a *live* origin root on the same machine are the ``foreign-local`` case
tools/certs.py refuses for a worktree that will itself certify; this deploy
tree never certifies, so the copy is safe here and is recorded as such.

Dry run.  ``--dry-run --home DIR`` runs every one of these scripts through
bash on this machine with ``HOME`` pointed at DIR and no ssh at all, so the
sequencing, the certificate choice, the port parsing, the kill/recover cut,
the exit-code classification and the evidence rendering are exercised by
tests/test_deploy_gate.py.  ``--overlay DIR`` copies files over the deployed
tree first; the dry run uses it to stand in for the ACL2-backed entry points.
"""
from __future__ import annotations

import argparse
import base64
import datetime as dt
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(Path(__file__).resolve().parent))
from farm import HOSTS as FARM_HOSTS      # noqa: E402  one table of farm boxes

# What tells an fn worktree from any other directory a `git rev-parse` finds.
FN_TREE_MARKERS = ("tools", "planning", "books")

DEFAULT_HOST = "persvati"
GATE_ROOT = "$HOME/fn-gates"
DEPLOY_ROOT = "$HOME/fn-deploy"
SEED_ID = "<stored@example.invalid>"
SEED_BODY = b"Message-ID: <stored@example.invalid>\r\n\r\nA stored letter.\r\n"
ABSENT_ID = "<absent@example.invalid>"
UNCERTAIN_ID = "<uncertain@example.invalid>"
POSTED_ID = "<posted@example.invalid>"
GROUPS = ("fn.letters", "fn.test")
NNTP_CLIENTS = ("slrn", "tin", "nn", "trn")
EXIT_OK, EXIT_REFUSED, EXIT_UNCERTAIN = 0, 1, 3
SERVER_READY_SECONDS = 300


class GateError(RuntimeError):
    """The gate cannot continue; what ran is still written out as evidence."""


# --------------------------------------------------------------------------
# hosts


class Host:
    """Somewhere a bash script can run and a git archive can land."""

    label = "?"

    def sh(self, script: str, timeout: int) -> subprocess.CompletedProcess:
        raise NotImplementedError

    def deploy(self, repo: Path, commit: str, target: str,
               timeout: int) -> subprocess.CompletedProcess:
        raise NotImplementedError


class SshHost(Host):
    def __init__(self, name: str):
        self.label = name
        self.name = name

    def _ssh(self, extra: list[str]) -> list[str]:
        return ["ssh", "-o", "BatchMode=yes", self.name] + extra

    def sh(self, script, timeout):
        return subprocess.run(self._ssh(["bash", "-s"]), input=script.encode(),
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                              timeout=timeout)

    def deploy(self, repo, commit, target, timeout):
        archive = subprocess.run(["git", "-C", str(repo), "archive", commit],
                                 stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                 check=True).stdout
        # stdin carries the archive, so the unpack is one remote command, not a
        # script read from the same stream.  The command is left unquoted: the
        # remote login shell is what expands the `$HOME` in the target.
        return subprocess.run(
            self._ssh(["rm -rf {t} && mkdir -p {t} && tar -x -C {t}".format(t=target)]),
            input=archive, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            timeout=timeout)


class LocalHost(Host):
    """The fake host: the same bash scripts, HOME redirected, no ssh."""

    def __init__(self, home: Path):
        self.label = "local:{}".format(home)
        self.home = Path(home)
        self.home.mkdir(parents=True, exist_ok=True)

    def _env(self) -> dict:
        env = dict(os.environ)
        env["HOME"] = str(self.home)
        return env

    def sh(self, script, timeout):
        return subprocess.run(["bash", "-s"], input=script.encode(), env=self._env(),
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                              timeout=timeout)

    def deploy(self, repo, commit, target, timeout):
        archive = subprocess.run(["git", "-C", str(repo), "archive", commit],
                                 stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                 check=True).stdout
        return subprocess.run(
            ["bash", "-c", "rm -rf {t} && mkdir -p {t} && tar -x -C {t}".format(t=target)],
            input=archive, env=self._env(), stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, timeout=timeout)


# --------------------------------------------------------------------------
# steps


class Step:
    """One command, its code, and what code was expected.

    `expect` is 0 for an ordinary step, the exit code that *is* the evidence
    for a refusal or an uncertain publication, and None for a probe whose
    failure the gate handles (a server entry point that may not start on this
    commit).  A step is failed only against its own expectation, so a refusal
    exiting 1 is not noise and a probe that fails is not a pass either -- it
    is recorded and explained in the gaps.
    """

    def __init__(self, name, command, rc, output, seconds, note="", expect=0):
        self.name = name
        self.command = command
        self.rc = rc
        self.output = output
        self.seconds = seconds
        self.note = note
        self.expect = expect

    @property
    def failed(self) -> bool:
        return self.rc is not None and self.expect is not None and self.rc != self.expect

    @property
    def first_line(self) -> str:
        for line in self.output.splitlines():
            if line.strip():
                return line.strip()[:200]
        return ""

    @property
    def exercised(self) -> bool:
        return self.rc is not None


def compact(script: str) -> str:
    """One readable line for a step's whole script, preamble dropped."""
    lines = [line.strip() for line in script.strip().splitlines()
             if line.strip() and not line.strip().startswith(
                 ("set -o pipefail", "export FN_ACL2", "#"))]
    joined = " ; ".join(lines)
    return joined if len(joined) <= 400 else joined[:397] + "..."


def not_exercised(name, command, reason) -> Step:
    """A step that did not run because something it NEEDS is absent.

    A dependency that is not installed, an interpreter the box does not have,
    a surface this commit has not built.  `rc` is None, so `Step.failed` is
    False and the gate can still pass: an absence is a finding, and the
    evidence file lists it, but it is not this commit failing.
    """
    return Step(name, command, None, "", 0.0, reason)


def did_not_complete(name, command, reason) -> Step:
    """A step that did not run because something the gate DID run failed.

    A symptom is not an absence, and until 2026-09-21 this gate and its three
    subclasses recorded both the same way.  A server that will not restart
    after the recovery it was killed for, a lab that produced no row, a
    profile pass that printed no JSON: each was a `not_exercised` step with
    `rc=None`, which `Step.failed` cannot see, so the gate printed `failed=0`
    and exited 0 over a durability defect.  This records rc=1 against
    expect=0, so it is a failed step, it appears in the FAILED list, and the
    exit code says so.
    """
    return Step(name, command, 1, reason, 0.0, reason, expect=0)


# --------------------------------------------------------------------------
# the drivers that run on the host

DRIVER = r'''#!/usr/bin/env python3
"""Independent NNTP driving for the deploy gate; no fn module is imported."""
import argparse, json, os, socket, sys, time


class Conn:
    def __init__(self, port, timeout=30):
        self.sock = socket.create_connection(("127.0.0.1", port), timeout=timeout)
        self.sock.settimeout(timeout)
        self.buf = b""
        self.log = []
        self.greeting = self.line()

    def line(self):
        while b"\r\n" not in self.buf:
            chunk = self.sock.recv(4096)
            if not chunk:
                raise RuntimeError("server closed the connection")
            self.buf += chunk
        out, self.buf = self.buf.split(b"\r\n", 1)
        return out.decode("utf-8", "replace")

    def send(self, text):
        self.sock.sendall(text.encode() + b"\r\n")

    def block(self):
        lines = []
        while True:
            one = self.line()
            if one == ".":
                return lines
            lines.append(one[1:] if one.startswith("..") else one)

    def cmd(self, text, multiline=False):
        self.send(text)
        status = self.line()
        body = self.block() if (multiline and status[:1] in "123") else []
        self.log.append({"command": text, "status": status, "body": body})
        return status, body

    def close(self):
        try:
            self.send("QUIT")
            self.line()
        except Exception:
            pass
        self.sock.close()


def transcript(args):
    conn = Conn(args.port)
    out = {"greeting": conn.greeting}
    status, caps = conn.cmd("CAPABILITIES", multiline=True)
    out["capabilities"] = caps
    out["post_offered"] = any(c.split()[0].upper() == "POST" for c in caps if c.strip())
    conn.cmd("LIST ACTIVE", multiline=True)
    conn.cmd("GROUP " + args.group)
    conn.cmd("ARTICLE 1", multiline=True)
    conn.cmd("OVER 1", multiline=True)
    conn.cmd("HEAD 1", multiline=True)
    conn.cmd("BOGUS")
    out["exchanges"] = conn.log
    conn.close()
    out["ok"] = out["exchanges"][2]["status"].startswith("211 ") and \
        out["exchanges"][3]["status"].startswith("220 ")
    return out


ARTICLE = ("From: gate@example.invalid\r\nSubject: deploy gate\r\n"
           "Newsgroups: {group}\r\nMessage-ID: {msgid}\r\n\r\n"
           "Posted by the deploy gate.\r\n")


def concurrent(args):
    """A second reader stays live across another connection's whole POST."""
    poster = Conn(args.port)
    watcher = Conn(args.port)
    out = {"post_offered": True}
    status, _ = watcher.cmd("GROUP " + args.group)
    out["watcher_before"] = status
    status, _ = poster.cmd("POST")
    out["post_open"] = status
    if not status.startswith("340"):
        out["ok"] = False
        out["reason"] = "server did not offer POST"
        poster.close(); watcher.close()
        return out
    body = ARTICLE.format(group=args.group, msgid=args.msgid)
    poster.sock.sendall(body.encode())
    status, _ = watcher.cmd("GROUP " + args.group)
    out["watcher_mid_post"] = status
    status, _ = watcher.cmd("ARTICLE 1", multiline=True)
    out["watcher_article_mid_post"] = status
    poster.sock.sendall(b".\r\n")
    out["post_result"] = poster.line()
    status, _ = watcher.cmd("GROUP " + args.group)
    out["watcher_after"] = status
    fresh = Conn(args.port)
    status, _ = fresh.cmd("GROUP " + args.group)
    out["fresh_after"] = status
    status, _ = fresh.cmd("ARTICLE " + args.msgid, multiline=True)
    out["fresh_article_by_id"] = status
    for conn in (poster, watcher, fresh):
        conn.close()
    out["ok"] = (out["post_result"].startswith("240")
                 and out["watcher_mid_post"].startswith("211")
                 and out["fresh_article_by_id"].startswith("220"))
    return out


def killcut(args):
    """SIGKILL the server mid-session, from inside an open POST."""
    conn = Conn(args.port)
    out = {}
    status, _ = conn.cmd("GROUP " + args.group)
    out["group"] = status
    status, _ = conn.cmd("POST")
    out["post_open"] = status
    partial = ("From: gate@example.invalid\r\nSubject: interrupted\r\n"
               "Newsgroups: {}\r\nMessage-ID: {}\r\n\r\nhalf an ".format(
                   args.group, args.msgid))
    conn.sock.sendall(partial.encode())
    time.sleep(0.5)
    os.kill(args.pid, 9)
    out["killed_pid"] = args.pid
    deadline = time.time() + 30
    out["after_kill"] = "no observation"
    while time.time() < deadline:
        try:
            conn.sock.sendall(b"article.\r\n.\r\n")
            reply = conn.line()
            out["after_kill"] = "reply: " + reply
            break
        except Exception as error:      # reset, EOF or timeout: all are the cut
            out["after_kill"] = "{}: {}".format(type(error).__name__, error)
            break
    try:
        conn.sock.close()
    except Exception:
        pass
    out["ok"] = not out["after_kill"].startswith("reply: 240")
    return out


def reread(args):
    conn = Conn(args.port)
    out = {"found": {}, "groups": {}}
    for group in args.groups.split(","):
        status, _ = conn.cmd("GROUP " + group)
        out["groups"][group] = status
    for msgid in args.msgids.split(","):
        status, body = conn.cmd("ARTICLE " + msgid, multiline=True)
        out["found"][msgid] = {"status": status, "lines": body}
    conn.close()
    out["ok"] = all(v["status"].startswith("220") for v in out["found"].values())
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="phase", required=True)
    for name in ("transcript", "concurrent", "killcut", "reread"):
        one = sub.add_parser(name)
        one.add_argument("--port", type=int, required=True)
        one.add_argument("--group", default="fn.letters")
        one.add_argument("--groups", default="fn.letters,fn.test")
        one.add_argument("--msgid", default="<gate@example.invalid>")
        one.add_argument("--msgids", default="")
        one.add_argument("--pid", type=int, default=0)
    args = parser.parse_args()
    handler = {"transcript": transcript, "concurrent": concurrent,
               "killcut": killcut, "reread": reread}[args.phase]
    try:
        result = handler(args)
    except Exception as error:
        print(json.dumps({"ok": False, "error": "{}: {}".format(
            type(error).__name__, error)}))
        return 1
    print(json.dumps(result))
    return 0 if result.get("ok") else 1


if __name__ == "__main__":
    sys.exit(main())
'''


CERTPICK = r'''#!/usr/bin/env python3
"""Copy in only the certificate pairs whose book content still matches.

A certificate is valid for a book and its whole include closure by content
(`ACL2_BOOK_HASH_ALISTP=NIL`), so a pair from a neighbouring revision of the
same tree is either exactly right or exactly wrong, and which one is decided
here rather than assumed: a pair is copied only when the `.lisp` beside it in
the gate hashes the same as the `.lisp` in the deploy tree.  ACL2 checks the
closure again at include time; this only avoids handing it pairs that cannot
hold.
"""
import hashlib, os, shutil, sys


def digest(path):
    with open(path, "rb") as handle:
        return hashlib.sha256(handle.read()).hexdigest()


def main():
    gate, deploy = sys.argv[1], sys.argv[2]
    matched = mismatched = absent = 0
    for sub in ("books", "tests/acl2"):
        source = os.path.join(gate, sub)
        target = os.path.join(deploy, sub)
        if not os.path.isdir(source) or not os.path.isdir(target):
            continue
        for name in sorted(os.listdir(source)):
            if not name.endswith(".cert"):
                continue
            stem = name[: -len(".cert")]
            book = os.path.join(source, stem + ".lisp")
            mine = os.path.join(target, stem + ".lisp")
            if not (os.path.exists(book) and os.path.exists(mine)):
                absent += 1
                continue
            if digest(book) != digest(mine):
                mismatched += 1
                continue
            for extension in (".cert", ".port"):
                one = os.path.join(source, stem + extension)
                if os.path.exists(one):
                    shutil.copy2(one, os.path.join(target, stem + extension))
            matched += 1
    print("matched={} mismatched={} absent={}".format(matched, mismatched, absent))
    return 0


if __name__ == "__main__":
    sys.exit(main())
'''


# --------------------------------------------------------------------------
# the gate


class DeployGate:
    """The single-node gate.  Its phases, its step accounting and its evidence
    renderer are the machinery a sibling gate reuses by subclassing; the four
    class attributes below are the only things such a subclass must restate."""

    TITLE = "Deploy gate"
    TOOL = "tools/deploy_gate.py"
    PREAMBLE = (
        "One commit, unpacked on a farm box, served to real clients, SIGKILLed",
        "mid-session and reopened through the real recovery path. This records what",
        "ran; it establishes nothing about the books beyond the fact that the",
        "certificates named below were the ones ACL2 read.")
    FACT_KEYS = ("os", "kernel", "python3", "acl2version", "certificates", "server",
                 "three outcomes")
    STANDING_GAPS = (
        "A SIGKILL of the server process is not a power loss: unflushed page cache\n"
        "  is not modeled here, and nothing in this run qualifies storage hardware.",
        "One kill point (inside an open POST) is exercised. The enumerated cut table\n"
        "  is `tests/campaign/cuts.py`; this gate does not replace it.",
        "No RFC 3977 conformance audit: the transcript exercises the verbs listed\n"
        "  above and no others, and the assertions are the driver's, not a spec's.",
        "No concurrent load, no multi-host peering, no BP/DTN transport.",
        "The certificates were not re-established here; see the certificate row.")

    def __init__(self, host: Host, repo: Path, commit: str, rev: str, tree: str,
                 overlay: Path | None = None, jobs: int = 16, keep: bool = False,
                 nntplib_python: str = "auto", acl2: str = "acl2"):
        self.host = host
        self.repo = repo
        self.commit = commit
        self.rev = rev
        self.tree = tree
        self.overlay = overlay
        self.jobs = jobs
        self.keep = keep
        self.nntplib_python = nntplib_python
        self.acl2 = acl2
        self.steps: list[Step] = []
        self.facts: dict[str, str] = {}
        self.gaps: list[str] = []
        self.deploy = "{}/{}".format(DEPLOY_ROOT, rev)
        self.run = "{}/gate-run".format(self.deploy)
        self.store = "{}/store".format(self.run)
        self.log = "{}/server.log".format(self.run)
        self.server_kind = "none"
        self.port = 0
        self.posted = [SEED_ID]     # what a reread after recovery must find
        self.post_enabled = False
        # The symptom of the last `start_server` that did not reach LISTENING.
        self.server_failure = ""
        # Whether this deploy tree ended up holding certificates.  It decides
        # whether a phase that needs a certified tree -- the native image,
        # which `tools/build_native_host.sh` refuses to build over an
        # uncertified book -- reports an absence or a failure.
        self.certificates_ok = False

    # -- plumbing ---------------------------------------------------------
    def sh(self, name, script, timeout=600, note="", expect=0) -> Step:
        start = time.monotonic()
        try:
            done = self.host.sh("set -o pipefail\nexport FN_ACL2={}\n".format(
                self.acl2) + script, timeout)
            rc, output = done.returncode, done.stdout.decode("utf-8", "replace")
        except subprocess.TimeoutExpired:
            rc, output = 124, "timed out after {}s".format(timeout)
        step = Step(name, compact(script), rc, output,
                    time.monotonic() - start, note, expect)
        self.steps.append(step)
        return step

    def skip(self, name, command, reason):
        """This step needs something that is not here.  See `not_exercised`."""
        self.steps.append(not_exercised(name, command, reason))
        self.gaps.append("{}: {}".format(name, reason))

    def broke(self, name, command, reason):
        """This step's subject failed.  See `did_not_complete`: a FAILED row."""
        self.steps.append(did_not_complete(name, command, reason))
        self.gaps.append("{}: {}".format(name, reason))

    def cd(self, script: str) -> str:
        return "cd {} || exit 9\n".format(self.deploy) + script

    def fn(self, args: str) -> str:
        """The store CLI.

        `bin/fn` (w5/fn-cli) is the service wrapper, not a second store CLI:
        its store surface is `fn status` and `fn group`, a different shape
        with its own exit codes, and it wraps `tools/run_store.py` for the
        rest.  The gate drives the wrapped entry point, so the exit codes it
        records are the ones the assurance rules are about.
        """
        return "python3 tools/run_store.py {}".format(args)

    # -- phases -----------------------------------------------------------
    def preflight(self):
        step = self.sh("preflight", """
. /etc/os-release 2>/dev/null || true
echo "os=${PRETTY_NAME:-unknown} kernel=$(uname -sr) arch=$(uname -m) cores=$(nproc 2>/dev/null || echo ?)"
echo "python3=$(python3 -V 2>&1)"
for p in python3.9 python3.10 python3.11 python3.12; do
  command -v $p >/dev/null && echo "alt=$p $($p -V 2>&1)"
done
for c in slrn tin nn trn inews expect script; do
  printf 'client %s=%s\\n' "$c" "$(command -v $c 2>/dev/null || echo ABSENT)"
done
{ printf '(good-bye)\\n' | ACL2_CUSTOMIZATION=NONE \\
    "$FN_ACL2" 2>&1 | grep -m1 -i 'ACL2 Version' \\
    | sed 's/^/acl2version=/'; } || echo "acl2version=unavailable on this host"
""", timeout=300)
        for line in step.output.splitlines():
            if "=" in line and not line.startswith("client "):
                key, _, value = line.partition("=")
                self.facts.setdefault(key.strip(), value.strip())
        self.clients = {}
        for line in step.output.splitlines():
            if line.startswith("client "):
                key, _, value = line[len("client "):].partition("=")
                self.clients[key] = value
        self.alt_pythons = [line[len("alt="):].split()[0]
                            for line in step.output.splitlines() if line.startswith("alt=")]
        return step

    def ship(self):
        start = time.monotonic()
        done = self.host.deploy(self.repo, self.commit, self.deploy, timeout=600)
        output = done.stdout.decode("utf-8", "replace")
        self.steps.append(Step("ship archive", "git archive {} | tar -x -C {}".format(
            self.rev, self.deploy), done.returncode, output, time.monotonic() - start))
        if done.returncode != 0:
            raise GateError("could not ship the archive: " + output[:400])
        self.sh("make run dir", "mkdir -p {}".format(self.run))
        if self.overlay is not None:
            self.push_tree(self.overlay)
        self.push_file(DRIVER, "{}/drive.py".format(self.run), mode="755")
        self.push_file(CERTPICK, "{}/certpick.py".format(self.run), mode="755")

    def push_file(self, content, remote: str, mode="644"):
        """Byte-exact: an article payload carries CRLF a heredoc would reshape."""
        if isinstance(content, str):
            content = content.encode()
        blob = base64.b64encode(content).decode()
        wrapped = "\n".join(blob[i:i + 76] for i in range(0, len(blob), 76)) or ""
        script = ("base64 -d > {path} <<'FN_GATE_EOF'\n{blob}\nFN_GATE_EOF\n"
                  "chmod {mode} {path}").format(path=remote, blob=wrapped, mode=mode)
        step = self.sh("install {}".format(Path(remote).name), script)
        if step.rc != 0:
            raise GateError("could not install {}: {}".format(remote, step.output[:200]))

    def push_tree(self, overlay: Path):
        for path in sorted(p for p in overlay.rglob("*") if p.is_file()):
            rel = path.relative_to(overlay)
            self.sh("overlay {}".format(rel),
                    "mkdir -p {}/{}".format(self.deploy, rel.parent))
            self.push_file(path.read_bytes(), "{}/{}".format(self.deploy, rel), mode="755")

    def certificates(self):
        """The host's own gate of this tree, verified pair by pair, else certify."""
        exact = "{}/{}-{}".format(GATE_ROOT, self.tree, self.rev)
        probe = self.sh("certificate source", """
if [ -d {exact}/books ]; then echo "GATE {exact}"; else
  newest=$(ls -dt {root}/{tree}-* 2>/dev/null | head -1)
  if [ -n "$newest" ] && [ -d "$newest/books" ]; then echo "NEIGHBOUR $newest"; else echo NOGATE; fi
fi
""".format(exact=exact, root=GATE_ROOT, tree=self.tree))
        first = probe.output.strip().splitlines()[-1] if probe.output.strip() else "NOGATE"
        if first.startswith(("GATE", "NEIGHBOUR")):
            kind, gate = first.split(None, 1)
            step = self.sh("install certificates",
                           "python3 {}/certpick.py {} {}".format(self.run, gate, self.deploy),
                           timeout=600,
                           note=("the host's own gate for this revision" if kind == "GATE"
                                 else "the host's newest gate of this tree; only the pairs "
                                      "whose book content matches this revision were copied"))
            self.facts["certificates"] = "{} {} -> {}".format(
                kind.lower(), gate, step.first_line)
            self.gaps.append(
                "certificates were copied from {}, a live origin root on the same host. "
                "tools/certs.py calls that foreign-local and refuses it for a worktree "
                "that will itself certify, because the pairs' post-alists name that "
                "root's absolute paths; this deploy tree never certifies, so ACL2 only "
                "reads them. Nothing in this gate re-establishes any certificate, and a "
                "book whose pair did not come across is included uncertified."
                .format(gate))
            if "mismatched=0" not in step.output:
                self.gaps.append(
                    "some books in the gate did not hash to this revision's sources, so "
                    "their pairs were not copied: {}".format(step.first_line))
            self.certificates_ok = step.rc == 0
            return step
        step = self.sh("certify on host",
                       self.cd("make certify FN_CERTIFY_JOBS={} 2>&1 | tail -40".format(self.jobs)),
                       timeout=6 * 3600)
        self.facts["certificates"] = "make certify on the host, {} jobs, rc={}".format(
            self.jobs, step.rc)
        self.certificates_ok = step.rc == 0
        return step

    def init_store(self):
        groups = " ".join("--group {}".format(g) for g in GROUPS)
        step = self.sh("store init", self.cd(self.fn(
            "--store {} init {}".format(self.store, groups))), timeout=900)
        if step.rc != 0:
            raise GateError("store init failed: " + step.output[:400])
        self.sh("store config", self.cd(self.fn("--store {} config".format(self.store))),
                timeout=900)
        return step

    def three_outcomes(self):
        """Accepted 0, refused 1, uncertain 3, from the real entry point."""
        payload = "{}/seed.article".format(self.run)
        self.push_file(SEED_BODY, payload)
        groups = " ".join("--group {}".format(g) for g in GROUPS)
        accepted = self.sh("outcome accepted", self.cd(self.fn(
            "--store {} post --message-id '{}' --payload {} {}".format(
                self.store, SEED_ID, payload, groups))), timeout=900, expect=EXIT_OK)
        refused = self.sh("outcome refused", self.cd(self.fn(
            "--store {} inspect --message-id '{}'".format(self.store, ABSENT_ID))),
            timeout=900, expect=EXIT_REFUSED)
        uncertain = self.sh("outcome uncertain", self.cd(self.fn(
            "--store {} post --message-id '{}' --payload {} --group {} "
            "--inject-fault postpublish".format(
                self.store, UNCERTAIN_ID, payload, GROUPS[0]))), timeout=900,
            expect=EXIT_UNCERTAIN)
        observed = (accepted.rc, refused.rc, uncertain.rc)
        expected = (EXIT_OK, EXIT_REFUSED, EXIT_UNCERTAIN)
        self.facts["three outcomes"] = "accepted={} refused={} uncertain={} (expected {})".format(
            *observed, expected)
        if observed != expected:
            self.gaps.append(
                "the three outcomes did not stay distinct in the exit codes: "
                "observed {}, expected {} (D13)".format(observed, expected))
        self.sh("recover after the uncertain publication",
                self.cd(self.fn("--store {} recover".format(self.store))), timeout=900)

    def server_command(self, store=None, run=None) -> tuple[str, str]:
        """bin/fn when it can be pointed at this store, else the owner, else the reader.

        `store` and `run` default to this gate's single store and run directory;
        a gate that runs more than one node passes one pair per node."""
        store = store or self.store
        run = run or self.run
        probe = self.sh("server selection", self.cd("""
if [ -x bin/fn ]; then
  if ./bin/fn run --help 2>&1 | grep -q -- '--store'; then echo fn
  else echo fn-config; fi
elif [ -f tools/run_owner.py ]; then echo owner
else echo reader; fi
"""))
        kind = probe.output.strip().splitlines()[-1] if probe.output.strip() else "reader"
        if kind == "fn":
            return kind, "./bin/fn run --store {} --port 0 --control {}/control.sock".format(
                store, run)
        if kind == "fn-config":
            self.gaps.append(
                "bin/fn is in this tree but its `run` is configuration-file driven and "
                "takes no --store, and this gate does not author a configuration for it. "
                "The gate drove tools/run_owner.py, the entry point bin/fn wraps, so the "
                "service wrapper's own argument handling and logging are not exercised.")
            kind = "owner"
        if kind == "owner":
            return kind, "python3 tools/run_owner.py --store {} --port 0 --control {}/control.sock".format(
                store, run)
        return kind, "python3 tools/run_reader.py --store {} --port 0 --post".format(store)

    def start_server(self, kind: str, command: str, tag: str, run=None) -> bool:
        run = run or self.run
        log = "{}/server-{}.log".format(run, tag)
        step = self.sh("start server ({}, {})".format(kind, tag), self.cd("""
rm -f {log}
nohup {command} > {log} 2>&1 < /dev/null &
echo $! > {run}/server.pid
for i in $(seq 1 {wait}); do
  if grep -m1 '^LISTENING' {log}; then exit 0; fi
  if ! kill -0 $(cat {run}/server.pid) 2>/dev/null; then echo SERVER-DIED; tail -25 {log}; exit 1; fi
  sleep 1
done
echo SERVER-TIMEOUT; tail -25 {log}; exit 1
""".format(command=command, log=log, run=run, wait=SERVER_READY_SECONDS)),
            timeout=SERVER_READY_SECONDS + 120, expect=None)
        match = re.search(r"^LISTENING (\d+)", step.output, re.M)
        if step.rc != 0 or match is None:
            # Why it did not start, for the row that records the consequence:
            # `SERVER-DIED` with the log tail, `SERVER-TIMEOUT`, or whatever
            # the shell said.  A reason of "it did not start" and no symptom
            # is a row nobody can act on.
            self.server_failure = step.first_line or "no LISTENING line"
            return False
        self.server_failure = ""
        self.port = int(match.group(1))
        self.server_kind = kind
        self.post_enabled = "--post" in command or kind.startswith(("owner", "fn"))
        self.facts["server"] = "{} on port {} ({})".format(kind, self.port, tag)
        return True

    def stop_server(self, tag="", run=None):
        run = run or self.run
        self.sh("stop server {}".format(tag).strip(), """
if [ -f {run}/server.pid ]; then
  pid=$(cat {run}/server.pid)
  kill $pid 2>/dev/null || true
  for i in $(seq 1 20); do kill -0 $pid 2>/dev/null || break; sleep 1; done
  kill -9 $pid 2>/dev/null || true
  rm -f {run}/server.pid
fi
echo stopped
""".format(run=run))

    def drive(self, phase: str, extra: str, name=None, timeout=300) -> Step:
        return self.sh(name or "drive {}".format(phase), self.cd(
            "python3 {}/drive.py {} --port {} {}".format(self.run, phase, self.port, extra)),
            timeout=timeout)

    def nntplib_probe(self):
        """tests/interop_store_nntplib.py needs a stdlib nntplib (Python <= 3.12)."""
        if self.nntplib_python == "none":
            self.skip("nntplib probe", "tests/interop_store_nntplib.py",
                      "--nntplib-python none: the operator excluded the stdlib-nntplib probe "
                      "for this run")
            return
        candidates = ([self.nntplib_python] if self.nntplib_python != "auto"
                      else list(getattr(self, "alt_pythons", [])))
        chooser = self.sh("nntplib interpreter", " ".join(
            ["for p in"] + (candidates or ["python3"]) +
            ["python3; do $p -c 'import nntplib' 2>/dev/null && { echo USE $p; exit 0; }; done;",
             "echo NONE"]))
        match = re.search(r"^USE (\S+)", chooser.output, re.M)
        if match is None:
            # waiver-ok: environment -- the probe asks each interpreter on the
            # box whether `import nntplib` works and prints USE or NONE, so it
            # reads a command's OUTPUT to learn that a dependency is absent
            # rather than to learn that something failed.  The reason below is
            # the predicate: no interpreter here has a stdlib nntplib.
            self.skip("nntplib probe", "tests/interop_store_nntplib.py",
                      "no interpreter on the host has a stdlib nntplib "
                      "(python3 is {}; nntplib was removed in 3.13 by PEP 594 and no "
                      "3.12 or earlier interpreter is installed)".format(
                          self.facts.get("python3", "unknown")))
            return
        interpreter = match.group(1)
        # The stored probe asserts POST is not offered, so it runs against a
        # read-only reader holding the shared lock, before the writer starts.
        if not self.start_server("reader (read-only)",
                                 "python3 tools/run_reader.py --store {} --port 0".format(
                                     self.store), "probe"):
            # `tools/run_reader.py` is on the tree this gate deployed, so a
            # reader that does not reach LISTENING is this commit failing to
            # serve, not a probe dependency the box is missing.
            self.broke("nntplib probe", "tests/interop_store_nntplib.py",
                       "the read-only reader did not reach LISTENING: {}".format(
                           self.server_failure or "no symptom recorded"))
            return
        self.sh("nntplib probe", self.cd("{} tests/interop_store_nntplib.py {}".format(
            interpreter, self.port)), timeout=300,
            note="independent client: {}".format(interpreter))
        self.stop_server("probe")

    def news_client(self):
        present = [c for c in NNTP_CLIENTS if self.clients.get(c, "ABSENT") != "ABSENT"]
        if not present:
            self.skip("scripted news client", "slrn/tin batch session",
                      "no news client is installed on the host (slrn, tin, nn and trn "
                      "are all absent; `sudo apt-get install -y slrn tin` was not run by "
                      "this gate because installing packages is a host change the gate "
                      "does not own)")
            return
        client = present[0]
        if client == "slrn":
            inner = ("slrn -f {run}/slrn.jnews -i {run}/slrn.rc --nntp -h 127.0.0.1 "
                     "-p {port} --create -n").format(run=self.run, port=self.port)
            prelude = """
cat > {run}/slrn.rc <<'FN_SLRN_EOF'
set hostname "gate.example.invalid"
set username "gate"
set realname "Deploy Gate"
FN_SLRN_EOF
""".format(run=self.run)
        else:
            inner = "tin -r -g 127.0.0.1 -p {} -R".format(self.port)
            prelude = ""
        # util-linux script takes `-c CMD FILE`; the BSD one takes `FILE CMD...`.
        script = self.cd(prelude + """
typescript={run}/{client}.typescript
# A newsreader is interactive; /dev/null on its stdin should end it, and the
# bounded wait is here because "should" is not a property of a strange client.
if script --version 2>/dev/null | grep -qi util-linux; then
  NNTPSERVER=127.0.0.1 script -q -c {inner} $typescript < /dev/null > /dev/null 2>&1 &
else
  NNTPSERVER=127.0.0.1 script -q $typescript /bin/sh -c {inner} < /dev/null > /dev/null 2>&1 &
fi
client_pid=$!
for i in $(seq 1 20); do kill -0 $client_pid 2>/dev/null || break; sleep 1; done
if kill -0 $client_pid 2>/dev/null; then
  kill -9 $client_pid 2>/dev/null || true
  echo "(the client was still running after 20 s and was killed)"
fi
wait $client_pid 2>/dev/null || true
head -5 $typescript 2>/dev/null || echo "(the client left no typescript)"
""".format(run=self.run, client=client, inner="'" + inner + "'"))
        self.sh("scripted {} session".format(client), script, timeout=180,
                note="a real newsreader driven over a pty by script(1); no expect on "
                     "the host, and the session is not interactive: it records that the "
                     "client connected and what it said, not a browsing session")

    # -- the whole gate ---------------------------------------------------
    def execute(self):
        self.preflight()
        self.ship()
        self.certificates()
        self.init_store()
        self.three_outcomes()
        self.nntplib_probe()
        kind, command = self.server_command()
        if not self.start_server(kind, command, "main"):
            fallback = "python3 tools/run_reader.py --store {} --port 0 --post".format(self.store)
            self.gaps.append(
                "the {} entry point did not reach LISTENING on this commit; the gate fell "
                "back to tools/run_reader.py --post. The served-read evidence below is the "
                "reader's, not the {}'s.".format(kind, kind))
            if kind == "reader" or not self.start_server("reader", fallback, "main"):
                raise GateError("no server entry point reached LISTENING")
        transcript = self.drive("transcript", "--group {}".format(GROUPS[0]))
        if self.post_enabled and '"post_offered": false' in transcript.output:
            self.gaps.append(
                "the server was started with POST enabled and answers POST with 340 (see "
                "the kill cut below), but its CAPABILITIES block does not list POST. RFC "
                "3977 section 5.2.2 requires the POST capability exactly when posting is "
                "permitted, so an independent client that reads capabilities before "
                "posting will not offer posting at all.")
        concurrent = self.drive("concurrent", "--group {} --msgid '{}'".format(
            GROUPS[0], POSTED_ID))
        if concurrent.rc == 0:
            self.posted.append(POSTED_ID)
        else:
            self.gaps.append(
                "a second reader live across another connection's POST was NOT exercised: "
                "tools/run_reader.py serves one connection at a time (its accept loop "
                "calls serve_client to completion before accepting again, and it listens "
                "with a backlog of 1), so the second connection never gets a greeting. "
                "The concurrent server is tools/run_owner.py, which did not start on this "
                "commit; nothing below establishes that a reader's pinned snapshot "
                "survives another connection's post.")
        pid = self.sh("server pid", "cat {}/server.pid".format(self.run)).output.strip()
        self.drive("killcut", "--group {} --msgid '<interrupted@example.invalid>' --pid {}".format(
            GROUPS[0], pid), name="kill -9 mid-session")
        self.sh("server is gone", "kill -0 {} 2>/dev/null && echo ALIVE || echo GONE".format(pid))
        self.sh("recover after the kill",
                self.cd(self.fn("--store {} recover".format(self.store))), timeout=1800)
        self.sh("status after recovery",
                self.cd(self.fn("--store {} status".format(self.store))), timeout=1800)
        if self.start_server(kind if kind != "owner" else "reader",
                             command if kind != "owner" else
                             "python3 tools/run_reader.py --store {} --port 0 --post".format(
                                 self.store), "after-recovery"):
            self.drive("reread", "--groups {} --msgids '{}'".format(
                ",".join(GROUPS), ",".join(self.posted)), name="reread after recovery")
            self.news_client()
            self.stop_server("after-recovery")
        else:
            # The subject of this gate is "serves, dies and recovers".  A
            # server that started before the kill and will not start after it
            # is that subject failing, not a dependency this box lacks.
            self.broke("reread after recovery", "drive.py reread",
                       "the server did not restart after recovery: {}".format(
                           self.server_failure or "no symptom recorded"))
        self.sh("server log tail", "tail -15 {}/server-main.log".format(self.run))
        if not self.keep:
            self.sh("remove the deploy tree", "rm -rf {}".format(self.deploy))

    # -- evidence ---------------------------------------------------------
    def evidence(self, path: Path, started: str, elapsed: float) -> Path:
        lines = [
            "# {}: {} on {}".format(self.TITLE, self.rev, self.host.label),
            "",
        ] + list(self.PREAMBLE) + [
            "",
            "## What ran",
            "",
            "| fact | value |",
            "| --- | --- |",
            "| commit | `{}` ({}) |".format(self.rev, self.commit),
            "| tree | `{}` |".format(self.tree),
            "| host | `{}` |".format(self.host.label),
            "| started | {} |".format(started),
            "| wall time | {:.1f} s |".format(elapsed),
            "| gate tool | `{}` |".format(self.TOOL),
        ]
        for key in self.FACT_KEYS:
            if key in self.facts:
                lines.append("| {} | {} |".format(key, self.facts[key].replace("|", "\\|")))
        clients = ", ".join("{}={}".format(k, v) for k, v in sorted(
            getattr(self, "clients", {}).items()))
        if clients:
            lines.append("| host clients | {} |".format(clients))
        lines += [
            "",
            "## Every command",
            "",
            "| # | step | rc | first line | s |",
            "| --- | --- | --- | --- | --- |",
        ]
        for index, step in enumerate(self.steps, 1):
            rc = "-" if step.rc is None else "{}{}".format(
                step.rc, "" if not step.failed else " FAIL")
            first = step.first_line.replace("|", "\\|") or ("not exercised"
                                                            if step.rc is None else "")
            lines.append("| {} | {} | {} | `{}` | {:.1f} |".format(
                index, step.name.replace("|", "\\|"), rc, first, step.seconds))
        lines += ["", "### Commands in full", ""]
        for index, step in enumerate(self.steps, 1):
            lines.append("{}. **{}** -- `{}`".format(
                index, step.name, step.command.replace("`", "'")))
            if step.note:
                lines.append("   - {}".format(step.note))
        lines += ["", "## What was NOT exercised", ""]
        if not self.gaps:
            lines.append("Nothing was skipped in this run.")
        for gap in self.gaps:
            lines.append("- {}".format(gap))
        lines += [
            "",
            "Standing gaps of the gate itself, independent of this run:",
            "",
        ] + ["- {}".format(gap) for gap in self.STANDING_GAPS] + [
            "",
            "## Raw step output",
            "",
            "```",
        ]
        for index, step in enumerate(self.steps, 1):
            head = "\n".join(step.output.splitlines()[:12])
            lines.append("--- {} {} (rc={})".format(index, step.name, step.rc))
            if head:
                lines.append(head)
        lines += ["```", ""]
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("\n".join(lines))
        return path


def is_fn_tree(path: Path) -> bool:
    """Whether `path` is an fn worktree rather than some other repository."""
    return all((path / marker).is_dir() for marker in FN_TREE_MARKERS)


def repo_root(start: Path | None = None) -> Path:
    """The fn worktree this command was INVOKED from, not the one the file is in.

    `Path(__file__).resolve().parents[1]` answers "where does this script
    live", which is a different question and the wrong one: a lane that runs
    the main checkout's copy of a harness -- by absolute path, or through a
    `tools/` that is on its `sys.path` from somewhere else -- gets the main
    checkout's `planning/evidence/`.  Measured on 2026-09-20: a lane working
    in `build/lanes/w6-peering-inbound-2` had `planning/evidence/twonode-*.md`
    written into `/Users/ember/dev/fn`, where it sat untracked and blocked a
    merge.

    `git rev-parse --show-toplevel` from inside a worktree answers that
    worktree, which is the tree whose `planning/` the operator is about to
    commit from.  A cwd in no repository, or in a repository that is not this
    one, falls back to this file's own tree, which is the only other tree
    that can be meant.
    """
    here = Path(start).resolve() if start else Path.cwd()
    try:
        found = subprocess.run(
            ["git", "-C", str(here), "rev-parse", "--show-toplevel"],
            stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, timeout=30,
            check=False)
    except (OSError, subprocess.SubprocessError):
        return ROOT
    if found.returncode != 0:
        return ROOT
    candidate = Path(found.stdout.decode("utf-8", "replace").strip() or ".")
    if not is_fn_tree(candidate):
        return ROOT
    chosen = candidate.resolve()
    if chosen != ROOT and is_fn_tree(ROOT):
        # Two fn worktrees in play: the one this command was run in and the
        # one the harness file lives in.  That is exactly the ambiguity that
        # put `planning/evidence/twonode-*.md` into the main checkout three
        # times, each time untracked and blocking a merge -- and it is
        # invisible, because the two trees hold the same file names.  Say
        # which was chosen, every run, so the next occurrence diagnoses
        # itself from the log instead of from a blocked merge.
        # stderr, not stdout: `tools/tcpcl_lab.py` prints one JSON object
        # per line and a caller reads every line of it.
        print("repo: {} (this command's tools/ live in {}; evidence and logs "
              "go to the tree it was INVOKED from -- pass --repo to override)"
              .format(chosen, ROOT), file=sys.stderr, flush=True)
    return chosen


def evidence_path(given: str | None, repo: Path, default_name: str) -> Path:
    """Where a harness writes its record, always under the tree it was run from.

    A relative `--evidence` used to resolve against the process's working
    directory and the default against the tree the script file lives in.
    Either can be a worktree other than the one the operator will commit, so
    both are anchored on `repo` here; an absolute path is still taken as
    given, which is how a run writes outside the tree on purpose.
    """
    if given:
        path = Path(given).expanduser()
        return path if path.is_absolute() else (repo / path)
    return repo / "planning" / "evidence" / default_name


def resolve(repo: Path, commit: str) -> tuple[str, str]:
    """The full and short revision for `commit`.

    Outside a repository (a `git archive` tree, as on the farm) a literal
    hexadecimal id is accepted as given; anything else still needs git.
    """
    try:
        full = subprocess.run(["git", "-C", str(repo), "rev-parse", commit],
                              stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                              check=True).stdout.decode().strip()
    except (subprocess.CalledProcessError, FileNotFoundError):
        if re.fullmatch(r"[0-9a-fA-F]{7,40}", commit):
            full = commit.lower()
        else:
            raise
    return full, full[:7]


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("commit", help="the commit-ish to deploy")
    parser.add_argument("--host", default=DEFAULT_HOST)
    parser.add_argument("--tree", default="dev", help="gate directory prefix on the host")
    parser.add_argument("--repo", default=None,
                        help="the fn worktree to read the commit from and "
                             "write evidence into (default: the one this "
                             "command was invoked from)")
    parser.add_argument("--jobs", type=int, default=16)
    parser.add_argument("--evidence", default=None)
    parser.add_argument("--keep", action="store_true",
                        help="leave the deploy tree on the host")
    parser.add_argument("--dry-run", action="store_true",
                        help="run every script through local bash with HOME redirected")
    parser.add_argument("--home", default=None, help="the fake HOME for --dry-run")
    parser.add_argument("--acl2", default=None,
                        help="the host's ACL2 image; the default is tools/farm.py's "
                             "entry for the host, else `acl2` on its PATH")
    parser.add_argument("--nntplib-python", default="auto",
                        help="auto, none, or an interpreter with a stdlib nntplib")
    parser.add_argument("--overlay", default=None,
                        help="a directory copied over the deployed tree before it runs")
    args = parser.parse_args(argv)

    repo = Path(args.repo).resolve() if args.repo else repo_root()
    commit, rev = resolve(repo, args.commit)
    if args.dry_run:
        if args.home is None:
            parser.error("--dry-run needs --home")
        host: Host = LocalHost(Path(args.home).resolve())
    else:
        host = SshHost(args.host)
    overlay = Path(args.overlay).resolve() if args.overlay else None
    gate = DeployGate(host, repo, commit, rev, args.tree, overlay=overlay,
                      jobs=args.jobs, keep=args.keep,
                      nntplib_python=args.nntplib_python,
                      acl2=args.acl2 or FARM_HOSTS.get(args.host, {}).get("acl2", "acl2"))
    started = dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    clock = time.monotonic()
    failure = None
    try:
        gate.execute()
    except GateError as error:
        failure = str(error)
        gate.gaps.append("the gate stopped early: {}".format(error))
    elapsed = time.monotonic() - clock
    date = dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%d")
    target = evidence_path(args.evidence, repo,
                           "deploy-{}-{}.md".format(rev, date))
    gate.evidence(target, started, elapsed)
    print("evidence: {}".format(target))
    bad = [s for s in gate.steps if s.failed]
    print("steps={} failed={} not-exercised={}".format(
        len(gate.steps), len(bad), sum(1 for s in gate.steps if s.rc is None)))
    for step in bad:
        print("  FAILED rc={} {}: {}".format(step.rc, step.name, step.first_line))
    if failure:
        print("gate error: {}".format(failure))
        return 2
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
