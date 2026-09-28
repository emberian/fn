#!/usr/bin/env python3
"""Put one commit on a farm box, serve real clients from it, kill it, recover it.

`make certify` establishes what the books prove.  This establishes nothing of
the kind and is the other half of the story: the tree at a named commit,
unpacked on a machine that is not the laptop, its native image (`--native-image`,
a path on the box, built from that commit) serving a real socket through
`operator CONFIG run`, driven by an independent client, SIGKILLed in the
middle of a session, restarted (the owner recovers at start), and reread.  Every command is recorded with its exit
code, the first line it printed and its wall time; the evidence file ends with
the list of what was *not* exercised and why, because a gate that silently
skips a phase is worse than no gate.

    python3 tools/deploy_gate.py HEAD --host hbox \
        --native-image /tank/fn/scratch/X/build/fn-host \
        --developer-image /tank/fn/scratch/X/build/fn-host-developer

The three outcomes stay distinct in the recorded exit codes (D13): an accepted
`operator post` exits 0, a refused `store inspect` of an absent Message-ID
exits 1, and a post whose durable outcome the owner cannot learn (the
developer image's `postpublish` control cut) exits 3.  The gate asserts that
distinctness rather than assuming it; without `--developer-image` the
uncertain arm is not exercised and says so.

The GATE's own exit is a separate scale with the same discipline.  0 means
every assertion this run stated was decided and held; 1 means one was decided
and violated, or a command exited other than it was expected to; 3 means
nothing was violated but something the run meant to decide it could not, so
the run establishes no release claim; 2 means the gate stopped early.  Before
2026-09-20 the exit read only `Step.failed`, and a scenario could watch its
promised behaviour fail, write the sentence into `gaps`, and exit 0; see
`Finding` below and planning/review-2026-09-20-astra-followup.md F1.

The Python host this gate first drove (tools/run_store.py, run_owner.py,
run_reader.py, bin/fn) retired in python-diet T5; `fn()`, `server_command`
and `certificates` below remain only for tools/twonode_gate.py and
tools/v0_matrix.py, which subclass this gate and retire with the v0 matrix.

Dry run.  ``--dry-run --home DIR`` runs every one of these scripts through
bash on this machine with ``HOME`` pointed at DIR and no ssh at all, so the
sequencing, the port parsing, the kill/restart cut, the exit-code
classification and the evidence rendering are exercised by
tests/test_deploy_gate.py against a stand-in image.
"""
from __future__ import annotations

import argparse
import base64
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
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
SEED_BODY = (b"From: gate@example.invalid\r\nNewsgroups: fn.letters\r\n"
             b"Subject: stored\r\nMessage-ID: <stored@example.invalid>\r\n\r\n"
             b"A stored letter.\r\n")
ABSENT_ID = "<absent@example.invalid>"
UNCERTAIN_ID = "<uncertain@example.invalid>"
POSTED_ID = "<posted@example.invalid>"
GROUPS = ("fn.letters", "fn.test")
NNTP_CLIENTS = ("slrn", "tin", "nn", "trn")
from outcome_codes import EXIT_OK, EXIT_REFUSED, EXIT_UNCERTAIN  # noqa: E402
# The developer image's control cut that loses a post's durable outcome
# (tests/test_native_operator_verbs.py NativeOperatorUncertainOutcomeTests).
UNCERTAIN_CUT = "FN_NATIVE_CONTROL_FAULT=postpublish"
SERVER_READY_SECONDS = 300


def deployment_identity(tree: str, rev: str) -> str:
    """One shell-safe identity shared by the deploy directory and its lock."""
    if not re.fullmatch(r"[A-Za-z0-9._-]+", tree):
        raise ValueError("--tree must contain only letters, digits, dot, dash or underscore")
    if not re.fullmatch(r"[0-9a-fA-F]{7,40}", rev):
        raise ValueError("revision must be 7 to 40 hexadecimal digits")
    return "{}-{}".format(tree, rev.lower())


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


FINDINGS_SCHEMA = 1


def slug(name: str) -> str:
    """A stable ad-hoc key for a non-claim, from the step name that raised it."""
    return re.sub(r"[^a-z0-9]+", "-", name.lower()).strip("-")[:80] or "unnamed"


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
# findings: what a scenario CONCLUDED, which is not what its commands exited
#
# A step's `expect` covers one command's exit code.  A scenario assertion --
# "node B holds the article exactly once", "the second offer draws 435" -- is
# not a command's exit code, and until 2026-09-20 every one of them appended a
# sentence to `gaps` and changed nothing: a gate's exit read only `Step.failed`,
# and a probe declared `expect=None` can never be failed.  The two-node gate
# could therefore watch its promised behaviour fail and still exit 0
# (planning/review-2026-09-20-astra-followup.md, F1).
#
# The vocabulary is `tools/v0_matrix.py`'s, which already keeps five verdicts
# apart over 190 rows: a fixed set of words never collapsed into pass/fail; a
# declared inventory, so a silently skipped item is impossible; one emitter
# that refuses an undeclared CLAIM or an undecided verdict with no blocker;
# and a sha256 over the records, so a verdict cannot be typed in afterwards.
# `violated` is deliberately outside the inventory rule: see `record`.
#
# Where this diverges from that file, and why.  A v0_matrix row is an
# OBSERVATION of a feature, and `accepted`, `refused` and `uncertain` are D13's
# three outcomes, all three of which can be the feature working.  A gate
# finding is a CONCLUSION about an assertion, so its two deciding words are
# `held` and `violated`, and D13's outcomes stay where they already are, in the
# steps' expected exit codes.  The three words that cannot decide are kept
# apart on purpose, because they answer different questions:
#
#   inconclusive   the scenario meant to decide this and could not on this run
#                  -- the instrument was absent, the cut never fired, the count
#                  was not in the reply.  It establishes nothing, so it is not
#                  a pass: exit 3, which is D13's own uncertain code.
#   not-exercised  the assertion was not reached on this run.
#   not-built      the feature it is about is not on this tree yet.
#   limitation     a scope boundary that no run of this gate can cross: a
#                  postpublish fault is indeterminate by construction, the
#                  certificates were copied rather than re-established.  These
#                  are the majority of the old `gaps` list, they are honest,
#                  and failing a gate on them would be the indiscriminate fix
#                  the review rules out.
#
# `limitation` is the line between "this run could not tell" and "no run of
# this harness can tell": the first is a defect in the run and must not
# establish a claim, the second is a property of the harness and is reported
# once.  A limitation therefore never changes the exit code and an
# inconclusive always does.

HELD, VIOLATED, INCONCLUSIVE = "held", "violated", "inconclusive"
NOT_EXERCISED, NOT_BUILT, LIMITATION = "not-exercised", "not-built", "limitation"
FINDINGS = (HELD, VIOLATED, INCONCLUSIVE, NOT_EXERCISED, NOT_BUILT, LIMITATION)
# The two that decide the assertion, and the three that decide nothing.
DECIDED = (HELD, VIOLATED)
UNDECIDED = (INCONCLUSIVE, NOT_EXERCISED, NOT_BUILT)

# The gate process's own exit codes.  0 and 1 are what they were; 3 is new and
# is D13's uncertain, so that an inconclusive run cannot be read as a pass by
# anything that only looks at "did it exit zero".
GATE_OK, GATE_VIOLATED, GATE_ERROR, GATE_INCONCLUSIVE = 0, 1, 2, 3


class Finding:
    """One stated assertion of a scenario, and what this run concluded about it.

    `detail` is the sentence a reader gets: the property, what was seen, and
    what it costs.  `blocker` says why an undecided finding could not be
    decided, and one is required -- an `inconclusive` with no reason is how a
    gap list becomes noise.
    """

    __slots__ = ("key", "instance", "title", "verdict", "detail", "observed",
                 "blocker", "owner", "planned")

    def __init__(self, key, instance, title, verdict, detail, observed="",
                 blocker="", owner="", planned=True):
        self.key = key
        self.instance = instance or ""
        self.title = title
        self.verdict = verdict
        self.detail = detail
        self.observed = observed
        self.blocker = blocker
        self.owner = owner
        self.planned = planned

    @property
    def id(self) -> str:
        return "{}[{}]".format(self.key, self.instance) if self.instance else self.key

    def as_json(self) -> dict:
        return {"id": self.id, "key": self.key, "instance": self.instance,
                "title": self.title, "verdict": self.verdict,
                "detail": self.detail, "observed": self.observed,
                "blocker": self.blocker, "owner": self.owner,
                "planned": self.planned}


class FindingError(RuntimeError):
    """The gate emitted a finding its own inventory does not allow."""


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


# --------------------------------------------------------------------------
# the gate


class DeployGate:
    """The single-node gate.  Its phases, its step accounting and its evidence
    renderer are the machinery a sibling gate reuses by subclassing; the four
    class attributes below are the only things such a subclass must restate."""

    TITLE = "Deploy gate"
    TOOL = "tools/deploy_gate.py"
    # Whether `evidence()` writes the `<evidence>.findings.json` sidecar.
    # `tools/v0_matrix.py` already publishes a richer machine-readable result
    # of its own (`planning/v0-matrix.json`, with its own digest), so it turns
    # this off rather than shipping two files a reader must reconcile.
    FINDINGS_SIDECAR = True
    PREAMBLE = (
        "One commit, unpacked on a farm box, its native image served to real",
        "clients, SIGKILLed mid-session and restarted through the owner's recovery",
        "at start. This records what ran; it establishes nothing about the books",
        "or about which source the named image was built from.")
    FACT_KEYS = ("os", "kernel", "python3", "native image", "developer image",
                 "server", "three outcomes", "verdict")
    # Every assertion this gate can DECIDE, declared before the run.  A key
    # that is never recorded is emitted `not-exercised` at the end rather than
    # vanishing, which is `tools/v0_matrix.py`'s PLAN discipline: a silently
    # skipped assertion is impossible.  The value is (one-line property, the
    # instances it is stated over; ("",) when there is only one).
    #
    # Only the DECIDING keys are declared.  A `skip` and a `limitation` are
    # non-claims -- they say what this run does not show -- so they carry an
    # ad-hoc key and are recorded `planned: false`; a claim must be declared
    # here before it can be made.
    ASSERTIONS: dict[str, tuple[str, tuple[str, ...]]] = {
        "outcomes-distinct": (
            "accepted, refused and uncertain stay distinct in the exit codes (D13)",
            ("",)),
        "post-capability": (
            "CAPABILITIES lists POST exactly when posting is permitted "
            "(RFC 3977 5.2.2)", ("",)),
        "certificates-match": (
            "every certificate pair installed hashes to this revision's source",
            ("",)),
        "entry-point-listening": (
            "the server entry point this gate selected reached LISTENING", ("",)),
    }
    STANDING_GAPS = (
        "A SIGKILL of the server process is not a power loss: unflushed page cache\n"
        "  is not modeled here, and nothing in this run qualifies storage hardware.",
        "One kill point (inside an open POST) is exercised. The enumerated cuts are\n"
        "  tests/campaign/native_operator_campaign.py and native_production_kill.py.",
        "No RFC 3977 conformance audit: the transcript exercises the verbs listed\n"
        "  above and no others, and the assertions are the driver's, not a spec's.",
        "No concurrent load, no multi-host peering, no BP/DTN transport.")

    def __init__(self, host: Host, repo: Path, commit: str, rev: str, tree: str,
                 overlay: Path | None = None, jobs: int = 16, keep: bool = False,
                 nntplib_python: str = "auto", acl2: str = "acl2",
                 artifact_profile: str = "default", native_image: str = "",
                 developer_image: str = "", native_openssl_prefix: str = ""):
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
        self.artifact_profile = artifact_profile
        self.native_image = native_image
        self.developer_image = developer_image
        self.native_openssl_prefix = native_openssl_prefix
        self.steps: list[Step] = []
        self.facts: dict[str, str] = {}
        self.found: list[Finding] = []
        self.deploy_id = deployment_identity(tree, rev)
        self.deploy = "{}/{}".format(DEPLOY_ROOT, self.deploy_id)
        self.deploy_lock = "{}/.locks/{}.lock".format(DEPLOY_ROOT, self.deploy_id)
        self.deploy_lock_acquired = False
        self.run = "{}/gate-run".format(self.deploy)
        self.store = "{}/store".format(self.run)
        self.log = "{}/server.log".format(self.run)
        self.node_dir = "{}/node".format(self.deploy)
        self.config = "{}/fn.toml".format(self.node_dir)
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

    def skip(self, name, command, reason, *, key=None, verdict=NOT_EXERCISED,
             owner=""):
        """A step that did not run, with the reason, as a step AND a finding.

        The default verdict is `not-exercised`: this run did not reach it.
        Pass `verdict=NOT_BUILT` when the feature is not on the tree at all --
        the review's "an unavailable feature may legitimately be unexercised"
        is that case, and it is reported, not failed."""
        self.steps.append(not_exercised(name, command, reason))
        self.record(key or slug(name), verdict, "{}: {}".format(name, reason),
                    blocker=reason, owner=owner, planned=False, title=name)
        return self.found[-1]

    # -- findings ---------------------------------------------------------
    def record(self, key, verdict, detail, *, instance="", observed="",
               blocker="", owner="", planned=None, title="") -> Finding:
        """The ONLY way a finding is created.  It refuses what it cannot check.

        `held` is the CLAIM, so its key must be in `ASSERTIONS` with this
        instance declared; an undecided verdict must name its blocker; an
        unknown verdict stops the gate.  Each of those is a defect in the
        gate, not in the tree, and a gate that records a verdict it cannot
        justify is the thing this whole file exists to stop."""
        if verdict not in FINDINGS:
            raise FindingError("{}: verdict {!r} is not one of {}".format(
                key, verdict, FINDINGS))
        declared = self.ASSERTIONS.get(key)
        if planned is None:
            planned = declared is not None
        if planned:
            if declared is None:
                raise FindingError(
                    "{}: a planned finding must be declared in ASSERTIONS".format(key))
            if instance not in declared[1]:
                raise FindingError("{}: instance {!r} is not one of {}".format(
                    key, instance, declared[1]))
            title = title or declared[0]
        if verdict == HELD and not planned:
            raise FindingError(
                "{}: held is a CLAIM, so it must be declared in ASSERTIONS".format(key))
        # `violated` is deliberately allowed without a declaration.  The
        # inventory exists to stop a gate claiming success for something it
        # never planned to check; refusing to RECORD a failure because
        # nobody declared it would be that rule pointed the wrong way, and a
        # violation can only ever make the verdict worse.
        if verdict in UNDECIDED and not blocker:
            raise FindingError("{}: a {} finding must name its blocker".format(
                key, verdict))
        found = Finding(key, instance, title or key, verdict, detail,
                        observed=observed, blocker=blocker, owner=owner,
                        planned=planned)
        self.found.append(found)
        return found

    def check(self, key, ok: bool, detail, *, instance="", observed="",
              held_detail="") -> Finding:
        """Decide one declared assertion.  `ok` is the observation, not a wish.

        `detail` is what the record says when it does NOT hold, which is the
        sentence the old `gaps.append` carried; `held_detail` is the one-line
        confirmation when it does."""
        if ok:
            return self.record(key, HELD, held_detail or self.ASSERTIONS[key][0],
                               instance=instance, observed=observed)
        return self.record(key, VIOLATED, detail, instance=instance,
                           observed=observed)

    def inconclusive(self, key, detail, blocker, *, instance="",
                     observed="") -> Finding:
        """This run could not decide a declared assertion.  Exit 3, never 0."""
        return self.record(key, INCONCLUSIVE, detail, instance=instance,
                           observed=observed, blocker=blocker)

    def not_built(self, key, detail, blocker, *, instance="", owner="") -> Finding:
        return self.record(key, NOT_BUILT, detail, instance=instance,
                           blocker=blocker, owner=owner)

    def limitation(self, key, detail) -> Finding:
        """A scope boundary of the harness itself.  Reported, never failed.

        `key` may be None, in which case it is taken from the text: a
        limitation is not a claim, so its identifier is a handle for the
        record rather than a promise anything else cites."""
        key = key or slug(detail)
        return self.record(key, LIMITATION, detail, planned=False, title=key)

    def finalize_findings(self):
        """Every declared assertion the run never reached, said out loud."""
        seen = {(one.key, one.instance) for one in self.found}
        for key in self.ASSERTIONS:
            title, instances = self.ASSERTIONS[key]
            for instance in instances:
                if (key, instance) in seen:
                    continue
                self.record(key, NOT_EXERCISED,
                            "{}{}: the run ended without reaching this assertion, "
                            "so nothing here establishes it.".format(
                                title, " ({})".format(instance) if instance else ""),
                            instance=instance,
                            blocker="the run ended before this assertion was reached")

    @property
    def gaps(self) -> list[str]:
        """Everything this run does NOT establish, in the order it was found.

        The old list of the same name, now derived: a finding that held is not
        a gap, and everything else is."""
        return [one.detail for one in self.found if one.verdict != HELD]

    def counts(self) -> dict:
        return {verdict: sum(1 for one in self.found if one.verdict == verdict)
                for verdict in FINDINGS}

    def verdict(self) -> str:
        """One word for the whole run, from the findings alone."""
        tally = self.counts()
        if tally[VIOLATED] or any(step.failed for step in self.steps):
            return VIOLATED
        if tally[INCONCLUSIVE]:
            return INCONCLUSIVE
        return HELD

    def exit_code(self, failure=None) -> int:
        if failure:
            return GATE_ERROR
        return {VIOLATED: GATE_VIOLATED, INCONCLUSIVE: GATE_INCONCLUSIVE,
                HELD: GATE_OK}[self.verdict()]

    def findings_document(self, rev: str, tool: str) -> dict:
        """The machine-readable result, with the digest that refuses a typed one."""
        rows = [one.as_json() for one in self.found]
        digest = hashlib.sha256(json.dumps(
            rows, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
        return {"schema": FINDINGS_SCHEMA, "tool": tool, "revision": rev,
                "verdicts": list(FINDINGS), "counts": self.counts(),
                "verdict": self.verdict(), "rows": rows, "rows_digest": digest}

    def broke(self, name, command, reason, *, key=None):
        """This step's subject failed.  A FAILED row AND a violated finding.

        The distinction this keeps from `skip`: a build script that ran and
        returned non-zero is a BROKEN subject, not an absent one, and a lab
        that ran and said nothing about a scenario it owns is a silence, not
        an absence.  See `did_not_complete`."""
        self.steps.append(did_not_complete(name, command, reason))
        self.record(key or slug(name), VIOLATED, "{}: {}".format(name, reason),
                    planned=False, title=name)
        return self.found[-1]

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
        lock = self.sh("acquire deploy lock", """
mkdir -p {root}/.locks
if ! mkdir {lock} 2>/dev/null; then
  echo "deploy identity is already active: {identity}"
  exit 73
fi
""".format(root=DEPLOY_ROOT, lock=self.deploy_lock, identity=self.deploy_id))
        if lock.rc != 0:
            raise GateError(lock.first_line or "deploy identity is already active")
        self.deploy_lock_acquired = True
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

    def release_deploy_lock(self):
        """Release this tree+revision's lock; safe to call once at cleanup."""
        if not self.deploy_lock_acquired:
            return None
        step = self.sh("release deploy lock", "rmdir {}".format(self.deploy_lock),
                       expect=None)
        if step.rc == 0:
            self.deploy_lock_acquired = False
        return step

    def certificates(self):
        """Acquire one coherent set and prove that ACL2 can load it."""
        cache = FARM_HOSTS.get(self.host.label, {}).get(
            "cache", "$HOME/.cache/fn-certs")
        acquire = self.sh(
            "acquire certificate artifact set",
            self.cd("python3 tools/proof_artifacts.py acquire "
                    "--profile {profile} --root {deploy} --cache {cache} "
                    "--acl2 \"$FN_ACL2\"".format(
                        profile=self.artifact_profile, deploy=self.deploy,
                        cache=cache)), timeout=3600, expect=None,
            note="one absolute origin, one ACL2 executable digest, then an actual ACL2 load")
        if acquire.rc == 0:
            self.facts["certificates"] = acquire.output.strip().splitlines()[-1]
            self.facts["native artifact profile"] = self.artifact_profile
            self.check("certificates-match", True, "", observed=acquire.first_line,
                       held_detail="one current origin/toolchain artifact set loaded "
                                   "without ACL2 errors or uncertified warnings")
            self.certificates_ok = True
            return acquire

        roots = "$(python3 tools/proof_artifacts.py roots --profile {profile})".format(
            profile=self.artifact_profile)
        certified = self.sh(
            "certify declared artifact closure",
            self.cd("export FN_CERT_CACHE={cache}\n"
                    "export FN_CERT_ORIGIN_KIND=gate\n"
                    "python3 tools/certify_books.py --jobs {jobs} --closure {roots}".format(
                        cache=cache, jobs=self.jobs, roots=roots)), timeout=6 * 3600,
            note="bounded to the selected native image and deployed entry points")
        loaded = self.sh(
            "load declared artifact closure",
            self.cd("python3 tools/proof_artifacts.py validate --profile {profile} "
                    "--root {deploy} --acl2 \"$FN_ACL2\"".format(
                        profile=self.artifact_profile, deploy=self.deploy)),
            timeout=3600)
        self.facts["native artifact profile"] = self.artifact_profile
        self.facts["certificates"] = (
            "cache acquisition rc={}; bounded certification rc={}; load rc={}: {}"
            .format(acquire.rc, certified.rc, loaded.rc, loaded.first_line))
        ok = certified.rc == 0 and loaded.rc == 0
        self.check(
            "certificates-match", ok,
            "no current coherent cache set loaded and the bounded certification/load "
            "failed: acquire rc={}, certify rc={}, load rc={}".format(
                acquire.rc, certified.rc, loaded.rc),
            observed=self.facts["certificates"],
            held_detail="the selected native image and deployed entry-point closure "
                        "was certified on this host and then loaded without ACL2 "
                        "errors or uncertified warnings")
        self.certificates_ok = ok
        if not ok:
            raise GateError("declared certificate artifact closure did not load")
        return loaded

    # -- the native node ----------------------------------------------------
    def native(self, *words, image=None, env="") -> str:
        """The packaged public entry, from the shipped tree, with the named image.

        `env` in front because the owner is started as `nohup <command> &` and
        nohup execs its first word."""
        if self.native_openssl_prefix:
            env += "FN_OPENSSL_PREFIX={} ".format(shlex.quote(self.native_openssl_prefix))
        return "env {}FN_NATIVE_HOST={} packaging/fn-native {}".format(
            env, shlex.quote(image or self.native_image), " ".join(words))

    def operator(self, *words, image=None, env="") -> str:
        return self.native("operator", self.config, *words, image=image, env=env)

    def native_node(self):
        """fn.toml (a free loopback port, posting on), then `operator init`."""
        self.sh("fn.toml", """
mkdir -p {node}
port=$(python3 -c 'import socket; s = socket.socket(); s.bind(("127.0.0.1", 0)); print(s.getsockname()[1])')
cat > {config} <<FN_TOML
[store]
path = "{node}/store"

[listener]
host = "127.0.0.1"
port = $port

[posting]
enabled = true

[control]
path = "{node}/control.sock"
FN_TOML
cat {config}
""".format(node=self.node_dir, config=self.config))
        init = self.sh("operator init", self.cd(self.operator("init", *GROUPS)),
                       timeout=900)
        if init.rc != 0:
            raise GateError("operator init failed: " + init.output[:400])

    def three_outcomes(self):
        """Accepted 0, refused 1, uncertain 3, from the image's own entries."""
        payload = "{}/seed.article".format(self.run)
        self.push_file(SEED_BODY, payload)
        accepted = self.sh("outcome accepted", self.cd(self.operator(
            "post", "--message-id", "'{}'".format(SEED_ID), "--payload", payload,
            "--group", GROUPS[0])), timeout=900, expect=EXIT_OK)
        refused = self.sh("outcome refused", self.cd(self.native(
            "store", "{}/store".format(self.node_dir), "inspect",
            "'{}'".format(ABSENT_ID))), timeout=900, expect=EXIT_REFUSED)
        if not self.developer_image:
            self.facts["three outcomes"] = "accepted={} refused={} uncertain=not run".format(
                accepted.rc, refused.rc)
            self.record("outcomes-distinct", NOT_EXERCISED,
                        "accepted={} refused={}; the uncertain arm was not run".format(
                            accepted.rc, refused.rc),
                        blocker="no --developer-image: the uncertain outcome is a "
                                "developer-image cut ({}); tests/test_native_operator_"
                                "verbs.py NativeOperatorUncertainOutcomeTests carries "
                                "it".format(UNCERTAIN_CUT))
            return
        if not self.start_server("owner (developer, postpublish cut)", self.operator(
                "run", image=self.developer_image, env=UNCERTAIN_CUT + " "), "uncertain"):
            self.broke("outcome uncertain", "operator run with " + UNCERTAIN_CUT,
                       "the developer owner did not reach LISTENING: {}".format(
                           self.server_failure or "no symptom recorded"))
            return
        uncertain = self.sh("outcome uncertain", self.cd(self.operator(
            "post", "--message-id", "'{}'".format(UNCERTAIN_ID), "--payload", payload,
            "--group", GROUPS[0])), timeout=900, expect=EXIT_UNCERTAIN)
        # The owner fences itself on the same observation and releases the store.
        self.sh("the owner fenced itself", """
pid=$(cat {run}/server.pid)
for i in $(seq 1 60); do kill -0 $pid 2>/dev/null || {{ echo FENCED; exit 0; }}; sleep 1; done
echo STILL-RUNNING; exit 1
""".format(run=self.run), timeout=120)
        self.stop_server("uncertain")
        self.sh("recover after the uncertain publication",
                self.cd(self.operator("recover")), timeout=900)
        observed = (accepted.rc, refused.rc, uncertain.rc)
        expected = (EXIT_OK, EXIT_REFUSED, EXIT_UNCERTAIN)
        self.facts["three outcomes"] = "accepted={} refused={} uncertain={} (expected {})".format(
            *observed, expected)
        self.check("outcomes-distinct", observed == expected,
                   "the three outcomes did not stay distinct in the exit codes: "
                   "observed {}, expected {} (D13)".format(observed, expected),
                   observed="accepted={} refused={} uncertain={}".format(*observed))

    def server_command(self, store=None, run=None) -> tuple[str, str]:
        """(tools/twonode_gate.py and tools/v0_matrix.py only: their Python-host
        entry points.)  bin/fn when it can be pointed at this store, else the
        owner, else the reader.

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
            self.limitation(
                "bin-fn-config-driven",
                "bin/fn is in this tree but its `run` is configuration-file driven and "
                "takes no --store, and this gate does not author a configuration for it. "
                "The gate drove tools/run_owner.py, the entry point bin/fn wraps, so the "
                "service wrapper's own argument handling and logging are not exercised.")
            kind = "owner"
        if kind == "owner":
            # 32, not the owner's default 8. A two-node run holds a
            # persistent feed connection in each direction, a wire tap's
            # backend session per feed dial, and the harness's own probes;
            # on gate run `ea76826` node B reached the bound and closed
            # four steps' connections at accept, which reads as
            # "server closed the connection". That the bound is reachable
            # at all in a two-node run is a finding, recorded on the board;
            # this is the harness giving itself room, not a fix for it.
            return kind, ("python3 tools/run_owner.py --store {} --port 0 "
                          "--max-connections 32 --control {}/control.sock".format(
                              store, run))
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
        """tests/interop_nntplib.py against the running owner (Python <= 3.12)."""
        if self.nntplib_python == "none":
            self.skip("nntplib probe", "tests/interop_nntplib.py",
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
            # waiver-ok: environment -- the chooser prints USE or NONE; NONE is
            # the predicate "no interpreter here has a stdlib nntplib".
            self.skip("nntplib probe", "tests/interop_nntplib.py",
                      "no interpreter on the host has a stdlib nntplib "
                      "(python3 is {}; nntplib was removed in 3.13 by PEP 594 and no "
                      "3.12 or earlier interpreter is installed)".format(
                          self.facts.get("python3", "unknown")))
            return
        self.sh("nntplib probe", self.cd("{} tests/interop_nntplib.py {} --group {}".format(
            match.group(1), self.port, GROUPS[0])), timeout=300,
            note="independent client: {}".format(match.group(1)))

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
        if not self.native_image:
            raise GateError("the served node is the native image: --native-image "
                            "(its path on the box) is required")
        self.facts["native image"] = self.native_image
        if self.developer_image:
            self.facts["developer image"] = self.developer_image
        self.preflight()
        self.ship()
        self.native_node()
        self.three_outcomes()
        command = self.operator("run")
        started = self.start_server("owner", command, "main")
        self.check("entry-point-listening", started,
                   "the native owner did not reach LISTENING on this commit: {}".format(
                       self.server_failure or "no symptom recorded"),
                   observed="started={}".format(started))
        if not started:
            raise GateError("the native owner did not reach LISTENING")
        transcript = self.drive("transcript", "--group {}".format(GROUPS[0]))
        self.check("post-capability", '"post_offered": false' not in transcript.output,
                   "posting is enabled in fn.toml and the owner answers POST with 340 "
                   "(see the kill cut below), but its CAPABILITIES block does not list "
                   "POST (RFC 3977 section 5.2.2).",
                   observed=transcript.first_line)
        concurrent = self.drive("concurrent", "--group {} --msgid '{}'".format(
            GROUPS[0], POSTED_ID))
        if concurrent.rc == 0:
            self.posted.append(POSTED_ID)
        pid = self.sh("server pid", "cat {}/server.pid".format(self.run)).output.strip()
        self.drive("killcut", "--group {} --msgid '<interrupted@example.invalid>' --pid {}".format(
            GROUPS[0], pid), name="kill -9 mid-session")
        self.sh("server is gone", "kill -0 {} 2>/dev/null && echo ALIVE || echo GONE".format(pid))
        if self.start_server("owner", command, "after-recovery"):
            self.drive("reread", "--groups {} --msgids '{}'".format(
                ",".join(GROUPS), ",".join(self.posted)), name="reread after recovery")
            self.nntplib_probe()
            self.news_client()
            self.stop_server("after-recovery")
        else:
            # The subject of this gate is "serves, dies and recovers".  An owner
            # that started before the kill and will not start after it is that
            # subject failing, not a dependency this box lacks.
            self.broke("reread after recovery", "drive.py reread",
                       "the owner did not restart after the kill: {}".format(
                           self.server_failure or "no symptom recorded"))
        self.sh("status after the run", self.cd(self.operator("status")),
                timeout=900, expect=None)
        self.sh("server log tail", "tail -15 {}/server-main.log".format(self.run))
        if not self.keep:
            self.sh("remove the deploy tree", "rm -rf {}".format(self.deploy))
        self.release_deploy_lock()

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
        # A fact recorded under a name the class did not enumerate is still a
        # measurement. Dropping it silently is how a number that was measured
        # disappears from the record; the enumeration is an ORDER, not a
        # filter.
        for key in sorted(self.facts):
            if key not in self.FACT_KEYS:
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
        tally = self.counts()
        lines += [
            "",
            "## Findings",
            "",
            "One row per stated assertion. `held` and `violated` are the two that",
            "DECIDE it; `inconclusive` means this run could not decide it and so",
            "establishes nothing; `not-exercised` and `not-built` mean it was not",
            "reached and why; `limitation` is a scope boundary no run of this",
            "harness crosses.",
            "",
            "The process exit is {} for a violation, {} for an inconclusive run "
            "with no violation, {} when the gate stopped early, {} otherwise.".format(
                GATE_VIOLATED, GATE_INCONCLUSIVE, GATE_ERROR, GATE_OK),
            "",
            "Verdict of this run: **{}** ({}).".format(
                self.verdict(),
                ", ".join("{} {}".format(tally[v], v) for v in FINDINGS if tally[v])
                or "no findings"),
            "",
            "| assertion | verdict | what it says |",
            "| --- | --- | --- |",
        ]
        for one in self.found:
            lines.append("| {} | {} | {} |".format(
                one.id.replace("|", "\\|"), one.verdict,
                one.detail.replace("|", "\\|").replace("\n", " ")))
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
        # The machine-readable half, beside the prose one.  The digest is what
        # a hand-typed verdict cannot survive: change a word in a row and it
        # no longer matches, exactly as `tools/v0_matrix.py` does it.
        if self.FINDINGS_SIDECAR:
            findings = path.with_suffix(".findings.json")
            findings.write_text(json.dumps(
                self.findings_document(self.rev, self.TOOL), indent=2) + "\n")
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


def report(gate) -> None:
    """The last lines of stdout: the contract `tools/verdict.py` reads.

    `steps=/failed=/not-exercised=` is unchanged so that reader keeps working;
    `violated=` and `inconclusive=` are appended because a step count was
    never the verdict -- an assertion violated inside a probe declared
    `expect=None` moved neither of the first two numbers."""
    bad = [s for s in gate.steps if s.failed]
    tally = gate.counts()
    print("steps={} failed={} not-exercised={} violated={} inconclusive={}".format(
        len(gate.steps), len(bad), sum(1 for s in gate.steps if s.rc is None),
        tally[VIOLATED], tally[INCONCLUSIVE]))
    print("verdict={} findings={}".format(
        gate.verdict(),
        " ".join("{}={}".format(v, tally[v]) for v in FINDINGS if tally[v]) or "none"))
    for step in bad:
        print("  FAILED rc={} {}: {}".format(step.rc, step.name, step.first_line))
    for one in gate.found:
        if one.verdict == VIOLATED:
            print("  FAILED assertion {}: {}".format(one.id, one.detail[:300]))
    for one in gate.found:
        if one.verdict == INCONCLUSIVE:
            print("  INCONCLUSIVE {}: {}".format(one.id, one.detail[:300]))


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
    parser.add_argument("--native-image", default="",
                        help="the production image's path on the box (the served node)")
    parser.add_argument("--developer-image", default="",
                        help="the developer image's path on the box, for the uncertain "
                             "outcome's control cut (else that arm is not exercised)")
    parser.add_argument("--native-openssl-prefix", default="",
                        help="FN_OPENSSL_PREFIX for the image, when the box needs one")
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
    try:
        gate = DeployGate(
            host, repo, commit, rev, args.tree, overlay=overlay,
            jobs=args.jobs, keep=args.keep,
            nntplib_python=args.nntplib_python,
            acl2=args.acl2 or FARM_HOSTS.get(args.host, {}).get("acl2", "acl2"),
            native_image=args.native_image, developer_image=args.developer_image,
            native_openssl_prefix=args.native_openssl_prefix)
    except ValueError as error:
        parser.error(str(error))
    started = dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    clock = time.monotonic()
    failure = None
    try:
        gate.execute()
    except GateError as error:
        failure = str(error)
        gate.limitation("gate-stopped-early",
                        "the gate stopped early: {}".format(error))
        gate.release_deploy_lock()
    elapsed = time.monotonic() - clock
    gate.finalize_findings()
    date = dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%d")
    target = evidence_path(args.evidence, repo,
                           "deploy-{}-{}.md".format(rev, date))
    gate.evidence(target, started, elapsed)
    print("evidence: {}".format(target))
    report(gate)
    if failure:
        print("gate error: {}".format(failure))
    return gate.exit_code(failure)


if __name__ == "__main__":
    sys.exit(main())
