"""The native cut campaign driven through the public operator verb.

Run on the box that holds a frozen image directory:

    python3 -m tests.campaign.native_operator_campaign \
        --images /abs/build/images/<rev> --work /abs/scratch --out result.json

For every cut of `native_cuts.ALL_CUTS` it records two observations over
fresh stores, each seeded with one prior article posted through
`operator CFG post` to a running `operator CFG run` owner:

served   the owner restarted with the cut's selector in its environment and
         the candidate posted through `operator CFG post`: the path the node
         serves.  Since the fix of campaign dabebb84 F1 the served owner reads
         the same selectors `store ROOT post` reads (`fnn-post-entry-fault`,
         host/native/io.lisp, called by `fnn-owner-run-normalized`), so the
         owner itself dies at the cut.  A recovery cut is taken by the owner's
         own recovery at start.  Then `operator CFG recover`, `store ROOT
         inspect`, a restarted owner's NNTP ARTICLE, and a resubmission.
cut      the candidate posted through `store ROOT post` with the selector
         (`fnn-command-post`), or `operator CFG recover` for a recovery cut,
         then the same recovery and rereads.

It also runs the developer faults once each, and every registered developer
selector against the production image, which must refuse to start with it
(exit 5, `fnn-developer-selector-gate`) before any store is opened.  It
judges nothing: the evidence file compares the observations with the table.
Exit codes are recorded raw; a negative code is the signal that ended the
process (subprocess convention).
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import select
import shutil
import signal
import socket
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(ROOT))
from tests.campaign import native_cuts  # noqa: E402

GROUP = "fn.letters"
PRIOR_ID = "<prior@campaign.invalid>"
CANDIDATE_ID = "<candidate@campaign.invalid>"
# One more than the staging observation bound (`*fn-sn-max-staging-observation*'
# = 64, books/store-sweep.lisp), the count campaign dabebb84 F2 measured.
ALLOCATION_DEATHS = 65
RECOVER_LINE = re.compile(
    rb"recovered transactions=(\d+) articles=(\d+) staging-orphans=(\d+)")


def article(message_id: str, subject: str, body: str) -> bytes:
    return ("From: campaign@campaign.invalid\r\nNewsgroups: {}\r\n"
            "Subject: {}\r\nMessage-ID: {}\r\n\r\n{}\r\n").format(
                GROUP, subject, message_id, body).encode("ascii")


def parse_recover(stdout: bytes) -> dict | None:
    """The three counts of `fnn-command-recover`'s report line, or None."""
    match = RECOVER_LINE.search(stdout)
    if not match:
        return None
    return {"transactions": int(match.group(1)), "articles": int(match.group(2)),
            "staging_orphans": int(match.group(3))}


# The fields the owner's injection adds ahead of a proto-article's own header
# (books/owner.lisp fn-own-operator-submit, host/native/owner.lisp
# fnn-owner-control-submit-serialized; Date only when the proto-article has
# none).  Since a0b6d41f `operator CFG post` stores the injected article, not
# the payload, so its bytes carry the owner's clock and cannot be predicted.
INJECTED_FIELDS = (b"path", b"injection-date", b"injection-info", b"date")


def split_article(octets: bytes) -> tuple[list[bytes], bytes] | None:
    head, sep, body = octets.partition(b"\r\n\r\n")
    if not sep:
        return None
    return head.split(b"\r\n"), body


def injected_from(stored: bytes, payload: bytes) -> bool:
    """`stored` is `payload` with only injection fields added ahead of its header.

    The body and every header line of the payload are kept, in order, as the
    tail of the stored header; each added line is one of INJECTED_FIELDS, at
    most once, and none of them duplicates a field the payload already had.
    """
    got, want = split_article(stored), split_article(payload)
    if got is None or want is None or got[1] != want[1]:
        return False
    stored_head, payload_head = got[0], want[0]
    added = len(stored_head) - len(payload_head)
    if added < 0 or stored_head[added:] != payload_head:
        return False
    names = [line.partition(b":")[0].strip().lower() for line in stored_head[:added]]
    present = {line.partition(b":")[0].strip().lower() for line in payload_head}
    return (all(name in INJECTED_FIELDS for name in names)
            and len(set(names)) == len(names) and not present & set(names))


def matches(stored: bytes, reference: bytes, injected: bool) -> bool:
    return injected_from(stored, reference) if injected else stored == reference


def undot(lines: list[bytes]) -> bytes:
    """RFC 3977 §3.1.1 multi-line block (terminator already removed) to octets."""
    return b"".join(line[1:] if line.startswith(b"..") else line for line in lines)


def free_port() -> int:
    with socket.socket() as s:
        s.bind(("127.0.0.1", 0))
        return s.getsockname()[1]


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def snapshot(store: Path) -> dict:
    def listing(name):
        d = store / name
        return {p.name: sha(p.read_bytes()) for p in sorted(d.iterdir())
                if p.is_file()} if d.is_dir() else None
    frontier = store / "allocation-frontier.json"
    return {"transactions": listing("transactions"),
            "staging": listing("staging"),
            "frontier": frontier.read_text("ascii", "replace")
            if frontier.is_file() else None}


class Node:
    def __init__(self, image: Path, base: Path, name: str):
        self.image, self.dir = image, base / name
        self.dir.mkdir(parents=True)
        self.store = self.dir / "store"
        self.control = self.dir / "control.sock"
        self.port = free_port()
        self.config = self.dir / "fn.toml"
        self.config.write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
            '[control]\npath = "{}"\n'.format(self.store, self.port, self.control),
            encoding="ascii")
        self.owners: list[dict] = []
        self.prior_stored: bytes | None = None

    def env(self, extra=None):
        env = {k: v for k, v in os.environ.items()
               if not k.startswith("FN_NATIVE_")}
        env["ACL2_CUSTOMIZATION"] = "NONE"
        env.pop("ACL2_SYSTEM_BOOKS", None)
        env.update(extra or {})
        return env

    def run(self, argv, extra=None, timeout=300) -> dict:
        started = time.monotonic()
        try:
            result = subprocess.run([str(self.image), "--fn", *argv],
                                    env=self.env(extra), cwd=self.dir,
                                    stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                    timeout=timeout, check=False)
            rc, out, err = result.returncode, result.stdout, result.stderr
        except subprocess.TimeoutExpired as expired:
            rc, out, err = "timeout", expired.stdout or b"", expired.stderr or b""
        return {"argv": ["IMAGE", "--fn", *map(str, argv)],
                "env": dict(extra or {}), "rc": rc,
                "stdout": out.decode("utf-8", "replace")[-2000:],
                "stderr": err.decode("utf-8", "replace")[-2000:],
                "seconds": round(time.monotonic() - started, 2), "_out": out}

    def operator(self, *words, extra=None, timeout=300):
        return self.run(["operator", str(self.config), *words], extra, timeout)

    def post(self, msgid, payload: Path, extra=None, timeout=300):
        return self.operator("post", "--message-id", msgid, "--payload",
                             str(payload), "--group", GROUP,
                             extra=extra, timeout=timeout)

    def store_post(self, msgid, payload: Path, extra=None, inject="-"):
        return self.run(["store", str(self.store), "post", msgid, str(payload),
                         "-", inject, GROUP], extra)

    def inspect(self, msgid):
        return self.run(["store", str(self.store), "inspect", msgid])

    def start_owner(self, extra=None) -> dict:
        log = open(self.dir / "owner-{}.err".format(len(self.owners)), "wb")
        proc = subprocess.Popen([str(self.image), "--fn", "operator",
                                 str(self.config), "run"], env=self.env(extra),
                                cwd=self.dir, stdout=subprocess.PIPE, stderr=log,
                                bufsize=0)
        owner = {"pid": proc.pid, "env": dict(extra or {}), "proc": proc,
                 "log": log, "ready": False, "lines": []}
        self.owners.append(owner)
        deadline = time.monotonic() + 240
        while time.monotonic() < deadline:
            if not select.select([proc.stdout], [], [], 5)[0]:
                if proc.poll() is not None:
                    break
                continue
            line = proc.stdout.readline()
            if not line:
                break
            owner["lines"].append(line.decode("utf-8", "replace").strip())
            if line.startswith(b"LISTENING "):
                owner["ready"] = True
                break
        return owner

    def stop_owner(self, owner, sig=signal.SIGTERM) -> dict:
        proc = owner["proc"]
        if proc.poll() is None:
            os.kill(owner["pid"], sig)
            if sig == signal.SIGKILL:
                os.kill(owner["pid"], signal.SIGCONT)
        try:
            rc = proc.wait(timeout=120)
        except subprocess.TimeoutExpired:
            os.kill(owner["pid"], signal.SIGKILL)
            rc = ("timeout", proc.wait(timeout=30))
        rest = proc.stdout.read() or b""
        proc.stdout.close()
        owner["lines"] += rest.decode("utf-8", "replace").split("\n")
        owner["log"].close()
        owner["stopped_by"] = signal.Signals(sig).name
        owner["rc"] = rc
        owner["stderr"] = (self.dir / Path(owner["log"].name).name).read_text(
            "utf-8", "replace")[-2000:]
        return public(owner)

    def reap(self):
        for owner in self.owners:
            if owner["proc"].poll() is None:
                os.kill(owner["pid"], signal.SIGKILL)
                os.kill(owner["pid"], signal.SIGCONT)
                owner["proc"].wait(timeout=30)
            if not owner["proc"].stdout.closed:
                owner["proc"].stdout.close()

    def nntp_article(self, msgid) -> dict:
        with socket.create_connection(("127.0.0.1", self.port), timeout=60) as conn:
            stream = conn.makefile("rb")
            greeting = stream.readline()
            conn.sendall("ARTICLE {}\r\n".format(msgid).encode("ascii"))
            status = stream.readline()
            lines = []
            if status.startswith(b"220"):
                while True:
                    line = stream.readline()
                    if line in (b".\r\n", b""):
                        break
                    lines.append(line)
            conn.sendall(b"QUIT\r\n")
        return {"greeting": greeting.decode("ascii", "replace").strip(),
                "status": status.decode("ascii", "replace").strip(),
                "octets": undot(lines)}


def public(record):
    return {k: v for k, v in record.items()
            if k not in ("proc", "log", "_out")}


def seed(node: Node, prior: Path, out: dict):
    out["init"] = public(node.operator("init", GROUP))
    owner = node.start_owner()
    out["seed_owner_ready"] = owner["ready"]
    out["seed_post"] = public(node.post(PRIOR_ID, prior))
    out["seed_owner"] = node.stop_owner(owner)
    out["seeded"] = snapshot(node.store)
    # The prior's durable bytes, the reference every later reread must equal.
    stored = node.inspect(PRIOR_ID)
    out["seed_inspect_prior"] = {"rc": stored["rc"],
                                 "sha256": sha(stored["_out"]),
                                 "injected": injected_from(
                                     stored["_out"], node.dir.parent.joinpath(
                                         "prior.art").read_bytes())}
    node.prior_stored = stored["_out"]


def reread(node: Node, candidate: bytes, out: dict, injected: bool):
    """Both articles through `store ROOT inspect` and a restarted owner's ARTICLE.

    The prior must equal the bytes `seed` read back when it was durable.  The
    candidate must equal its payload when `store ROOT post` wrote it, and be
    the payload's injected form when the owner did (`injected`); the two
    readers must also return the same octets.

    The candidate is resubmitted through the entry that first submitted it:
    `operator CFG post` to the restarted owner when the owner injected it,
    `store ROOT post` after the owner stops otherwise.  The two entries store
    different octets for one payload; under D25 the Store compares the
    poster's bytes, so a retry through the other entry is still the
    duplicate (the `cross-entry-retry` fault row).
    """
    checks = (("prior", PRIOR_ID, node.prior_stored, False),
              ("candidate", CANDIDATE_ID, candidate, injected))
    read = {}
    for label, msgid, want, inj in checks:
        got = node.inspect(msgid)
        read[label] = got["_out"] if got["rc"] == 0 else None
        out["inspect_" + label] = {"rc": got["rc"],
                                   "identical": matches(got["_out"], want, inj),
                                   "sha256": sha(got["_out"]),
                                   "stderr": got["stderr"][-300:]}
    out["candidate_injected"] = injected
    owner = node.start_owner()
    out["reread_owner_ready"] = owner["ready"]
    if owner["ready"]:
        for label, msgid, want, inj in checks:
            got = node.nntp_article(msgid)
            out["nntp_" + label] = {
                "status": got["status"],
                "identical": matches(got["octets"], want, inj),
                "same_as_inspect": (read[label] == got["octets"]
                                    if read[label] is not None else None)}
        if injected:
            out["resubmit"] = public(node.post(CANDIDATE_ID, node.dir.parent / "candidate.art"))
            out["after_resubmit"] = snapshot(node.store)
    out["reread_owner"] = node.stop_owner(owner)
    if not injected:
        out["resubmit"] = public(node.store_post(CANDIDATE_ID, node.dir.parent / "candidate.art"))
        out["after_resubmit"] = snapshot(node.store)


def settle(node: Node, candidate: Path, out: dict, injected: bool):
    """After a death: the image, recovery, and every reread of both articles."""
    out["killed"] = snapshot(node.store)
    recovered = node.operator("recover")
    out["recover"] = public(recovered)
    out["recover_counts"] = parse_recover(recovered["_out"])
    out["recovered"] = snapshot(node.store)
    reread(node, candidate.read_bytes(), out, injected)


def orphan(node: Node, candidate: Path, out: dict):
    """A `.stage-` orphan for recovery to sweep: a post killed after staging."""
    out["orphan_post"] = public(node.store_post(
        CANDIDATE_ID, candidate,
        {"FN_NATIVE_POST_FAULT": "record-staged-durable:kill"}))
    out["orphaned"] = snapshot(node.store)


def run_cut(image: Path, base: Path, cut, prior: Path, candidate: Path) -> dict:
    recovery = cut in native_cuts.RECOVERY_CUTS
    variable = "FN_NATIVE_RECOVERY_FAULT" if recovery else "FN_NATIVE_POST_FAULT"
    selector = {variable: cut.name + ":kill"}
    row = {"cut": cut.name, "program": cut.program, "follows": cut.follows,
           "table_candidate": cut.candidate, "variable": variable}
    served = row["served"] = {}
    node = Node(image, base, cut.name + "-served")
    try:
        seed(node, prior, served)
        if recovery:
            orphan(node, candidate, served)
        owner = node.start_owner(selector)
        served["owner_ready"] = owner["ready"]
        if owner["ready"]:
            served["post"] = public(node.post(CANDIDATE_ID, candidate))
            served["owner_alive_after_post"] = owner["proc"].poll() is None
        served["owner"] = node.stop_owner(owner)
        settle(node, candidate, served, injected=not recovery)
    finally:
        node.reap()
    cutrow = row["cut_run"] = {}
    node = Node(image, base, cut.name + "-cut")
    try:
        seed(node, prior, cutrow)
        if recovery:
            orphan(node, candidate, cutrow)
            cutrow["killed_recover"] = public(node.operator("recover", extra=selector))
        else:
            cutrow["killed_post"] = public(node.store_post(CANDIDATE_ID, candidate, selector))
        settle(node, candidate, cutrow, injected=False)
    finally:
        node.reap()
    return row


THIRD_ID = "<third@campaign.invalid>"
GROUP_LINE = re.compile(rb"211 (\d+) (\d+) (\d+) ")


def nntp_group(node: Node) -> tuple[int, int, int] | None:
    with socket.create_connection(("127.0.0.1", node.port), timeout=60) as conn:
        stream = conn.makefile("rb")
        stream.readline()
        conn.sendall("GROUP {}\r\n".format(GROUP).encode("ascii"))
        line = stream.readline()
        conn.sendall(b"QUIT\r\n")
    match = GROUP_LINE.match(line)
    return tuple(int(x) for x in match.groups()) if match else None


def stopped_then_killed(node: Node, argv, extra) -> dict:
    """Run one entry with a FN_CHECKPOINT_TEST_STOP selector; SIGKILL it at the stop.

    The host SIGSTOPs itself at the selected cut (`fnn-checkpoint-test-stop');
    a process that never stops ran to its end.
    """
    started = time.monotonic()
    proc = subprocess.Popen([str(node.image), "--fn", *map(str, argv)],
                            env=node.env(extra), cwd=node.dir,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    stopped = False
    while proc.poll() is None and time.monotonic() - started < 300:
        try:
            state = Path("/proc/{}/stat".format(proc.pid)).read_text().rsplit(")", 1)[1].split()[0]
        except (FileNotFoundError, IndexError):
            state = ""
        if state == "T":
            stopped = True
            os.kill(proc.pid, signal.SIGKILL)
            os.kill(proc.pid, signal.SIGCONT)
            break
        time.sleep(0.02)
    out, err = proc.communicate(timeout=60)
    return {"argv": ["IMAGE", "--fn", *map(str, argv)], "env": extra,
            "stopped": stopped, "rc": proc.returncode,
            "stdout": out.decode("utf-8", "replace")[-1000:],
            "stderr": err.decode("utf-8", "replace")[-1000:],
            "seconds": round(time.monotonic() - started, 2)}


def compaction_steps(node: Node, entry: str):
    if entry == "operator":
        return [("operator", str(node.config), "store", "compact")]
    return [("checkpoint", "pack", str(node.store), "select"),
            ("checkpoint", "pack-reclaim", str(node.store)),
            ("checkpoint", "pack-retire", str(node.store))]


def reread_all(node: Node, want: dict) -> dict:
    return {msgid: node.inspect(msgid)["_out"] == octets
            for msgid, octets in want.items()}


def run_checkpoint_cut(dev: Path, base: Path, cut, prior: Path, candidate: Path,
                       third: Path) -> dict:
    """One CHECKPOINT_CUTS cut through both compaction entries on a developer image.

    Seed: two articles, the first already compacted (pack generation 0
    selected, its file reclaimed), so that the compaction under test packs,
    selects, reclaims one covered file and retires one older generation and
    reaches every cut at its first occurrence.  Then: the entry killed at
    the cut, `recover', every article reread byte-identical, the same entry
    resumed to completion, a further compaction refused as already compact,
    every article reread again, and a new POST at GROUP high+1.
    """
    row = {"cut": cut.name, "program": cut.program, "book": cut.book,
           "table_candidate": cut.candidate, "entries": {}}
    for entry in ("developer", "operator"):
        node = Node(dev, base, "{}-{}".format(cut.name, entry))
        out = row["entries"][entry] = {}
        try:
            seed(node, prior, out)
            out["seed_compact"] = [public(node.run(argv)) for argv in compaction_steps(node, entry)]
            owner = node.start_owner()
            out["candidate_post"] = public(node.post(CANDIDATE_ID, candidate))
            node.stop_owner(owner)
            want = {PRIOR_ID: node.inspect(PRIOR_ID)["_out"],
                    CANDIDATE_ID: node.inspect(CANDIDATE_ID)["_out"]}
            out["before"] = snapshot(node.store)
            killed_at = None
            runs = []
            for index, argv in enumerate(compaction_steps(node, entry)):
                result = stopped_then_killed(node, argv, {"FN_CHECKPOINT_TEST_STOP": cut.name})
                runs.append(result)
                if result["stopped"]:
                    killed_at = index
                    break
            out["cut_runs"] = runs
            out["reached"] = killed_at is not None
            out["killed"] = snapshot(node.store)
            recovered = node.operator("recover")
            out["recover_rc"] = recovered["rc"]
            out["identical_after_cut"] = reread_all(node, want)
            resume = compaction_steps(node, entry)[(0 if entry == "operator" else killed_at or 0):]
            out["resume"] = [public(node.run(argv)) for argv in resume]
            again = node.operator("store", "compact")
            out["again"] = public(again)
            out["after"] = snapshot(node.store)
            out["identical_after_resume"] = reread_all(node, want)
            owner = node.start_owner()
            before = nntp_group(node) if owner["ready"] else None
            out["third_post"] = public(node.post(THIRD_ID, third))
            after = nntp_group(node) if owner["ready"] else None
            out["group_before"], out["group_after"] = before, after
            node.stop_owner(owner)
            out["pass"] = bool(
                out["reached"] and out["recover_rc"] == 0
                and all(out["identical_after_cut"].values())
                and all(r["rc"] == 0 for r in out["resume"]
                        if entry == "developer" or "already-compact" not in r["stderr"])
                and again["rc"] == 1 and "already-compact" in again["stderr"]
                and all(out["identical_after_resume"].values())
                and out["third_post"]["rc"] == 0
                and before and after and after[2] == before[2] + 1)
        finally:
            node.reap()
    row["pass"] = all(e.get("pass") for e in row["entries"].values())
    return row


def run_faults(dev: Path, prod: Path, base: Path, prior: Path, candidate: Path):
    rows = []

    def fresh(image, name):
        node = Node(image, base, name)
        row = {"name": name, "image": image.name}
        seed(node, prior, row)
        return node, row

    # Developer FN_NATIVE_POST_FAULT, an EIO after the final link, through
    # `store ROOT post` and through the served owner.
    node, row = fresh(dev, "dev-post-fault-eio")
    try:
        row["post"] = public(node.store_post(
            CANDIDATE_ID, candidate, {"FN_NATIVE_POST_FAULT": "record-attempted:eio"}))
        settle(node, candidate, row, injected=False)
    finally:
        node.reap()
    rows.append(row)
    node, row = fresh(dev, "dev-owner-post-fault-eio")
    try:
        owner = node.start_owner({"FN_NATIVE_POST_FAULT": "record-attempted:eio"})
        row["owner_ready"] = owner["ready"]
        row["post"] = public(node.post(CANDIDATE_ID, candidate))
        row["owner_alive_after_post"] = owner["proc"].poll() is None
        row["owner"] = node.stop_owner(owner)
        settle(node, candidate, row, injected=True)
    finally:
        node.reap()
    rows.append(row)

    # Developer FN_NATIVE_CONTROL_FAULT=postpublish on the owner.
    node, row = fresh(dev, "dev-control-fault")
    try:
        owner = node.start_owner({"FN_NATIVE_CONTROL_FAULT": "postpublish"})
        row["owner_ready"] = owner["ready"]
        row["post"] = public(node.post(CANDIDATE_ID, candidate))
        row["owner_alive_after_post"] = owner["proc"].poll() is None
        row["owner"] = node.stop_owner(owner)
        settle(node, candidate, row, injected=True)
    finally:
        node.reap()
    rows.append(row)

    # Developer FN_NATIVE_CONTROL_TEST_STOP: the worker that holds the reply
    # stops the owner after a durable completion and before its reply; then
    # the owner is killed.  Since F3's fix the client must answer 3.
    for repetition in range(5):
        node, row = fresh(dev, "dev-control-test-stop-kill-{}".format(repetition))
        try:
            owner = node.start_owner({"FN_NATIVE_CONTROL_TEST_STOP": "after-submit"})
            row["owner_ready"] = owner["ready"]
            client = subprocess.Popen(
                [str(dev), "--fn", "operator", str(node.config), "post", "--message-id",
                 CANDIDATE_ID, "--payload", str(candidate), "--group", GROUP],
                env=node.env(), cwd=node.dir, stdout=subprocess.PIPE,
                stderr=subprocess.PIPE)
            deadline = time.monotonic() + 240
            stopped = False
            while time.monotonic() < deadline and not stopped:
                state = Path("/proc/{}/stat".format(owner["pid"])).read_text().split()[2]
                stopped = state == "T"
                if not stopped:
                    time.sleep(0.5)
            row["owner_stopped_itself"] = stopped
            row["client_exited_before_kill"] = client.poll()
            row["at_stop"] = snapshot(node.store)
            row["owner"] = node.stop_owner(owner, signal.SIGKILL)
            out, err = client.communicate(timeout=300)
            row["post"] = {"rc": client.returncode, "stdout": out.decode()[-500:],
                           "stderr": err.decode()[-500:]}
            settle(node, candidate, row, injected=True)
        finally:
            node.reap()
        rows.append(row)

    # Since a0b6d41f the owner injects what `operator CFG post` hands it and
    # `store ROOT post` stores the payload as read.  Under D25 the Store
    # compares the poster's bytes, not the stored copy, so one payload
    # through the two entries is one article: the second submission is the
    # duplicate.  A third submission, through the second entry, changes one
    # authored byte (the Subject) under the same Message-ID: the conflict.
    # Each order, with no fault.
    changed = candidate.with_name("candidate-changed.art")
    changed.write_bytes(article(CANDIDATE_ID, "candidatf", "candidate content"))
    for first, second in (("store", "operator"), ("operator", "store")):
        node, row = fresh(dev, "cross-entry-retry-{}-then-{}".format(first, second))
        try:
            owner = None
            for entry, label, payload in ((first, "first", candidate),
                                          (second, "second", candidate),
                                          (second, "changed", changed)):
                if entry == "operator":
                    owner = node.start_owner()
                    row[label] = public(node.post(CANDIDATE_ID, payload))
                    row[label + "_owner"] = node.stop_owner(owner)
                else:
                    row[label] = public(node.store_post(CANDIDATE_ID, payload))
                row["after_" + label] = snapshot(node.store)
        finally:
            node.reap()
        rows.append(row)

    # Campaign dabebb84 F2: deaths at `frontier-staged-durable` each leave an
    # `.allocation-` stage; 65 of them passed the 64-name observation bound and
    # the store could not be opened.  Since the sweep of 2026-09-22 recovery
    # removes every orphan in bounded rounds.  Two stores: the next open after
    # the deaths is `operator CFG recover` in one and a plain `store ROOT post`
    # in the other; then an owner starts and the candidate is posted.
    for opener in ("recover", "store-post"):
        node, row = fresh(dev, "dev-allocation-orphans-{}".format(opener))
        try:
            row["deaths"] = [public(node.store_post(
                CANDIDATE_ID, candidate,
                {"FN_NATIVE_POST_FAULT": "frontier-staged-durable:kill"}))["rc"]
                for _ in range(ALLOCATION_DEATHS)]
            row["killed"] = snapshot(node.store)
            row["status"] = public(node.operator("status"))
            if opener == "recover":
                recovered = node.operator("recover")
                row["recover"] = public(recovered)
                row["recover_counts"] = parse_recover(recovered["_out"])
            else:
                row["open_post"] = public(node.store_post(CANDIDATE_ID, candidate))
            row["opened"] = snapshot(node.store)
            owner = node.start_owner()
            row["owner_ready"] = owner["ready"]
            if owner["ready"]:
                row["post"] = public(node.post(CANDIDATE_ID, candidate))
            row["owner"] = node.stop_owner(owner)
            row["after"] = snapshot(node.store)
        finally:
            node.reap()
        rows.append(row)

    # Production image: every registered developer selector, and the store
    # post FAULT argument, must be refused at startup with exit 5 and the
    # store's bytes unchanged.  `operator CFG run`, `operator CFG recover` and
    # `store ROOT post` each meet each selector.
    node, row = fresh(prod, "prod-selectors-refused-at-start")
    try:
        row["before"] = snapshot(node.store)
        row["starts"] = []
        for variable in native_cuts.developer_selectors():
            extra = {variable: "x"}
            owner = node.start_owner(extra)
            started = node.stop_owner(owner)
            row["starts"].append({
                "variable": variable,
                "operator_run": {k: started[k] for k in ("rc", "lines", "stderr")},
                "operator_recover": public(node.operator("recover", extra=extra)),
                "store_post": public(node.store_post(CANDIDATE_ID, candidate, extra)),
            })
        row["store_post_fault_argument"] = public(
            node.store_post(CANDIDATE_ID, candidate, inject="postpublish"))
        row["after"] = snapshot(node.store)
        row["unchanged"] = row["after"] == row["before"]
    finally:
        node.reap()
    rows.append(row)
    node = Node(prod, base, "prod-raw-store-post-guard")
    row = {"name": "prod-raw-store-post-guard", "image": prod.name}
    absent_payload = node.dir / "absent-payload.art"
    row["plain_post"] = public(node.store_post(CANDIDATE_ID, absent_payload))
    row["store_created"] = node.store.exists()
    row["payload_created"] = absent_payload.exists()
    rows.append(row)
    node = Node(prod, base, "prod-init-fault")
    row = {"name": "prod-init-fault", "image": prod.name}
    row["init"] = public(node.operator(
        "init", GROUP, extra={"FN_NATIVE_INIT_FAULT": "init-config-written:kill"}))
    row["store_created"] = node.store.exists()
    rows.append(row)
    return rows


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--images", type=Path, required=True)
    parser.add_argument("--work", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--only", action="append", default=[],
                        help="run only these cut names (repeatable)")
    parser.add_argument("--no-faults", action="store_true")
    parser.add_argument("--checkpoint-only", action="store_true",
                        help="run only the checkpoint cuts through both compaction entries")
    args = parser.parse_args(argv)
    native_cuts.verify_native_cut_map()
    dev, prod = args.images / "fn-host-developer", args.images / "fn-host"
    if args.work.exists():
        shutil.rmtree(args.work)
    args.work.mkdir(parents=True)
    prior, candidate = args.work / "prior.art", args.work / "candidate.art"
    prior.write_bytes(article(PRIOR_ID, "prior", "prior accepted content"))
    candidate.write_bytes(article(CANDIDATE_ID, "candidate", "candidate content"))
    third = args.work / "third.art"
    third.write_bytes(article(THIRD_ID, "third", "third content after compaction"))
    result = {"images": str(args.images), "cuts": [], "checkpoint_cuts": [], "faults": []}
    for cut in native_cuts.CHECKPOINT_CUTS:
        if args.only and cut.name not in args.only:
            continue
        print("checkpoint cut", cut.name, flush=True)
        result["checkpoint_cuts"].append(
            run_checkpoint_cut(dev, args.work, cut, prior, candidate, third))
        args.out.write_text(json.dumps(result, indent=1, default=str))
    for cut in (() if args.checkpoint_only else native_cuts.ALL_CUTS):
        if args.only and cut.name not in args.only:
            continue
        print("cut", cut.name, flush=True)
        result["cuts"].append(run_cut(dev, args.work, cut, prior, candidate))
        args.out.write_text(json.dumps(result, indent=1, default=str))
    if not args.no_faults and not args.checkpoint_only:
        print("faults", flush=True)
        result["faults"] = run_faults(dev, prod, args.work, prior, candidate)
    args.out.write_text(json.dumps(result, indent=1, default=str))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
