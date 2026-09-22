"""The native cut campaign driven through the public operator verb.

Run on the box that holds a frozen image directory:

    python3 -m tests.campaign.native_operator_campaign \
        --images /abs/build/images/<rev> --work /abs/scratch --out result.json

For every cut of `native_cuts.ALL_CUTS` it records two observations over
fresh stores, each seeded with one prior article posted through
`operator CFG post` to a running `operator CFG run` owner:

served   the owner restarted with the cut's selector in its environment and
         the candidate posted through `operator CFG post`: the path the node
         serves.  What the owner does with the selector is the observation.
cut      the candidate posted through `store ROOT post` with the selector,
         the entry that reads it (`fnn-command-post`, host/native/io.lisp),
         then `operator CFG recover`, `store ROOT inspect`, a restarted
         owner's NNTP ARTICLE, and a resubmission through `operator CFG post`.

It also runs the developer faults once each and the same selectors against the
production image.  It judges nothing: the evidence file compares the
observations with the table.  Exit codes are recorded raw; a negative code is
the signal that ended the process (subprocess convention).
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


def reread(node: Node, prior: bytes, candidate: bytes, out: dict):
    for label, msgid, want in (("prior", PRIOR_ID, prior),
                               ("candidate", CANDIDATE_ID, candidate)):
        got = node.inspect(msgid)
        out["inspect_" + label] = {"rc": got["rc"],
                                   "identical": got["_out"] == want,
                                   "stderr": got["stderr"][-300:]}
    owner = node.start_owner()
    out["reread_owner_ready"] = owner["ready"]
    if owner["ready"]:
        for label, msgid, want in (("prior", PRIOR_ID, prior),
                                   ("candidate", CANDIDATE_ID, candidate)):
            got = node.nntp_article(msgid)
            out["nntp_" + label] = {"status": got["status"],
                                    "identical": got["octets"] == want}
        out["resubmit"] = public(node.post(CANDIDATE_ID, node.dir.parent / "candidate.art"))
        out["after_resubmit"] = snapshot(node.store)
    out["reread_owner"] = node.stop_owner(owner)


def run_cut(image: Path, base: Path, cut, prior: Path, candidate: Path) -> dict:
    variable = ("FN_NATIVE_RECOVERY_FAULT" if cut in native_cuts.RECOVERY_CUTS
                else "FN_NATIVE_POST_FAULT")
    selector = {variable: cut.name + ":kill"}
    row = {"cut": cut.name, "program": cut.program,
           "table_candidate": cut.candidate, "variable": variable}
    served = row["served"] = {}
    node = Node(image, base, cut.name + "-served")
    try:
        seed(node, prior, served)
        if variable == "FN_NATIVE_POST_FAULT":
            owner = node.start_owner(selector)
            served["owner_ready"] = owner["ready"]
            served["post"] = public(node.post(CANDIDATE_ID, candidate))
            served["owner_alive_after_post"] = owner["proc"].poll() is None
            served["owner"] = node.stop_owner(owner)
        else:
            # An orphan for recovery to unlink, then the owner's own recovery
            # with the selector in its environment.
            served["orphan_post"] = public(node.store_post(
                CANDIDATE_ID, candidate,
                {"FN_NATIVE_POST_FAULT": "record-staged-durable:kill"}))
            served["orphaned"] = snapshot(node.store)
            owner = node.start_owner(selector)
            served["owner_ready"] = owner["ready"]
            served["owner"] = node.stop_owner(owner)
        served["after"] = snapshot(node.store)
        served["recover"] = public(node.operator("recover"))
    finally:
        node.reap()
    cutrow = row["cut_run"] = {}
    node = Node(image, base, cut.name + "-cut")
    try:
        seed(node, prior, cutrow)
        if variable == "FN_NATIVE_POST_FAULT":
            cutrow["killed_post"] = public(node.store_post(CANDIDATE_ID, candidate, selector))
        else:
            cutrow["orphan_post"] = public(node.store_post(
                CANDIDATE_ID, candidate,
                {"FN_NATIVE_POST_FAULT": "record-staged-durable:kill"}))
            cutrow["orphaned"] = snapshot(node.store)
            cutrow["killed_recover"] = public(node.operator("recover", extra=selector))
        cutrow["killed"] = snapshot(node.store)
        recovered = node.operator("recover")
        cutrow["recover"] = public(recovered)
        cutrow["recover_counts"] = parse_recover(recovered["_out"])
        cutrow["recovered"] = snapshot(node.store)
        reread(node, prior.read_bytes(), candidate.read_bytes(), cutrow)
    finally:
        node.reap()
    return row


def run_faults(dev: Path, prod: Path, base: Path, prior: Path, candidate: Path):
    rows = []

    def fresh(image, name):
        node = Node(image, base, name)
        row = {"name": name, "image": image.name}
        seed(node, prior, row)
        return node, row

    # Developer FN_NATIVE_POST_FAULT, an EIO after the final link.
    node, row = fresh(dev, "dev-post-fault-eio")
    try:
        row["post"] = public(node.store_post(
            CANDIDATE_ID, candidate, {"FN_NATIVE_POST_FAULT": "record-attempted:eio"}))
        row["after"] = snapshot(node.store)
        recovered = node.operator("recover")
        row["recover"] = public(recovered)
        row["recover_counts"] = parse_recover(recovered["_out"])
        reread(node, prior.read_bytes(), candidate.read_bytes(), row)
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
        row["after"] = snapshot(node.store)
        recovered = node.operator("recover")
        row["recover"] = public(recovered)
        row["recover_counts"] = parse_recover(recovered["_out"])
        reread(node, prior.read_bytes(), candidate.read_bytes(), row)
    finally:
        node.reap()
    rows.append(row)

    # Developer FN_NATIVE_CONTROL_TEST_STOP: the owner stops itself after a
    # durable completion and before its reply; then it is killed.
    node, row = fresh(dev, "dev-control-test-stop-kill")
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
        row["at_stop"] = snapshot(node.store)
        row["owner"] = node.stop_owner(owner, signal.SIGKILL)
        out, err = client.communicate(timeout=300)
        row["post"] = {"rc": client.returncode, "stdout": out.decode()[-500:],
                       "stderr": err.decode()[-500:]}
        row["after"] = snapshot(node.store)
        recovered = node.operator("recover")
        row["recover"] = public(recovered)
        row["recover_counts"] = parse_recover(recovered["_out"])
        reread(node, prior.read_bytes(), candidate.read_bytes(), row)
    finally:
        node.reap()
    rows.append(row)

    # Production image: each selector once.
    node, row = fresh(prod, "prod-post-fault")
    try:
        row["post"] = public(node.store_post(
            CANDIDATE_ID, candidate, {"FN_NATIVE_POST_FAULT": "record-attempted:kill"}))
        row["after"] = snapshot(node.store)
    finally:
        node.reap()
    rows.append(row)
    for name, variable, value in (
            ("prod-control-fault", "FN_NATIVE_CONTROL_FAULT", "postpublish"),
            ("prod-control-test-stop", "FN_NATIVE_CONTROL_TEST_STOP", "after-submit")):
        node, row = fresh(prod, name)
        try:
            owner = node.start_owner({variable: value})
            row["owner_ready"] = owner["ready"]
            row["post"] = public(node.post(CANDIDATE_ID, candidate, timeout=240))
            row["owner_alive_after_post"] = owner["proc"].poll() is None
            row["owner"] = node.stop_owner(owner)
            row["after"] = snapshot(node.store)
        finally:
            node.reap()
        rows.append(row)
    # Production: the selectors and argument the image does not gate.
    node, row = fresh(prod, "prod-recovery-fault")
    try:
        orphan = Node(dev, base, "prod-recovery-fault-orphaner")
        orphan.store = node.store
        row["orphan_post_dev_image"] = public(orphan.store_post(
            CANDIDATE_ID, candidate, {"FN_NATIVE_POST_FAULT": "record-staged-durable:kill"}))
        row["orphaned"] = snapshot(node.store)
        row["recover"] = public(node.operator(
            "recover", extra={"FN_NATIVE_RECOVERY_FAULT": "recovery-stage-unlinked:kill"}))
        row["after"] = snapshot(node.store)
        row["recover_clean"] = public(node.operator("recover"))
    finally:
        node.reap()
    rows.append(row)
    node, row = fresh(prod, "prod-store-post-inject")
    try:
        row["post"] = public(node.store_post(CANDIDATE_ID, candidate, inject="postpublish"))
        row["after"] = snapshot(node.store)
        row["recover"] = public(node.operator("recover"))
    finally:
        node.reap()
    rows.append(row)
    node = Node(prod, base, "prod-init-fault")
    row = {"name": "prod-init-fault", "image": prod.name}
    row["init"] = public(node.operator(
        "init", GROUP, extra={"FN_NATIVE_INIT_FAULT": "init-config-written:kill"}))
    row["after"] = snapshot(node.store) if node.store.is_dir() else None
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
    args = parser.parse_args(argv)
    native_cuts.verify_native_cut_map()
    dev, prod = args.images / "fn-host-developer", args.images / "fn-host"
    if args.work.exists():
        shutil.rmtree(args.work)
    args.work.mkdir(parents=True)
    prior, candidate = args.work / "prior.art", args.work / "candidate.art"
    prior.write_bytes(article(PRIOR_ID, "prior", "prior accepted content"))
    candidate.write_bytes(article(CANDIDATE_ID, "candidate", "candidate content"))
    result = {"images": str(args.images), "cuts": [], "faults": []}
    for cut in native_cuts.ALL_CUTS:
        if args.only and cut.name not in args.only:
            continue
        print("cut", cut.name, flush=True)
        result["cuts"].append(run_cut(dev, args.work, cut, prior, candidate))
        args.out.write_text(json.dumps(result, indent=1, default=str))
    if not args.no_faults:
        print("faults", flush=True)
        result["faults"] = run_faults(dev, prod, args.work, prior, candidate)
    args.out.write_text(json.dumps(result, indent=1, default=str))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
