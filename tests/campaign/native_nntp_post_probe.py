"""The served POST's process-death and EIO cuts observed at the NNTP wire,
on the record log (lane ack-before-barrier, restoring the per-cut
wire probe log-recovery-2 deleted with the per-file route).

A served POST on the record log is a member of the owner's batch quantum
(host/native/owner.lisp fnn-owner-commit-start-locked): its reservation
(frontier-reserved), its record's take and place (record-completing) and its
in-memory finish (finish-consumed, finish-durable) run inside START; the
batch's append (log-written) and barrier (log-fenced) follow; the member's
reply leaves only in COMPLETE, after the barrier
(books/owner-commit-steps.lisp fn-ocs-members-told-only-after-the-barrier,
books/owner-ack-after-barrier.lisp fn-oab-quantum-reports-after-its-barrier).
So every served cut lies BEFORE the reply, and the reply a cut allows follows
from its coordinate (`served_arm'), never from a hand list:

  pre-append  the cut's program runs before the batch's append
              (fn-lg-reserve-program, fn-lg-order-program,
              fn-bs-finish-program): the record is absent at a death; an EIO
              ends the START uncertain (the batch is not appended);
  appended    the append's cut (log-written): a death keeps a prefix of the
              batch (either); an EIO fences the kernel: uncertain;
  fenced      the barrier's cut (log-fenced): the record is durable; a death
              leaves it present with no reply owed; an EIO is uncertain.

Whatever the arm, a faulted row is NEVER answered 240: no cut lies after the
barrier and before the reply.  A kill row owes no reply at all; an EIO row
is answered ACL2's uncertain line or closed (uncertain to the client), and
the owner stops (exit 3).  The table's candidate column
(native_cuts.POST_LOG_CUTS, and frontier-reserved of POST_CUTS) must be the
arm's fate, and the statement cut (native_cuts.STATEMENT_CUTS) must lie after
its barrier: `verify_served_arms' refuses a table that disagrees.

Per cut and action (`kill`, `eio`), over a fresh store seeded with a prior
article: the owner is started with FN_NATIVE_POST_FAULT=<cut>:<action>, the
candidate is POSTed over NNTP, the owner is stopped by pid, then `operator
CFG recover`, `store ROOT inspect`, a restarted owner's ARTICLE for both
articles, and the candidate POSTed once more.  Controls: an unfaulted POST
(SIGKILL after the reply, restart, reread) on both images, a POST the
injection refuses (no From), and a SIGKILL while the article is half sent.
`--judge FILE` re-judges a recorded result.
"""
from __future__ import annotations

import argparse
import json
import shutil
import signal
import socket
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(ROOT))
from tests.campaign import native_cuts  # noqa: E402
from tests.campaign.native_operator_campaign import (  # noqa: E402
    CANDIDATE_ID, PRIOR_ID, Node, article, matches, parse_recover, public, seed,
    sha, snapshot)

def nntp_post(node: Node, payload: bytes, timeout=120) -> dict:
    """POST `payload`; the raw greeting, 340 and final reply lines."""
    out = {}
    try:
        with socket.create_connection(("127.0.0.1", node.port), timeout=timeout) as conn:
            stream = conn.makefile("rb")
            out["greeting"] = stream.readline().decode("ascii", "replace")
            conn.sendall(b"POST\r\n")
            out["post_reply"] = stream.readline().decode("ascii", "replace")
            if not out["post_reply"].startswith("340"):
                return out
            conn.sendall(payload + b".\r\n")
            try:
                out["reply"] = stream.readline().decode("ascii", "replace")
            except (ConnectionResetError, socket.timeout) as error:
                out["reply"] = ""
                out["reply_error"] = type(error).__name__
            try:
                conn.sendall(b"QUIT\r\n")
                out["quit_reply"] = stream.readline().decode("ascii", "replace")
            except OSError as error:
                out["quit_error"] = type(error).__name__
    except OSError as error:
        out["error"] = "{}: {}".format(type(error).__name__, error)
    return out


def reread(node: Node, payload: bytes, out: dict, repost=True):
    read = {}
    for label, msgid, want, inj in (("prior", PRIOR_ID, node.prior_stored, False),
                                    ("candidate", CANDIDATE_ID, payload, True)):
        got = node.inspect(msgid)
        read[label] = got["_out"] if got["rc"] == 0 else None
        out["inspect_" + label] = {"rc": got["rc"], "sha256": sha(got["_out"]),
                                   "identical": matches(got["_out"], want, inj),
                                   "stderr": got["stderr"][-300:]}
    owner = node.start_owner()
    out["reread_owner_ready"] = owner["ready"]
    if owner["ready"]:
        for label, msgid, want, inj in (("prior", PRIOR_ID, node.prior_stored, False),
                                        ("candidate", CANDIDATE_ID, payload, True)):
            got = node.nntp_article(msgid)
            out["nntp_" + label] = {
                "status": got["status"], "sha256": sha(got["octets"]),
                "identical": matches(got["octets"], want, inj),
                "same_as_inspect": (read[label] == got["octets"]
                                    if read[label] is not None else None)}
        if repost:
            out["repost"] = nntp_post(node, payload)
            out["after_repost"] = snapshot(node.store)
    out["reread_owner"] = node.stop_owner(owner)


def settle(node: Node, payload: bytes, out: dict, repost=True):
    out["killed"] = snapshot(node.store)
    recovered = node.operator("recover")
    out["recover"] = public(recovered)
    out["recover_counts"] = parse_recover(recovered["_out"])
    out["recovered"] = snapshot(node.store)
    reread(node, payload, out, repost)


def faulted(dev: Path, base: Path, prior: Path, payload: bytes, cut, action) -> dict:
    row = {"cut": cut.name, "program": cut.program, "action": action,
           "table_candidate": cut.candidate}
    node = Node(dev, base, "{}-{}".format(cut.name, action))
    try:
        seed(node, prior, row)
        owner = node.start_owner({"FN_NATIVE_POST_FAULT": "{}:{}".format(cut.name, action)})
        row["owner_ready"] = owner["ready"]
        if owner["ready"]:
            row["post"] = nntp_post(node, payload)
            row["owner_alive_after_post"] = owner["proc"].poll() is None
        row["owner"] = node.stop_owner(owner)
        settle(node, payload, row)
    finally:
        node.reap()
    return row


def plain(image: Path, base: Path, prior: Path, payload: bytes, name, kill_after=True,
          half=False) -> dict:
    row = {"name": name, "image": image.name}
    node = Node(image, base, name)
    try:
        seed(node, prior, row)
        owner = node.start_owner()
        row["owner_ready"] = owner["ready"]
        if half:
            # The owner is killed by pid while the connection is open and
            # half the article has been sent: no reply can have been owed.
            with socket.create_connection(("127.0.0.1", node.port), timeout=120) as conn:
                stream = conn.makefile("rb")
                row["post"] = {"greeting": stream.readline().decode("ascii", "replace")}
                conn.sendall(b"POST\r\n")
                row["post"]["post_reply"] = stream.readline().decode("ascii", "replace")
                conn.sendall(payload[: len(payload) // 2])
                row["post"]["half_sent_octets"] = len(payload) // 2
                row["owner_alive_after_post"] = owner["proc"].poll() is None
                row["owner"] = node.stop_owner(owner, signal.SIGKILL)
                try:
                    row["post"]["after_kill"] = stream.readline().decode("ascii", "replace")
                except OSError as error:
                    row["post"]["after_kill"] = type(error).__name__
        else:
            row["post"] = nntp_post(node, payload)
            row["owner_alive_after_post"] = owner["proc"].poll() is None
            row["owner"] = node.stop_owner(
                owner, signal.SIGKILL if kill_after else signal.SIGTERM)
        settle(node, payload, row, repost=not half)
    finally:
        node.reap()
    return row


# P2 at the wire: the exact reply lines (books/nntp-post.lisp
# fn-nntp-post-outcome and fn-post-store-refusal-line).  The refusal words are
# a local policy choice pending ember's decision; the judge holds the bytes.
OK_240 = "240 article received OK\r\n"
UNCERTAIN = "441 posting failed; the outcome is uncertain, do not repost\r\n"
STORAGE_FAILED = ("441 posting failed; the store could not write the article, "
                  "nothing was stored\r\n")
DUPLICATE = "441 posting failed; this article is already stored here\r\n"
CONFLICT = ("441 posting failed; a different article with this Message-ID is "
            "stored here\r\n")
NO_FROM = "441 posting failed; From is required\r\n"
from tools.outcome_codes import EXIT_UNCERTAIN  # noqa: E402

# The served commit's programs in the host's order (START: the member's
# reservation, its record's place, its finish; then the batch's append and
# barrier; checked against the host by native_cuts.verify_post_log_cut_map).
SERVED_PROGRAMS = ("fn-lg-reserve-program", "fn-lg-order-program", "fn-bs-finish-program",
                   "fn-lg-append-program", "fn-lg-fence-program")
ARMS = ("pre-append", "appended", "fenced")
# The fate each arm fixes; the table's candidate column must agree.
ARM_FATE = {"pre-append": "absent", "appended": "either", "fenced": "present"}
FATE = {"absent": False, "present": True, "either": None}


def served_cuts() -> tuple:
    """The served route's cuts: frontier-reserved (POST_CUTS: the member's
    reservation, the same inside a quantum) and POST_LOG_CUTS."""
    reserved = tuple(c for c in native_cuts.POST_CUTS if c.program == "fn-lg-reserve-program")
    if tuple(c.name for c in reserved) != ("frontier-reserved",):
        raise AssertionError("the reservation's cut is not frontier-reserved alone")
    return reserved + native_cuts.POST_LOG_CUTS


def served_arm(cut) -> str:
    """The arm a served cut's coordinate gives: where its program runs
    relative to the batch's append and barrier."""
    order = SERVED_PROGRAMS
    if cut.program not in order:
        raise AssertionError("{}: program {} is not a served program".format(cut.name, cut.program))
    at = order.index(cut.program)
    if at < order.index("fn-lg-append-program"):
        return "pre-append"
    if cut.program == "fn-lg-append-program":
        return "appended"
    return "fenced"


def verify_served_arms(cuts=None) -> dict:
    arms = {}
    for cut in cuts if cuts is not None else served_cuts():
        arm = served_arm(cut)
        if cut.candidate != ARM_FATE[arm]:
            raise AssertionError("{}: arm {} needs candidate {}, table says {}".format(
                cut.name, arm, ARM_FATE[arm], cut.candidate))
        arms[cut.name] = arm
    # The statement's cut lies after the statement's own barrier
    # (fnn-owner-statement-barrier before fnn-owner-key-statement-cut,
    # native_cuts.verify_statement_cut_map): the statement is present.
    for cut in native_cuts.STATEMENT_CUTS:
        if cut.candidate != "present":
            raise AssertionError("{}: the statement cut follows its barrier, table says {}".format(
                cut.name, cut.candidate))
        arms[cut.name] = "fenced"
    return arms


def _rc(row):
    return (row.get("owner") or {}).get("rc")


def _present(row):
    return (row.get("inspect_candidate") or {}).get("rc") == 0


def _cut(name):
    return next(c for c in served_cuts() if c.name == name)


def expectation(row) -> dict:
    """What the wire must show for one faulted row."""
    cut = _cut(row["cut"])
    arm = served_arm(cut)
    present = FATE[ARM_FATE[arm]]
    if row["action"] == "kill":
        # A dead process owes no line: no cut lies after the barrier and
        # before the reply.
        return {"arm": arm, "replies": {""}, "rc": -9, "present": present}
    # EIO: the store is fenced and the owner stops; the poster is told
    # uncertain (ACL2's line) or the connection closes -- never 240, never a
    # refusal (the batch's members are uncertain together).
    fate = present if arm != "appended" else None
    return {"arm": arm, "replies": {UNCERTAIN, ""}, "rc": EXIT_UNCERTAIN, "present": fate}


def _repost_ok(row, failures, required=False):
    repost = (row.get("repost") or {}).get("reply")
    if repost is None:
        if required and row.get("reread_owner_ready"):
            failures.append("no repost was made to the restarted owner")
        return
    want = {DUPLICATE} if _present(row) else {OK_240}
    if repost not in want:
        failures.append("repost {!r} not in {}".format(repost, sorted(want)))


def judge_cut(row) -> list:
    failures = []
    want = expectation(row)
    reply = (row.get("post") or {}).get("reply")
    if reply == OK_240:
        failures.append("a cut before the reply answered 240")
    elif reply not in want["replies"]:
        failures.append("reply {!r} not in {}".format(reply, sorted(want["replies"])))
    if _rc(row) != want["rc"]:
        failures.append("owner exit {!r} != {}".format(_rc(row), want["rc"]))
    if want["present"] is not None and _present(row) != want["present"]:
        failures.append("candidate present={} != {}".format(_present(row), want["present"]))
    for label in ("prior", "candidate"):
        got = row.get("inspect_" + label) or {}
        if got.get("rc") == 0 and not got.get("identical"):
            failures.append(label + " does not reread identical")
    if not (row.get("inspect_prior") or {}).get("rc") == 0:
        failures.append("the prior article is not present")
    _repost_ok(row, failures, required=True)
    return failures


def judge_control(row) -> list:
    failures = []
    reply = (row.get("post") or {}).get("reply")
    name = row["name"]
    if name == "dev-refused-no-from":
        if reply != NO_FROM:
            failures.append("reply {!r} != {!r}".format(reply, NO_FROM))
        if _present(row):
            failures.append("refused article is present")
    elif name == "prod-sigkill-mid-article":
        if _present(row):
            failures.append("half-sent article is present")
    else:
        if reply != OK_240:
            failures.append("reply {!r} != {!r}".format(reply, OK_240))
        if not (row.get("inspect_candidate") or {}).get("identical"):
            failures.append("accepted candidate does not reread identical")
        _repost_ok(row, failures)
    return failures


def judge(result) -> dict:
    rows = []
    for row in result["cuts"]:
        rows.append({"row": "{} {}".format(row["cut"], row["action"]),
                     "arm": expectation(row)["arm"],
                     "reply": (row.get("post") or {}).get("reply"),
                     "rc": _rc(row), "present": _present(row),
                     "repost": (row.get("repost") or {}).get("reply"),
                     "failures": judge_cut(row)})
    for row in result["controls"]:
        rows.append({"row": row["name"], "arm": "control", "reply": (row.get("post") or {}).get("reply"),
                     "rc": _rc(row), "present": _present(row),
                     "repost": (row.get("repost") or {}).get("reply"),
                     "failures": judge_control(row)})
    return {"rows": rows, "failed": sum(1 for r in rows if r["failures"]),
            "total": len(rows)}


def print_judgement(verdict) -> None:
    for row in verdict["rows"]:
        print("{:<30} {:<10} {:<5} rc={!s:<4} present={!s:<5} reply={!r} repost={!r}{}".format(
            row["row"], row.get("arm", ""), "FAIL" if row["failures"] else "pass", row["rc"],
            row["present"], row["reply"], row["repost"],
            "".join("\n    " + f for f in row["failures"])))
    print("{} of {} rows pass".format(verdict["total"] - verdict["failed"],
                                      verdict["total"]))


def run(images: Path, work: Path, out: Path, cuts=None, actions=("kill", "eio")) -> dict:
    verify_served_arms()
    dev, prod = images / "fn-host-developer", images / "fn-host"
    if work.exists():
        shutil.rmtree(work)
    work.mkdir(parents=True)
    prior = work / "prior.art"
    prior.write_bytes(article(PRIOR_ID, "prior", "prior accepted content"))
    payload = article(CANDIDATE_ID, "candidate", "candidate content")
    (work / "candidate.art").write_bytes(payload)
    refused = payload.replace(b"From: campaign@campaign.invalid\r\n", b"")
    result = {"images": str(images), "cuts": [], "controls": []}
    for cut in served_cuts():
        if cuts and cut.name not in cuts:
            continue
        for action in actions:
            print("cut", cut.name, action, flush=True)
            result["cuts"].append(faulted(dev, work, prior, payload, cut, action))
            out.write_text(json.dumps(result, indent=1, default=str))
    print("controls", flush=True)
    result["controls"].append(plain(dev, work, prior, payload, "dev-accepted-then-sigkill"))
    result["controls"].append(plain(dev, work, prior, refused, "dev-refused-no-from",
                                    kill_after=False))
    if prod.exists():
        result["controls"].append(plain(prod, work, prior, payload, "prod-accepted-then-sigkill"))
        result["controls"].append(plain(prod, work, prior, payload, "prod-sigkill-mid-article",
                                        half=True))
    result["judgement"] = judge(result)
    out.write_text(json.dumps(result, indent=1, default=str))
    return result


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--images", type=Path)
    parser.add_argument("--work", type=Path)
    parser.add_argument("--out", type=Path)
    parser.add_argument("--judge", type=Path,
                        help="re-judge a recorded result (.json or .json.gz) and exit")
    args = parser.parse_args(argv)
    if args.judge:
        import gzip
        raw = args.judge.read_bytes()
        if args.judge.suffix == ".gz":
            raw = gzip.decompress(raw)
        verdict = judge(json.loads(raw))
        print_judgement(verdict)
        return 1 if verdict["failed"] else 0
    if not (args.images and args.work and args.out):
        parser.error("--images, --work and --out are required to run the probe")
    result = run(args.images, args.work, args.out)
    print_judgement(result["judgement"])
    return 1 if result["judgement"]["failed"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
