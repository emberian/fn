"""The post cuts of `native_cuts.POST_CUTS` observed at the NNTP wire.

`native_operator_campaign` submits the candidate through `operator CFG post`
and records its exit code.  Plan P2 is stated at the NNTP wire: `240` only
after the completion was consumed, `441` naming its reason, an uncertain
outcome `441 ... do not repost`, and the acknowledged article rereading
byte-identical after a kill at any cut.  This probe takes the same cuts on
the same served owner, but submits the candidate with NNTP POST and records
the reply octets the client received (b"" when the connection closed with no
reply).  `judge` compares every row with P2's wire bar (the exact bytes
below); `--judge FILE` re-judges a recorded result without running anything.

Per post cut and per action (`kill`, `eio`), over a fresh store seeded as the
operator campaign seeds it: the owner is started with
FN_NATIVE_POST_FAULT=<cut>:<action>, the candidate is POSTed, the owner is
stopped by its recorded pid, then `operator CFG recover`, `store ROOT
inspect`, a restarted owner's ARTICLE for both articles, and the same
candidate POSTed once more to that restarted owner.

Controls on the developer image: an unfaulted POST (then SIGKILL of the
owner by pid after the reply, restart, reread), and a POST refused by the
injection checks.  On the production image (no selector is accepted there):
the same unfaulted POST, SIGKILL by pid after the reply, restart, reread;
and a SIGKILL by pid while a POST's article is half sent.
"""
from __future__ import annotations

import argparse
import json
import re
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
EXIT_UNCERTAIN = 3

# The expectation per cut is derived from its model coordinate
# (native_cuts.POST_CUTS: the program and the cut's place in it), never from
# a hand list of cut names (campaign 6c0626c5, H1: a hand list went stale
# when lane p10-k0 added four cuts).  `post_arm' reads the program's steps:
#
#   refused    the cut precedes the program's first publication step (a
#              rename or link into a directory other than staging): an EIO
#              is a known pre-publication failure (P-RECORD `On error before
#              941'), answered STORAGE_FAILED, the article absent, the owner
#              serving on, a repost accepted;
#   swallowed  the cut lies between two best-effort staging steps after the
#              record's directory barrier (P-RECORD `Errors from 970-971 are
#              swallowed'): the record is durable, the client gets 240, and
#              the owner log must name the swallowed cleanup error once;
#   consumed   the program issues no syscall at all (P-FINISH): the record
#              is durable, so 240 or uncertain, never a refusal;
#   uncertain  also every cut of a program that begins after the record
#              program's end (P-MARKER, fnn-mark-committed): the record is
#              durable and any error there is uncertain, never a refusal;
#   uncertain  every other cut (at or after the publication attempt).
#
# native_cuts.verify_swallowed_cuts checks the host's `ignore-errors' holds
# exactly the swallowed cuts; `verify_post_arms' checks each arm against the
# table's candidate column.
ARMS = ("refused", "swallowed", "consumed", "uncertain")


def post_arm(cut) -> str:
    steps = native_cuts.model_steps(cut.program, cut.book)
    if not any(s.kind in native_cuts.SYSCALL_KINDS for s in steps):
        return "consumed"
    order = native_cuts.POST_PROGRAMS
    if order.index(cut.program) > order.index("fn-bs-record-program"):
        return "uncertain"
    index = native_cuts.cut_step_index(cut)
    published = next(j for j, s in enumerate(steps)
                     if s.kind in ("rename", "link") and s.directory != ":staging")
    if index < published:
        return "refused"
    if native_cuts.swallowed_cut(cut):
        return "swallowed"
    return "uncertain"


# The table's candidate column, as the fate a row must show (None: either).
FATE = {"absent": False, "present": True, "either": None}
# The arms that fix the fate whatever the table says; the table must agree.
ARM_FATE = {"refused": "absent", "swallowed": "present", "consumed": "present"}


def verify_post_arms() -> dict:
    arms = {}
    for cut in native_cuts.POST_CUTS:
        arm = post_arm(cut)
        want = ARM_FATE.get(arm)
        if want is not None and cut.candidate != want:
            raise AssertionError("{}: arm {} needs candidate {}, table says {}".format(
                cut.name, arm, want, cut.candidate))
        arms[cut.name] = arm
    return arms


# The owner-log line a swallowed cleanup error must leave, exactly once: it
# names the staging cleanup and the error (EIO, errno 5).  The line's other
# words are the host's to choose.
SWALLOWED_LOG = re.compile(r"(?i)^(?=.*\bstaging\b)(?=.*\bcleanup\b)(?=.*(\bEIO\b|errno\W*5\b)).*$")


def swallowed_log_lines(row) -> list:
    text = (row.get("owner") or {}).get("stderr") or ""
    return [line for line in text.splitlines() if SWALLOWED_LOG.match(line)]


def _rc(row):
    return (row.get("owner") or {}).get("rc")


def _present(row):
    return (row.get("inspect_candidate") or {}).get("rc") == 0


def _cut(name):
    return next(c for c in native_cuts.POST_CUTS if c.name == name)


def expectation(row) -> dict:
    """What P2 requires of one faulted row: replies allowed, owner exit, fate."""
    cut = _cut(row["cut"])
    present = FATE[cut.candidate]
    if row["action"] == "kill":
        # A dead process owes no line, and no 240 may precede the death.
        return {"arm": "kill", "replies": {""}, "rc": -9, "present": present,
                "log_lines": None}
    arm = post_arm(cut)
    if arm == "refused":
        return {"arm": arm, "replies": {STORAGE_FAILED}, "rc": 0, "present": False,
                "log_lines": None}
    if arm == "swallowed":
        # 240 after the completion was consumed; the owner serves on and is
        # stopped by SIGTERM.
        return {"arm": arm, "replies": {OK_240}, "rc": 0, "present": True,
                "log_lines": 1}
    if arm == "consumed":
        return {"arm": arm, "replies": {OK_240, UNCERTAIN}, "rc": EXIT_UNCERTAIN,
                "present": True, "log_lines": None}
    return {"arm": arm, "replies": {UNCERTAIN}, "rc": EXIT_UNCERTAIN,
            "present": present, "log_lines": None}


def _repost_ok(row, failures, required=False):
    repost = (row.get("repost") or {}).get("reply")
    if repost is None:
        if required and row.get("reread_owner_ready"):
            failures.append("no repost was made to the restarted owner")
        return
    # D25: the repost is the poster's own octets, so a present article is
    # "already stored here" at any later clock second.  Before D25 the
    # conflict line was accepted too, because the key held Injection-Date
    # (campaign 47bdb9a4, finding K1).
    want = {DUPLICATE} if _present(row) else {OK_240}
    if repost not in want:
        failures.append("repost {!r} not in {}".format(repost, sorted(want)))


def judge_cut(row) -> list:
    failures = []
    want = expectation(row)
    reply = (row.get("post") or {}).get("reply")
    if reply not in want["replies"]:
        failures.append("reply {!r} not in {}".format(reply, sorted(want["replies"])))
    if _rc(row) != want["rc"]:
        failures.append("owner exit {!r} != {}".format(_rc(row), want["rc"]))
    if want["present"] is not None and _present(row) != want["present"]:
        failures.append("candidate present={} != {}".format(_present(row), want["present"]))
    if want["log_lines"] is not None:
        lines = swallowed_log_lines(row)
        if len(lines) != want["log_lines"]:
            failures.append("owner log names the swallowed cleanup error {} times, "
                            "not {}: {!r}".format(len(lines), want["log_lines"], lines))
    for label in ("prior", "candidate"):
        got = row.get("inspect_" + label) or {}
        if got.get("rc") == 0 and not got.get("identical"):
            failures.append(label + " does not reread identical")
    _repost_ok(row, failures, required=True)
    return failures


OVERSIZE_441 = "441 posting failed; the article exceeds the configured size"


def judge_control(row) -> list:
    failures = []
    reply = (row.get("post") or {}).get("reply")
    name = row["name"]
    if name == "dev-refused-no-from":
        if reply != NO_FROM:
            failures.append("reply {!r} != {!r}".format(reply, NO_FROM))
    elif name == "prod-sigkill-mid-article":
        if _present(row):
            failures.append("half-sent article is present")
    elif name.startswith("dev-size-") and not row.get("within_bound"):
        # D27: a POST past the operator's profile bound is refused at the wire
        # with the 441 that names the size, and nothing is stored.
        if (reply or "").rstrip("\r\n") != OVERSIZE_441:
            failures.append("oversize reply {!r} != {!r}".format(reply, OVERSIZE_441))
        if _present(row):
            failures.append("oversize article is present")
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
        print("{:<36} {:<9} {:<5} rc={!s:<4} present={!s:<5} reply={!r} repost={!r}{}".format(
            row["row"], row.get("arm", ""), "FAIL" if row["failures"] else "pass", row["rc"],
            row["present"], row["reply"], row["repost"],
            "".join("\n    " + f for f in row["failures"])))
    print("{} of {} rows pass".format(verdict["total"] - verdict["failed"],
                                      verdict["total"]))


def body_of(octets: int) -> str:
    """A body of about OCTETS octets in lines of 78 letters and CRLF."""
    lines = max(1, octets // 80)
    return "\r\n".join("x" * 78 for _ in range(lines))


def sized_article(total: int) -> bytes:
    """The candidate proto-article padded to exactly TOTAL octets."""
    head = article(CANDIDATE_ID, "candidate", "")
    need = total - len(head)
    if need < 1:
        raise ValueError("size {} is below the header".format(total))
    body, left = [], need
    while left > 80:
        body.append("x" * 78)
        left -= 80
    body.append("y" * left)
    octets = article(CANDIDATE_ID, "candidate", "\r\n".join(body))
    assert len(octets) == total
    return octets


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--images", type=Path)
    parser.add_argument("--work", type=Path)
    parser.add_argument("--out", type=Path)
    parser.add_argument("--body-octets", type=int, default=0,
                        help="candidate body of this many octets in 80-octet lines "
                        "(D27: the cuts on a large article)")
    parser.add_argument("--size-controls", default="",
                        help="comma-separated article sizes in octets, each POSTed "
                        "once to a developer owner as a control row")
    parser.add_argument("--profile-bound", type=int, default=32768,
                        help="the store profile's payload bound the size controls "
                        "are judged against (fn-sbud-payload-bound)")
    parser.add_argument("--init-flags", default="",
                        help="operator fields for every seeded store's init, e.g. "
                        "'--max-article-octets 4194304' (D27)")
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
    native_cuts.verify_native_cut_map()
    verify_post_arms()
    import tests.campaign.native_operator_campaign as campaign
    campaign.INIT_FLAGS[:] = args.init_flags.split()
    dev, prod = args.images / "fn-host-developer", args.images / "fn-host"
    if args.work.exists():
        shutil.rmtree(args.work)
    args.work.mkdir(parents=True)
    prior = args.work / "prior.art"
    prior.write_bytes(article(PRIOR_ID, "prior", "prior accepted content"))
    payload = article(CANDIDATE_ID, "candidate",
                      body_of(args.body_octets) if args.body_octets
                      else "candidate content")
    (args.work / "candidate.art").write_bytes(payload)
    refused = payload.replace(b"From: campaign@campaign.invalid\r\n", b"")
    result = {"images": str(args.images), "init_flags": args.init_flags,
              "profile_bound": args.profile_bound, "cuts": [], "controls": []}
    for cut in native_cuts.POST_CUTS:
        for action in ("kill", "eio"):
            print("cut", cut.name, action, flush=True)
            result["cuts"].append(faulted(dev, args.work, prior, payload, cut, action))
            args.out.write_text(json.dumps(result, indent=1, default=str))
    print("controls", flush=True)
    result["controls"].append(plain(dev, args.work, prior, payload, "dev-accepted-then-sigkill"))
    result["controls"].append(plain(dev, args.work, prior, refused, "dev-refused-no-from",
                                    kill_after=False))
    result["controls"].append(plain(prod, args.work, prior, payload, "prod-accepted-then-sigkill"))
    result["controls"].append(plain(prod, args.work, prior, payload, "prod-sigkill-mid-article",
                                    half=True))
    for size in [int(x) for x in args.size_controls.split(",") if x]:
        sized = sized_article(size)
        print("size control", size, flush=True)
        row = plain(dev, args.work, prior, sized, "dev-size-{}".format(size),
                    kill_after=False)
        row["octets"] = len(sized)
        row["within_bound"] = len(sized) <= args.profile_bound
        result["controls"].append(row)
        args.out.write_text(json.dumps(result, indent=1, default=str))
    result["judgement"] = judge(result)
    args.out.write_text(json.dumps(result, indent=1, default=str))
    print_judgement(result["judgement"])
    return 1 if result["judgement"]["failed"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
