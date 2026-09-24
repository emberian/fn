"""The post cuts of `native_cuts.POST_CUTS` observed at the NNTP wire.

`native_operator_campaign` submits the candidate through `operator CFG post`
and records its exit code.  Plan P2 is stated at the NNTP wire: `240` only
after the completion was consumed, `441` naming its reason, an uncertain
outcome `441 ... do not repost`, and the acknowledged article rereading
byte-identical after a kill at any cut.  This probe takes the same cuts on
the same served owner, but submits the candidate with NNTP POST and records
the reply octets the client received (b"" when the connection closed with no
reply).  It judges nothing; the evidence record compares.

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


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--images", type=Path, required=True)
    parser.add_argument("--work", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args(argv)
    native_cuts.verify_native_cut_map()
    dev, prod = args.images / "fn-host-developer", args.images / "fn-host"
    if args.work.exists():
        shutil.rmtree(args.work)
    args.work.mkdir(parents=True)
    prior = args.work / "prior.art"
    prior.write_bytes(article(PRIOR_ID, "prior", "prior accepted content"))
    payload = article(CANDIDATE_ID, "candidate", "candidate content")
    (args.work / "candidate.art").write_bytes(payload)
    refused = payload.replace(b"From: campaign@campaign.invalid\r\n", b"")
    result = {"images": str(args.images), "cuts": [], "controls": []}
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
    args.out.write_text(json.dumps(result, indent=1, default=str))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
