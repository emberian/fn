#!/usr/bin/env python3
"""Build a scale-grid store of N articles in G groups with P payload octets.

Every article goes through the real acceptance path: `fn-store-sn-prepare`,
a published immutable transaction file, and `fn-store-sn-finish`.  Nothing
here reimplements acceptance, identity, charging or framing; the generator
only chooses bytes and records wall time.

The payload stream is a deterministic SHA-256 counter mode over (seed, index),
so a grid point is reproducible from its `--seed` alone and two runs at the
same point compare like for like.  Incompressible payloads are deliberate: a
repeated-byte payload would make the decimal-octet bridge measurement
optimistic in a way no real article is.

Usage (from the repository root):
  python3 tests/bench/generate.py --root DIR --articles 128 --groups 2 \
      --payload 1024 --seed 1 --profile scale --json OUT.json
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import statistics
import sys
import time

ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(ROOT))
from tools import frame_bridge  # noqa: E402
from tools.run_store import (Acl2Store, DEFAULT_CONFIG, SCALE_CONFIG, Store,  # noqa: E402
                             conservative_charge, group_codes, metadata)

PROFILES = {"dev": DEFAULT_CONFIG, "scale": SCALE_CONFIG}
GROUP_NAMES = ("fn.letters", "fn.test")


def filler(seed, index, size):
    """Deterministic, incompressible body octets for one grid article."""
    out = bytearray()
    counter = 0
    while len(out) < size:
        out += hashlib.sha256(
            ("fn-bench|%d|%d|%d" % (seed, index, counter)).encode("ascii")).digest()
        counter += 1
    return bytes(out[:size])


def message_id(seed, index, octets=0):
    """A distinct Message-ID, optionally padded to an exact octet length.

    `books/article-fields`'s `*fn-af-max-message-id-octets*` is 250 and
    `fn-af-message-idp` is the only judge of the shape; padding the local part
    keeps that shape while reaching the bound.
    """
    base = "<bench-%d-%d@example.invalid>" % (seed, index)
    if not octets or octets <= len(base):
        return base.encode("ascii")
    return ("<bench-%d-%d-%s@example.invalid>"
            % (seed, index, "a" * (octets - len(base) - 1))).encode("ascii")


def body_lines(seed, index, octets):
    """Hex body lines inside `*fn-article-max-line-octets*` (998)."""
    text = filler(seed, index, max(0, octets // 2 + 2)).hex().encode("ascii")
    out = bytearray()
    while len(out) < octets:
        take = min(72, octets - len(out) - 2)
        if take <= 0:
            out += b".."[:octets - len(out)]
            break
        out += text[:take] + b"\r\n"
        text = text[take:] or filler(seed, index + 7919, octets).hex().encode("ascii")
    return bytes(out[:octets])


def article_octets(seed, index, size, msgid, groups, kind="random"):
    """A projectable article of exactly `size` octets.

    The store takes the payload as opaque octets, but `books/nntp`'s archive
    projection parses it on retrieval, so a random blob answers ARTICLE with
    `503 stored article framing unavailable` and measures nothing.  These
    octets carry the same Message-ID the store accepted and the groups the
    post names, inside `books/article`'s line, header and total bounds.
    """
    headers = [b"Message-ID: " + msgid,
               b"Newsgroups: " + ",".join(groups).encode("ascii"),
               b"From: bench <bench@example.invalid>",
               b"Subject: bench %d" % index]
    if kind == "folded":
        # `*fn-article-max-header-lines*` is 128 and
        # `*fn-article-max-header-octets*` is 8192: fold a header as hard as
        # the parser will accept before the body starts.
        used = sum(len(line) + 2 for line in headers) + 2
        while len(headers) < 120 and used + 66 < 8192:
            headers.append(b" " + b"f" * 60)
            used += 64
    head = b"\r\n".join(headers) + b"\r\n\r\n"
    if len(head) >= size:
        raise ValueError("payload %d octets is smaller than its header block %d"
                         % (size, len(head)))
    return head + body_lines(seed, index, size - len(head))


def rss_kib(pid):
    """VmRSS/VmHWM of the ACL2 bridge process, or None off Linux."""
    try:
        status = Path("/proc/%d/status" % pid).read_text()
    except OSError:
        return None
    out = {}
    for line in status.splitlines():
        if line.startswith(("VmRSS:", "VmHWM:")):
            out[line.split(":")[0]] = int(line.split()[1])
    return out or None


class CallMeter:
    """Count the octets this host writes into the ACL2 pipe, per call."""
    def __init__(self, bridge):
        self.bridge, self.calls, self.form_bytes = bridge, 0, 0
        self._original = bridge.call

        def counted(form, timeout=None):
            self.calls += 1
            self.form_bytes += len(form) + 1
            return self._original(form, timeout=timeout)
        bridge.call = counted


def build(root, count, groups, payload_bytes, seed, profile, fanout,
          payload_kind="random", msgid_octets=0):
    names = list(GROUP_NAMES[:groups])
    result = {
        "articles": count, "groups": groups, "group_names": names,
        "fanout": fanout, "payload_bytes": payload_bytes, "seed": seed,
        "payload_kind": payload_kind, "message_id_octets": msgid_octets,
        "profile": profile["profile"] if "profile" in profile else "dev",
        "max_transactions": profile["max_transactions"],
        "status": "running", "root": str(root),
    }
    started = time.monotonic()
    store = Store(root, writable=True, profile=profile)
    bridge = None
    try:
        store.initialize()
        store.acquire()
        bridge = Acl2Store()
        meter = CallMeter(bridge)
        # One ACL2 process for the node and the framing/identity wrappers, so
        # the RSS figure below covers the whole bridge rather than one of two
        # sessions.
        frame_bridge.adopt(bridge)
        store.recover(bridge)
        # `group_codes` takes the Store: it reads the allocation domain the
        # core handed it at recover (`store.config_domain`), which a bare
        # configuration dict does not carry.  Passing the dict raised
        # AttributeError on every run after the configuration-history
        # realignment, which is how this lane found it.
        codes = group_codes(names, store)
        result["group_codes"] = list(codes)
        per_article = []
        post_form_bytes = []
        for sequence in range(count):
            msgid = message_id(seed, sequence, msgid_octets)
            chosen = [codes[(sequence + k) % groups] for k in range(fanout)]
            payload = article_octets(seed, sequence, payload_bytes, msgid,
                                     [names[codes.index(c)] for c in chosen],
                                     payload_kind)
            before, before_bytes = time.monotonic(), meter.form_bytes
            obligation, subject, evidence = metadata(msgid, payload)
            store.advance_frontier(bridge, bridge.next_txid())
            if bridge.prepare(msgid, payload, chosen, obligation, subject, evidence,
                              conservative_charge(payload)) != "prepared":
                raise RuntimeError("core refused a generated article")
            if store.publish(bridge, sequence, bridge.pending_record()) != "durable":
                raise RuntimeError("publication was not durable")
            if store.finish(bridge) != "durable":
                raise RuntimeError("completion was not durable")
            per_article.append(time.monotonic() - before)
            post_form_bytes.append(meter.form_bytes - before_bytes)
            result["committed"] = sequence + 1
        result["commit_seconds"] = time.monotonic() - started
        result["per_article_seconds"] = per_article
        result["post_form_bytes"] = post_form_bytes
        warm = per_article[min(8, len(per_article) // 4):] or per_article
        result["steady_state"] = {
            "from_article": count - len(warm),
            "min_seconds": min(warm), "median_seconds": statistics.median(warm),
            "articles_per_second_median": 1.0 / statistics.median(warm),
            "articles_per_second_best": 1.0 / min(warm),
            "median_post_form_bytes": statistics.median(
                post_form_bytes[count - len(warm):]),
        }
        result["acl2_rss_kib_after_posting"] = rss_kib(bridge.proc.pid)
        result["bridge_calls"] = meter.calls
        result["bridge_form_bytes"] = meter.form_bytes
        result["status"] = "passed"
    except BaseException as error:  # honest partial results
        result.update(status="failed", error=repr(error)[:400])
        raise
    finally:
        if bridge is not None:
            bridge.close()
        store.close()
        result["elapsed_seconds"] = time.monotonic() - started
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", required=True)
    parser.add_argument("--articles", type=int, required=True)
    parser.add_argument("--groups", type=int, default=2)
    parser.add_argument("--fanout", type=int, default=0,
                        help="groups per article; 0 means every configured group")
    parser.add_argument("--payload", type=int, default=1024)
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--profile", choices=sorted(PROFILES), default="dev")
    parser.add_argument("--payload-kind", choices=("random", "folded"),
                        default="random")
    parser.add_argument("--message-id-octets", type=int, default=0,
                        help="pad the Message-ID to exactly this many octets")
    parser.add_argument("--json", default=None)
    args = parser.parse_args()
    if not 1 <= args.groups <= len(GROUP_NAMES):
        parser.error("books/store-config owns the group table: it has %d groups"
                     % len(GROUP_NAMES))
    fanout = args.fanout or args.groups
    profile = PROFILES[args.profile]
    if args.articles > profile["max_transactions"]:
        parser.error("%s bounds a store at %d transactions"
                     % (args.profile, profile["max_transactions"]))
    result = build(Path(args.root), args.articles, args.groups, args.payload,
                   args.seed, profile, fanout, args.payload_kind,
                   args.message_id_octets)
    result["loadavg"] = os.getloadavg()
    text = json.dumps(result, sort_keys=True)
    if args.json:
        Path(args.json).write_text(text + "\n")
    summary = dict(result)
    summary.pop("per_article_seconds", None)
    summary.pop("post_form_bytes", None)
    print(json.dumps(summary, sort_keys=True))


if __name__ == "__main__":
    main()
