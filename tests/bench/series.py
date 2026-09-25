#!/usr/bin/env python3
"""One store, grown by doubling, until an operation crosses the bridge's limits.

`tests/bench/generate.py` builds a store of a fixed N and `tests/bench/measure.py`
reads it back; this is the third thing the scale question needs, and the one the
pre-realignment measurement could not do: grow a *single* store through a
doubling series and record, at every size, what the host waited for.

Three differences from `generate.py`, each deliberate:

* **One store, not one per point.** Point N+1 continues the store that point N
  left on disk, so the series costs `max(N)` posts instead of their sum, and
  the post curve is one curve rather than five unrelated ones.
* **The host's own post.** `tools/run_store.py`'s `post_article` is the
  function the CLI and the served POST both call -- duplicate check, boundary
  guard, `durable_post` -- where `generate.py` calls `prepare`/`publish`/
  `finish` directly. The numbers here therefore include the two bridge calls
  the real path makes and `generate.py`'s do not.
* **The prompt wait is the measurement.** Every call through the bridge is
  timed against the deadline `Acl2Store.form_timeout` (or the caller) gave it:
  `ACL2_CALL_BASE_SECONDS` is 20 s plus 0.004 s/KiB of form, and reaching it
  is `StoreError: ACL2 prompt timeout`, which is how a store stops serving.
  A point records the worst call and its headroom, so the ceiling is reported
  as a distance, not as a pass.

The series stops at the first point where a single post exceeds
`--post-ceiling` seconds, a reopen exceeds `--recover-ceiling`, the elapsed
budget runs out, or the profile's transaction bound is reached -- and it
**always writes its JSON**, including for a point that died mid-post, which is
the open item `planning/lanes/HANDOFF-w3-scale-profile.md` left behind.

Usage (from the repository root):
  python3 tests/bench/series.py --root DIR --payload 1024 --max 4096 --json OUT
"""
import argparse
import json
import os
from pathlib import Path
import statistics
import sys
import time

ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(ROOT))
from tools import frame_bridge  # noqa: E402
from tools.run_store import (Acl2Store, Store, profile_config,  # noqa: E402
                             StoreError, open_live_store, post_article)
from tests.bench.generate import article_octets, message_id, rss_kib  # noqa: E402

GROUP_NAMES = ["fn.letters", "fn.test"]


class CallTimer:
    """Every bridge call: its wall time, and the deadline it was racing.

    `Acl2Store.call` reads to the ACL2 prompt under a deadline it computes
    from the form's own length; the host raises `StoreError: ACL2 prompt
    timeout` the moment that deadline passes. Timing the call from this side
    measures the same wait the deadline bounds (the correlation marker's round
    trip is inside it), so `seconds / budget_seconds` is the fraction of the
    ceiling one operation has spent.
    """

    def __init__(self, bridge):
        self.bridge = bridge
        self.calls = 0
        self.form_bytes = 0
        self.worst = None

    def install(self):
        original = self.bridge.call

        def timed(form, timeout=None):
            budget = (self.bridge.form_timeout(form) if timeout is None else timeout)
            start = time.monotonic()
            try:
                return original(form, timeout=timeout)
            finally:
                spent = time.monotonic() - start
                self.calls += 1
                self.form_bytes += len(form) + 1
                if self.worst is None or spent > self.worst["seconds"]:
                    self.worst = {"seconds": spent, "budget_seconds": budget,
                                  "form_head": form[:60], "form_bytes": len(form)}
        self.bridge.call = timed
        return self

    def snapshot(self):
        out = {"calls": self.calls, "form_bytes": self.form_bytes}
        if self.worst is not None:
            out["worst_call"] = dict(self.worst)
            out["worst_call"]["headroom_seconds"] = (
                self.worst["budget_seconds"] - self.worst["seconds"])
            out["worst_call"]["fraction_of_deadline"] = (
                self.worst["seconds"] / self.worst["budget_seconds"]
                if self.worst["budget_seconds"] else None)
        return out


def scale_config():
    """The scale profile's values, as ACL2 frames them."""
    return dict(profile_config("scale"), profile="scale")


def summarize(values):
    if not values:
        return None
    ordered = sorted(values)
    return {"runs": len(values), "min": ordered[0], "median": statistics.median(ordered),
            "p90": ordered[min(len(ordered) - 1, int(0.9 * len(ordered)))],
            "max": ordered[-1], "total": sum(values)}


def open_writable(root, first):
    """The store, its bridge and its records; the first call also initializes.

    `open_live_store` is the host's own reopen -- lock, `Acl2Store`, and
    `fn-store-sn-recover` over every committed record -- so timing this call
    times recovery, and no second implementation of it exists here.
    """
    if first:
        store = Store(root, writable=True, profile="scale")
        store.initialize()
        store.acquire()
        bridge = Acl2Store()
        return store, bridge, store.recover(bridge)
    return open_live_store(root, writable=True)


def shut(store, bridge):
    if bridge is not None:
        bridge.close()
    frame_bridge.close()
    if store is not None:
        store.close()


def read_only_reopen(root):
    """Time the reopen a reader does, and report what the process then holds."""
    before = time.monotonic()
    store, bridge, records = open_live_store(root, writable=False)
    seconds = time.monotonic() - before
    try:
        out = {"recover_seconds": seconds, "records": len(records),
               "article_count": bridge.article_count(),
               "rss_kib": rss_kib(bridge.proc.pid)}
    finally:
        shut(store, bridge)
    return out


def profile_calls(root):
    """Where one reopen's seconds go, by ACL2 entry point, on an existing store.

    The bridge is the only place the host can see inside ACL2 without changing
    it: every decision crosses this pipe as one form and one prompt, so
    attributing seconds to the head symbol of each form attributes them to the
    ACL2 function that spent them. The image start and the `include-book` that
    `Acl2Store()` performs are timed separately, because they are a constant
    the store size does not move.
    """
    out = {"root": str(root)}
    by_name = {}
    before = time.monotonic()
    store = Store(root, writable=False)
    store.acquire()
    bridge = Acl2Store()
    out["bridge_start_seconds"] = time.monotonic() - before
    original = bridge.call

    def timed(form, timeout=None):
        head = form.split(None, 1)[0].lstrip("(").strip() or "?"
        start = time.monotonic()
        try:
            return original(form, timeout=timeout)
        finally:
            entry = by_name.setdefault(head, {"calls": 0, "seconds": 0.0,
                                              "form_bytes": 0})
            entry["calls"] += 1
            entry["seconds"] += time.monotonic() - start
            entry["form_bytes"] += len(form) + 1
    bridge.call = timed
    frame_bridge.adopt(bridge)
    try:
        before = time.monotonic()
        records = store.recover(bridge)
        out["reopen_seconds"] = time.monotonic() - before
        out["records"] = len(records)
        out["article_count"] = bridge.article_count()
        out["rss_kib"] = rss_kib(bridge.proc.pid)
        out["by_entry_point"] = dict(sorted(
            by_name.items(), key=lambda kv: -kv[1]["seconds"]))
    finally:
        shut(store, bridge)
    return out


def checkpoints(start, top):
    out, size = [], start
    while size < top:
        out.append(size)
        size *= 2
    out.append(top)
    return out


def peak_rss(point):
    return max([(point.get(key) or {}).get("VmRSS") or 0
                for key in ("rss_kib", "rss_kib_after_posting")], default=0)


def series(root, payload_bytes, start, top, seed, post_ceiling, recover_ceiling,
           budget_seconds, rss_ceiling_kib):
    result = {"payload_bytes": payload_bytes, "profile": scale_config()["profile"],
              "groups": GROUP_NAMES, "seed": seed, "start": start, "max_articles": top,
              "post_ceiling_seconds": post_ceiling,
              "recover_ceiling_seconds": recover_ceiling,
              "rss_ceiling_kib": rss_ceiling_kib,
              "bound": scale_config()["max_transactions"],
              "points": [], "stopped_by": None, "committed": 0, "status": "running"}
    started = time.monotonic()
    committed = 0
    for index, target in enumerate(checkpoints(start, top)):
        if time.monotonic() - started > budget_seconds:
            result["stopped_by"] = "the elapsed budget of %ds" % budget_seconds
            break
        point = {"articles": target, "loadavg": os.getloadavg()}
        store = bridge = None
        posts, forms = [], []
        try:
            before = time.monotonic()
            store, bridge, records = open_writable(root, index == 0)
            point["reopen_writable_seconds"] = time.monotonic() - before
            timer = CallTimer(bridge).install()
            frame_bridge.adopt(bridge)
            committed = len(records)
            point["records_at_open"] = committed
            while committed < target:
                msgid = message_id(seed, committed)
                payload = article_octets(seed, committed, payload_bytes, msgid,
                                         GROUP_NAMES)
                spent_before = timer.form_bytes
                before = time.monotonic()
                sequence, _ = post_article(store, bridge, committed, msgid, payload,
                                           GROUP_NAMES, None)
                posts.append(time.monotonic() - before)
                forms.append(timer.form_bytes - spent_before)
                if sequence is None:
                    raise RuntimeError("the store already held %s" % msgid)
                committed += 1
                result["committed"] = committed
            point["rss_kib_after_posting"] = rss_kib(bridge.proc.pid)
        except (StoreError, RuntimeError) as error:
            point["error"] = "%s: %s" % (type(error).__name__, str(error)[:300])
            result["stopped_by"] = point["error"]
        finally:
            if bridge is not None:
                point.update(timer.snapshot())
            shut(store, bridge)
        point["posted"] = len(posts)
        point["post_seconds"] = summarize(posts)
        point["post_form_bytes"] = summarize(forms)
        if point["posted"]:
            try:
                point.update(read_only_reopen(root))
            except StoreError as error:
                point["reopen_error"] = str(error)[:300]
                result["stopped_by"] = result["stopped_by"] or "reopen: " + str(error)[:200]
        result["points"].append(point)
        if result["stopped_by"]:
            break
        if point["post_seconds"] and point["post_seconds"]["max"] > post_ceiling:
            result["stopped_by"] = ("a single post took %.1f s, over the %.0f s ceiling"
                                    % (point["post_seconds"]["max"], post_ceiling))
            break
        if point.get("recover_seconds", 0) > recover_ceiling:
            result["stopped_by"] = ("recover took %.1f s, over the %.0f s ceiling"
                                    % (point["recover_seconds"], recover_ceiling))
            break
        # Articles are held by value: the box is a ceiling too, and this one
        # is a guard as much as a measurement -- the host is co-tenant.
        if peak_rss(point) > rss_ceiling_kib:
            result["stopped_by"] = ("the bridge process reached %.1f GiB, over the "
                                    "%.1f GiB ceiling"
                                    % (peak_rss(point) / 1048576.0,
                                       rss_ceiling_kib / 1048576.0))
            break
        if target >= scale_config()["max_transactions"]:
            result["stopped_by"] = ("the %s transaction bound of %d, reached with every "
                                    "measured operation still inside its ceiling"
                                    % (scale_config()["profile"],
                                       scale_config()["max_transactions"]))
            break
    result["elapsed_seconds"] = time.monotonic() - started
    # "Passing" is inside both ceilings, not merely returned: the point that
    # crosses a ceiling is measured and reported, and is not the answer to
    # "how many articles does this hold".
    result["largest_passing"] = max(
        [p["articles"] for p in result["points"]
         if p.get("posted") and not p.get("error") and not p.get("reopen_error")
         and (p.get("post_seconds") or {}).get("max", 0) <= post_ceiling
         and p.get("recover_seconds", 0) <= recover_ceiling],
        default=0)
    result["largest_measured"] = max(
        [p["articles"] for p in result["points"] if p.get("posted")], default=0)
    result["status"] = "measured"
    return result


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", required=True)
    parser.add_argument("--payload", type=int, default=1024)
    parser.add_argument("--start", type=int, default=16)
    parser.add_argument("--max", type=int, default=scale_config()["max_transactions"])
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--post-ceiling", type=float, default=20.0,
                        help="tools/run_store.py's ACL2_CALL_BASE_SECONDS")
    parser.add_argument("--recover-ceiling", type=float, default=60.0)
    parser.add_argument("--rss-ceiling-kib", type=int, default=16 * 1024 * 1024,
                        help="stop when the ACL2 bridge process reaches this RSS")
    parser.add_argument("--budget-seconds", type=float, default=3600.0)
    parser.add_argument("--profile-only", action="store_true",
                        help="do not post: reopen the store at --root once and "
                             "attribute the seconds to ACL2 entry points")
    parser.add_argument("--json", default=None)
    args = parser.parse_args(argv)
    if args.max > scale_config()["max_transactions"]:
        parser.error("%s bounds a store at %d transactions"
                     % (scale_config()["profile"], scale_config()["max_transactions"]))
    if args.profile_only:
        profile = {"status": "crashed", "root": args.root}
        try:
            profile = profile_calls(Path(args.root))
            return 0
        except BaseException as error:
            profile["error"] = "%s: %s" % (type(error).__name__, str(error)[:300])
            return 3
        finally:
            text = json.dumps(profile, sort_keys=True)
            if args.json:
                Path(args.json).write_text(text + "\n")
            print("SCALE-PROFILE " + text)
    result = {"status": "crashed", "root": args.root}
    try:
        result = series(Path(args.root), args.payload, args.start, args.max, args.seed,
                        args.post_ceiling, args.recover_ceiling, args.budget_seconds,
                        args.rss_ceiling_kib)
        result["root"] = args.root
        return 0
    except BaseException as error:               # the partial curve is the evidence
        result["error"] = "%s: %s" % (type(error).__name__, str(error)[:300])
        return 3
    finally:
        text = json.dumps(result, sort_keys=True)
        if args.json:
            Path(args.json).write_text(text + "\n")
        summary = dict(result)
        summary["points"] = [
            {k: v for k, v in point.items() if k != "loadavg"}
            for point in result.get("points", [])]
        print("SCALE-SERIES " + json.dumps(summary, sort_keys=True))


if __name__ == "__main__":
    sys.exit(main())
