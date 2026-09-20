#!/usr/bin/env python3
"""How many articles fn holds before an operation crosses the bridge's limits.

`tools/deploy_gate.py` establishes that one commit serves, dies and recovers,
with one article in the store. This asks the number that has to ship beside
that claim: at what store size does a single `post` stop returning, at what
size does `recover` stop being a startup and become an outage, and what does a
reader pay per command at the largest size that still works.

Three phases, all on the host, all through the real paths:

1. **store** -- `tests/bench/series.py` grows one store by doubling, at 1 KiB
   and at 32 KiB per article, recording per point the wall time of each post,
   of the reopen the host performs (`open_live_store`, which is lock +
   `fn-store-sn-recover` over every record), and of the slowest single bridge
   call against the deadline that call was racing. It stops at the first point
   where a post exceeds 20 s (`tools/run_store.py`'s `ACL2_CALL_BASE_SECONDS`,
   the prompt timeout that ends the operation) or a recover exceeds 60 s.
2. **reader** -- against the largest passing store, served over a socket by
   the entry point this commit has: GROUP, ARTICLE by number across the range,
   OVER over the whole range (or the LISTGROUP+HEAD substitution, labelled,
   when the commit has no OVER), and 100 sequential connections.
3. **like for like** -- the same `tests/bench/generate.py` and
   `tests/bench/measure.py` the pre-realignment measurement used, at its own
   grid points, so the comparison against the table in
   `planning/lanes/HANDOFF-w3-scale-profile.md` is between two runs of one
   method rather than between two methods.

    python3 tools/scale_gate.py dev --host persvati

Shipping the commit, installing the host's certificates pair by pair,
starting a server, the step accounting and the evidence renderer are
`tools/deploy_gate.py`'s, reused by subclassing. This file owns the series,
the reader measurement, the comparison and the tables.

Dry run. ``--dry-run --home DIR`` runs every script through bash on this
machine with `HOME` redirected and no ssh; `--overlay` puts fakes over the
deployed tree. `tests/test_scale_gate.py` drives exactly that, with fake
series, generate, measure and server entry points: it establishes that this
gate parses, stops, compares and renders, and nothing whatever about fn.
"""
from __future__ import annotations

import argparse
import datetime as dt
import json
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(Path(__file__).resolve().parent))

import deploy_gate                                             # noqa: E402
from deploy_gate import (DEFAULT_HOST, GROUPS, GateError, Host,  # noqa: E402
                         LocalHost, SshHost, resolve)

# The pre-realignment measurement, quoted from its own handoff so the
# comparison table cites a number this repository can check, not a memory.
# planning/lanes/HANDOFF-w3-scale-profile.md, "Cliffs found, with numbers":
# hbox, ACL2 8.7 over SBCL 2.6.8, five runs per point (three at N >= 256),
# G=2, both groups per article, P=1024, dev profile.
HANDOFF = {
    "source": "planning/lanes/HANDOFF-w3-scale-profile.md",
    "host": "hbox (24 cores), load average 2.7 to 5.7",
    "reopen_median_seconds": {16: 0.793, 128: 2.718, 256: 12.729},
    "post": "N=512 and N=1024 each ended in `StoreError: ACL2 prompt timeout` "
            "inside one `fn-store-sn-prepare`, after about 35 minutes of posting; "
            "the N=256 median prepare was still under a second",
    "spread": "absolute latencies there carry about +/- 20% with host load; the "
              "ratios replicated",
}

# The grid the handoff ran, so phase 3 lands on its points exactly.
PREVIOUS_METHOD_POINTS = (16, 32, 64, 128, 256)
PREVIOUS_METHOD_RUNS = 3


READER_DRIVER = r'''#!/usr/bin/env python3
"""Reader-side scale measurement over a live socket. No fn module is imported.

`Conn` is tools/deploy_gate.py's driver, already on the host as drive.py: one
socket implementation for every gate, so a reply read here is read the way the
deploy gate reads one.
"""
import argparse, json, os, statistics, sys, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from drive import Conn


def summarize(values):
    if not values:
        return None
    ordered = sorted(values)
    return {"runs": len(ordered), "min": ordered[0],
            "median": statistics.median(ordered),
            "p90": ordered[min(len(ordered) - 1, int(0.9 * len(ordered)))],
            "max": ordered[-1], "total": sum(ordered)}


def timed(conn, text, multiline=False):
    before = time.monotonic()
    status, body = conn.cmd(text, multiline=multiline)
    return time.monotonic() - before, status, body


def span(status):
    """RFC 3977 section 6.1.1: `211 number low high group`."""
    parts = status.split()
    if len(parts) >= 4 and parts[0] == "211":
        try:
            return int(parts[1]), int(parts[2]), int(parts[3])
        except ValueError:
            return None
    return None


def spread(low, high, count):
    if high <= low:
        return [low]
    step = max(1, (high - low) // max(1, count - 1))
    out = list(range(low, high + 1, step))[:count]
    if out[-1] != high:
        out.append(high)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--port", type=int, required=True)
    ap.add_argument("--group", required=True)
    ap.add_argument("--connections", type=int, default=100)
    ap.add_argument("--samples", type=int, default=16)
    ap.add_argument("--timeout", type=float, default=600.0)
    ap.add_argument("--over-budget", type=float, default=900.0)
    ap.add_argument("--json", default=None)
    args = ap.parse_args()
    out = {"port": args.port, "group_name": args.group}

    before = time.monotonic()
    conn = Conn(args.port, timeout=args.timeout)
    out["first_connection_seconds"] = time.monotonic() - before
    out["greeting"] = conn.greeting

    seconds, status, _ = timed(conn, "GROUP " + args.group)
    out["group"] = {"seconds": seconds, "status": status}
    bounds = span(status)
    if bounds is None:
        out["ok"] = False
        out["reason"] = "GROUP did not answer 211: " + status
        conn.close()
        return out
    count, low, high = bounds
    out["count"], out["low"], out["high"] = count, low, high

    numbers = spread(low, high, args.samples)
    by_number, bytes_read = [], 0
    for number in numbers:
        seconds, status, body = timed(conn, "ARTICLE %d" % number, multiline=True)
        by_number.append({"number": number, "seconds": seconds,
                          "status": status[:32], "lines": len(body)})
        bytes_read += sum(len(one) + 2 for one in body)
    out["article_by_number"] = by_number
    out["article_by_number_seconds"] = summarize([one["seconds"] for one in by_number])
    out["article_bytes"] = bytes_read

    # OVER over the whole range.  books/nntp admits GROUP, LISTGROUP, LAST,
    # NEXT, ARTICLE, HEAD, BODY and STAT; when OVER is not there the
    # enumeration a client must do instead is measured under its own name.
    seconds, status, body = timed(conn, "OVER %d-%d" % (low, high), multiline=True)
    over = {"command": "OVER %d-%d" % (low, high), "seconds": seconds,
            "status": status[:64], "lines": len(body)}
    over["served"] = status.startswith("224")
    if not over["served"]:
        seconds, status, listed = timed(conn, "LISTGROUP " + args.group, multiline=True)
        over["listgroup"] = {"seconds": seconds, "status": status[:32],
                             "lines": len(listed)}
        if status.startswith("211"):
            wanted = [int(one) for one in listed if one.strip().isdigit()]
        else:
            wanted = list(range(low, high + 1))
        heads, head_bytes = 0, 0
        before = time.monotonic()
        for number in wanted:
            _, status, block = timed(conn, "HEAD %d" % number, multiline=True)
            heads += 1
            head_bytes += sum(len(one) + 2 for one in block)
            if time.monotonic() - before > args.over_budget:
                break
        elapsed = time.monotonic() - before
        over["substitution"] = {
            "what": "LISTGROUP then HEAD per number, the enumeration a client "
                    "does when the server has no OVER",
            "heads": heads, "of": len(wanted), "seconds": elapsed,
            "seconds_per_article": elapsed / heads if heads else None,
            "reply_bytes": head_bytes,
            "complete": heads == len(wanted)}
    out["over"] = over
    conn.close()

    # N sequential connections: greeting, GROUP, one ARTICLE, QUIT.  A reader
    # that pins a snapshot per connection pays for the store size here.
    per_connection, failures = [], 0
    middle = (low + high) // 2
    for index in range(args.connections):
        before = time.monotonic()
        try:
            one = Conn(args.port, timeout=args.timeout)
            one.cmd("GROUP " + args.group)
            one.cmd("ARTICLE %d" % middle, multiline=True)
            one.close()
            per_connection.append(time.monotonic() - before)
        except Exception as error:               # a refused connection is data
            failures += 1
            out.setdefault("connection_errors", []).append(
                "%d: %s: %s" % (index, type(error).__name__, str(error)[:120]))
    out["connections"] = {"asked": args.connections, "completed": len(per_connection),
                          "failed": failures,
                          "seconds": summarize(per_connection)}
    out["ok"] = failures == 0 and bool(per_connection)
    return out


if __name__ == "__main__":
    result = main()
    print("SCALE-READER " + json.dumps(result, sort_keys=True))
    sys.exit(0 if result.get("ok") else 1)
'''


def extract(output: str, tag: str):
    """The one JSON line a driver printed, or None with the reason kept."""
    for line in output.splitlines():
        if line.startswith(tag + " "):
            try:
                return json.loads(line[len(tag) + 1:])
            except ValueError:
                return None
    return None


def cell(value, spec="{:.3f}"):
    return "-" if value is None else spec.format(value)


class ScaleGate(deploy_gate.DeployGate):
    """The deploy gate's machinery, driving a measurement instead of a demo."""

    TITLE = "Scale gate"
    TOOL = "tools/scale_gate.py"
    PREAMBLE = (
        "One commit, unpacked on a farm box, grown by doubling until an operation",
        "crosses the bridge's limits, then read through a live socket. Every figure",
        "is a wall time measured on that host under its load at that moment; none of",
        "it is a proof, a bound, or a guarantee about another machine.")
    FACT_KEYS = ("os", "kernel", "python3", "acl2version", "certificates", "server",
                 "ceiling", "largest store")
    STANDING_GAPS = (
        "A wall time is not a complexity bound. The exponents quoted below are fits\n"
        "  over a handful of doublings on one host, not theorems about the books.",
        "One host, one load window. The pre-realignment table this compares against\n"
        "  was measured on a different box; only the like-for-like phase re-runs its\n"
        "  method here, and even that is a different machine from its original.",
        "The series posts through `post_article`, the function the CLI and the served\n"
        "  POST call. It does not exercise POST over a socket at scale, nor two\n"
        "  writers, nor any crash point: the deploy and two-node gates own those.",
        "Articles are one shape (two groups, incompressible body, ordinary headers).\n"
        "  The hostile-input axes -- folded headers, maximum Message-IDs -- are the\n"
        "  handoff's grid and are not re-run here.",
        "The certificates were not re-established here; see the certificate row.")

    def __init__(self, host, repo, commit, rev, tree, payloads=(1024, 32768),
                 max_articles=4096, start=16, post_ceiling=20.0,
                 recover_ceiling=60.0, budget_seconds=3600.0, connections=100,
                 previous_points=PREVIOUS_METHOD_POINTS, skip_previous=False,
                 niceness=10, rss_ceiling_kib=16 * 1024 * 1024, reuse=False,
                 adopted=None, extra_overlays=(), **kwargs):
        super().__init__(host, repo, commit, rev, tree, **kwargs)
        self.payloads = list(payloads)
        self.max_articles = max_articles
        self.start = start
        self.post_ceiling = post_ceiling
        self.recover_ceiling = recover_ceiling
        self.budget_seconds = budget_seconds
        self.connections = connections
        self.previous_points = list(previous_points)
        self.skip_previous = skip_previous
        self.niceness = niceness
        self.rss_ceiling_kib = rss_ceiling_kib
        self.reuse = reuse
        self.adopted = dict(adopted or {})
        self.extra_overlays = [Path(one) for one in extra_overlays]
        self.series: dict[int, dict] = {}
        self.reader: dict = {}
        self.profile: dict = {}
        self.previous: dict[int, dict] = {}
        self.cli_recover = None

    # -- phases -----------------------------------------------------------
    def nice(self, command: str) -> str:
        """persvati is co-tenant: a measurement waits, it does not take."""
        return "nice -n {} {}".format(self.niceness, command)

    def store_root(self, payload: int) -> str:
        return "{}/store-{}".format(self.run, payload)

    def run_series(self, payload: int):
        """One doubling series, one store, one JSON. Its stop is the finding."""
        root = self.store_root(payload)
        out = "{}/series-{}.json".format(self.run, payload)
        step = self.sh("series {} octets".format(payload), self.cd(self.nice(
            "python3 tests/bench/series.py --root {root} --payload {payload} "
            "--start {start} --max {top} --post-ceiling {post} "
            "--recover-ceiling {recover} --rss-ceiling-kib {rss} "
            "--budget-seconds {budget} --json {out}"
            .format(root=root, payload=payload, start=self.start, top=self.max_articles,
                    post=self.post_ceiling, recover=self.recover_ceiling,
                    rss=self.rss_ceiling_kib,
                    budget=int(self.budget_seconds), out=out))),
            timeout=int(self.budget_seconds) + 1800, expect=None)
        data = extract(step.output, "SCALE-SERIES")
        if data is None:
            self.gaps.append(
                "the {} octet series produced no JSON line; its store is at {} on the "
                "host and its last output was: {}".format(payload, root,
                                                          step.first_line or "(nothing)"))
            return None
        self.series[payload] = data
        if data.get("stopped_by"):
            self.facts.setdefault("ceiling", "{} octets: {} articles, stopped by {}".format(
                payload, data.get("largest_passing"), data["stopped_by"]))
        if step.rc not in (0, None):
            self.gaps.append(
                "the {} octet series exited {}: {}. The points it did measure are "
                "below; the curve past them is not measured, not absent."
                .format(payload, step.rc, data.get("error", "no error recorded")))
        return data

    def adopt_series(self, payload: int, path: str):
        """Take a series JSON an earlier invocation left on the host.

        A series at the profile bound is hours of posting; a gate that could
        only ever measure it from an empty store would re-post four thousand
        articles to render a table. The adopted run is recorded as a gap
        naming its file, because the steps that produced it are in that run's
        record and not in this one's.
        """
        step = self.sh("adopt series {} octets".format(payload),
                       "cat {}".format(path), timeout=300, expect=None)
        data = None
        if step.rc == 0 and step.output.strip():
            try:
                data = json.loads(step.output.strip().splitlines()[-1])
            except ValueError:
                data = None
        if data is None:
            self.skip("series {} octets".format(payload), "cat " + path,
                      "the adopted series JSON at {} could not be read or parsed"
                      .format(path))
            return None
        self.series[payload] = data
        self.gaps.append(
            "the {} octet series was measured by an earlier invocation of this gate "
            "against the same host, tree and store, and its JSON was adopted here "
            "from {}. Its per-step record is that run's, not this one's; the numbers "
            "in the tables are the ones that file holds.".format(payload, path))
        if data.get("stopped_by"):
            self.facts.setdefault("ceiling", "{} octets: {} articles, stopped by {}".format(
                payload, data.get("largest_passing"), data["stopped_by"]))
        return data

    def profile_slowest(self, payload: int):
        """Where the reopen's seconds go, by ACL2 entry point, once."""
        step = self.sh("profile the reopen ({} octets)".format(payload), self.cd(self.nice(
            "python3 tests/bench/series.py --root {root} --profile-only --json "
            "{run}/profile-{payload}.json".format(root=self.store_root(payload),
                                                  run=self.run, payload=payload))),
            timeout=3600, expect=None)
        data = extract(step.output, "SCALE-PROFILE")
        if data is None:
            self.skip("profile the reopen", "series.py --profile-only",
                      "the profile pass printed no JSON: " + (step.first_line or "nothing"))
            return None
        self.profile = data
        return data

    def cli_recover_once(self, payload: int):
        """The recover the operator runs, process start included, at the top."""
        step = self.sh("CLI recover at the largest store", self.cd(self.nice(self.fn(
            "--store {} recover".format(self.store_root(payload))))),
            timeout=int(max(1800, self.recover_ceiling * 20)), expect=None)
        self.cli_recover = {"seconds": step.seconds, "rc": step.rc,
                            "first_line": step.first_line, "payload": payload}
        if step.rc not in (0, None):
            self.gaps.append("`run_store.py recover` exited {} at the largest store: {}"
                             .format(step.rc, step.first_line))
        return step

    def read_at_scale(self, payload: int):
        """The served path at the largest passing store: GROUP, ARTICLE, OVER, 100."""
        root = self.store_root(payload)
        kind, command = self.server_command(store=root, run=self.run)
        command = self.nice(command)
        if not self.start_server(kind, command, "scale"):
            fallback = self.nice(
                "python3 tools/run_reader.py --store {} --port 0".format(root))
            self.gaps.append(
                "the {} entry point did not reach LISTENING over this store; the gate "
                "fell back to a read-only tools/run_reader.py. Every reader figure "
                "below is the reader's, not the {}'s.".format(kind, kind))
            kind = "reader (read-only)"
            if not self.start_server(kind, fallback, "scale"):
                self.skip("reader at scale", "scale_reader.py",
                          "no server entry point reached LISTENING over the {} article "
                          "store; the reader figures are missing, not zero".format(
                              self.series.get(payload, {}).get("largest_measured")))
                return None
        step = self.sh("reader at scale", self.cd(
            "python3 {run}/scale_reader.py --port {port} --group {group} "
            "--connections {n} --json {run}/reader.json".format(
                run=self.run, port=self.port, group=GROUPS[0], n=self.connections)),
            timeout=7200, expect=None)
        data = extract(step.output, "SCALE-READER")
        self.stop_server("scale")
        if data is None:
            self.gaps.append("the reader driver printed no JSON: "
                             + (step.first_line or "nothing"))
            return None
        data["server"] = kind
        data["payload_bytes"] = payload
        self.reader = data
        if not data.get("over", {}).get("served"):
            self.gaps.append(
                "OVER is not served on this commit (it answered '{}'), so the range "
                "figure below is the LISTGROUP+HEAD enumeration a client must do "
                "instead, under its own name. books/nntp admits GROUP, LISTGROUP, "
                "LAST, NEXT, ARTICLE, HEAD, BODY and STAT.".format(
                    data.get("over", {}).get("status", "?")))
        if data.get("connections", {}).get("failed"):
            self.gaps.append("{} of {} sequential connections did not complete".format(
                data["connections"]["failed"], data["connections"]["asked"]))
        return data

    def previous_method(self):
        """The handoff's own scripts, at the handoff's own points, here."""
        for count in self.previous_points:
            root = "{}/prev-{}".format(self.run, count)
            build = self.sh("previous method: generate {}".format(count), self.cd(self.nice(
                "python3 tests/bench/generate.py --root {root} --articles {n} "
                "--groups 2 --payload 1024 --seed 1 --profile scale "
                "--json {run}/prev-gen-{n}.json".format(root=root, n=count, run=self.run))),
                timeout=7200, expect=None)
            if build.rc not in (0, None):
                self.gaps.append(
                    "the previous method did not build its N={} point ({}); the "
                    "comparison stops there".format(count, build.first_line))
                break
            read = self.sh("previous method: measure {}".format(count), self.cd(self.nice(
                "python3 tests/bench/measure.py --root {root} --articles {n} --runs {r} "
                "--group {group} --json {run}/prev-measure-{n}.json".format(
                    root=root, n=count, r=PREVIOUS_METHOD_RUNS, group=GROUPS[0],
                    run=self.run))),
                timeout=7200, expect=None)
            line = [one for one in read.output.splitlines() if one.startswith("{")]
            if read.rc not in (0, None) or not line:
                self.gaps.append("the previous method measured no N={} point: {}".format(
                    count, read.first_line))
                continue
            try:
                self.previous[count] = json.loads(line[-1])
            except ValueError:
                self.gaps.append("the previous method's N={} JSON did not parse".format(count))
            self.sh("drop the previous method's N={} store".format(count),
                    "rm -rf {}".format(root))

    # -- the whole gate ---------------------------------------------------
    def execute(self):
        self.preflight()
        if self.reuse:
            # The stores under this tree are the measurement; re-shipping would
            # `rm -rf` them.  The drivers are still refreshed from this source.
            probe = self.sh("reuse the deployed tree",
                            "test -d {d}/tests/bench && echo REUSING {d} || "
                            "{{ echo NO-TREE {d}; exit 1; }}".format(d=self.deploy))
            if probe.rc != 0:
                raise GateError("--reuse but there is no tree at " + self.deploy)
            self.sh("make run dir", "mkdir -p {}".format(self.run))
            self.push_file(deploy_gate.DRIVER, "{}/drive.py".format(self.run), mode="755")
            self.push_file(deploy_gate.CERTPICK, "{}/certpick.py".format(self.run),
                           mode="755")
        else:
            self.ship()
        for overlay in self.extra_overlays:
            self.push_tree(overlay)
        self.push_file(READER_DRIVER, "{}/scale_reader.py".format(self.run), mode="755")
        self.certificates()
        for payload, path in sorted(self.adopted.items()):
            self.adopt_series(payload, path)
        for payload in self.payloads:
            if payload in self.adopted:
                continue            # adopted above; measuring it twice is not a check
            self.run_series(payload)
        largest = self.largest_store()
        if largest is None:
            raise GateError("no series measured a single point; nothing to read")
        self.facts["largest store"] = (
            "{} articles of {} octets inside both ceilings; {} measured".format(
                self.series[largest].get("largest_passing"), largest,
                self.series[largest].get("largest_measured")))
        self.profile_slowest(largest)
        self.cli_recover_once(largest)
        self.read_at_scale(largest)
        if self.skip_previous:
            self.skip("previous method", "tests/bench/generate.py + measure.py",
                      "--skip-previous: the like-for-like comparison was not run")
        else:
            self.previous_method()

    def largest_store(self):
        """The payload size whose series got furthest, for the reader phase."""
        for key in ("largest_passing", "largest_measured"):
            best = max([(data.get(key) or 0, payload)
                        for payload, data in self.series.items()], default=(0, None))
            if best[0]:
                return best[1]
        return None

    def cleanup(self):
        self.stop_server("scale")
        if not self.keep:
            self.sh("remove the deploy tree", "rm -rf {}".format(self.deploy))

    # -- evidence ---------------------------------------------------------
    def evidence(self, path: Path, started: str, elapsed: float):
        path = super().evidence(path, started, elapsed)
        text = path.read_text()
        head, _, tail = text.partition("\n## Every command\n")
        path.write_text(head + "\n".join(self.tables()) + "\n## Every command\n" + tail)
        return path

    def tables(self) -> list[str]:
        lines: list[str] = []
        lines += self.series_tables()
        lines += self.ceiling_table()
        lines += self.reader_table()
        lines += self.comparison_table()
        return lines

    def series_tables(self) -> list[str]:
        lines = ["", "## The series: one store, grown by doubling", ""]
        if not self.series:
            return lines + ["No series point was measured.", ""]
        for payload in sorted(self.series):
            data = self.series[payload]
            lines += [
                "### {} octets per article".format(payload),
                "",
                "| N | posted | post median s | post max s | reopen (writable) s | "
                "recover (read-only) s | worst bridge call s | its deadline s | "
                "RSS MiB |",
                "| --- | --- | --- | --- | --- | --- | --- | --- | --- |",
            ]
            for point in data.get("points", []):
                post = point.get("post_seconds") or {}
                worst = point.get("worst_call") or {}
                rss = (point.get("rss_kib") or {}).get("VmRSS")
                lines.append("| {} | {} | {} | {} | {} | {} | {} | {} | {} |".format(
                    point.get("articles"), point.get("posted"),
                    cell(post.get("median")), cell(post.get("max")),
                    cell(point.get("reopen_writable_seconds")),
                    cell(point.get("recover_seconds")),
                    cell(worst.get("seconds")), cell(worst.get("budget_seconds"), "{:.1f}"),
                    cell(rss / 1024.0 if rss else None, "{:.0f}")))
            lines += ["",
                      "Stopped by: {}".format(data.get("stopped_by") or "nothing"),
                      "",
                      "Largest passing store: {} articles; {} committed in {:.0f} s.".format(
                          data.get("largest_passing"), data.get("committed"),
                          data.get("elapsed_seconds") or 0.0),
                      ""]
            for point in data.get("points", []):
                if point.get("error") or point.get("reopen_error"):
                    lines.append("- N={}: {}".format(point.get("articles"),
                                                     point.get("error")
                                                     or point.get("reopen_error")))
            lines.append("")
        return lines

    def growth(self, payload: int, key: str):
        """The exponent a straight line through the doublings implies, or None."""
        points = [(p["articles"], p.get(key)) for p in
                  self.series.get(payload, {}).get("points", []) if p.get(key)]
        points = [(n, v) for n, v in points if n and v and v > 0]
        if len(points) < 2:
            return None
        (n0, v0), (n1, v1) = points[0], points[-1]
        if n1 <= n0 or v1 <= 0 or v0 <= 0:
            return None
        from math import log
        return log(v1 / v0) / log(n1 / n0)

    def ceiling_table(self) -> list[str]:
        """One sentence per operation: the pessimistic number and its scope."""
        lines = ["", "## The ceiling per operation", "",
                 "Each sentence is the pessimistic number measured in this run with the "
                 "scope it covers; nothing here is a bound proved of the books.", ""]
        for payload in sorted(self.series):
            data = self.series[payload]
            points = [p for p in data.get("points", []) if p.get("posted")]
            if not points:
                continue
            top = points[-1]
            post = top.get("post_seconds") or {}
            worst = top.get("worst_call") or {}
            exponent = self.growth(payload, "recover_seconds")
            lines.append(
                "- **post, {} octets**: the slowest single post at the largest measured "
                "store ({} articles) took {} s, against the {} s prompt deadline that "
                "call was racing -- {} of it; median {} s. Scope: this host, this load, "
                "two groups per article, one writer, incompressible bodies.".format(
                    payload, top.get("articles"), cell(post.get("max")),
                    cell(worst.get("budget_seconds"), "{:.1f}"),
                    cell(worst.get("fraction_of_deadline"), "{:.1%}"),
                    cell(post.get("median"))))
            lines.append(
                "- **recover, {} octets**: reopening the {} article store took {} s "
                "read-only{}. Scope: one reopen per point on this host; the CLI recover, "
                "process start included, is the row below.".format(
                    payload, top.get("articles"), cell(top.get("recover_seconds")),
                    "" if exponent is None else
                    ", growing as about N^{:.2f} across the measured doublings".format(
                        exponent)))
        if self.cli_recover:
            lines.append(
                "- **`run_store.py recover`**: {:.1f} s wall at the largest store "
                "({} octets), exit {}. Scope: one invocation, ACL2 image start and "
                "`include-book` included, no concurrent load of ours.".format(
                    self.cli_recover["seconds"], self.cli_recover["payload"],
                    self.cli_recover["rc"]))
        if self.profile:
            share = self.profile.get("by_entry_point") or {}
            worst = max(share.items(), key=lambda kv: kv[1].get("seconds", 0),
                        default=(None, {}))
            lines.append(
                "- **where the reopen's seconds go**: image start and `include-book` "
                "{} s; then {} took {} s over {} calls of the {:.1f} s reopen. Scope: "
                "one profiled reopen of the largest store, timed at the bridge.".format(
                    cell(self.profile.get("bridge_start_seconds"), "{:.1f}"),
                    worst[0], cell(worst[1].get("seconds"), "{:.1f}"),
                    worst[1].get("calls"), self.profile.get("reopen_seconds") or 0.0))
        reader = self.reader
        if reader:
            article = reader.get("article_by_number_seconds") or {}
            over = reader.get("over") or {}
            conn = reader.get("connections") or {}
            lines.append(
                "- **GROUP**: {} s on a {} article group, served over a socket by {}. "
                "Scope: one command on a fresh connection.".format(
                    cell((reader.get("group") or {}).get("seconds")),
                    reader.get("count"), reader.get("server")))
            lines.append(
                "- **ARTICLE by number**: worst of {} positions across the range "
                "{}..{} was {} s, median {} s. Scope: one connection, sampled "
                "positions, {} octet articles.".format(
                    article.get("runs"), reader.get("low"), reader.get("high"),
                    cell(article.get("max")), cell(article.get("median")),
                    reader.get("payload_bytes")))
            if over.get("served"):
                lines.append(
                    "- **OVER over the full range**: {} s for {} lines over {}..{}. "
                    "Scope: one command, one connection.".format(
                        cell(over.get("seconds")), over.get("lines"),
                        reader.get("low"), reader.get("high")))
            else:
                sub = over.get("substitution") or {}
                lines.append(
                    "- **OVER-equivalent over the full range**: OVER answered '{}', so "
                    "the measured figure is LISTGROUP plus HEAD per number: {} s for "
                    "{} of {} articles ({} s each){}. Scope: the enumeration a client "
                    "must do on a server with no OVER; it is a substitution, not OVER."
                    .format(over.get("status"), cell(sub.get("seconds"), "{:.1f}"),
                            sub.get("heads"), sub.get("of"),
                            cell(sub.get("seconds_per_article")),
                            "" if sub.get("complete") else
                            ", cut off at the driver's budget"))
            lines.append(
                "- **a connection**: {} of {} sequential connections completed, each "
                "greeting, GROUP, one ARTICLE and QUIT; worst {} s, median {} s, {} s "
                "for all of them. Scope: sequential, one client, no concurrency.".format(
                    conn.get("completed"), conn.get("asked"),
                    cell((conn.get("seconds") or {}).get("max")),
                    cell((conn.get("seconds") or {}).get("median")),
                    cell((conn.get("seconds") or {}).get("total"), "{:.0f}")))
        lines.append("")
        return lines

    def reader_table(self) -> list[str]:
        lines = ["", "## The reader at the largest store", ""]
        if not self.reader:
            return lines + ["The reader phase did not run.", ""]
        reader = self.reader
        lines += ["| what | seconds |", "| --- | --- |",
                  "| first connection (greeting) | {} |".format(
                      cell(reader.get("first_connection_seconds"))),
                  "| GROUP {} ({} articles) | {} |".format(
                      reader.get("group_name"), reader.get("count"),
                      cell((reader.get("group") or {}).get("seconds")))]
        for one in reader.get("article_by_number", []):
            lines.append("| ARTICLE {} ({}) | {} |".format(
                one["number"], one["status"].split()[0], cell(one["seconds"])))
        over = reader.get("over") or {}
        lines.append("| {} | {} |".format(over.get("command"), cell(over.get("seconds"))))
        if over.get("substitution"):
            sub = over["substitution"]
            lines.append("| LISTGROUP + {} HEADs (OVER substitution) | {} |".format(
                sub.get("heads"), cell(sub.get("seconds"))))
        conn = (reader.get("connections") or {}).get("seconds") or {}
        lines += ["| {} sequential connections, total | {} |".format(
            (reader.get("connections") or {}).get("completed"), cell(conn.get("total"))),
            "| one connection, median | {} |".format(cell(conn.get("median"))),
            "| one connection, worst | {} |".format(cell(conn.get("max"))), ""]
        return lines

    def comparison_table(self) -> list[str]:
        lines = ["", "## Like for like with the pre-realignment measurement", "",
                 "The rows below ran `tests/bench/generate.py` and "
                 "`tests/bench/measure.py` -- the same two scripts, at the same grid "
                 "points -- so the only differences from the cited table are the tree "
                 "and the host. The cited column is {} ({}); {}.".format(
                     HANDOFF["source"], HANDOFF["host"], HANDOFF["spread"]), ""]
        if not self.previous:
            return lines + ["The like-for-like phase did not run.", ""]
        lines += ["| N | reopen median s, this run | reopen median s, cited | ratio | "
                  "GROUP median s | OVER-equivalent s/article |",
                  "| --- | --- | --- | --- | --- | --- |"]
        for count in sorted(self.previous):
            data = self.previous[count]
            here = (data.get("reopen_seconds") or {}).get("median")
            cited = HANDOFF["reopen_median_seconds"].get(count)
            ratio = (here / cited) if (here and cited) else None
            lines.append("| {} | {} | {} | {} | {} | {} |".format(
                count, cell(here), cell(cited), cell(ratio, "{:.2f}x"),
                cell((data.get("group_seconds") or {}).get("median")),
                cell((data.get("over_equivalent_seconds_per_article") or {}).get("median"))))
        lines += ["",
                  "Cited, on posting: {}.".format(HANDOFF["post"]),
                  ""]
        return lines


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("commit", help="the commit-ish to measure")
    parser.add_argument("--host", default=DEFAULT_HOST)
    parser.add_argument("--tree", default="dev", help="gate directory prefix on the host")
    parser.add_argument("--repo", default=str(ROOT))
    parser.add_argument("--jobs", type=int, default=16)
    parser.add_argument("--evidence", default=None)
    parser.add_argument("--keep", action="store_true",
                        help="leave the deploy tree and its stores on the host")
    parser.add_argument("--dry-run", action="store_true",
                        help="run every script through local bash with HOME redirected")
    parser.add_argument("--home", default=None, help="the fake HOME for --dry-run")
    parser.add_argument("--acl2", default=None,
                        help="the host's ACL2 image; the default is tools/farm.py's entry")
    parser.add_argument("--overlay", action="append", default=[],
                        help="a directory copied over the deployed tree; repeatable")
    parser.add_argument("--payload", action="append", type=int, default=[],
                        help="octets per article; repeatable, default 1024 and 32768")
    parser.add_argument("--start", type=int, default=16)
    parser.add_argument("--max-articles", type=int, default=4096,
                        help="the scale profile's transaction bound")
    parser.add_argument("--post-ceiling", type=float, default=20.0)
    parser.add_argument("--recover-ceiling", type=float, default=60.0)
    parser.add_argument("--budget-seconds", type=float, default=3600.0,
                        help="per series; a stop at the budget is recorded as one")
    parser.add_argument("--connections", type=int, default=100)
    parser.add_argument("--server-ready", type=int, default=1800,
                        help="seconds to wait for LISTENING over a large store")
    parser.add_argument("--reuse", action="store_true",
                        help="do not re-ship: measure against the tree and stores "
                             "already at $HOME/fn-deploy/<rev> on the host")
    parser.add_argument("--adopt-series", action="append", default=[],
                        metavar="PAYLOAD=PATH",
                        help="take this payload size's series from a JSON an earlier "
                             "invocation wrote on the host, instead of running it")
    parser.add_argument("--rss-ceiling-gib", type=float, default=16.0,
                        help="stop a series when the bridge process reaches this RSS")
    parser.add_argument("--nice", type=int, default=10,
                        help="niceness for every measured command on the host")
    parser.add_argument("--skip-previous", action="store_true",
                        help="do not run the like-for-like phase")
    args = parser.parse_args(argv)

    repo = Path(args.repo).resolve()
    commit, rev = resolve(repo, args.commit)
    if args.dry_run:
        if args.home is None:
            parser.error("--dry-run needs --home")
        host: Host = LocalHost(Path(args.home).resolve())
    else:
        host = SshHost(args.host)
    # A server that has to recover a four-thousand article store before it
    # prints LISTENING needs longer than the deploy gate's demo store did.
    deploy_gate.SERVER_READY_SECONDS = max(deploy_gate.SERVER_READY_SECONDS,
                                           args.server_ready)
    adopted = {}
    for one in args.adopt_series:
        if "=" not in one:
            parser.error("--adopt-series takes PAYLOAD=PATH, not " + one)
        size, _, where = one.partition("=")
        adopted[int(size)] = where
    overlays = [Path(one).resolve() for one in args.overlay]
    gate = ScaleGate(host, repo, commit, rev, args.tree,
                     overlay=overlays[0] if overlays else None,
                     extra_overlays=overlays[1:],
                     jobs=args.jobs, keep=args.keep, nntplib_python="none",
                     acl2=args.acl2 or deploy_gate.FARM_HOSTS.get(
                         args.host, {}).get("acl2", "acl2"),
                     payloads=args.payload or [1024, 32768],
                     max_articles=args.max_articles, start=args.start,
                     post_ceiling=args.post_ceiling,
                     recover_ceiling=args.recover_ceiling,
                     budget_seconds=args.budget_seconds,
                     connections=args.connections, niceness=args.nice,
                     rss_ceiling_kib=int(args.rss_ceiling_gib * 1024 * 1024),
                     reuse=args.reuse, adopted=adopted,
                     skip_previous=args.skip_previous)
    started = dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    clock = time.monotonic()
    failure = None
    try:
        gate.execute()
    except GateError as error:
        failure = str(error)
        gate.gaps.append("the gate stopped early: {}".format(error))
    finally:
        try:
            gate.cleanup()
        except Exception as error:      # cleanup must never hide the result
            gate.gaps.append("cleanup did not finish: {}: {}".format(
                type(error).__name__, error))
    elapsed = time.monotonic() - clock
    date = dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%d")
    target = Path(args.evidence) if args.evidence else (
        repo / "planning/evidence/scale-{}-{}.md".format(rev, date))
    gate.evidence(target, started, elapsed)
    print("evidence: {}".format(target))
    bad = [s for s in gate.steps if s.failed]
    print("steps={} failed={} not-exercised={}".format(
        len(gate.steps), len(bad), sum(1 for s in gate.steps if s.rc is None)))
    for step in bad:
        print("  FAILED rc={} {}: {}".format(step.rc, step.name, step.first_line))
    for payload, data in sorted(gate.series.items()):
        print("  series {} octets: largest passing {} articles, stopped by {}".format(
            payload, data.get("largest_passing"), data.get("stopped_by")))
    if failure:
        print("gate error: {}".format(failure))
        return 2
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
