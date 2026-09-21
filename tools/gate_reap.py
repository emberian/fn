#!/usr/bin/env python3
"""List the gate directories on a box, and remove the ones nothing can want.

A gate is a `git archive` export of one commit plus the certificates it
earned: `$HOME/fn-gates/<tree>-<rev>` on persvati, `/tank/fn/gates/<tree>-<rev>`
on hbox.  Nothing has ever removed one.  On 2026-09-21 persvati carried 25 of
them over 1.1 G, and **a retired gate does not take its processes with it**:
three ACL2 children of the retired gate `dev-6ac2278` survived 19 hours at 0%
CPU holding 1.7 G before the root coordinator stopped them.

This tool answers four questions per directory and acts on the answers:

  revision   the sha in the directory name, and whether git still knows it
  ancestor   whether that revision is an ancestor of `dev` -- if it is, the
             work landed and the export is recoverable from the repository
  age        mtime, because a gate is written once and then only read
  live       whether any process on the box has that directory (or anything
             under it) as its working directory.  A live gate is NEVER
             removed, whatever else is true of it.
  size       on-disk kilobytes, so the cost of keeping 25 of them is visible
  certs      how many `.cert` files it holds, because that is what a gate is
             scavenged for (`certpick.py`, `tools/certs.py`) and what its
             removal actually costs

    python3 tools/gate_reap.py --host persvati
    python3 tools/gate_reap.py --host hbox --json
    python3 tools/gate_reap.py --host persvati --remove        # acts

`--remove` deletes exactly the rows the listing called `stale`, one
`rm -rf` per row, by a name that must have come back from the listing and
must contain no `/`.  It refuses outright while the box's gate lock is held,
because a held `flock` means a certification is running.

Reading a box's memory, and why not `free`.  hbox is a ZFS box: the ARC is
counted in `used` and in unreclaimable slab and never in `buff/cache`, so
`free`'s `available` under-reports by tens of gigabytes and a lane that reads
it concludes the box is full when it is idle.  Measured 2026-09-21: Slab
87.0 G with SUnreclaim 82.3 G, AnonPages 1.2 G, ARC 45.1 G of which 43.8 G is
metadata, and every process's RSS summed 2.7 G across 988 processes.  So this
tool reports AnonPages, the RSS sum, and the ARC separately, and says what the
ARC returns under pressure.  Judge a box by AnonPages and the RSS sum.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))

from deploy_gate import Host, LocalHost, SshHost, repo_root   # noqa: E402

DEFAULT_ROOTS = {"persvati": "$HOME/fn-gates", "hbox": "/tank/fn/gates"}
DEFAULT_LOCKS = {"persvati": "$HOME/fn-gates/.gate.lock", "hbox": "/tank/fn/gates/.lock"}
REV = re.compile(r"^(?P<tree>.+)-(?P<rev>[0-9a-f]{7,40})$")

# One round trip per box.  Bash sets the two parameters and python does the
# reading, because /proc and du parsing in shell is where this kind of tool
# grows its bugs.
PROBE = r"""
set -u
export FN_GATE_ROOT="@ROOT@"
export FN_GATE_LOCK="@LOCK@"
if flock -n "$FN_GATE_LOCK" true 2>/dev/null; then export FN_GATE_LOCKED=no
elif [ -e "$FN_GATE_LOCK" ]; then export FN_GATE_LOCKED=yes
else export FN_GATE_LOCKED=absent; fi
python3 - <<'FN_REAP_PROBE'
import json, os, subprocess

root = os.path.expandvars(os.environ["FN_GATE_ROOT"])
out = {"root": root, "locked": os.environ.get("FN_GATE_LOCKED", "unknown"),
       "gates": [], "memory": {}, "proc": True}

names = sorted(n for n in os.listdir(root)
               if os.path.isdir(os.path.join(root, n)) and not n.startswith("."))

# Which directory each running process sits in.  /proc/<pid>/cwd is a
# symlink readable for our own processes, which is all a gate ever starts.
cwds = {}
if os.path.isdir("/proc"):
    for pid in os.listdir("/proc"):
        if not pid.isdigit():
            continue
        try:
            cwd = os.readlink(os.path.join("/proc", pid, "cwd"))
            with open(os.path.join("/proc", pid, "cmdline"), "rb") as handle:
                cmd = handle.read().replace(b"\x00", b" ").decode(
                    "utf-8", "replace").strip()
        except OSError:
            continue
        cwds.setdefault(cwd, []).append({"pid": int(pid), "cmd": cmd[:120]})
else:
    out["proc"] = False

for name in names:
    path = os.path.join(root, name)
    entry = {"name": name, "path": path, "mtime": os.stat(path).st_mtime}
    try:
        entry["kilobytes"] = int(subprocess.run(
            ["du", "-sk", path], stdout=subprocess.PIPE, timeout=300
        ).stdout.split()[0])
    except Exception:
        entry["kilobytes"] = None
    books = os.path.join(path, "books")
    entry["certs"] = (len([f for f in os.listdir(books) if f.endswith(".cert")])
                      if os.path.isdir(books) else 0)
    live = []
    for cwd, procs in cwds.items():
        if cwd == path or cwd.startswith(path + os.sep):
            live.extend(procs)
    entry["live"] = sorted(live, key=lambda one: one["pid"])
    out["gates"].append(entry)

# Memory, read the way a ZFS box has to be read.  See this file's docstring.
meminfo = {}
try:
    with open("/proc/meminfo") as handle:
        for line in handle:
            key, _, rest = line.partition(":")
            meminfo[key] = int(rest.split()[0])          # kB
except OSError:
    pass
rss = 0
for pid in os.listdir("/proc") if os.path.isdir("/proc") else []:
    if not pid.isdigit():
        continue
    try:
        with open(os.path.join("/proc", pid, "statm")) as handle:
            rss += int(handle.read().split()[1]) * (os.sysconf("SC_PAGE_SIZE") // 1024)
    except (OSError, IndexError, ValueError):
        continue
arc = None
try:
    with open("/proc/spl/kstat/zfs/arcstats") as handle:
        for line in handle:
            if line.startswith("size "):
                arc = int(line.split()[-1]) // 1024
except OSError:
    pass
out["memory"] = {"mem_total_kb": meminfo.get("MemTotal"),
                 "mem_free_kb": meminfo.get("MemFree"),
                 "anon_pages_kb": meminfo.get("AnonPages"),
                 "slab_unreclaim_kb": meminfo.get("SUnreclaim"),
                 "rss_sum_kb": rss, "arc_kb": arc}
print(json.dumps(out))
FN_REAP_PROBE
"""


class ReapError(RuntimeError):
    pass


def probe(host: Host, root: str, lock: str, timeout: int = 600) -> dict:
    # `str.replace`, not `str.format`: the probe is a python heredoc full of
    # dict literals, and `{` is not a placeholder there.
    script = PROBE.replace("@ROOT@", root).replace("@LOCK@", lock)
    done = host.sh(script, timeout)
    text = done.stdout.decode("utf-8", "replace")
    for line in reversed(text.splitlines()):
        if line.startswith("{"):
            return json.loads(line)
    raise ReapError("no listing came back from {}:\n{}".format(host.label, text[-2000:]))


def ancestry(repo: Path, revs):
    """`unknown`, `ancestor` or `present-not-ancestor`, per revision.

    The repository is the authority, not the box: a gate directory carries no
    `.git`, so the box cannot answer this about itself.
    """
    answer = {}
    for rev in revs:
        if rev is None:
            continue
        known = subprocess.run(["git", "-C", str(repo), "cat-file", "-e",
                                rev + "^{commit}"], stdout=subprocess.DEVNULL,
                               stderr=subprocess.DEVNULL)
        if known.returncode != 0:
            answer[rev] = "unknown"
            continue
        merged = subprocess.run(["git", "-C", str(repo), "merge-base",
                                 "--is-ancestor", rev, "dev"],
                                stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        answer[rev] = "ancestor" if merged.returncode == 0 else "present-not-ancestor"
    return answer


def verdicts(listing: dict, ancestors: dict, now: float, min_age_hours: float,
             keep_recent: int, include_unknown: bool) -> list:
    """One row per gate: `live`, `keep` with a reason, or `stale`.

    Pure, so the whole policy is testable without a box.  The order of the
    tests is the order of their authority: a live gate is never touched
    whatever else is true, and a lock held on the box stops everything.
    """
    rows = []
    newest = {}
    for entry in listing["gates"]:
        match = REV.match(entry["name"])
        tree = match.group("tree") if match else entry["name"]
        newest.setdefault(tree, []).append((entry["mtime"], entry["name"]))
    protected = set()
    for tree, pairs in newest.items():
        for _, name in sorted(pairs, reverse=True)[:max(0, keep_recent)]:
            protected.add(name)

    for entry in listing["gates"]:
        match = REV.match(entry["name"])
        rev = match.group("rev") if match else None
        age = (now - entry["mtime"]) / 3600.0
        row = dict(entry, rev=rev, tree=match.group("tree") if match else entry["name"],
                   age_hours=round(age, 1),
                   ancestor=ancestors.get(rev, "unnamed" if rev is None else "unknown"))
        if entry["live"]:
            row["verdict"], row["reason"] = "live", "{} process(es) have it as cwd: {}".format(
                len(entry["live"]), ", ".join(str(one["pid"]) for one in entry["live"]))
        elif not listing.get("proc", True):
            row["verdict"], row["reason"] = "keep", (
                "this box has no /proc, so no process could be ruled out")
        elif listing.get("locked") == "yes":
            row["verdict"], row["reason"] = "keep", (
                "the box's gate lock is held: a certification is running")
        elif rev is None:
            row["verdict"], row["reason"] = "keep", "the name carries no revision"
        elif entry["name"] in protected:
            row["verdict"], row["reason"] = "keep", (
                "one of the {} newest gates of tree `{}`, which is what a "
                "deploy scavenges its certificates from".format(keep_recent, row["tree"]))
        elif age < min_age_hours:
            row["verdict"], row["reason"] = "keep", "{:.1f} h old, under the {:g} h floor".format(
                age, min_age_hours)
        elif row["ancestor"] == "ancestor":
            row["verdict"], row["reason"] = "stale", (
                "the revision is an ancestor of dev, so the export is "
                "reproducible from the repository")
        elif row["ancestor"] == "unknown":
            row["verdict"] = "stale" if include_unknown else "keep"
            row["reason"] = (
                "git does not know this revision, so this export may be the only "
                "copy of that tree" + ("; removed anyway (--include-unknown)"
                                       if include_unknown else ""))
        else:
            row["verdict"], row["reason"] = "keep", (
                "the revision is in the repository but not an ancestor of dev: "
                "a branch that has not landed")
        rows.append(row)
    return rows


def remove(host: Host, root: str, rows, timeout: int = 600) -> list:
    """`rm -rf` exactly the rows the listing called stale, by name.

    Every name came back from the box's own listing and is re-checked here:
    no separator, no `..`, not empty.  A path is rebuilt from the root rather
    than taken from the row, so nothing the box said can widen the target.
    """
    removed = []
    for row in rows:
        name = row["name"]
        if not name or "/" in name or name in (".", "..") or name.startswith("-"):
            raise ReapError("refusing to remove a gate named {!r}".format(name))
        if row["verdict"] != "stale":
            raise ReapError("refusing to remove {}: verdict is {}".format(
                name, row["verdict"]))
        script = 'set -eu\nR="{root}"\nrm -rf -- "$R/{name}"\necho REMOVED {name}\n'.format(
            root=root, name=name)
        done = host.sh(script, timeout)
        output = done.stdout.decode("utf-8", "replace").strip()
        removed.append({"name": name, "rc": done.returncode, "output": output,
                        "kilobytes": row.get("kilobytes"), "certs": row.get("certs")})
    return removed


def render(listing: dict, rows: list, removed=None) -> str:
    lines = ["gate root {} on this box; lock {}".format(
        listing["root"], listing.get("locked", "unknown"))]
    memory = listing.get("memory") or {}
    if memory.get("mem_total_kb"):
        lines.append(
            "memory: total {:.0f} G, AnonPages {:.1f} G, RSS sum {:.1f} G, "
            "ARC {} (ARC and unreclaimable slab are NOT free's `available`; "
            "judge the box by AnonPages and the RSS sum)".format(
                memory["mem_total_kb"] / 1048576.0,
                (memory.get("anon_pages_kb") or 0) / 1048576.0,
                (memory.get("rss_sum_kb") or 0) / 1048576.0,
                "{:.1f} G".format(memory["arc_kb"] / 1048576.0)
                if memory.get("arc_kb") else "not a ZFS box"))
    width = max([len(row["name"]) for row in rows] + [4])
    lines.append("{:<{w}}  {:>7}  {:>7}  {:>6}  {:<20}  {:<7}  {}".format(
        "gate", "age(h)", "size(M)", "certs", "revision", "verdict", "why", w=width))
    for row in sorted(rows, key=lambda one: (one["verdict"], -one["age_hours"])):
        lines.append("{:<{w}}  {:>7.1f}  {:>7}  {:>6}  {:<20}  {:<7}  {}".format(
            row["name"], row["age_hours"],
            "?" if row["kilobytes"] is None else round(row["kilobytes"] / 1024),
            row["certs"], "{} {}".format(row["rev"] or "-", row["ancestor"]),
            row["verdict"], row["reason"], w=width))
    stale = [row for row in rows if row["verdict"] == "stale"]
    live = [row for row in rows if row["verdict"] == "live"]
    total = sum(row["kilobytes"] or 0 for row in rows)
    freeable = sum(row["kilobytes"] or 0 for row in stale)
    lines.append("{} gates, {:.1f} G; {} stale ({:.1f} G freeable), {} live, "
                 "{} kept".format(len(rows), total / 1048576.0, len(stale),
                                  freeable / 1048576.0, len(live),
                                  len(rows) - len(stale) - len(live)))
    if removed is not None:
        for one in removed:
            lines.append("removed {} ({} M, {} certs) rc={} {}".format(
                one["name"], round((one["kilobytes"] or 0) / 1024), one["certs"],
                one["rc"], one["output"]))
    return "\n".join(lines)


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--host", default="persvati",
                        help="box to read; `local` with --home for a dry run")
    parser.add_argument("--home", help="LocalHost root, for --host local")
    parser.add_argument("--gate-root", help="default: per-box, see DEFAULT_ROOTS")
    parser.add_argument("--lock", help="default: per-box, see DEFAULT_LOCKS")
    parser.add_argument("--repo", help="the fn checkout that answers ancestry")
    parser.add_argument("--min-age-hours", type=float, default=24.0)
    parser.add_argument("--keep-recent", type=int, default=2,
                        help="newest gates per tree that are never removed")
    parser.add_argument("--include-unknown", action="store_true",
                        help="also remove gates of revisions git does not know")
    parser.add_argument("--remove", action="store_true", help="act on the listing")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)

    host = LocalHost(Path(args.home)) if args.host == "local" else SshHost(args.host)
    root = args.gate_root or DEFAULT_ROOTS.get(args.host)
    lock = args.lock or DEFAULT_LOCKS.get(args.host, (root or "") + "/.lock")
    if not root:
        parser.error("no default gate root for host {}; pass --gate-root".format(args.host))
    repo = Path(args.repo) if args.repo else repo_root()

    listing = probe(host, root, lock)
    revs = []
    for entry in listing["gates"]:
        match = REV.match(entry["name"])
        if match:
            revs.append(match.group("rev"))
    rows = verdicts(listing, ancestry(repo, revs), time.time(), args.min_age_hours,
                    args.keep_recent, args.include_unknown)

    removed = None
    if args.remove:
        if listing.get("locked") == "yes":
            print("refusing to remove anything: {} is held".format(lock))
            return 1
        removed = remove(host, root, [row for row in rows if row["verdict"] == "stale"])

    if args.json:
        print(json.dumps({"host": host.label, "listing": listing, "rows": rows,
                          "removed": removed}, indent=2, sort_keys=True))
    else:
        print(render(listing, rows, removed))
    return 0


if __name__ == "__main__":
    sys.exit(main())
