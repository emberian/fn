#!/usr/bin/env python3
"""Make a cited certification run resolvable from the repository alone.

Every certification claim in this tree names an evidence directory under
`build/acl2/certify-<UTC>-<pid>/`.  `build/` is ignored (`.gitignore:6`), the
directory lives only on the box that ran it, and a lane worktree or a gate
directory is removed as routine housekeeping.  So a reader at any revision
could not check a single certification claim the tree makes: on 2026-09-21,
316 run ids were cited in committed prose and none of them was committed.

The claim is in the manifest, not in the logs.  `manifest.json` is about 4 kB
and carries the requested books, the expected and observed success markers,
the per-book verdicts and wall seconds, the source and certificate digests,
the ACL2 build and the run's own identity; `certify.log` is the bulk and is
not the claim.  So the manifests are committed under
`planning/evidence/manifests/<run-id>.json` and the logs stay where they were
produced.

The archive is written by the tools, at the three points a manifest reaches
this laptop: `tools/certify_books.py` when a local run finishes,
`tools/farm.py wait` when a farm run's evidence is fetched, and
`tools/verdict.py` when a gate is harvested.  A run id resolves by NAME, with
no box, lane or gate in the path, because the box, the lane and the gate are
exactly the things that get deleted.

`planning/evidence/manifests/` is ignored by default and a manifest is
tracked with `git add -f`, which `sync` does.  Committing a manifest is
therefore the same act as citing the run: an exploratory run nobody cites
stays out of the history, and every run somebody cites is in it.

    python3 tools/evidence_manifests.py archive build/acl2/certify-...
    python3 tools/evidence_manifests.py sync [--add] [--from DIR ...]
    python3 tools/evidence_manifests.py harvest --host persvati [--root DIR]
    python3 tools/evidence_manifests.py check [--strict]

`check` compares the run ids cited in TRACKED files against the manifests
TRACKED under the archive, because what a reader can verify is what is
committed, not what happens to be on this disk.
"""

from __future__ import annotations

import argparse
import io
import json
from pathlib import Path
import re
import shlex
import socket
import subprocess
import sys
import tarfile

ROOT = Path(__file__).resolve().parent.parent
ARCHIVE = ROOT / "planning" / "evidence" / "manifests"
ARCHIVE_REL = "planning/evidence/manifests"
# The named backlog: run ids a committed claim cites whose manifest no longer
# exists on this laptop or on either box.  It is the list `check` tolerates,
# so a new unresolvable citation fails while an old one only waits for its
# lane owner to re-run the claim or retract it.
LOST_REL = "planning/evidence/manifests/LOST.txt"
RUN_ID = re.compile(r"certify-[0-9]{8}T[0-9]{6}Z-[0-9]+")
# POSIX ERE for `git grep`, which has no \d.
RUN_ID_ERE = "certify-[0-9]{8}T[0-9]{6}Z-[0-9]+"
# Where a manifest can be found on this laptop without asking a box.
LOCAL_ROOTS = ("build/acl2", "build/lanes/*/build/acl2")
# Where a box keeps them.  A gate directory is the most exposed of these:
# a gate reaper removed twelve stale gates from persvati on 2026-09-21.
BOX_ROOTS = {
    "persvati": ("$HOME/fn-lanes", "$HOME/fn-gates", "$HOME/fn-live", "$HOME/fn-deploy"),
    "hbox": ("/tank/fn/lanes", "/tank/fn/gates", "/tank/fn/scale"),
}


def remote_path(name: str) -> str:
    """Quote a box path, leaving a leading `$HOME` for the remote shell.

    `shlex.quote("$HOME/fn-gates")` is a path no box has; persvati answered
    "found none" until this existed.
    """
    if name.startswith("$HOME/"):
        return '"$HOME"/' + shlex.quote(name[len("$HOME/"):])
    return shlex.quote(name)


def git(*args: str, root: Path = ROOT) -> str:
    result = subprocess.run(["git", "-C", str(root), *args],
                            capture_output=True, text=True, check=False)
    return result.stdout


def cited_run_ids(root: Path = ROOT) -> dict[str, list[str]]:
    """Every run id named in a tracked file, with the file:line that names it.

    The archive is excluded: a manifest records its own run id, and a
    manifest citing itself would make every archived run look cited.  Unit
    test sources are excluded too: a run id in `tests/test_*.py` is a
    fixture exercising this code, not a claim about a certification.  The
    validation plan and every other file under `tests/` are prose and are
    swept.
    """
    out = git("grep", "-nI", "-oE", RUN_ID_ERE, "--", ".",
              f":(exclude){ARCHIVE_REL}", ":(exclude)tests/test_*.py", root=root)
    cites: dict[str, list[str]] = {}
    for line in out.splitlines():
        parts = line.split(":", 2)
        if len(parts) != 3:
            continue
        path, number, run_id = parts
        if RUN_ID.fullmatch(run_id):
            cites.setdefault(run_id, []).append(f"{path}:{number}")
    return cites


def tracked_manifests(root: Path = ROOT) -> set[str]:
    """Run ids whose manifest is committed, which is what a reader can see."""
    names = git("ls-files", "--", ARCHIVE_REL, root=root).split()
    return {Path(name).stem for name in names
            if RUN_ID.fullmatch(Path(name).stem)}


def archived(root: Path = ROOT) -> set[str]:
    """Run ids whose manifest is in the archive on this disk, tracked or not."""
    directory = root / ARCHIVE_REL
    if not directory.is_dir():
        return set()
    return {path.stem for path in directory.glob("certify-*.json")
            if RUN_ID.fullmatch(path.stem)}


def lost_run_ids(root: Path = ROOT) -> dict[str, str]:
    """The run ids recorded as gone for good, with where they are cited."""
    path = root / LOST_REL
    if not path.is_file():
        return {}
    lost: dict[str, str] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        run_id, _, where = line.partition(" ")
        if RUN_ID.fullmatch(run_id):
            lost[run_id] = where.strip()
    return lost


def run_id_of(path: Path) -> str | None:
    """`.../certify-<stamp>-<pid>/manifest.json` or `<run-id>.json`."""
    for candidate in (path.parent.name, path.stem):
        if RUN_ID.fullmatch(candidate):
            return candidate
    return None


# Two fields the archive adds.  They say which run this is and where its
# logs were left; everything else in the file is the producer's own record.
ADDED = ("run_id", "archived_from")


def _is_remote(origin: str) -> bool:
    """Does this `archived_from` name another host rather than a local path?

    `<host>:<path>` is remote; a bare absolute path is local.  A Windows
    drive letter cannot occur here and is not considered.
    """
    head, sep, _ = str(origin).partition(":")
    return bool(sep) and bool(head) and not head.startswith("/")


def write_manifest(run_id: str, text: str, source: str = "",
                   root: Path = ROOT) -> str:
    """Put one manifest in the archive.  Returns what happened to it.

    `source` is `<host>:<absolute run directory>`: the manifest is the claim
    and is durable, `certify.log` is the bulk and is not, so the archived
    copy says where the log was while it lasted.
    """
    try:
        payload = json.loads(text)
    except ValueError:
        return "unreadable"
    if not isinstance(payload, dict):
        return "unreadable"
    payload.setdefault("run_id", run_id)
    if source:
        payload.setdefault("archived_from", source)
    body = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    target = root / ARCHIVE_REL / f"{run_id}.json"
    target.parent.mkdir(parents=True, exist_ok=True)
    if target.exists():
        try:
            existing = json.loads(target.read_text(encoding="utf-8"))
        except (OSError, ValueError):
            return "conflict"
        if ({k: v for k, v in existing.items() if k not in ADDED}
                == {k: v for k, v in payload.items() if k not in ADDED}):
            # The same run reached the archive twice -- produced here and
            # later swept off the box it also ran on.  Keep one copy, and
            # make WHICH one deterministic, because two trees that archive
            # the same run from different places otherwise commit two
            # different files and git conflicts on them (measured
            # 2026-09-21, certify-20260921T021134Z-1437596, laptop path
            # against `hbox:...`).  A remote origin wins: it names the box
            # the logs are still on, which is what a reader needs, and for
            # a manifest produced before `hostname`/`tree` were recorded it
            # is the only provenance there is.
            if _is_remote(payload.get("archived_from", "")) and not _is_remote(
                    existing.get("archived_from", "")):
                merged = dict(existing)
                merged["archived_from"] = payload["archived_from"]
                target.write_text(
                    json.dumps(merged, indent=2, sort_keys=True) + "\n",
                    encoding="utf-8")
                return "written"
            return "present"
        # Two boxes could in principle mint one run id (UTC second plus pid).
        return "conflict"
    target.write_text(body, encoding="utf-8")
    return "written"


def archive_run(source: Path, root: Path = ROOT, origin: str = "") -> str:
    """Archive one run directory or one `manifest.json`.

    Called by `certify_books.py`, `farm.py` and `verdict.py`; never raises,
    because failing to file a copy of the evidence must not fail the run that
    produced it.  `origin` names where the LOGS are: for a farm run that is
    the remote root on the box, not the fetched copy under `build/`.
    """
    try:
        path = source / "manifest.json" if source.is_dir() else source
        run_id = run_id_of(path)
        if run_id is None or not path.is_file():
            return "skipped"
        return write_manifest(run_id, path.read_text(encoding="utf-8"),
                              origin or f"{socket.gethostname()}:{path.parent}",
                              root)
    except OSError:
        return "skipped"


def local_candidates(root: Path, extra: list[str]) -> dict[str, Path]:
    """Every manifest this laptop holds, by run id, nearest tree first.

    A `--from` directory is searched for run directories directly under it
    and one level of `build/acl2` below it, which covers a fetched tarball
    and a sibling worktree.  It is not a recursive walk: a `find` over
    `build/` costs minutes here.
    """
    found: dict[str, Path] = {}
    patterns = [(root, name) for name in LOCAL_ROOTS]
    for name in extra:
        base = Path(name)
        base = base if base.is_absolute() else root / base
        patterns = [(base, "."), (base, "*"), (base, "*/build/acl2"),
                    (base, "*/*/build/acl2"), *patterns]
    for base, name in patterns:
        for manifest in sorted(base.glob(f"{name}/certify-*/manifest.json")):
            run_id = run_id_of(manifest)
            if run_id and run_id not in found:
                found[run_id] = manifest
    return found


# ---------------------------------------------------------------- subcommands


def cmd_archive(args: argparse.Namespace) -> int:
    counts: dict[str, int] = {}
    for name in args.paths:
        outcome = archive_run(Path(name).resolve())
        counts[outcome] = counts.get(outcome, 0) + 1
    print(", ".join(f"{key} {value}" for key, value in sorted(counts.items())) or "nothing")
    return 0


def cmd_sync(args: argparse.Namespace) -> int:
    cites = cited_run_ids()
    have = archived()
    candidates = local_candidates(ROOT, args.source)
    recovered = 0
    for run_id in sorted(set(cites) - have):
        if run_id in candidates:
            manifest = candidates[run_id]
            if write_manifest(run_id, manifest.read_text(encoding="utf-8"),
                              f"{socket.gethostname()}:{manifest.parent}") in {
                    "written", "present"}:
                recovered += 1
    have = archived()
    to_add = sorted(set(cites) & have)
    if args.add and to_add:
        # `-f` because the archive is ignored: a manifest becomes tracked
        # exactly when the run it records is cited.
        for start in range(0, len(to_add), 200):
            batch = [f"{ARCHIVE_REL}/{run_id}.json" for run_id in to_add[start:start + 200]]
            subprocess.run(["git", "-C", str(ROOT), "add", "-f", *batch], check=False)
    tracked = tracked_manifests()
    missing = sorted(set(cites) - have)
    if args.record_lost:
        body = [
            "# Certification runs a committed claim cites whose manifest no",
            "# longer exists on this laptop, on persvati or on hbox: the",
            "# directory under `build/` was deleted with its lane worktree,",
            "# farm root or gate before anything durable was kept.  Each row",
            "# is a claim a reader cannot check; its lane owner re-runs the",
            "# certification or walks the claim back, and deletes the row.",
            "# Generated by `tools/evidence_manifests.py sync --record-lost`.",
            "",
        ]
        body += [f"{run_id} {cites[run_id][0]}" for run_id in missing]
        (ROOT / LOST_REL).parent.mkdir(parents=True, exist_ok=True)
        (ROOT / LOST_REL).write_text("\n".join(body) + "\n", encoding="utf-8")
        print(f"recorded {len(missing)} unresolvable run ids in {LOST_REL}")
    print(f"cited run ids {len(cites)}; archived here {len(set(cites) & have)}; "
          f"tracked {len(set(cites) & tracked)}; recovered this run {recovered}; "
          f"missing {len(missing)}")
    if args.list_missing:
        for run_id in missing:
            print(f"  {run_id}  {cites[run_id][0]}")
    return 0


def cmd_harvest(args: argparse.Namespace) -> int:
    """Pull the manifests of cited runs off a box before its trees are reaped."""
    wanted = sorted(set(cited_run_ids()) - archived())
    if not wanted:
        print("every cited run id is already archived")
        return 0
    roots = args.root or list(BOX_ROOTS.get(args.host, ()))
    if not roots:
        print(f"no known evidence roots for {args.host}; pass --root", file=sys.stderr)
        return 2
    # One ssh, one bounded `find`, one tar stream.  A manifest is 4 kB, so
    # every manifest on a box is a couple of MB compressed: cheaper than a
    # round trip per run id, and it reads nothing but manifests.
    script = (
        "find " + " ".join(remote_path(name) for name in roots) +
        " -maxdepth 7 -name manifest.json -path '*certify-*' -print0 2>/dev/null"
        " | tar czf - --null -T - 2>/dev/null"
    )
    result = subprocess.run(["ssh", args.host, script], capture_output=True,
                            check=False)
    counts: dict[str, int] = {}
    try:
        with tarfile.open(fileobj=io.BytesIO(result.stdout), mode="r:gz") as archive:
            for member in archive.getmembers():
                run_id = run_id_of(Path("/" + member.name))
                if run_id not in wanted:
                    continue
                handle = archive.extractfile(member)
                if handle is None:
                    continue
                outcome = write_manifest(
                    run_id, handle.read().decode("utf-8", "replace"),
                    f"{args.host}:/{member.name.lstrip('./')}".rsplit("/", 1)[0])
                counts[outcome] = counts.get(outcome, 0) + 1
    except (tarfile.TarError, EOFError) as error:
        print(f"{args.host}: the manifest stream did not arrive: {error}",
              file=sys.stderr)
        return 2
    print(f"{args.host}: wanted {len(wanted)}; " +
          (", ".join(f"{key} {value}" for key, value in sorted(counts.items())) or "found none"))
    return 0


def cmd_check(args: argparse.Namespace) -> int:
    cites = cited_run_ids()
    tracked = tracked_manifests()
    lost = lost_run_ids()
    resolved = sorted(set(cites) & tracked)
    missing = sorted(set(cites) - tracked)
    fresh = [run_id for run_id in missing if run_id not in lost]
    print(f"certification run ids cited in tracked files: {len(cites)}; "
          f"manifests committed under {ARCHIVE_REL}/: {len(tracked)}; "
          f"cited and resolvable: {len(resolved)}; cited and unresolvable: "
          f"{len(missing)}, of which {len(missing) - len(fresh)} are the "
          f"recorded backlog in {LOST_REL}")
    # Say which of them are still recoverable here.  A lane worktree under
    # `build/lanes/` usually still holds its own runs when its handoff lands,
    # and then the repair is one command rather than a question.
    here = set(local_candidates(ROOT, [])) & set(fresh) if fresh else set()
    for run_id in (fresh if not args.list_missing else missing):
        state = "on this laptop" if run_id in here else "not on this laptop"
        print(f"  no committed manifest: {run_id}  ({cites[run_id][0]}) "
              f"[{state}]")
    if fresh and not args.report_only:
        print(f"{len(fresh)} newly cited certification run(s) have no committed "
              f"manifest, so a reader cannot check the claim. {len(here)} of "
              f"them are still under build/ here: `python3 "
              f"tools/evidence_manifests.py sync --add` files those. For the "
              f"rest try `harvest --host persvati` and `harvest --host hbox`; "
              f"if the evidence is gone from all three, record it in "
              f"{LOST_REL} with `sync --record-lost` and say so where you "
              f"cite it.", file=sys.stderr)
        return 1
    if missing and args.strict:
        print(f"{len(missing)} cited certification runs have no committed "
              f"manifest.", file=sys.stderr)
        return 1
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    subs = parser.add_subparsers(dest="action", required=True)

    one = subs.add_parser("archive", help="file one or more run directories")
    one.add_argument("paths", nargs="+")
    one.set_defaults(func=cmd_archive)

    sync = subs.add_parser("sync", help="archive every cited run this laptop holds")
    sync.add_argument("--from", dest="source", action="append", default=[],
                      help="an extra directory of certify-* run directories")
    sync.add_argument("--add", action="store_true",
                      help="git add -f the archived manifests of cited runs")
    sync.add_argument("--list-missing", action="store_true")
    sync.add_argument("--record-lost", action="store_true",
                      help=f"write the still-unresolvable run ids to {LOST_REL}")
    sync.set_defaults(func=cmd_sync)

    harvest = subs.add_parser("harvest", help="pull cited manifests off a box")
    harvest.add_argument("--host", required=True)
    harvest.add_argument("--root", action="append", default=[])
    harvest.set_defaults(func=cmd_harvest)

    check = subs.add_parser("check", help="every cited run id has a committed manifest")
    check.add_argument("--strict", action="store_true",
                       help="fail on the recorded backlog too, not only on "
                            "a newly cited run with no manifest")
    check.add_argument("--report-only", action="store_true",
                       help="print the counts and exit 0 whatever they are")
    check.add_argument("--list-missing", action="store_true")
    check.set_defaults(func=cmd_check)

    args = parser.parse_args(argv)
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())
