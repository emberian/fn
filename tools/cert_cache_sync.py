#!/usr/bin/env python3
"""Copy one box's new certificate-cache entries into the other box's cache.

After a batch splits certification across hbox and persvati, each box's
cache holds what was certified there, so a REPL or farm run on the other box
refuses or recertifies (flip-bridge, 2026-09-27).  Cache entries are
immutable directories, KEY/ORIGIN-TOKEN, keyed by the book's closure bytes
(tools/certs.py), so copying an entry the destination lacks is safe; the
destination's installer still checks toolchain and certificate alists.

    python3 tools/cert_cache_sync.py hbox persvati            # entries of the last 24 h
    python3 tools/cert_cache_sync.py persvati hbox --hours 6 --dry-run

The boxes cannot reach each other by name, so the copy goes through this
machine (a staging directory under build/, removed afterwards).

An entry is only useful where its ACL2 toolchain identity is the one the
destination certifies with.  By default the tool copies only entries whose
toolchain is one the destination uses: the identities of the launchers
tools/farm.py HOSTS names for it (computed ON the destination by
tools/acl2_toolchain.py), and those of its cache's newest entries.  It says
how many it left because their toolchain differs.  On 2026-09-27 hbox (w28,
identity d5f2b9f0) and persvati (w25, identity 1b4169e9) ran different ACL2
builds and a sync copied nothing usable; since lane toolchain-unify
(2026-09-28) both run w28 from the same absolute paths, so the identities
are equal and the caches interchangeable.  `tools/farm.py`'s fetch runs this
after every run, from the box that ran to the other one.
"""
from __future__ import annotations

import argparse
import json
import shlex
import shutil
import tempfile
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(Path(__file__).resolve().parent))
import certs  # noqa: E402

# Runs on a box: `scan CACHE SINCE` prints each entry directory changed since
# SINCE (epoch seconds) with its toolchain identity; `have CACHE` reads entry
# paths on stdin and prints those the cache holds; `toolchains CACHE` counts
# the identities of the cache's newest entries. `selected CACHE` reads exact
# key/origin coordinates on stdin and returns only those entries' metadata.
REMOTE = r'''
import json, os, re, sys
mode, cache = sys.argv[1], os.path.expanduser(sys.argv[2])
def meta(path):
    try:
        with open(os.path.join(cache, path, "meta.json")) as handle:
            return json.load(handle)
    except (OSError, ValueError):
        return None
def entries():
    for key in os.scandir(cache):
        if key.is_dir():
            for origin in os.scandir(key.path):
                if origin.is_dir():
                    yield key.name + "/" + origin.name, origin.stat().st_mtime
if mode == "scan":
    since = float(sys.argv[3])
    for path, mtime in entries():
        if mtime >= since:
            found = meta(path)
            if found is not None:
                print(json.dumps([path, found.get("toolchain_identity")]))
elif mode == "selected":
    for line in sys.stdin:
        path = line.strip()
        if not re.fullmatch(r"[A-Za-z0-9_-]+/[A-Za-z0-9_-]+", path):
            raise SystemExit("invalid cache entry coordinate")
        found = meta(path)
        if found is not None:
            print(json.dumps([path, found.get("toolchain_identity")]))
elif mode == "have":
    for line in sys.stdin:
        path = line.strip()
        if path and meta(path) is not None:
            print(path)
elif mode == "toolchains":
    newest = sorted(entries(), key=lambda item: item[1], reverse=True)[:400]
    counts = {}
    for path, _ in newest:
        found = meta(path) or {}
        identity = found.get("toolchain_identity")
        counts[identity] = counts.get(identity, 0) + 1
    print(json.dumps(counts))
'''


def cache_of(host: str) -> str:
    try:
        return certs.REMOTE_CACHES[host]
    except KeyError:
        raise SystemExit(f"cert_cache_sync: no cache path for {host!r} "
                         f"(known: {', '.join(sorted(certs.REMOTE_CACHES))})") from None


def rsync_path(cache: str) -> str:
    """CACHE as an rsync remote path: `~/x` becomes `x` (relative to the
    remote home).  rsync >= 3.2.4 protects arguments from the remote shell,
    so a literal `~/fn-certcache` reached persvati as /home/ember/~/fn-certcache
    and every sync from or to persvati failed with rsync exit 3 or 12."""
    return cache[2:] if cache.startswith("~/") else cache


def remote(host: str, arguments: list[str], stdin: str = "", run=subprocess.run) -> str:
    command = "python3 -c " + shlex.quote(REMOTE) + " " + " ".join(
        shlex.quote(word) for word in arguments)
    answer = run(["ssh", host, command], input=stdin, capture_output=True, text=True)
    if answer.returncode != 0:
        raise SystemExit(f"cert_cache_sync: {host}: {answer.stderr.strip() or 'ssh failed'}")
    return answer.stdout


def plan(scanned: list[tuple[str, str | None]], present: set[str],
         usable: set[str | None], all_toolchains: bool) -> dict:
    """Which scanned entries to copy: absent at the destination, usable there."""
    missing = [(path, identity) for path, identity in scanned if path not in present]
    copy = [path for path, identity in missing if all_toolchains or identity in usable]
    other = sorted({identity or "none" for path, identity in missing
                    if not all_toolchains and identity not in usable})
    return {"scanned": len(scanned), "present": len(scanned) - len(missing),
            "copy": copy, "other_toolchain": len(missing) - len(copy),
            "other_identities": other}


def configured_identities(host: str, run=subprocess.run) -> set[str]:
    """The toolchain identities of the launchers farm.py HOSTS names for HOST,
    fingerprinted on HOST itself (the identity hashes the files there)."""
    import ast  # farm.py imports the native campaign; read HOSTS as a literal
    tree = ast.parse((ROOT / "tools" / "farm.py").read_text(encoding="utf-8"))
    hosts = next(ast.literal_eval(node.value) for node in tree.body
                 if isinstance(node, ast.Assign) and len(node.targets) == 1
                 and getattr(node.targets[0], "id", None) == "HOSTS")
    source = (ROOT / "tools" / "acl2_toolchain.py").read_text(encoding="utf-8")
    found: set[str] = set()
    seen: set[str] = set()
    for role in ("acl2", "image_acl2"):
        launcher = hosts.get(host, {}).get(role)
        if not launcher or launcher in seen:
            continue
        seen.add(launcher)
        answer = run(["ssh", host, "python3 - identity " + shlex.quote(launcher)],
                     input=source, capture_output=True, text=True)
        identity = (answer.stdout or "").strip()
        if answer.returncode == 0 and identity:
            found.add(identity)
        else:
            print(f"cert_cache_sync: {host}: {launcher} is not a qualified launcher: "
                  f"{(answer.stderr or '').strip() or 'ssh failed'}", file=sys.stderr)
    return found


def sync(source: str, target: str, hours: float, dry_run: bool = False,
         all_toolchains: bool = False, run=subprocess.run,
         since: float | None = None,
         entries: list[str] | None = None) -> int:
    """Copy SOURCE's cache entries changed since SINCE (epoch seconds; default
    HOURS ago) that TARGET lacks and can use into TARGET's cache. ENTRIES,
    when supplied, selects exact publication coordinates instead of a scan."""
    if since is None:
        since = time.time() - hours * 3600
    else:
        hours = max(0.0, (time.time() - since) / 3600)
    source_cache, target_cache = cache_of(source), cache_of(target)
    # Farm publication already knows the exact closure-key/origin coordinates.
    # Read their current metadata; never treat the caller's list as proof.
    selected = (remote(source, ["selected", source_cache],
                       "\n".join(dict.fromkeys(entries)), run=run)
                if entries is not None else
                remote(source, ["scan", source_cache, str(since)], run=run))
    scanned = [tuple(json.loads(line)) for line in selected.splitlines()
               if line.strip()]
    if not scanned:
        print(f"{source} -> {target}: no matching cache entries to mirror")
        return 0
    present = set(remote(target, ["have", target_cache],
                         "\n".join(path for path, _ in scanned), run=run).split())
    usable = configured_identities(target, run=run)
    # Common farm case: every missing entry uses the configured launcher.
    # The historical-cache fallback changes nothing about which entries may
    # be copied, but is unnecessary when those identities already suffice.
    unknown = {identity for path, identity in scanned if path not in present} - usable
    if unknown and not all_toolchains:
        usable |= set(json.loads(remote(target, ["toolchains", target_cache],
                                        run=run) or "{}"))
    decided = plan(scanned, present, usable, all_toolchains)
    scope = (f"entries selected from this publication" if entries is not None
             else f"entries changed in the last {hours:.3g} h")
    print(f"{source} -> {target}: {decided['scanned']} {scope}; "
          f"{decided['present']} already there; "
          f"{len(decided['copy'])} to copy; {decided['other_toolchain']} left: their ACL2 "
          f"toolchain is not one {target}'s cache uses")
    if decided["other_toolchain"]:
        print(f"  {source}'s toolchain(s) {', '.join(i[:8] for i in decided['other_identities'])}"
              f"; {target}'s: {', '.join(sorted((i or 'none')[:8] for i in usable))}"
              " (one toolchain on both boxes is what makes the caches interchangeable)")
    if dry_run or not decided["copy"]:
        return 0
    # One staging directory and list per invocation: two syncs of the same
    # pair from one worktree (concurrent `farm.py wait`s) shared a fixed
    # name, and the first to finish removed the other's list ("persvati-
    # hbox.list missing", batch BB 2026-09-29).
    base = ROOT / "build" / "cert-cache-sync"
    base.mkdir(parents=True, exist_ok=True)
    staging = Path(tempfile.mkdtemp(prefix=f"{source}-{target}-", dir=base))
    listing = staging.with_suffix(".list")
    listing.write_text("\n".join(decided["copy"]) + "\n")
    try:
        for command in (
                ["rsync", "-a", "-r", f"--files-from={listing}",
                 f"{source}:{rsync_path(source_cache)}/", f"{staging}/"],
                ["rsync", "-a", "-r", f"--files-from={listing}",
                 f"{staging}/", f"{target}:{rsync_path(target_cache)}/"]):
            done = run(command)
            if done.returncode != 0:
                print(f"cert_cache_sync: {' '.join(command[:2])} ... exit {done.returncode}")
                return 1
    finally:
        shutil.rmtree(staging, ignore_errors=True)
        listing.unlink(missing_ok=True)
    print(f"  copied {len(decided['copy'])} entries into {target}:{target_cache}")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("source", help="box to copy from (hbox, persvati)")
    parser.add_argument("target", help="box to copy into")
    parser.add_argument("--hours", type=float, default=24.0,
                        help="entries changed within this many hours (default 24)")
    parser.add_argument("--dry-run", action="store_true", help="count, copy nothing")
    parser.add_argument("--all-toolchains", action="store_true",
                        help="copy entries of every toolchain, usable at the target or not")
    args = parser.parse_args(argv)
    if args.source == args.target:
        parser.error("source and target are the same box")
    return sync(args.source, args.target, args.hours, args.dry_run, args.all_toolchains)


if __name__ == "__main__":
    raise SystemExit(main())
