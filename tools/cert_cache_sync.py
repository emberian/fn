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
toolchain the destination's cache already uses, and says how many it left
because their toolchain differs: on 2026-09-27 hbox (w28, identity d5f2b9f0)
and persvati (w25, identity 1b4169e9) ran different ACL2 builds, so no hbox
certificate could install on persvati or the reverse, and a sync copied
nothing usable.  One toolchain on both boxes is what makes their caches
interchangeable.
"""
from __future__ import annotations

import argparse
import json
import shlex
import shutil
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
# the identities of the cache's newest entries.
REMOTE = r'''
import json, os, sys
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


def sync(source: str, target: str, hours: float, dry_run: bool = False,
         all_toolchains: bool = False, run=subprocess.run) -> int:
    since = time.time() - hours * 3600
    source_cache, target_cache = cache_of(source), cache_of(target)
    scanned = [tuple(json.loads(line)) for line in
               remote(source, ["scan", source_cache, str(since)], run=run).splitlines()
               if line.strip()]
    present = set(remote(target, ["have", target_cache],
                         "\n".join(path for path, _ in scanned), run=run).split())
    usable = set(json.loads(remote(target, ["toolchains", target_cache], run=run) or "{}"))
    decided = plan(scanned, present, usable, all_toolchains)
    print(f"{source} -> {target}: {decided['scanned']} entries changed in the last "
          f"{hours:g} h; {decided['present']} already there; "
          f"{len(decided['copy'])} to copy; {decided['other_toolchain']} left: their ACL2 "
          f"toolchain is not one {target}'s cache uses")
    if decided["other_toolchain"]:
        print(f"  {source}'s toolchain(s) {', '.join(i[:8] for i in decided['other_identities'])}"
              f"; {target}'s: {', '.join(sorted((i or 'none')[:8] for i in usable))}"
              " (one toolchain on both boxes is what makes the caches interchangeable)")
    if dry_run or not decided["copy"]:
        return 0
    staging = ROOT / "build" / "cert-cache-sync" / f"{source}-{target}"
    shutil.rmtree(staging, ignore_errors=True)
    staging.mkdir(parents=True)
    listing = staging.parent / f"{source}-{target}.list"
    listing.write_text("\n".join(decided["copy"]) + "\n")
    try:
        for command in (
                ["rsync", "-a", "-r", f"--files-from={listing}",
                 f"{source}:{source_cache}/", f"{staging}/"],
                ["rsync", "-a", "-r", f"--files-from={listing}",
                 f"{staging}/", f"{target}:{target_cache}/"]):
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
