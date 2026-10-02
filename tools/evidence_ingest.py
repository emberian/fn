#!/usr/bin/env python3
"""Place evidence objects in a content-addressed directory, verified and durable.

The one writer of `objects/<sha256[:2]>/<sha256>.gz` (tools/evidence_store.py
imports it for the cache and a local archive, and runs this file's source on
the archive box for a remote one).  Standard library only: it runs as
`python3 -c <this file> ARCHIVE STAGING` with the expected digests on stdin.

What `place` guarantees when it returns: the object at its final name
decompresses to bytes whose SHA-256 is its name, it was read back after the
write, and the file, its directory and every directory `place` created were
fsync'd -- an object already at its name too, before `place` reports it
present, so the index can never become durable before the object (r61 F1).
A failed fsync is an error, never swallowed.  So an index line written after
`place` (or after `ingest` reported every expected digest) never names bytes
the archive lacks, to the extent the archive's filesystem honours a fsync
that reported success (hbox: ZFS, sync=standard).  An existing object is
never trusted by its name: it is re-read and re-hashed (any decoder error,
zlib's included, is "does not verify"); one that does not verify is moved to
`quarantine/` (kept, never deleted) and replaced.
"""

from __future__ import annotations

import gzip
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import time
import zlib

HEX64 = re.compile(r"[0-9a-f]{64}")


def object_rel(sha: str) -> str:
    if not isinstance(sha, str) or not HEX64.fullmatch(sha):
        raise ValueError(f"not a sha256 digest: {sha!r}")
    return f"objects/{sha[:2]}/{sha}.gz"


def matches(data_gz: bytes, sha: str) -> bool:
    try:
        return hashlib.sha256(gzip.decompress(data_gz)).hexdigest() == sha
    except (OSError, EOFError, ValueError, zlib.error):
        return False


def fsync_file(path: Path) -> None:
    fd = os.open(path, os.O_RDONLY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def fsync_dir(path: Path) -> None:
    """fsync a directory, so the names in it are durable.  Errors propagate:
    a barrier that failed is not a filesystem honouring one (r61 F1)."""
    fd = os.open(path, os.O_RDONLY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def make_dirs(path: Path) -> None:
    """mkdir -p, then fsync each directory created into its parent, so a
    fresh shard (or a fresh archive) survives a crash with its object."""
    created = []
    walk = path
    while not walk.exists():
        created.append(walk)
        walk = walk.parent
    path.mkdir(parents=True, exist_ok=True)
    for made in reversed(created):
        fsync_dir(made)
        fsync_dir(made.parent)


def _readable_and_matching(path: Path, sha: str) -> bool:
    try:
        return matches(path.read_bytes(), sha)
    except OSError:
        return False


def quarantine(directory: Path, path: Path, sha: str) -> Path:
    """Move a file that does not verify out of the object namespace (kept)."""
    place_dir = directory / "quarantine"
    make_dirs(place_dir)
    target = place_dir / f"{sha}.gz.{time.time_ns()}.{os.getpid()}"
    os.replace(path, target)
    fsync_dir(place_dir)
    fsync_dir(path.parent)
    return target


def place(directory: Path, sha: str, data_gz: bytes | None = None,
          staged: Path | None = None) -> str:
    """Put one verified object at its final name.  Returns placed|present|replaced.

    Exactly one of `data_gz` (bytes to write) or `staged` (a file on the same
    filesystem to rename into place) is given; either must verify first.
    """
    target = directory / object_rel(sha)
    if staged is not None:
        if not _readable_and_matching(staged, sha):
            raise ValueError(f"staged object {staged} does not hash to {sha}")
    elif data_gz is None or not matches(data_gz, sha):
        raise ValueError(f"object bytes do not hash to {sha}")
    outcome = "placed"
    if target.exists():
        if _readable_and_matching(target, sha):
            # Verified, but perhaps never synced (a crashed writer, a copy
            # made by hand): make it durable before anyone indexes it.
            fsync_file(target)
            fsync_dir(target.parent)
            fsync_dir(target.parent.parent)
            if staged is not None:
                staged.unlink()
            return "present"
        quarantine(directory, target, sha)
        outcome = "replaced"
    make_dirs(target.parent)
    if staged is not None:
        fsync_file(staged)
        os.replace(staged, target)
    else:
        temporary = target.with_name(f"{target.name}.tmp{os.getpid()}")
        with open(temporary, "wb") as handle:
            handle.write(data_gz)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, target)
    fsync_dir(target.parent)
    fsync_dir(target.parent.parent)
    if not _readable_and_matching(target, sha):
        raise ValueError(f"object {sha} did not read back verified after placement")
    return outcome


def ingest(directory: Path, staging: Path, expect: list[str]) -> dict:
    """Move every staged object into place; then read back every expected one."""
    counts = {"placed": 0, "present": 0, "replaced": 0}
    bad: list[str] = []
    for path in sorted(staging.glob("objects/*/*.gz")):
        sha = path.name[:-3]
        try:
            counts[place(directory, sha, staged=path)] += 1
        except (ValueError, OSError) as error:
            bad.append(f"{sha}: {error}")
    missing = [sha for sha in expect
               if not (HEX64.fullmatch(sha)
                       and _readable_and_matching(directory / object_rel(sha), sha))]
    for sub in sorted(staging.glob("objects/*"), reverse=True):
        try:
            sub.rmdir()
        except OSError:
            pass
    for leftover in (staging / "objects", staging):
        try:
            leftover.rmdir()
        except OSError:
            pass
    return {**counts, "bad": bad, "missing": missing, "expected": len(expect)}


def main(argv: list[str]) -> int:
    directory, staging = Path(argv[0]), Path(argv[1])
    expect = [line.strip() for line in sys.stdin if line.strip()]
    report = ingest(directory, staging, expect)
    print(json.dumps(report))
    return 1 if report["bad"] or report["missing"] else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
