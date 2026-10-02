#!/usr/bin/env python3
"""Evidence lives in a content-addressed archive; the repository keeps the index.

`planning/evidence/` was 885 MB of the 986 MB tracked tree at origin/dev on
2026-10-02 (2,828 certify manifests at up to 2.4 MB each, plus reports, logs
and transcripts), and every lane worktree paid for it.  ember's decision
(2026-10-02): the repository must be small enough for a public forge.  So:

  * the BYTES of every evidence file live in a content-addressed archive,
    `objects/<sha256[:2]>/<sha256>.gz` (gzip, mtime 0, of the exact file
    bytes), on hbox at `/tank/fn/evidence` (FN_EVIDENCE_ARCHIVE overrides,
    `HOST:/path` or a local directory);
  * the repository keeps ONE tracked index, `planning/evidence-index.tsv`:
    one line per file, `<sha256> <bytes> <logical path>`, sorted by path,
    merged with git's union driver (`.gitattributes`), so two lanes that
    each add a run do not conflict;
  * the logical path stays the name.  `planning/evidence/manifests/<run>.json`
    is still what proofs.json, the scenario catalog and the prose cite, and
    what every reader keys on; only where its bytes come from moved.

A reader asks this module, never the filesystem.  For an INDEXED path,
`read_bytes(root, rel)` returns bytes that hash to the index line, always:
the working-tree file if it is there and matches (a working-tree file that
differs from its index line raises `EvidenceMismatch`, never silently
preferred), else the object from the local cache (`build/evidence-cache/` of
the shared checkout; FN_EVIDENCE_CACHE overrides) or fetched from the archive
by hash, each verified on every read.  An UNINDEXED working-tree file (a
lane's fresh, not yet filed output) is returned too, but `locate` labels it
"local", and nothing may count it as archived or certified.  A path named by
neither is absent.  An indexed object that cannot be read, fetched, or does
not hash to its name raises `EvidenceUnavailable`: an unreadable claim is
uncertain (exit 3), never "absent".

Writers verify before the index names anything: every object, including one
already at its name, is re-hashed (a bad one is quarantined, never trusted
or deleted), fsync'd with its directory and read back on the archive box
(tools/evidence_ingest.py), and only then is the index line written, under
a lock, fsync'd.  So the committed index never names bytes the archive lacks,
to the extent the archive's filesystem honours fsync (hbox: ZFS).

    python3 tools/evidence_store.py put PATH...        # archive + index
    python3 tools/evidence_store.py fetch [--all | GLOB...]
    python3 tools/evidence_store.py cat REL
    python3 tools/evidence_store.py ls GLOB
    python3 tools/evidence_store.py index-tree [--write]  # index == tracked tree
    python3 tools/evidence_store.py verify [--archive]
    python3 tools/evidence_store.py verify-paths [--revision REV] PATH...
    python3 tools/evidence_store.py history-check [--all-refs] [--path P]
    python3 tools/evidence_store.py migrate-history [--all-refs]
"""

from __future__ import annotations

import argparse
import contextlib
import fcntl
import fnmatch
import gzip
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath
import shlex
import socket
import subprocess
import sys
import tarfile
import tempfile
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import evidence_ingest  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
EVIDENCE_REL = "planning/evidence"
INDEX_REL = "planning/evidence-index.tsv"
DEFAULT_ARCHIVE = "hbox:/tank/fn/evidence"
HEADER = ("# fn evidence index: <sha256> <bytes> <path>; the bytes live in the "
          "archive at objects/<sha256[:2]>/<sha256>.gz (tools/evidence_store.py)")


class EvidenceUnavailable(RuntimeError):
    """An indexed object could not be read or fetched, or did not hash to its name."""


class EvidenceMismatch(EvidenceUnavailable):
    """A working-tree file differs from the bytes its index line names."""


HEX64 = evidence_ingest.HEX64
EXIT_UNAVAILABLE = 3


# ------------------------------------------------------------------ places


def archive_spec() -> str:
    return os.environ.get("FN_EVIDENCE_ARCHIVE") or DEFAULT_ARCHIVE


def split_spec(spec: str) -> tuple[str, str]:
    """`HOST:/path` -> (HOST, /path); a bare path -> ("", path)."""
    head, sep, tail = spec.partition(":")
    if sep and head and not head.startswith("/"):
        return head, tail
    return "", spec


def local_archive(spec: str | None = None) -> Path | None:
    """The archive directory when this machine holds it (hbox), else None."""
    host, path = split_spec(spec or archive_spec())
    if host and host != socket.gethostname().split(".")[0]:
        return None
    candidate = Path(path)
    if not host or (candidate / "objects").is_dir():
        return candidate
    return None


def checkout_of(root: Path) -> Path:
    """The shared checkout a worktree belongs to (its cache is shared)."""
    try:
        common = subprocess.run(
            ["git", "-C", str(root), "rev-parse", "--path-format=absolute",
             "--git-common-dir"], capture_output=True, text=True, check=False
        ).stdout.strip()
    except OSError:
        common = ""
    if common and Path(common).name == ".git":
        return Path(common).parent
    return root


def cache_dir(root: Path) -> Path:
    override = os.environ.get("FN_EVIDENCE_CACHE")
    return Path(override) if override else checkout_of(root) / "build" / "evidence-cache"


def object_rel(sha: str) -> str:
    """`objects/<sha[:2]>/<sha>.gz`; refuses anything but a 64-hex digest."""
    return evidence_ingest.object_rel(sha)


def inside(directory: Path, path: Path) -> Path:
    """`path`, after checking it resolves strictly inside `directory`."""
    if not path.resolve().is_relative_to(directory.resolve()):
        raise ValueError(f"{path} escapes {directory}")
    return path


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def compress(data: bytes) -> bytes:
    return gzip.compress(data, compresslevel=6, mtime=0)


# ------------------------------------------------------------------- index

_INDEX: dict[tuple[str, int, int], dict[str, tuple[str, int]]] = {}


def parse_index(text: str) -> dict[str, tuple[str, int]]:
    entries: dict[str, tuple[str, int]] = {}
    for number, line in enumerate(text.splitlines(), 1):
        if not line.strip() or line.startswith("#"):
            continue
        parts = line.split(" ", 2)
        if (len(parts) != 3 or not HEX64.fullmatch(parts[0])
                or not parts[1].isdigit() or not canonical_path(parts[2])):
            raise ValueError(f"{INDEX_REL}:{number}: malformed line {line!r}")
        sha, size, path = parts
        if path in entries and entries[path] != (sha, int(size)):
            # A union merge kept two versions of one path: say so, never pick.
            raise ValueError(f"{INDEX_REL}:{number}: {path} indexed twice with "
                             "different bytes (a merge kept both; keep the one "
                             "the lane meant and run `evidence_store.py verify`)")
        entries[path] = (sha, int(size))
    return entries


def canonical_path(path: str) -> bool:
    """A relative POSIX path with no empty, `.` or `..` segment."""
    if not path or path.startswith("/") or "\\" in path or "\0" in path:
        return False
    return all(part not in ("", ".", "..") for part in path.split("/"))


def read_index(root: Path = ROOT) -> dict[str, tuple[str, int]]:
    """Logical path -> (sha256, bytes).  Missing index: empty."""
    path = root / INDEX_REL
    try:
        stat = path.stat()
    except OSError:
        return {}
    key = (str(path), stat.st_mtime_ns, stat.st_size)
    if key not in _INDEX:
        _INDEX[key] = parse_index(path.read_text(encoding="utf-8"))
    return _INDEX[key]


def render_index(entries: dict[str, tuple[str, int]]) -> str:
    lines = [HEADER]
    lines += [f"{sha} {size} {path}" for path, (sha, size) in sorted(entries.items())]
    return "\n".join(lines) + "\n"


def write_index(root: Path, entries: dict[str, tuple[str, int]]) -> None:
    """Replace the index atomically and durably (callers hold `index_lock`)."""
    path = root / INDEX_REL
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + f".tmp{os.getpid()}")
    with open(temporary, "w", encoding="utf-8") as handle:
        handle.write(render_index(entries))
        handle.flush()
        os.fsync(handle.fileno())
    os.replace(temporary, path)
    evidence_ingest.fsync_dir(path.parent)


@contextlib.contextmanager
def index_lock(root: Path):
    """One writer at a time per index file (flock; released on process death)."""
    index = (root / INDEX_REL).resolve()
    locks = cache_dir(root) / "locks"
    locks.mkdir(parents=True, exist_ok=True)
    name = hashlib.sha256(str(index).encode()).hexdigest()[:32] + ".lock"
    with open(locks / name, "a") as handle:
        fcntl.flock(handle.fileno(), fcntl.LOCK_EX)
        try:
            yield
        finally:
            fcntl.flock(handle.fileno(), fcntl.LOCK_UN)


def add_to_index(root: Path, new: dict[str, tuple[str, int]]) -> None:
    """Merge rows into the index under the lock, reading it fresh inside it."""
    with index_lock(root):
        path = root / INDEX_REL
        try:
            text = path.read_text(encoding="utf-8")
        except FileNotFoundError:
            text = ""
        entries = parse_index(text)
        entries.update(new)
        write_index(root, entries)


# ------------------------------------------------------------------ objects


def _verified(data_gz: bytes, sha: str) -> bytes:
    try:
        data = gzip.decompress(data_gz)
    except (OSError, EOFError) as error:
        raise EvidenceUnavailable(f"object {sha} is not a gzip stream: {error}") from error
    if sha256_bytes(data) != sha:
        raise EvidenceUnavailable(f"object {sha} does not hash to its name")
    return data


def store_object(directory: Path, data: bytes, sha: str | None = None) -> str:
    """Place one object under `directory`: verified, durable, read back.

    An object already at its name is re-hashed, never trusted; one that does
    not verify is quarantined and replaced (tools/evidence_ingest.py).
    """
    sha = sha or sha256_bytes(data)
    if sha256_bytes(data) != sha:
        raise EvidenceUnavailable(f"bytes offered for {sha} do not hash to it")
    try:
        evidence_ingest.place(directory, sha, compress(data))
    except (OSError, ValueError) as error:
        raise EvidenceUnavailable(f"could not place object {sha} in {directory}: "
                                  f"{error}") from error
    return sha


def _quarantine(directory: Path, path: Path, sha: str) -> None:
    with contextlib.suppress(OSError):
        evidence_ingest.quarantine(directory, path, sha)


def _read_verified(path: Path, sha: str) -> bytes:
    try:
        data_gz = path.read_bytes()
    except OSError as error:
        raise EvidenceUnavailable(f"object {sha} at {path} is unreadable: {error}") from error
    return _verified(data_gz, sha)


def object_path(root: Path, sha: str) -> Path | None:
    """Where this machine already has the object, without fetching."""
    for directory in (cache_dir(root), local_archive()):
        if directory is not None and (directory / object_rel(sha)).is_file():
            return directory / object_rel(sha)
    return None


def fetch(root: Path, shas: list[str] | set[str], verify_present: bool = True) -> None:
    """Bring every named object into the cache, one rsync; verify each.

    With `verify_present` (the CLI) an object already here is re-hashed too:
    a bad cached copy is quarantined and fetched again, a bad local-archive
    copy is reported UNAVAILABLE (fetch never writes the archive).
    `prefetch` passes False: every read verifies anyway (`object_bytes`).
    """
    cache = cache_dir(root)
    wanted_set: set[str] = set()
    corrupt_archive: list[str] = []
    for sha in set(shas):
        object_rel(sha)
        found = object_path(root, sha)
        if found is not None and verify_present:
            try:
                _read_verified(found, sha)
            except EvidenceUnavailable:
                if found.is_relative_to(cache):
                    _quarantine(cache, found, sha)
                    found = object_path(root, sha)
                    if found is not None:
                        try:
                            _read_verified(found, sha)
                        except EvidenceUnavailable:
                            corrupt_archive.append(sha)
                        continue
                else:
                    corrupt_archive.append(sha)
                    continue
        if found is None:
            wanted_set.add(sha)
    if corrupt_archive:
        raise EvidenceUnavailable(
            f"{len(corrupt_archive)} objects in the local archive {local_archive()} do "
            f"not verify (first {sorted(corrupt_archive)[0]})")
    wanted = sorted(wanted_set)
    if not wanted:
        return
    host, path = split_spec(archive_spec())
    if not host:
        raise EvidenceUnavailable(
            f"{len(wanted)} evidence objects are in neither {cache_dir(root)} nor "
            f"the archive {archive_spec()} (first {wanted[0]})")
    cache.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile("w", suffix=".list", delete=False) as listing:
        listing.write("".join(object_rel(sha) + "\n" for sha in wanted))
        listing_name = listing.name
    try:
        done = subprocess.run(
            ["rsync", "-a", "--files-from", listing_name,
             f"{host}:{path.rstrip('/')}/", str(cache) + "/"],
            capture_output=True, text=True, check=False)
    finally:
        os.unlink(listing_name)
    bad = []
    for sha in wanted:
        target = cache / object_rel(sha)
        try:
            _read_verified(target, sha)
        except EvidenceUnavailable:
            bad.append(sha)
            if target.exists():
                _quarantine(cache, target, sha)
    if bad:
        raise EvidenceUnavailable(
            f"{len(bad)} of {len(wanted)} evidence objects did not arrive verified "
            f"from {archive_spec()} (rsync exit {done.returncode}: "
            f"{done.stderr.strip()[-300:]}); first {bad[0]}")


def object_bytes(root: Path, sha: str) -> bytes:
    """The object's bytes, verified on this read; a bad cached copy is
    quarantined and fetched again; anything else unreadable is UNAVAILABLE."""
    object_rel(sha)
    cache = cache_dir(root)
    found = object_path(root, sha)
    if found is not None:
        try:
            return _read_verified(found, sha)
        except EvidenceUnavailable:
            if not found.is_relative_to(cache):
                raise
            _quarantine(cache, found, sha)
            found = object_path(root, sha)
            if found is not None:
                return _read_verified(found, sha)
    fetch(root, [sha], verify_present=False)
    found = object_path(root, sha)
    if found is None:
        raise EvidenceUnavailable(f"object {sha} did not arrive")
    return _read_verified(found, sha)


# ------------------------------------------------------------------ readers


def _rel(root: Path, rel: str | Path) -> str:
    path = Path(rel)
    if path.is_absolute():
        try:
            path = path.resolve().relative_to(root.resolve())
        except ValueError:
            return str(rel)
    return path.as_posix()


def exists(root: Path, rel: str | Path) -> bool:
    """A file at this logical path: in the working tree or in the index."""
    name = _rel(root, rel)
    return (root / name).is_file() or name in read_index(root)


def is_dir(root: Path, rel: str | Path) -> bool:
    name = _rel(root, rel).rstrip("/")
    if (root / name).is_dir():
        return True
    prefix = name + "/"
    return any(path.startswith(prefix) for path in read_index(root))


def indexed(root: Path, rel: str | Path) -> bool:
    """The committed index names this path (its bytes are archived by hash)."""
    return _rel(root, rel) in read_index(root)


def _local_matching(local: Path, name: str, entry: tuple[str, int]) -> bytes:
    try:
        data = local.read_bytes()
    except OSError as error:
        raise EvidenceUnavailable(f"{name}: the working-tree copy is unreadable: "
                                  f"{error}") from error
    if len(data) != entry[1] or sha256_bytes(data) != entry[0]:
        raise EvidenceMismatch(
            f"{name}: the working-tree file differs from its index line ({entry[0]}); "
            "`evidence_store.py put` it to file the new bytes, or restore them")
    return data


def locate(root: Path, rel: str | Path) -> tuple[bytes, str]:
    """(bytes, "indexed" | "local").  Indexed bytes always hash to the index
    line; "local" is an unindexed working-tree file, never archived."""
    name = _rel(root, rel)
    local = root / name
    entry = read_index(root).get(name)
    if entry is not None:
        if local.is_file():
            return _local_matching(local, name, entry), "indexed"
        return object_bytes(root, entry[0]), "indexed"
    if local.is_file():
        return local.read_bytes(), "local"
    raise FileNotFoundError(name)


def read_bytes(root: Path, rel: str | Path) -> bytes:
    """The indexed bytes (verified), else an unindexed working-tree file."""
    return locate(root, rel)[0]


def read_text(root: Path, rel: str | Path) -> str:
    return read_bytes(root, rel).decode("utf-8")


def glob(root: Path, pattern: str) -> list[str]:
    """Logical paths matching `pattern` (fnmatch, `*` crosses no `/`)."""
    def matches(path: str) -> bool:
        return (path.count("/") == pattern.count("/")
                and fnmatch.fnmatchcase(path, pattern))
    found = {path for path in read_index(root) if matches(path)}
    found.update(path.relative_to(root).as_posix() for path in root.glob(pattern)
                 if path.is_file())
    return sorted(found)


def materialize(root: Path, rel: str | Path) -> Path:
    """A filesystem path holding the logical file's bytes (for an executor).

    The working-tree file itself, or a verified copy in the cache keyed by
    hash under `tree/<sha>/<basename>` so a script keeps its name.
    """
    name = _rel(root, rel)
    local = root / name
    entry = read_index(root).get(name)
    if entry is None:
        if local.is_file():
            return local
        raise FileNotFoundError(name)
    if local.is_file():
        _local_matching(local, name, entry)
        return local
    sha = entry[0]
    cache = cache_dir(root)
    object_rel(sha)
    target = inside(cache, cache / "tree" / sha / Path(name).name)
    if target.is_file():
        try:
            if sha256_bytes(target.read_bytes()) == sha:
                return target
        except OSError:
            pass
        _quarantine(cache, target, sha)
    data = object_bytes(root, sha)
    target.parent.mkdir(parents=True, exist_ok=True)
    temporary = target.with_name(target.name + f".tmp{os.getpid()}")
    temporary.write_bytes(data)
    os.replace(temporary, target)
    return target


def prefetch(root: Path, rels: list[str]) -> None:
    """One fetch for every indexed path a caller is about to read."""
    index = read_index(root)
    fetch(root, {index[rel][0] for rel in rels
                 if rel in index and not (root / rel).is_file()}, verify_present=False)


def verify_paths(root: Path, rels: list[str],
                 index: dict[str, tuple[str, int]] | None = None
                 ) -> dict[str, Exception | None]:
    """{path: None if its indexed bytes are readable and verify, else why}.

    Names are not bytes: an index row alone proves nothing (r56 F3).  A
    path the index does not name is FileNotFoundError; an indexed one that
    cannot be fetched or does not verify is EvidenceUnavailable.
    """
    index = read_index(root) if index is None else index
    result: dict[str, Exception | None] = {}
    with contextlib.suppress(EvidenceUnavailable):
        fetch(root, {index[rel][0] for rel in rels if rel in index},
              verify_present=False)
    for rel in rels:
        entry = index.get(rel)
        if entry is None:
            result[rel] = FileNotFoundError(rel)
            continue
        try:
            data = object_bytes(root, entry[0])
            if len(data) != entry[1]:
                raise EvidenceUnavailable(f"{rel}: {len(data)} bytes, index says {entry[1]}")
            result[rel] = None
        except EvidenceUnavailable as error:
            result[rel] = error
    return result


# ------------------------------------------------------------------ writers


def _remote_ingest(host: str, path: str, staging: str, shas: list[str]) -> dict:
    """Run tools/evidence_ingest.py on the archive box: move the staged
    objects into place (verifying existing ones), fsync, read every expected
    digest back.  Raises unless every expected object verified there."""
    script = Path(evidence_ingest.__file__).read_text(encoding="utf-8")
    command = " ".join(shlex.quote(part) for part in
                       ["python3", "-c", script, path.rstrip("/"), staging])
    done = subprocess.run(["ssh", host, command], input="".join(s + "\n" for s in shas),
                          capture_output=True, text=True, check=False)
    try:
        report = json.loads(done.stdout.strip().splitlines()[-1])
    except (ValueError, IndexError):
        report = {}
    if done.returncode != 0 or report.get("bad") or report.get("missing") \
            or report.get("expected") != len(shas):
        raise EvidenceUnavailable(
            f"the archive {host}:{path} did not confirm {len(shas)} objects "
            f"(ingest exit {done.returncode}; bad {report.get('bad', '?')}; "
            f"missing {str(report.get('missing', '?'))[:300]}; "
            f"{done.stderr.strip()[-300:]})")
    return report


def _staging_name() -> str:
    return f"incoming/{socket.gethostname().split('.')[0]}-{os.getpid()}-{time.time_ns()}"


def push(root: Path, shas: list[str]) -> None:
    """Copy cached objects to the archive and have the archive confirm them.

    Local directory: `store_object` there (verify existing, fsync, read back).
    `HOST:/path`: rsync into a fresh staging directory inside the archive,
    then evidence_ingest on the box (verify, quarantine a bad existing
    object, rename into place, fsync, read every digest back).  Raises
    EvidenceUnavailable unless every object is confirmed.
    """
    shas = sorted(set(shas))
    if not shas:
        return
    host, path = split_spec(archive_spec())
    if not host:
        archive = Path(path)
        for sha in shas:
            store_object(archive, object_bytes(root, sha), sha)
        return
    cache = cache_dir(root)
    for sha in shas:
        _read_verified(cache / object_rel(sha), sha)
    staging = f"{path.rstrip('/')}/{_staging_name()}"
    made = subprocess.run(["ssh", host, f"mkdir -p {shlex.quote(staging)}"],
                          capture_output=True, text=True, check=False)
    if made.returncode != 0:
        raise EvidenceUnavailable(f"push to {archive_spec()}: cannot make the staging "
                                  f"directory (ssh exit {made.returncode}): "
                                  f"{made.stderr.strip()[-300:]}")
    with tempfile.NamedTemporaryFile("w", suffix=".list", delete=False) as listing:
        listing.write("".join(object_rel(sha) + "\n" for sha in shas))
        listing_name = listing.name
    try:
        done = subprocess.run(
            ["rsync", "-a", "--files-from", listing_name,
             str(cache) + "/", f"{host}:{staging}/"],
            capture_output=True, text=True, check=False)
    finally:
        os.unlink(listing_name)
    if done.returncode != 0:
        raise EvidenceUnavailable(f"push to {archive_spec()} failed "
                                  f"(rsync exit {done.returncode}): {done.stderr.strip()[-300:]}")
    _remote_ingest(host, path, staging, shas)


def archive_objects(root: Path, objects: dict[str, bytes]) -> None:
    """{sha: bytes} -> confirmed in the archive (or raise).  Nothing indexed."""
    archive = local_archive()
    if archive is not None:
        for sha, data in objects.items():
            store_object(archive, data, sha)
        return
    cache = cache_dir(root)
    for sha, data in objects.items():
        store_object(cache, data, sha)
    push(root, list(objects))


def put(root: Path, rels: list[str], publish: bool = True) -> dict[str, tuple[str, int]]:
    """Archive working-tree files, then record them in the index.

    The index line is written (locked, fsync'd) only after the
    archive confirm every object, so a committed index never names bytes the
    archive lacks (subject to the archive filesystem honouring fsync).
    `publish=False` (tests, `put --no-push`) caches without publishing:
    never before a commit.
    """
    entries: dict[str, tuple[str, int]] = {}
    objects: dict[str, bytes] = {}
    for rel in rels:
        name = _rel(root, rel)
        if not canonical_path(name):
            raise ValueError(f"not a canonical repository path: {rel}")
        data = (root / name).read_bytes()
        sha = sha256_bytes(data)
        objects[sha] = data
        entries[name] = (sha, len(data))
    if publish:
        archive_objects(root, objects)
    else:
        for sha, data in objects.items():
            store_object(cache_dir(root), data, sha)
    add_to_index(root, entries)
    return entries


# --------------------------------------------------------------- transition


def git_lines(root: Path, *args: str) -> list[str]:
    done = subprocess.run(["git", "-C", str(root), *args], capture_output=True,
                          text=True, check=False)
    return done.stdout.splitlines()


def tree_blobs(root: Path, revision: str = "HEAD") -> dict[str, str]:
    """{path: blob id} of every file tracked under planning/evidence at REVISION."""
    rows = git_lines(root, "ls-tree", "-r", "-l", revision, "--", EVIDENCE_REL)
    blobs = {}
    for row in rows:
        meta, _, path = row.partition("\t")
        parts = meta.split()
        if len(parts) == 4 and parts[1] == "blob":
            blobs[path] = parts[2]
    return blobs


def tree_entries(root: Path, revision: str = "HEAD") -> dict[str, tuple[str, int]]:
    """(sha256, bytes) of every file tracked under planning/evidence at REVISION."""
    entries: dict[str, tuple[str, int]] = {}
    for path, data in cat_blobs(root, tree_blobs(root, revision)):
        entries[path] = (sha256_bytes(data), len(data))
    return entries


def index_at(root: Path, revision: str) -> dict[str, tuple[str, int]]:
    """The committed index at REVISION (empty when it has none)."""
    done = subprocess.run(["git", "-C", str(root), "show", f"{revision}:{INDEX_REL}"],
                          capture_output=True, text=True, check=False)
    return parse_index(done.stdout) if done.returncode == 0 else {}


def cat_blobs(root: Path, blobs: dict[str, str]):
    """Yield (path, bytes) for {path: blob id} through one `git cat-file --batch`."""
    order = list(blobs.items())
    process = subprocess.Popen(["git", "-C", str(root), "cat-file", "--batch"],
                               stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    assert process.stdin and process.stdout

    def feed():
        for _, blob in order:
            process.stdin.write((blob + "\n").encode())
        process.stdin.close()

    import threading
    writer = threading.Thread(target=feed, daemon=True)
    writer.start()
    for path, _ in order:
        header = process.stdout.readline().split()
        size = int(header[2])
        data = process.stdout.read(size)
        process.stdout.read(1)
        yield path, data
    writer.join()
    process.stdout.close()
    process.wait()


def history_blobs(root: Path, refs: list[str],
                  prefixes: list[str] | None = None) -> dict[str, str]:
    """{blob id: first path} for every blob ever under PREFIXES (default
    planning/evidence; a prefix is a directory or one file)."""
    prefixes = prefixes or [EVIDENCE_REL]
    found: dict[str, str] = {}
    rows = git_lines(root, "rev-list", "--objects", *refs, "--", *prefixes)
    candidates = {}
    for row in rows:
        oid, _, path = row.partition(" ")
        if any(path == prefix or path.startswith(prefix.rstrip("/") + "/")
               for prefix in prefixes):
            candidates.setdefault(oid, path)
    checked = subprocess.run(["git", "-C", str(root), "cat-file",
                              "--batch-check=%(objectname) %(objecttype)"],
                             input="".join(oid + "\n" for oid in candidates),
                             capture_output=True, text=True, check=False).stdout
    for row in checked.splitlines():
        parts = row.split()
        if len(parts) == 2 and parts[1] == "blob":
            found[parts[0]] = candidates[parts[0]]
    return found


def stream_objects_to_archive(root: Path, blobs: dict[str, str],
                              extra_files: list[Path]) -> list[tuple[str, int, str, str]]:
    """Tar every object into a fresh staging directory inside the archive
    over one ssh, then ingest it there (evidence_ingest: verify each staged
    and each existing object, quarantine a bad existing one, rename into
    place, fsync, read every digest back); return the ledger rows.  Nothing
    is extracted over a final object name, so an interrupted run leaves only
    staging debris, never a truncated object at a content address."""
    host, path = split_spec(archive_spec())
    rows: list[tuple[str, int, str, str]] = []
    staging = f"{path.rstrip('/')}/{_staging_name()}"
    if host:
        sink = subprocess.Popen(
            ["ssh", host, f"mkdir -p {shlex.quote(staging)} && "
                          f"tar -x -C {shlex.quote(staging)}"],
            stdin=subprocess.PIPE)
        out = sink.stdin
    else:
        Path(staging).mkdir(parents=True, exist_ok=True)
        sink = subprocess.Popen(["tar", "-x", "-C", staging], stdin=subprocess.PIPE)
        out = sink.stdin
    assert out is not None
    seen: set[str] = set()
    with tarfile.open(fileobj=out, mode="w|") as tar:
        def add(data: bytes, blob: str, logical: str) -> None:
            sha = sha256_bytes(data)
            rows.append((sha, len(data), blob, logical))
            if sha in seen:
                return
            seen.add(sha)
            body = compress(data)
            info = tarfile.TarInfo(object_rel(sha))
            info.size = len(body)
            info.mode = 0o444
            tar.addfile(info, io.BytesIO(body))
        pairs = {logical + "\0" + blob: blob for blob, logical in blobs.items()}
        for key, data in cat_blobs(root, pairs):
            logical, _, blob = key.partition("\0")
            add(data, blob, logical)
        for extra in extra_files:
            add(extra.read_bytes(), "untracked",
                extra.resolve().relative_to(checkout_of(root).resolve()).as_posix()
                if extra.resolve().is_relative_to(checkout_of(root).resolve())
                else str(extra))
    out.close()
    if sink.wait() != 0:
        raise EvidenceUnavailable(f"archive tar sink exited {sink.returncode}")
    expected = sorted(seen)
    if host:
        report = _remote_ingest(host, path, staging, expected)
    else:
        report = evidence_ingest.ingest(Path(path), Path(staging), expected)
        if report["bad"] or report["missing"]:
            raise EvidenceUnavailable(f"ingest into {path}: bad {report['bad'][:5]}, "
                                      f"missing {report['missing'][:5]}")
    print(f"ingested: {report['placed']} placed, {report['present']} already present "
          f"and verified, {report['replaced']} replaced (bad copy quarantined); "
          f"{report['expected']} read back", flush=True)
    return rows


def archive_listing(spec: str | None = None) -> dict[str, int]:
    """sha -> compressed size of every object the archive holds."""
    host, path = split_spec(spec or archive_spec())
    command = (f"cd {shlex.quote(path)} 2>/dev/null && find objects -name '*.gz' "
               "-printf '%f %s\\n'")
    if host:
        text = subprocess.run(["ssh", host, command], capture_output=True,
                              text=True, check=False).stdout
    else:
        text = "".join(f"{p.name} {p.stat().st_size}\n"
                       for p in Path(path, "objects").glob("*/*.gz"))
    listing = {}
    for row in text.splitlines():
        name, _, size = row.partition(" ")
        if name.endswith(".gz"):
            listing[name[:-3]] = int(size or 0)
    return listing


VERIFY_SCRIPT = r"""
import gzip, hashlib, sys, pathlib
root = pathlib.Path(sys.argv[1]); bad = 0; n = 0
for p in sorted(root.glob('objects/*/*.gz')):
    n += 1
    try:
        ok = hashlib.sha256(gzip.decompress(p.read_bytes())).hexdigest() == p.name[:-3]
    except Exception:
        ok = False
    if not ok:
        bad += 1; print('BAD', p)
print('verified', n, 'objects,', bad, 'bad')
sys.exit(1 if bad else 0)
"""


# --------------------------------------------------------------------- CLI


def cmd_put(args) -> int:
    entries = put(ROOT, args.paths, publish=not args.no_push)
    for path, (sha, size) in sorted(entries.items()):
        print(f"{sha} {size} {path}")
    print(f"indexed {len(entries)} in {INDEX_REL}; `git add {INDEX_REL}` commits the claim")
    return 0


def cmd_fetch(args) -> int:
    index = read_index(ROOT)
    if args.all:
        rels = list(index)
    else:
        rels = sorted({rel for pattern in args.patterns for rel in index
                       if fnmatch.fnmatchcase(rel, pattern)})
    before = sum(1 for rel in rels if object_path(ROOT, index[rel][0]))
    fetch(ROOT, {index[rel][0] for rel in rels}, verify_present=True)
    print(f"{len(rels)} indexed files; {before} were here; every one now verified "
          f"in {cache_dir(ROOT)} or the local archive")
    return 0


def cmd_cat(args) -> int:
    sys.stdout.buffer.write(read_bytes(ROOT, args.path))
    return 0


def cmd_ls(args) -> int:
    for rel in glob(ROOT, args.pattern):
        print(rel)
    return 0


def cmd_index_tree(args) -> int:
    """The transition check: the index names exactly the tracked evidence."""
    tree = tree_entries(ROOT, args.revision)
    index = read_index(ROOT)
    missing = sorted(set(tree) - set(index))
    extra = sorted(set(index) - set(tree))
    differ = sorted(path for path in set(tree) & set(index) if tree[path] != index[path])
    if args.write:
        # Archive first, then index (r56 F7): every new or changed row's bytes
        # are confirmed by the archive before the index names them.
        wanted = missing + differ
        blobs = tree_blobs(ROOT, args.revision)
        for start in range(0, len(wanted), 2000):
            batch = wanted[start:start + 2000]
            objects = {sha256_bytes(data): data
                       for _, data in cat_blobs(ROOT, {p: blobs[p] for p in batch})}
            archive_objects(ROOT, objects)
            add_to_index(ROOT, {p: tree[p] for p in batch})
        print(f"wrote {INDEX_REL}: {len(tree)} tracked files "
              f"(+{len(missing)} new, {len(differ)} changed, each archived first; "
              f"{len(extra)} index-only kept)")
        return 0
    print(f"tracked {len(tree)}; indexed {len(index)}; unindexed {len(missing)}; "
          f"changed {len(differ)}; index-only {len(extra)}")
    for path in (missing + differ)[:20]:
        print(f"  not indexed at these bytes: {path}")
    return 1 if (missing or differ) else 0


def cmd_verify(args) -> int:
    index = read_index(ROOT)
    listing = archive_listing()
    absent = sorted(path for path, (sha, _) in index.items() if sha not in listing)
    print(f"index {len(index)} files ({len({sha for sha, _ in index.values()})} "
          f"distinct objects); archive {archive_spec()} holds {len(listing)} objects "
          f"({sum(listing.values()) / 1e6:.1f} MB compressed); "
          f"indexed but not archived: {len(absent)}")
    for path in absent[:20]:
        print(f"  not archived: {path}")
    status = 1 if absent else 0
    if args.archive:
        host, path = split_spec(archive_spec())
        command = ["python3", "-", path]
        done = subprocess.run(["ssh", host, *map(shlex.quote, command)] if host else command,
                              input=VERIFY_SCRIPT, text=True, check=False)
        status = status or done.returncode
    return status


def cmd_verify_paths(args) -> int:
    """Each PATH's indexed bytes are readable and verify (exit 0); a path the
    index does not name is refused (1); an unverifiable one is UNAVAILABLE (3)."""
    index = index_at(ROOT, args.revision) if args.revision else read_index(ROOT)
    problems = verify_paths(ROOT, args.paths, index)
    for rel, problem in problems.items():
        if problem is None:
            print(f"verified {rel}")
        elif isinstance(problem, FileNotFoundError):
            print(f"NOT INDEXED {rel}")
        else:
            print(f"UNAVAILABLE {rel}: {problem}")
    if any(isinstance(p, FileNotFoundError) for p in problems.values()):
        return 1
    return EXIT_UNAVAILABLE if any(problems.values()) else 0


def cmd_history_check(args) -> int:
    """Every blob ever under the prefixes, on the refs, is in the archive by
    the SHA-256 of its bytes.  With `verify --archive` (each archive object
    hashes to its name) that is: every historical blob is archived intact."""
    refs = ["--all"] if args.all_refs else [args.revision]
    prefixes = args.path or [EVIDENCE_REL]
    blobs = history_blobs(ROOT, refs, prefixes)
    digests = {blob: (sha256_bytes(data), len(data))
               for blob, data in cat_blobs(ROOT, {blob: blob for blob in blobs})}
    listing = archive_listing()
    missing = sorted((blobs[blob], blob, sha) for blob, (sha, _) in digests.items()
                     if sha not in listing)
    distinct = {sha for sha, _ in digests.values()}
    print(f"history {' '.join(refs)} under {' '.join(prefixes)}: {len(blobs)} blobs, "
          f"{len(distinct)} distinct sha256, "
          f"{sum(size for _, size in digests.values()) / 1e6:.1f} MB raw; archive "
          f"{archive_spec()} holds {len(listing)} objects; historical blobs not in "
          f"the archive: {len(missing)}")
    for path, blob, sha in missing[:20]:
        print(f"  not archived: {blob} {sha} {path}")
    if len(digests) != len(blobs):
        print(f"  git delivered {len(digests)} of {len(blobs)} blobs")
        return 1
    return 1 if missing else 0


def cmd_migrate_history(args) -> int:
    refs = ["--all"] if args.all_refs else [args.revision]
    blobs = history_blobs(ROOT, refs, args.path or None)
    extras = []
    if args.untracked:
        tracked = set(git_lines(checkout_of(ROOT), "ls-files", "--", EVIDENCE_REL))
        base = checkout_of(ROOT)
        for path in sorted((base / EVIDENCE_REL).rglob("*")):
            rel = path.relative_to(base).as_posix()
            if path.is_file() and rel not in tracked:
                extras.append(path)
    print(f"migrating {len(blobs)} historical blobs + {len(extras)} untracked files "
          f"to {archive_spec()}", flush=True)
    rows = stream_objects_to_archive(ROOT, blobs, extras)
    # One ledger per run, never over an earlier one: a narrower run (one
    # --path, one revision) must not replace the ledger of a wider run.
    stamp = time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
    kind = "history-ledger" if not args.path else "history-ledger-extra"
    ledger = cache_dir(ROOT) / f"{kind}-{stamp}-{time.time_ns() % 10**9:09d}.tsv"
    ledger.parent.mkdir(parents=True, exist_ok=True)
    ledger.write_text("".join(f"{sha} {size} {blob} {path}\n"
                              for sha, size, blob, path in sorted(rows, key=lambda r: r[3])))
    host, path = split_spec(archive_spec())
    if host:
        done = subprocess.run(["rsync", "-a", str(ledger), f"{host}:{path}/{ledger.name}"],
                              capture_output=True, text=True, check=False)
        if done.returncode != 0:
            raise EvidenceUnavailable(f"the history ledger did not reach {host}:{path} "
                                      f"(rsync exit {done.returncode}): {done.stderr[-300:]}")
    print(f"streamed {len(rows)} rows, {len({r[0] for r in rows})} distinct objects; "
          f"ledger {ledger}")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    subs = parser.add_subparsers(dest="action", required=True)
    one = subs.add_parser("put", help="archive files and add them to the index")
    one.add_argument("paths", nargs="+")
    one.add_argument("--no-push", action="store_true",
                     help="cache and index only (tests; never before a commit)")
    one.set_defaults(func=cmd_put)
    one = subs.add_parser("fetch", help="fill the cache by hash")
    one.add_argument("patterns", nargs="*")
    one.add_argument("--all", action="store_true")
    one.set_defaults(func=cmd_fetch)
    one = subs.add_parser("cat", help="print one logical file")
    one.add_argument("path")
    one.set_defaults(func=cmd_cat)
    one = subs.add_parser("ls", help="list logical files matching a glob")
    one.add_argument("pattern")
    one.set_defaults(func=cmd_ls)
    one = subs.add_parser("index-tree", help="compare (or --write) the index "
                                             "against the tracked planning/evidence")
    one.add_argument("--revision", default="HEAD")
    one.add_argument("--write", action="store_true")
    one.set_defaults(func=cmd_index_tree)
    one = subs.add_parser("verify", help="every indexed object is in the archive")
    one.add_argument("--archive", action="store_true",
                     help="also decompress and hash every archived object on the box")
    one.set_defaults(func=cmd_verify)
    one = subs.add_parser("verify-paths", help="fetch and verify the indexed bytes "
                                               "of each PATH (the cut's evidence gate)")
    one.add_argument("paths", nargs="+")
    one.add_argument("--revision", default=None,
                     help="read the index committed at REV instead of the working tree's")
    one.set_defaults(func=cmd_verify_paths)
    one = subs.add_parser("history-check", help="every historical blob under the "
                                                "prefixes is in the archive by hash")
    one.add_argument("--revision", default="HEAD")
    one.add_argument("--all-refs", action="store_true")
    one.add_argument("--path", action="append", default=[])
    one.set_defaults(func=cmd_history_check)
    one = subs.add_parser("migrate-history",
                          help="copy every historical planning/evidence blob to the archive")
    one.add_argument("--revision", default="HEAD")
    one.add_argument("--all-refs", action="store_true")
    one.add_argument("--path", action="append", default=[],
                     help="a path prefix to migrate instead of planning/evidence "
                          "(repeatable; the history-rewrite drop list)")
    one.add_argument("--untracked", action="store_true",
                     help="also the shared checkout's untracked evidence files")
    one.set_defaults(func=cmd_migrate_history)
    args = parser.parse_args(argv)
    try:
        return args.func(args)
    except EvidenceUnavailable as error:
        print(f"evidence_store: UNAVAILABLE: {error}", file=sys.stderr)
        return EXIT_UNAVAILABLE


if __name__ == "__main__":
    raise SystemExit(main())
