#!/usr/bin/env python3
"""Evidence lives in a content-addressed archive; the repository keeps the index.

`planning/evidence/` was 885 MB of the 986 MB tracked tree at origin/dev on
2026-10-02 (2,828 certify manifests at up to 2.4 MB each, plus reports, logs
and transcripts), and every lane worktree paid for it.  ember's decision
(2026-10-02): the repository must be small enough for a public forge.  So:

  * the BYTES of every evidence file live in a content-addressed archive,
    `objects/<sha256[:2]>/<sha256>.gz` (gzip, mtime 0, of the exact file
    bytes), held by an ordered SET of archive members, by default
    `hbox:/tank/fn/evidence` then `persvati:/home/ember/fn-evidence`
    (FN_EVIDENCE_ARCHIVES, comma-separated, overrides; FN_EVIDENCE_ARCHIVE is
    a one-element set; a member is `HOST:/path` or a local directory);
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
neither is absent.  Three outcomes stay distinct (r61 F3): an indexed object
that cannot be read or fetched raises `EvidenceUnavailable` -- uncertain,
exit 3, never "absent"; bytes that are there but do not hash to their index
line (a differing working-tree file, a corrupt object with no good copy, any
gzip or zlib decoder error) raise `EvidenceRefused` (`EvidenceMismatch` for
the working tree) -- refused, exit 4; a path the index does not name is
absent.  Both derive from `EvidenceError`; `exit_code` maps them.

Writers verify before the index names anything: every object, including one
already at its name, is re-hashed (a bad one is quarantined, never trusted
or deleted), fsync'd with its directory and read back on the archive box
(tools/evidence_ingest.py), and only then is the index line written, under
a lock, fsync'd.  So the committed index never names bytes the archive lacks,
to the extent the archive's filesystem honours fsync (hbox: ZFS).

The durability claim, exactly: an index line means AT LEAST ONE archive member
confirmed that object (verify, fsync, read back through evidence_ingest) --
not that every member holds it.  `put` writes every member, with ssh
`ConnectTimeout=10 BatchMode=yes` so a down box costs ten seconds, succeeds
when one member confirms every object, and names each member it skipped on
stderr with the count of objects that member is now behind; with no member
confirming it raises `EvidenceUnavailable` and writes no index line.  Readers
(`fetch`, `object_bytes`) try the cache, then the members in order: an
unreachable member falls through to the next, and bytes that fail their hash
are quarantined (cache) or left for reconcile (a member), never returned,
whatever another member says -- a good copy elsewhere is used, no good copy is
REFUSED.  `reconcile [--dry-run]` is stateless (the member listings are the
truth): for each reachable member it fetches, hash-verified, what another
member holds and it lacks, and pushes it with evidence_ingest confirmation;
it exits nonzero for an unreachable member or an unconfirmed copy.
`verify [--archive]` reports "unmirrored N on <member>" (nonzero) for indexed
objects a member lacks.  A member that holds an object at its address but with
bad bytes is not in any listing's "missing"; `verify --archive` finds it
(REFUSED), and the next `put` of those bytes replaces it.

    python3 tools/evidence_store.py put PATH...        # archive + index
    python3 tools/evidence_store.py fetch [--all | GLOB...]
    python3 tools/evidence_store.py cat REL
    python3 tools/evidence_store.py ls GLOB
    python3 tools/evidence_store.py index-tree [--write]  # index == tracked tree
    python3 tools/evidence_store.py verify [--archive]
    python3 tools/evidence_store.py reconcile [--dry-run]  # mirror the members
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
import shutil
import socket
import subprocess
import sys
import tarfile
import tempfile
import time
import zlib

sys.path.insert(0, str(Path(__file__).resolve().parent))
import evidence_ingest  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
EVIDENCE_REL = "planning/evidence"
INDEX_REL = "planning/evidence-index.tsv"
DEFAULT_ARCHIVES = ("hbox:/tank/fn/evidence", "persvati:/home/ember/fn-evidence")
# A down box must cost seconds, not an ssh default timeout per object.
SSH_OPTIONS = ("-o", "ConnectTimeout=10", "-o", "BatchMode=yes")
HEADER = ("# fn evidence index: <sha256> <bytes> <path>; the bytes live in the "
          "archive at objects/<sha256[:2]>/<sha256>.gz (tools/evidence_store.py)")


class EvidenceError(RuntimeError):
    """Indexed evidence could not be accepted (see the two kinds below)."""


class EvidenceUnavailable(EvidenceError):
    """An indexed object could not be read or fetched: uncertain (exit 3)."""


class EvidenceRefused(EvidenceError):
    """Bytes are there and do not hash to the name they claim: refused (exit 4)."""


class EvidenceConflict(EvidenceRefused):
    """An existing logical name cannot be assigned different bytes implicitly."""


class EvidenceMismatch(EvidenceRefused):
    """A working-tree file differs from the bytes its index line names."""


HEX64 = evidence_ingest.HEX64
EXIT_UNAVAILABLE = 3
EXIT_REFUSED = 4


def exit_code(error: EvidenceError) -> int:
    return EXIT_REFUSED if isinstance(error, EvidenceRefused) else EXIT_UNAVAILABLE


def outcome(error: EvidenceError) -> str:
    return "REFUSED" if isinstance(error, EvidenceRefused) else "UNAVAILABLE"


# ------------------------------------------------------------------ places


def archive_specs() -> list[str]:
    """The ordered archive set: FN_EVIDENCE_ARCHIVES (comma-separated), else
    FN_EVIDENCE_ARCHIVE as a one-element set, else DEFAULT_ARCHIVES."""
    plural = os.environ.get("FN_EVIDENCE_ARCHIVES", "")
    specs = [part.strip() for part in plural.split(",") if part.strip()]
    if not specs:
        singular = os.environ.get("FN_EVIDENCE_ARCHIVE")
        specs = [singular] if singular else list(DEFAULT_ARCHIVES)
    return list(dict.fromkeys(specs))


def archive_label() -> str:
    return ", ".join(archive_specs())


def ssh_argv(host: str) -> list[str]:
    return ["ssh", *SSH_OPTIONS, host]


def rsync_ssh() -> str:
    return " ".join(["ssh", *SSH_OPTIONS])


def split_spec(spec: str) -> tuple[str, str]:
    """`HOST:/path` -> (HOST, /path); a bare path -> ("", path)."""
    head, sep, tail = spec.partition(":")
    if sep and head and not head.startswith("/"):
        return head, tail
    return "", spec


def local_member(spec: str) -> Path | None:
    """The directory of archive member SPEC when this machine holds it
    (a bare path, or HOST:/path with HOST this machine and the archive
    present), else None."""
    host, path = split_spec(spec)
    if host and host != socket.gethostname().split(".")[0]:
        return None
    candidate = Path(path)
    if not host or (candidate / "objects").is_dir():
        return candidate
    return None


def local_archives() -> list[Path]:
    """Every member of the set this machine holds, in set order."""
    return [found for found in map(local_member, archive_specs()) if found is not None]


def local_archive() -> Path | None:
    """This machine's member of the archive set (hbox or persvati), else None."""
    held = local_archives()
    return held[0] if held else None


def remote_members() -> list[str]:
    """The members this machine must reach over ssh, in set order."""
    return [spec for spec in archive_specs() if local_member(spec) is None]


_CHECKOUTS: dict[tuple, Path] = {}


def _locator_state(root: Path) -> tuple:
    """Git discovery markers, including absent ancestor markers and commondir.

    Remembering an absent marker is safe only while every ancestor still lacks
    one. Linked worktrees also depend on their admin directory's commondir.
    """
    def signature(path):
        try:
            stat = path.stat()
            return (str(path), stat.st_dev, stat.st_ino, stat.st_mtime_ns,
                    stat.st_ctime_ns, stat.st_size)
        except OSError:
            return (str(path), None)

    directory = root.resolve()
    state = [str(directory)]
    for ancestor in (directory, *directory.parents):
        marker = ancestor / ".git"
        stamp = signature(marker)
        state.append(stamp)
        if stamp[1] is None:
            continue
        gitdir = marker
        if marker.is_file():
            try:
                pointer = marker.read_text().strip()
                if pointer.startswith("gitdir: "):
                    gitdir = (ancestor / pointer[8:]).resolve()
            except (OSError, UnicodeError):
                pass
        state.extend((signature(gitdir), signature(gitdir / "commondir")))
        break
    # Git discovery can be explicitly redirected by the calling environment.
    state.append(tuple(sorted((key, value) for key, value in os.environ.items()
                              if key.startswith("GIT_"))))
    return tuple(state)


def checkout_of(root: Path) -> Path:
    """Locate the cache once while Git discovery state remains unchanged.

    Missing ancestor markers are checked on every lookup, so later git init
    is visible. Only the location is memoized; objects still verify on read.
    """
    key = _locator_state(root)
    if key in _CHECKOUTS:
        return _CHECKOUTS[key]
    try:
        common = subprocess.run(
            ["git", "-C", str(root), "rev-parse", "--path-format=absolute",
             "--git-common-dir"], capture_output=True, text=True, check=False
        ).stdout.strip()
    except OSError:
        common = ""
    checkout = Path(common).parent if common and Path(common).name == ".git" else root
    _CHECKOUTS[key] = checkout
    return checkout


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


def index_lock_path(root: Path) -> Path:
    """The lock beside the index it guards: one name per index file whatever
    FN_EVIDENCE_CACHE says (r61 F6: two cache settings were two locks)."""
    index = (root / INDEX_REL).resolve()
    return index.with_name(index.name + ".lock")


@contextlib.contextmanager
def index_lock(root: Path):
    """One writer at a time per index file (flock; released on process death)."""
    lock = index_lock_path(root)
    lock.parent.mkdir(parents=True, exist_ok=True)
    with open(lock, "a") as handle:
        fcntl.flock(handle.fileno(), fcntl.LOCK_EX)
        try:
            yield
        finally:
            fcntl.flock(handle.fileno(), fcntl.LOCK_UN)


def add_to_index(root: Path, new: dict[str, tuple[str, int]], *,
                 replace: bool = False) -> None:
    """Merge rows into the index under the lock, reading it fresh inside it."""
    with index_lock(root):
        path = root / INDEX_REL
        try:
            text = path.read_text(encoding="utf-8")
        except FileNotFoundError:
            text = ""
        entries = parse_index(text)
        if not replace:
            for name, entry in new.items():
                if name in entries and entries[name] != entry:
                    raise EvidenceConflict(f"{name}: already indexed with different bytes")
        entries.update(new)
        write_index(root, entries)


# ------------------------------------------------------------------ objects


def _verified(data_gz: bytes, sha: str) -> bytes:
    try:
        data = gzip.decompress(data_gz)
    except (OSError, EOFError, ValueError, zlib.error) as error:
        raise EvidenceRefused(f"object {sha} is not a gzip stream: {error}") from error
    if sha256_bytes(data) != sha:
        raise EvidenceRefused(f"object {sha} does not hash to its name")
    return data


def store_object(directory: Path, data: bytes, sha: str | None = None) -> str:
    """Place one object under `directory`: verified, durable, read back.

    An object already at its name is re-hashed, never trusted; one that does
    not verify is quarantined and replaced (tools/evidence_ingest.py).
    """
    sha = sha or sha256_bytes(data)
    if sha256_bytes(data) != sha:
        raise EvidenceRefused(f"bytes offered for {sha} do not hash to it")
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


def _holders(root: Path) -> list[Path]:
    """Directories this machine reads objects from: the cache, then each
    local archive member."""
    return [cache_dir(root), *local_archives()]


def object_path(root: Path, sha: str) -> Path | None:
    """Where this machine already has the object, without fetching."""
    for directory in _holders(root):
        if (directory / object_rel(sha)).is_file():
            return directory / object_rel(sha)
    return None


def _local_good(root: Path, sha: str) -> tuple[bytes | None, EvidenceRefused | None]:
    """(verified bytes, None) from the first holder whose copy verifies, else
    (None, the first refusal or None).  A bad cached copy is quarantined; a
    bad copy in an archive member is left for reconcile (a reader never
    writes an archive) and never returned."""
    cache = cache_dir(root)
    refused: EvidenceRefused | None = None
    for directory in _holders(root):
        path = directory / object_rel(sha)
        if not path.is_file():
            continue
        try:
            return _read_verified(path, sha), None
        except EvidenceRefused as error:
            refused = refused or error
            if directory == cache:
                _quarantine(cache, path, sha)
    return None, refused


def _fetch_remote(root: Path, wanted: list[str]) -> tuple[list[str], list[str], list[str]]:
    """Try the remote members in order for WANTED; each arrival is verified
    into the cache.  Returns (still wanted, ever arrived-and-bad, notes).
    An unreachable member falls through; bytes that fail the hash are
    quarantined and the next member is asked for that object."""
    cache = cache_dir(root)
    bad: list[str] = []
    notes: list[str] = []
    wanted = list(wanted)
    for spec in remote_members():
        if not wanted:
            break
        host, path = split_spec(spec)
        cache.mkdir(parents=True, exist_ok=True)
        with tempfile.NamedTemporaryFile("w", suffix=".list", delete=False) as listing:
            listing.write("".join(object_rel(sha) + "\n" for sha in wanted))
            listing_name = listing.name
        try:
            done = subprocess.run(
                ["rsync", "-a", "-e", rsync_ssh(), "--files-from", listing_name,
                 f"{host}:{path.rstrip('/')}/", str(cache) + "/"],
                capture_output=True, text=True, check=False)
        finally:
            os.unlink(listing_name)
        left = []
        for sha in wanted:
            target = cache / object_rel(sha)
            try:
                _read_verified(target, sha)
            except EvidenceRefused:
                bad.append(sha)
                _quarantine(cache, target, sha)
                left.append(sha)
            except EvidenceUnavailable:
                left.append(sha)
        if done.returncode != 0 or left:
            notes.append(f"{spec}: rsync exit {done.returncode}: {done.stderr.strip()[-200:]}")
        wanted = left
    return wanted, bad, notes


def fetch(root: Path, shas: list[str] | set[str], verify_present: bool = True) -> None:
    """Bring every named object into the cache; verify each.

    Held here already (the cache, or a local archive member): with
    `verify_present` (the CLI) it is re-hashed too, a bad cached copy is
    quarantined and fetched again.  Otherwise the remote members are tried
    in set order, one rsync each; an unreachable member falls through to the
    next, and an arrival that fails its hash is quarantined and asked for
    from the next member.  What no member supplies verified is REFUSED when
    some copy was there and wrong, UNAVAILABLE otherwise.  `prefetch` passes
    False: every read verifies anyway (`object_bytes`).
    """
    wanted: list[str] = []
    refused_here: list[str] = []
    for sha in sorted(set(shas)):
        object_rel(sha)
        if verify_present:
            data, refused = _local_good(root, sha)
            if data is None:
                (refused_here if refused else wanted).append(sha)
        elif object_path(root, sha) is None:
            wanted.append(sha)
    wanted += refused_here
    if not wanted:
        return
    wanted.sort()
    count = len(wanted)
    left, bad, notes = _fetch_remote(root, wanted)
    if not left:
        return
    if not remote_members():
        if refused_here:
            raise EvidenceRefused(
                f"{len(refused_here)} objects in the local archive {local_archive()} do "
                f"not verify (first {refused_here[0]})")
        raise EvidenceUnavailable(
            f"{count} evidence objects are in neither {cache_dir(root)} nor "
            f"the archive {archive_label()} (first {wanted[0]})")
    refusals = sorted(set(bad) | (set(refused_here) & set(left)))
    kind = EvidenceRefused if refusals else EvidenceUnavailable
    raise kind(
        f"{len(left)} of {count} evidence objects did not arrive "
        f"verified from {archive_label()} ({len(set(bad))} arrived and do not verify, "
        f"{len(left) - len(set(bad) & set(left))} did not arrive; "
        f"{'; '.join(notes)[-400:]}); first {left[0]}")


def object_bytes(root: Path, sha: str) -> bytes:
    """The object's bytes, verified on this read.  The cache, then each local
    member; a bad cached copy is quarantined; then the remote members in
    order.  A copy that does not verify is never returned: with no good copy
    anywhere it is REFUSED, and anything merely unreadable is UNAVAILABLE."""
    object_rel(sha)
    data, refused = _local_good(root, sha)
    if data is not None:
        return data
    left, bad, notes = _fetch_remote(root, [sha])
    if not left:
        return _read_verified(cache_dir(root) / object_rel(sha), sha)
    if refused is not None:
        raise refused
    if bad:
        raise EvidenceRefused(f"object {sha} did not arrive verified from "
                              f"{archive_label()} (it arrived and does not verify); "
                              f"{'; '.join(notes)[-300:]}")
    raise EvidenceUnavailable(f"object {sha} did not arrive from {archive_label()}"
                              f"{': ' + '; '.join(notes)[-300:] if notes else ''}")


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


# The two fields a run-manifest self-archive adds (which run, where its logs
# were left).  evidence_manifests.ADDED is this tuple.
ADDED = ("run_id", "archived_from")
MANIFEST_DIR = "planning/evidence/manifests/"


def same_manifest_modulo_provenance(name: str, local: bytes, indexed: bytes) -> bool:
    """Is `local` the indexed run manifest re-archived with other provenance?

    Only for a file under planning/evidence/manifests/, both sides JSON
    objects equal once the ADDED keys are dropped.  Anything else is False.
    """
    if not name.startswith(MANIFEST_DIR):
        return False
    try:
        mine, theirs = json.loads(local), json.loads(indexed)
    except ValueError:
        return False
    if not isinstance(mine, dict) or not isinstance(theirs, dict):
        return False
    return ({k: v for k, v in mine.items() if k not in ADDED}
            == {k: v for k, v in theirs.items() if k not in ADDED})


def _heal_provenance(root: Path, local: Path, name: str, entry: tuple[str, int],
                     data: bytes) -> bytes | None:
    """Replace a provenance-only-different manifest by the indexed bytes."""
    if not name.startswith(MANIFEST_DIR):
        return None
    try:
        indexed = object_bytes(root, entry[0])
    except EvidenceError:
        return None  # nothing verified to heal from: the difference stands
    if not same_manifest_modulo_provenance(name, data, indexed):
        return None

    def origin(blob: bytes) -> object:
        return json.loads(blob).get("archived_from")

    descriptor, tmp = tempfile.mkstemp(dir=local.parent, prefix=local.name + ".")
    try:
        with os.fdopen(descriptor, "wb") as handle:
            handle.write(indexed)
        os.replace(tmp, local)
    except BaseException:
        with contextlib.suppress(OSError):
            os.unlink(tmp)
        raise
    print(f"evidence_store: {name}: working-tree manifest differed from the index only "
          f"in provenance; restored the indexed bytes (archived_from {origin(data)!r} "
          f"-> {origin(indexed)!r})", file=sys.stderr)
    return indexed


def _local_matching(root: Path, local: Path, name: str, entry: tuple[str, int]) -> bytes:
    try:
        data = local.read_bytes()
    except OSError as error:
        raise EvidenceUnavailable(f"{name}: the working-tree copy is unreadable: "
                                  f"{error}") from error
    if len(data) != entry[1] or sha256_bytes(data) != entry[0]:
        healed = _heal_provenance(root, local, name, entry, data)
        if healed is not None:
            return healed
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
            return _local_matching(root, local, name, entry), "indexed"
        return object_bytes(root, entry[0]), "indexed"
    if local.is_file():
        return local.read_bytes(), "local"
    raise FileNotFoundError(name)


def read_bytes(root: Path, rel: str | Path) -> bytes:
    """The indexed bytes (verified), else an unindexed working-tree file."""
    return locate(root, rel)[0]


def read_text(root: Path, rel: str | Path) -> str:
    return read_bytes(root, rel).decode("utf-8")


def read_input_text(root: Path, path: str | Path) -> str:
    """CLI input: logical evidence names use the store, ordinary files stay local."""
    path = Path(path)
    # Normalize spelling lexically: resolving a local symlink could hide the
    # indexed name behind a shadow outside the tree.
    absolute = Path(os.path.abspath(path))
    name = os.path.normpath(path.as_posix())
    for base in (root.absolute(), root.resolve()):
        try:
            name = absolute.relative_to(base).as_posix()
            break
        except ValueError:
            pass
    if name.startswith(EVIDENCE_REL + "/"):
        name = os.path.normpath(name)
        if name.startswith(EVIDENCE_REL + "/"):
            return read_text(root, name)
    return path.read_text(encoding="utf-8")


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
        _local_matching(root, local, name, entry)
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
                 index: dict[str, tuple[str, int]] | None = None,
                 prefer_local: bool = False) -> dict[str, Exception | None]:
    """{path: None if its indexed bytes are readable and verify, else why}.

    Names are not bytes: an index row alone proves nothing (r56 F3).  A path
    the index does not name is FileNotFoundError; an indexed one whose
    object cannot be fetched is EvidenceUnavailable; one whose bytes are
    there and wrong is EvidenceRefused.  A working-tree file at an indexed
    path must hash to the index line (EvidenceMismatch otherwise, r61 F2);
    with `prefer_local` (a reader's question: what `locate` would return)
    a matching working-tree file answers without the archive, without it
    (the cut gate's question) the archive object must verify too.
    """
    index = read_index(root) if index is None else index
    result: dict[str, Exception | None] = {}
    with contextlib.suppress(EvidenceError):
        fetch(root, {index[rel][0] for rel in rels if rel in index
                     and not (prefer_local and (root / rel).is_file())},
              verify_present=False)
    for rel in rels:
        entry = index.get(rel)
        if entry is None:
            result[rel] = FileNotFoundError(rel)
            continue
        try:
            local = root / rel
            if local.is_file():
                _local_matching(root, local, rel, entry)
                if prefer_local:
                    result[rel] = None
                    continue
            data = object_bytes(root, entry[0])
            if len(data) != entry[1]:
                raise EvidenceRefused(f"{rel}: {len(data)} bytes, index says {entry[1]}")
            result[rel] = None
        except EvidenceError as error:
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
    done = subprocess.run([*ssh_argv(host), command], input="".join(s + "\n" for s in shas),
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


def push(root: Path, shas: list[str], spec: str) -> None:
    """Copy cached objects to archive member SPEC and have it confirm them.

    Local directory: `store_object` there (verify existing, fsync, read back).
    `HOST:/path`: rsync into a fresh staging directory inside the archive,
    then evidence_ingest on the box (verify, quarantine a bad existing
    object, rename into place, fsync, read every digest back).  Raises
    EvidenceUnavailable unless every object is confirmed by this member.
    """
    shas = sorted(set(shas))
    if not shas:
        return
    host, path = split_spec(spec)
    if not host:
        archive = Path(path)
        for sha in shas:
            store_object(archive, object_bytes(root, sha), sha)
        return
    cache = cache_dir(root)
    for sha in shas:
        _read_verified(cache / object_rel(sha), sha)
    staging = f"{path.rstrip('/')}/{_staging_name()}"
    made = subprocess.run([*ssh_argv(host), f"mkdir -p {shlex.quote(staging)}"],
                          capture_output=True, text=True, check=False)
    if made.returncode != 0:
        raise EvidenceUnavailable(f"push to {spec}: cannot make the staging "
                                  f"directory (ssh exit {made.returncode}): "
                                  f"{made.stderr.strip()[-300:]}")
    with tempfile.NamedTemporaryFile("w", suffix=".list", delete=False) as listing:
        listing.write("".join(object_rel(sha) + "\n" for sha in shas))
        listing_name = listing.name
    try:
        done = subprocess.run(
            ["rsync", "-a", "-e", rsync_ssh(), "--files-from", listing_name,
             str(cache) + "/", f"{host}:{staging}/"],
            capture_output=True, text=True, check=False)
    finally:
        os.unlink(listing_name)
    if done.returncode != 0:
        raise EvidenceUnavailable(f"push to {spec} failed "
                                  f"(rsync exit {done.returncode}): {done.stderr.strip()[-300:]}")
    _remote_ingest(host, path, staging, shas)


def _skipped(spec: str, behind: int, error: Exception) -> None:
    print(f"evidence_store: archive member {spec} skipped, now {behind} objects "
          f"behind (`evidence_store.py reconcile` brings it up): {error}",
          file=sys.stderr, flush=True)


def archive_objects(root: Path, objects: dict[str, bytes]) -> list[str]:
    """{sha: bytes} -> written to EVERY archive member; returns the members
    that confirmed all of them.  Raises EvidenceUnavailable only when no
    member confirms; a member that does not is reported on stderr with the
    count of objects it is now behind.  Nothing indexed."""
    confirmed: list[str] = []
    failures: list[str] = []
    cached = False
    for spec in archive_specs():
        try:
            held = local_member(spec)
            if held is not None:
                for sha, data in objects.items():
                    store_object(held, data, sha)
            else:
                if not cached:
                    for sha, data in objects.items():
                        store_object(cache_dir(root), data, sha)
                    cached = True
                push(root, list(objects), spec)
            confirmed.append(spec)
        except EvidenceUnavailable as error:
            failures.append(f"{spec}: {error}")
            _skipped(spec, len(objects), error)
    if not confirmed:
        raise EvidenceUnavailable("no archive member confirmed the objects; "
                                  + "; ".join(failures))
    return confirmed


def put(root: Path, rels: list[str], publish: bool = True, *, replace: bool = False) -> dict[str, tuple[str, int]]:
    """Archive working-tree files, then record them in the index.

    The index line is written (locked, fsync'd) only after at least one
    archive member confirmed every object, so a committed index never names
    bytes no archive holds (subject to the filesystem honouring fsync);
    `reconcile` brings the other members up.
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
    if not replace:
        current = read_index(root)
        for name, entry in entries.items():
            if name in current and current[name] != entry:
                raise EvidenceConflict(f"{name}: already indexed with different bytes")
    if publish:
        archive_objects(root, objects)
    else:
        for sha, data in objects.items():
            store_object(cache_dir(root), data, sha)
    add_to_index(root, entries, replace=replace)
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
    """{blob id: first path} for every blob version ever under PREFIXES
    (default planning/evidence; a prefix is a directory or one file, or a
    `glob:`/`regex:` rule as the rewrite list writes it) on REFS (`--all`).

    The full raw-diff walk of tools/evidence_history.py, never a pathspec
    walk: `rev-list --objects REFS -- PATHS` simplifies history and missed
    real versions (r61 F11)."""
    import evidence_history  # noqa: PLC0415
    rules = evidence_history.parse_rules("\n".join(prefixes or [EVIDENCE_REL]))
    snapshot = evidence_history.resolve_refs(root, refs)
    return evidence_history.union(evidence_history.rule_blobs(root, rules, snapshot))


class _Fanout:
    """One tar stream written to every live sink; a sink that breaks drops
    out (its member is reported skipped), the others carry on."""

    def __init__(self, sinks: dict[str, subprocess.Popen]):
        self.sinks = dict(sinks)

    def write(self, data: bytes) -> int:
        for spec, process in list(self.sinks.items()):
            try:
                process.stdin.write(data)
            except OSError:
                del self.sinks[spec]
        return len(data)

    def flush(self) -> None:
        pass

    def close(self) -> None:
        for spec, process in list(self.sinks.items()):
            try:
                process.stdin.close()
            except OSError:
                del self.sinks[spec]


def stream_objects_to_archive(root: Path, blobs: dict[str, str],
                              extra_files: list[Path]) -> list[tuple[str, int, str, str]]:
    """Tar every object into a fresh staging directory inside EVERY archive
    member over one ssh each (one pass over git), then ingest it there
    (evidence_ingest: verify each staged and each existing object, quarantine
    a bad existing one, rename into place, fsync, read every digest back);
    return the ledger rows.  Nothing is extracted over a final object name,
    so an interrupted run leaves only staging debris, never a truncated
    object at a content address.  Unavailable only when no member confirms;
    a member that does not is reported skipped."""
    rows: list[tuple[str, int, str, str]] = []
    staging_name = _staging_name()
    sinks: dict[str, subprocess.Popen] = {}
    for spec in archive_specs():
        host, path = split_spec(spec)
        staging = f"{path.rstrip('/')}/{staging_name}"
        if host:
            argv = [*ssh_argv(host), f"mkdir -p {shlex.quote(staging)} && "
                                     f"tar -x -C {shlex.quote(staging)}"]
        else:
            Path(staging).mkdir(parents=True, exist_ok=True)
            argv = ["tar", "-x", "-C", staging]
        sinks[spec] = subprocess.Popen(argv, stdin=subprocess.PIPE)
    out = _Fanout(sinks)
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
    expected = sorted(seen)
    confirmed: list[str] = []
    failures: list[str] = []
    for spec, process in sinks.items():
        host, path = split_spec(spec)
        staging = f"{path.rstrip('/')}/{staging_name}"
        try:
            code = process.wait()
            if spec not in out.sinks or code != 0:
                raise EvidenceUnavailable(f"archive tar sink for {spec} exited {code}")
            if host:
                report = _remote_ingest(host, path, staging, expected)
            else:
                report = evidence_ingest.ingest(Path(path), Path(staging), expected)
                if report["bad"] or report["missing"]:
                    raise EvidenceUnavailable(f"ingest into {path}: bad {report['bad'][:5]}, "
                                              f"missing {report['missing'][:5]}")
        except EvidenceUnavailable as error:
            failures.append(f"{spec}: {error}")
            _skipped(spec, len(expected), error)
            continue
        confirmed.append(spec)
        print(f"ingested into {spec}: {report['placed']} placed, {report['present']} "
              f"already present and verified, {report['replaced']} replaced (bad copy "
              f"quarantined); {report['expected']} read back", flush=True)
    if not confirmed:
        raise EvidenceUnavailable("no archive member confirmed the stream; "
                                  + "; ".join(failures))
    return rows


def archive_listing(spec: str) -> dict[str, int]:
    """sha -> compressed size of every object the archive holds AT ITS
    CANONICAL NAME objects/<sha[:2]>/<sha>.gz (r61 F5: a file of the right
    name in another shard is not at the address every reader opens)."""
    host, path = split_spec(spec)
    command = (f"cd {shlex.quote(path)} && find objects -name '*.gz' "
               "-printf '%h/%f %s\\n'")
    if host:
        done = subprocess.run([*ssh_argv(host), command], capture_output=True,
                              text=True, check=False)
        if done.returncode != 0:
            raise EvidenceUnavailable(f"cannot list the archive {host}:{path} "
                                      f"(exit {done.returncode}): {done.stderr.strip()[-300:]}")
        text = done.stdout
    else:
        text = "".join(f"objects/{p.parent.name}/{p.name} {p.stat().st_size}\n"
                       for p in Path(path, "objects").glob("*/*.gz"))
    listing = {}
    for row in text.splitlines():
        rel, _, size = row.rpartition(" ")
        name = rel.rsplit("/", 1)[-1]
        if not name.endswith(".gz") or not HEX64.fullmatch(name[:-3]):
            continue
        if rel == object_rel(name[:-3]):
            listing[name[:-3]] = int(size or 0)
    return listing


VERIFY_SCRIPT = r"""
import gzip, hashlib, re, sys, pathlib
root = pathlib.Path(sys.argv[1]); bad = 0; n = 0; hex64 = re.compile('[0-9a-f]{64}')
for p in sorted(root.glob('objects/*/*.gz')):
    n += 1
    sha = p.name[:-3]
    if not hex64.fullmatch(sha) or p.parent.name != sha[:2]:
        bad += 1; print('MISPLACED', p); continue
    try:
        ok = hashlib.sha256(gzip.decompress(p.read_bytes())).hexdigest() == sha
    except Exception:
        ok = False
    if not ok:
        bad += 1; print('BAD', p)
print('verified', n, 'objects,', bad, 'bad or misplaced')
sys.exit(4 if bad else 0)
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
            add_to_index(ROOT, {p: tree[p] for p in batch}, replace=True)
        print(f"wrote {INDEX_REL}: {len(tree)} tracked files "
              f"(+{len(missing)} new, {len(differ)} changed, each archived first; "
              f"{len(extra)} index-only kept)")
        return 0
    print(f"tracked {len(tree)}; indexed {len(index)}; unindexed {len(missing)}; "
          f"changed {len(differ)}; index-only {len(extra)}")
    for path in (missing + differ)[:20]:
        print(f"  not indexed at these bytes: {path}")
    return 1 if (missing or differ) else 0


def _listings() -> tuple[dict[str, dict[str, int]], dict[str, EvidenceUnavailable]]:
    """({member: listing} for reachable members, {member: why} for the rest)."""
    listings: dict[str, dict[str, int]] = {}
    down: dict[str, EvidenceUnavailable] = {}
    for spec in archive_specs():
        try:
            listings[spec] = archive_listing(spec)
        except EvidenceUnavailable as error:
            down[spec] = error
    return listings, down


def reconcile(root: Path, dry_run: bool = False, batch: int = 500) -> dict[str, dict]:
    """Bring every archive member up to the union of all members' listings.

    Stateless: the listings are the truth.  For each reachable member, the
    objects some other member holds and it lacks are fetched with hash
    verification (`object_bytes`: cache, local members, remote members in
    order) and pushed to it with evidence_ingest confirmation (`push`).
    Returns {member: {present, missing, copied, confirmed, unreachable}};
    `dry_run` lists and counts, writes nothing.
    """
    listings, down = _listings()
    union = set().union(*listings.values()) if listings else set()
    report: dict[str, dict] = {spec: {"present": 0, "missing": 0, "copied": 0,
                                      "confirmed": 0, "unreachable": str(down[spec])}
                               for spec in down}
    for spec, listing in listings.items():
        lacking = sorted(union - set(listing))
        report[spec] = {"present": len(listing), "missing": len(lacking), "copied": 0,
                        "confirmed": 0, "unreachable": None}
        if dry_run:
            continue
        for start in range(0, len(lacking), batch):
            chunk = lacking[start:start + batch]
            supplied: list[str] = []
            for sha in chunk:
                try:
                    data = object_bytes(root, sha)
                    if not (cache_dir(root) / object_rel(sha)).is_file():
                        store_object(cache_dir(root), data, sha)
                except EvidenceError as error:
                    print(f"evidence_store: reconcile: {sha} has no verified source: "
                          f"{error}", file=sys.stderr, flush=True)
                    continue
                supplied.append(sha)
            report[spec]["copied"] += len(supplied)
            try:
                push(root, supplied, spec)
            except EvidenceError as error:
                _skipped(spec, len(supplied), error)
                continue
            report[spec]["confirmed"] += len(supplied)
    return report


def cmd_reconcile(args) -> int:
    report = reconcile(ROOT, dry_run=args.dry_run)
    status = 0
    for spec, row in report.items():
        if row["unreachable"]:
            print(f"{spec}: UNREACHABLE: {row['unreachable'][:200]}")
            status = EXIT_UNAVAILABLE
            continue
        print(f"{spec}: present {row['present']}, missing before {row['missing']}, "
              f"copied {row['copied']}, confirmed {row['confirmed']}"
              f"{' (dry run)' if args.dry_run else ''}")
        if not args.dry_run and row["confirmed"] < row["missing"]:
            status = status or EXIT_UNAVAILABLE
    if not any(not row["unreachable"] for row in report.values()):
        raise EvidenceUnavailable("no archive member could be listed")
    return status


def cmd_verify(args) -> int:
    index = read_index(ROOT)
    wanted = {sha for sha, _ in index.values()}
    listings, down = _listings()
    if not listings:
        raise EvidenceUnavailable("no archive member could be listed: "
                                  + "; ".join(f"{s}: {e}" for s, e in down.items()))
    union = set().union(*listings.values())
    absent = sorted(path for path, (sha, _) in index.items() if sha not in union)
    print(f"index {len(index)} files ({len(wanted)} distinct objects); "
          f"archive {archive_label()}; indexed but in no archive: {len(absent)}")
    for path in absent[:20]:
        print(f"  not archived: {path}")
    status = 1 if absent else 0
    for spec, listing in listings.items():
        lacks = wanted - set(listing)
        print(f"  {spec}: {len(listing)} objects "
              f"({sum(listing.values()) / 1e6:.1f} MB compressed)"
              + (f"; unmirrored {len(lacks)} on {spec}" if lacks else ""))
        if lacks:
            status = status or 1
    for spec, error in down.items():
        print(f"  {spec}: UNAVAILABLE: {str(error)[:200]}", file=sys.stderr)
        status = status or EXIT_UNAVAILABLE
    if args.archive:
        # Every object on each reachable box, decompressed and re-hashed
        # there; a bad or misplaced one is refused (4); a box that cannot run
        # it is uncertain.
        for spec in listings:
            host, path = split_spec(spec)
            command = ["python3", "-", path]
            done = subprocess.run([*ssh_argv(host), *map(shlex.quote, command)] if host
                                  else command, input=VERIFY_SCRIPT, text=True, check=False)
            if done.returncode == EXIT_REFUSED:
                return EXIT_REFUSED
            if done.returncode != 0:
                print(f"evidence_store: UNAVAILABLE: the archive check of {spec} did not "
                      f"run (exit {done.returncode})", file=sys.stderr)
                status = status or EXIT_UNAVAILABLE
    return status


def cmd_verify_paths(args) -> int:
    """Each PATH's indexed bytes are readable and verify (exit 0); a path the
    index does not name is refused (1); bytes there and wrong are REFUSED (4);
    an object that cannot be fetched is UNAVAILABLE (3)."""
    index = index_at(ROOT, args.revision) if args.revision else read_index(ROOT)
    problems = verify_paths(ROOT, args.paths, index)
    for rel, problem in problems.items():
        if problem is None:
            print(f"verified {rel}")
        elif isinstance(problem, FileNotFoundError):
            print(f"NOT INDEXED {rel}")
        else:
            print(f"{outcome(problem)} {rel}: {problem}")
    if any(isinstance(p, FileNotFoundError) for p in problems.values()):
        return 1
    if any(isinstance(p, EvidenceRefused) for p in problems.values()):
        return EXIT_REFUSED
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
    if len(digests) != len(blobs):
        print(f"  git delivered {len(digests)} of {len(blobs)} blobs")
        return 1
    import evidence_history  # noqa: PLC0415
    # The canonical object, decompressed and re-hashed on the box (r61 F5).
    report = evidence_history.archive_check({sha: size for sha, size in digests.values()})
    absent, bad = set(report["missing"]), set(report["bad"])
    missing = sorted((blobs[blob], blob, sha) for blob, (sha, _) in digests.items()
                     if sha in absent or sha in bad)
    distinct = {sha for sha, _ in digests.values()}
    print(f"history {' '.join(refs)} under {' '.join(prefixes)}: {len(blobs)} blobs, "
          f"{len(distinct)} distinct sha256, "
          f"{sum(size for _, size in digests.values()) / 1e6:.1f} MB raw; archive "
          f"{archive_label()}: historical blobs not archived and verified at their "
          f"canonical name: {len(missing)} ({len(absent)} absent, {len(bad)} refused)")
    for path, blob, sha in missing[:20]:
        print(f"  not archived: {blob} {sha} {path}")
    if bad:
        return EXIT_REFUSED
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
          f"to {archive_label()}", flush=True)
    rows = stream_objects_to_archive(ROOT, blobs, extras)
    ledger = write_ledger(rows, "history-ledger" if not args.path else "history-ledger-extra")
    print(f"streamed {len(rows)} rows, {len({r[0] for r in rows})} distinct objects; "
          f"ledger {ledger}")
    return 0


def write_ledger(rows: list[tuple[str, int, str, str]], kind: str) -> Path:
    """One ledger per run (sha256, bytes, blob id, path), beside the cache and
    on the archive, never over an earlier one: a narrower run (one --path,
    one revision) must not replace the ledger of a wider run."""
    stamp = time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
    ledger = cache_dir(ROOT) / f"{kind}-{stamp}-{time.time_ns() % 10**9:09d}.tsv"
    ledger.parent.mkdir(parents=True, exist_ok=True)
    ledger.write_text("".join(f"{sha} {size} {blob} {path}\n"
                              for sha, size, blob, path in sorted(rows, key=lambda r: r[3])))
    reached = 0
    failures = []
    for spec in archive_specs():
        host, path = split_spec(spec)
        if not host:
            Path(path).mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ledger, Path(path) / ledger.name)
            reached += 1
            continue
        done = subprocess.run(["rsync", "-a", "-e", rsync_ssh(), str(ledger),
                               f"{host}:{path}/{ledger.name}"],
                              capture_output=True, text=True, check=False)
        if done.returncode != 0:
            failures.append(f"{host}:{path} (rsync exit {done.returncode}): "
                            f"{done.stderr[-200:]}")
        else:
            reached += 1
    if not reached:
        raise EvidenceUnavailable("the history ledger reached no archive member: "
                                  + "; ".join(failures))
    return ledger


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
    one = subs.add_parser("reconcile", help="copy to each archive member the objects "
                                            "another holds and it lacks")
    one.add_argument("--dry-run", action="store_true")
    one.set_defaults(func=cmd_reconcile)
    one = subs.add_parser("verify", help="every indexed object is in every archive")
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
    except EvidenceError as error:
        print(f"evidence_store: {outcome(error)}: {error}", file=sys.stderr)
        return exit_code(error)


if __name__ == "__main__":
    raise SystemExit(main())
