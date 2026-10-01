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

A reader asks this module, never the filesystem: `read_bytes(root, rel)`
returns the working-tree file when one is there (a lane's fresh, not yet
filed output, exactly as a git working tree would show it) and otherwise the
indexed object, from the local cache (`build/evidence-cache/` of the shared
checkout; FN_EVIDENCE_CACHE overrides) or fetched from the archive by hash
and verified against it.  A file named by neither is absent.  An indexed
object that cannot be fetched or does not hash to its name raises
`EvidenceUnavailable`: an unreadable claim is uncertain, never "absent".

    python3 tools/evidence_store.py put PATH...        # archive + index
    python3 tools/evidence_store.py fetch [--all | GLOB...]
    python3 tools/evidence_store.py cat REL
    python3 tools/evidence_store.py ls GLOB
    python3 tools/evidence_store.py index-tree [--write]  # index == tracked tree
    python3 tools/evidence_store.py verify [--archive]
    python3 tools/evidence_store.py migrate-history [--all-refs]
"""

from __future__ import annotations

import argparse
import fnmatch
import gzip
import hashlib
import io
import os
from pathlib import Path
import shlex
import socket
import subprocess
import sys
import tarfile
import tempfile

ROOT = Path(__file__).resolve().parents[1]
EVIDENCE_REL = "planning/evidence"
INDEX_REL = "planning/evidence-index.tsv"
DEFAULT_ARCHIVE = "hbox:/tank/fn/evidence"
HEADER = ("# fn evidence index: <sha256> <bytes> <path>; the bytes live in the "
          "archive at objects/<sha256[:2]>/<sha256>.gz (tools/evidence_store.py)")


class EvidenceUnavailable(RuntimeError):
    """An indexed object could not be fetched, or did not hash to its name."""


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
    return f"objects/{sha[:2]}/{sha}.gz"


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
        if len(parts) != 3 or len(parts[0]) != 64 or not parts[1].isdigit():
            raise ValueError(f"{INDEX_REL}:{number}: malformed line {line!r}")
        sha, size, path = parts
        if path in entries and entries[path] != (sha, int(size)):
            # A union merge kept two versions of one path: say so, never pick.
            raise ValueError(f"{INDEX_REL}:{number}: {path} indexed twice with "
                             "different bytes (a merge kept both; keep the one "
                             "the lane meant and run `evidence_store.py verify`)")
        entries[path] = (sha, int(size))
    return entries


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
    path = root / INDEX_REL
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + f".tmp{os.getpid()}")
    temporary.write_text(render_index(entries), encoding="utf-8")
    os.replace(temporary, path)


def add_to_index(root: Path, new: dict[str, tuple[str, int]]) -> None:
    entries = dict(read_index(root))
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
    """Write one object under `directory` (atomic, idempotent).  Returns sha."""
    sha = sha or sha256_bytes(data)
    target = directory / object_rel(sha)
    if target.is_file():
        return sha
    target.parent.mkdir(parents=True, exist_ok=True)
    temporary = target.with_name(target.name + f".tmp{os.getpid()}")
    temporary.write_bytes(compress(data))
    os.replace(temporary, target)
    return sha


def object_path(root: Path, sha: str) -> Path | None:
    """Where this machine already has the object, without fetching."""
    for directory in (cache_dir(root), local_archive()):
        if directory is not None and (directory / object_rel(sha)).is_file():
            return directory / object_rel(sha)
    return None


def fetch(root: Path, shas: list[str] | set[str]) -> None:
    """Bring every named object into the cache, one rsync; verify each."""
    wanted = sorted({sha for sha in shas if object_path(root, sha) is None})
    if not wanted:
        return
    host, path = split_spec(archive_spec())
    if not host:
        raise EvidenceUnavailable(
            f"{len(wanted)} evidence objects are in neither {cache_dir(root)} nor "
            f"the archive {archive_spec()} (first {wanted[0]})")
    cache = cache_dir(root)
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
            _verified(target.read_bytes(), sha)
        except (OSError, EvidenceUnavailable):
            bad.append(sha)
            with _suppress():
                target.unlink()
    if bad:
        raise EvidenceUnavailable(
            f"{len(bad)} of {len(wanted)} evidence objects did not arrive verified "
            f"from {archive_spec()} (rsync exit {done.returncode}: "
            f"{done.stderr.strip()[-300:]}); first {bad[0]}")


class _suppress:
    def __enter__(self):
        return self

    def __exit__(self, *exc):
        return exc[0] is not None and issubclass(exc[0], OSError)


def object_bytes(root: Path, sha: str) -> bytes:
    found = object_path(root, sha)
    if found is None:
        fetch(root, [sha])
        found = object_path(root, sha)
    if found is None:
        raise EvidenceUnavailable(f"object {sha} did not arrive")
    return _verified(found.read_bytes(), sha)


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


def read_bytes(root: Path, rel: str | Path) -> bytes:
    """The working-tree file if present, else the indexed object."""
    name = _rel(root, rel)
    local = root / name
    if local.is_file():
        return local.read_bytes()
    entry = read_index(root).get(name)
    if entry is None:
        raise FileNotFoundError(name)
    return object_bytes(root, entry[0])


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
    if local.is_file():
        return local
    entry = read_index(root).get(name)
    if entry is None:
        raise FileNotFoundError(name)
    target = cache_dir(root) / "tree" / entry[0] / Path(name).name
    if not target.is_file():
        data = object_bytes(root, entry[0])
        target.parent.mkdir(parents=True, exist_ok=True)
        temporary = target.with_name(target.name + f".tmp{os.getpid()}")
        temporary.write_bytes(data)
        os.replace(temporary, target)
    return target


def prefetch(root: Path, rels: list[str]) -> None:
    """One fetch for every indexed path a caller is about to read."""
    index = read_index(root)
    fetch(root, {index[rel][0] for rel in rels
                 if rel in index and not (root / rel).is_file()})


# ------------------------------------------------------------------ writers


def push(root: Path, shas: list[str]) -> None:
    """Copy cached objects to the archive (no-op when this box is the archive)."""
    if not shas:
        return
    host, path = split_spec(archive_spec())
    cache = cache_dir(root)
    if not host:
        archive = Path(path)
        for sha in shas:
            source = cache / object_rel(sha)
            if source.is_file() and not (archive / object_rel(sha)).is_file():
                store_object(archive, _verified(source.read_bytes(), sha), sha)
        return
    with tempfile.NamedTemporaryFile("w", suffix=".list", delete=False) as listing:
        listing.write("".join(object_rel(sha) + "\n" for sha in sorted(set(shas))))
        listing_name = listing.name
    try:
        done = subprocess.run(
            ["rsync", "-a", "--ignore-existing", "--files-from", listing_name,
             str(cache) + "/", f"{host}:{path.rstrip('/')}/"],
            capture_output=True, text=True, check=False)
    finally:
        os.unlink(listing_name)
    if done.returncode != 0:
        raise EvidenceUnavailable(f"push to {archive_spec()} failed "
                                  f"(rsync exit {done.returncode}): {done.stderr.strip()[-300:]}")


def put(root: Path, rels: list[str], publish: bool = True) -> dict[str, tuple[str, int]]:
    """Archive working-tree files and record them in the index.

    The index line is written only after the object reached the archive, so a
    committed index never names bytes the archive lacks.
    """
    entries: dict[str, tuple[str, int]] = {}
    cache = cache_dir(root)
    archive = local_archive()
    for rel in rels:
        name = _rel(root, rel)
        data = (root / name).read_bytes()
        sha = store_object(archive or cache, data)
        entries[name] = (sha, len(data))
    if publish and archive is None:
        push(root, [sha for sha, _ in entries.values()])
    add_to_index(root, entries)
    return entries


# --------------------------------------------------------------- transition


def git_lines(root: Path, *args: str) -> list[str]:
    done = subprocess.run(["git", "-C", str(root), *args], capture_output=True,
                          text=True, check=False)
    return done.stdout.splitlines()


def tree_entries(root: Path, revision: str = "HEAD") -> dict[str, tuple[str, int]]:
    """(sha256, bytes) of every file tracked under planning/evidence at REVISION."""
    rows = git_lines(root, "ls-tree", "-r", "-l", revision, "--", EVIDENCE_REL)
    blobs = {}
    for row in rows:
        meta, _, path = row.partition("\t")
        parts = meta.split()
        if len(parts) == 4 and parts[1] == "blob":
            blobs[path] = parts[2]
    entries: dict[str, tuple[str, int]] = {}
    for path, data in cat_blobs(root, blobs):
        entries[path] = (sha256_bytes(data), len(data))
    return entries


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


def history_blobs(root: Path, refs: list[str]) -> dict[str, str]:
    """{blob id: first path} for every blob ever under planning/evidence."""
    found: dict[str, str] = {}
    rows = git_lines(root, "rev-list", "--objects", *refs, "--", EVIDENCE_REL)
    candidates = {}
    for row in rows:
        oid, _, path = row.partition(" ")
        if path.startswith(EVIDENCE_REL + "/"):
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
    """Tar every object to the archive over one ssh; return the ledger rows."""
    host, path = split_spec(archive_spec())
    rows: list[tuple[str, int, str, str]] = []
    if host:
        sink = subprocess.Popen(
            ["ssh", host, f"mkdir -p {shlex.quote(path)} && "
                          f"tar -x -C {shlex.quote(path)} --skip-old-files"],
            stdin=subprocess.PIPE)
        out = sink.stdin
    else:
        Path(path).mkdir(parents=True, exist_ok=True)
        sink = subprocess.Popen(["tar", "-x", "-C", path], stdin=subprocess.PIPE)
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
    fetch(ROOT, {index[rel][0] for rel in rels})
    print(f"{len(rels)} indexed files; {before} were cached; all now in {cache_dir(ROOT)}")
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
        write_index(ROOT, {**index, **tree})
        print(f"wrote {INDEX_REL}: {len(tree)} tracked files "
              f"(+{len(missing)} new, {len(differ)} changed, {len(extra)} index-only kept)")
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


def cmd_migrate_history(args) -> int:
    refs = ["--all"] if args.all_refs else [args.revision]
    blobs = history_blobs(ROOT, refs)
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
    ledger = cache_dir(ROOT) / "history-ledger.tsv"
    ledger.parent.mkdir(parents=True, exist_ok=True)
    ledger.write_text("".join(f"{sha} {size} {blob} {path}\n"
                              for sha, size, blob, path in sorted(rows, key=lambda r: r[3])))
    host, path = split_spec(archive_spec())
    if host:
        subprocess.run(["rsync", "-a", str(ledger), f"{host}:{path}/history-ledger.tsv"],
                       check=False)
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
    one = subs.add_parser("migrate-history",
                          help="copy every historical planning/evidence blob to the archive")
    one.add_argument("--revision", default="HEAD")
    one.add_argument("--all-refs", action="store_true")
    one.add_argument("--untracked", action="store_true",
                     help="also the shared checkout's untracked evidence files")
    one.set_defaults(func=cmd_migrate_history)
    args = parser.parse_args(argv)
    try:
        return args.func(args)
    except EvidenceUnavailable as error:
        print(f"evidence_store: UNAVAILABLE: {error}", file=sys.stderr)
        return 3


if __name__ == "__main__":
    raise SystemExit(main())
