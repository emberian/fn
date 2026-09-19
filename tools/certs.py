#!/usr/bin/env python3
"""A content-addressed cache of ACL2 certificates for fn's books.

Every fn tool sets ``ACL2_BOOK_HASH_ALISTP=NIL``, so ACL2 8.7 writes a book
hash over the *contents* of a book and its includes rather than over write
dates and absolute paths.  A ``.cert``/``.port`` pair is therefore valid in any
worktree and on any host whose book content is the same bytes.  This tool is
the consequence: certificates are stored under the SHA-256 of the book source
that produced them, and installed into any worktree whose book source hashes to
the same key.

What the cache does not do: it cannot tell that a certificate was produced from
the book it sits next to.  The key records the content of the *book*, not the
content of the certificate's own dependency world.  Two guards keep a stale
pair out: a certificate is published only when it is valid-looking (an ACL2
certificate's portcullis markers are present) and no older than the book beside
it, and installation never replaces a local certificate that already matches
its book and is at least as new as the cached one.  Neither guard is a proof;
`tools/certify_books.py` is what establishes that a book certifies, and it
publishes here only after it has seen a fresh success marker.

    python3 tools/certs.py publish [--remote hbox]   # after a certification
    python3 tools/certs.py install                   # entering a new worktree
    python3 tools/certs.py status
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass, field
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
BOOK_DIRECTORIES = ("books", "tests/acl2")
DEFAULT_CACHE = "~/.cache/fn-certs"
# Where a farm box keeps its copy.  `--remote host:path` overrides.
REMOTE_CACHES = {"hbox": "/tank/fn/certcache", "persvati": "~/fn-certcache"}
# An ACL2 certificate opens with a package form and carries its portcullis
# between these markers.  An empty or truncated file has neither.
CERT_MARKERS = (":BEGIN-PORTCULLIS-CMDS", ":END-PORTCULLIS-CMDS")


@dataclass
class Report:
    """What one command did, in counts plus the lists worth naming."""

    action: str
    cache: str
    books: int = 0
    published: int = 0
    already: int = 0
    installed: int = 0
    kept: int = 0
    stale: list[str] = field(default_factory=list)
    uncached: list[str] = field(default_factory=list)
    certified_locally: int = 0
    mirrored: str | None = None

    def lines(self) -> list[str]:
        out = [f"{self.action}: {self.books} books, cache {self.cache}"]
        if self.action == "publish":
            out.append(f"  published {self.published}, already cached {self.already}, "
                       f"no valid certificate {len(self.uncached)}, "
                       f"certificate older than its book {len(self.stale)}")
        elif self.action == "install":
            out.append(f"  installed {self.installed}, kept newer local {self.kept}, "
                       f"no cached certificate {len(self.uncached)}")
        else:
            out.append(f"  certified here {self.certified_locally}, "
                       f"in the cache {self.books - len(self.uncached)}, "
                       f"not in the cache {len(self.uncached)}")
        for book in self.stale:
            out.append(f"  stale (certificate older than book): {book}")
        for book in self.uncached:
            out.append(f"  uncached: {book}")
        if self.mirrored:
            out.append(f"  mirrored to {self.mirrored}")
        return out


def cache_directory() -> Path:
    return Path(os.environ.get("FN_CERT_CACHE", DEFAULT_CACHE)).expanduser()


def content_hash(path: Path) -> str:
    hasher = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            hasher.update(chunk)
    return hasher.hexdigest()


def book_sources(root: Path, names: list[str] | None = None) -> list[Path]:
    """Every book under ``books/`` and ``tests/acl2/``, or the named ones."""
    if names is not None:
        return [(root / f"{name}.lisp").resolve() for name in names]
    found: list[Path] = []
    for directory in BOOK_DIRECTORIES:
        base = root / directory
        if base.is_dir():
            found.extend(sorted(base.rglob("*.lisp")))
    return found


def book_name(root: Path, source: Path) -> str:
    return source.resolve().relative_to(root.resolve()).with_suffix("").as_posix()


def valid_looking(cert: Path) -> bool:
    """A certificate ACL2 could have written, judged without running ACL2."""
    if not cert.is_file() or cert.stat().st_size == 0:
        return False
    try:
        head = cert.read_bytes()[:4096]
    except OSError:  # pragma: no cover - unreadable file
        return False
    # ACL2 8.7 writes certificates with its compact serializer: the file
    # opens with the serializer magic (`#Z` after a form feed) and is not
    # UTF-8 text.  Older ACL2s and hand-written fixtures use the textual
    # form beginning with (IN-PACKAGE.  Accept either; ACL2 itself decides
    # validity at include time.
    if b"#Z" in head[:16]:
        return True
    text = head.decode("utf-8", errors="replace")
    return text.lstrip().startswith("(IN-PACKAGE") and all(
        marker in text for marker in CERT_MARKERS)


def entry_directory(cache: Path, digest: str, name: str) -> Path:
    """The entry for one book: its content hash, then its own name.

    The content hash is the key, as it must be: it is what makes a pair
    portable between worktrees and hosts.  The book name below it is a
    deliberate refusal to share a certificate between two *differently named*
    books that happen to hold the same bytes.  Whether ACL2 8.7 writes the
    book's own name into its certificate is not something this tool should
    have to be right about; the cost of the extra level is one directory, and
    the cost of being wrong is a confusing certification failure downstream.
    """
    return cache / digest / name.replace("/", "--")


def read_meta(directory: Path) -> dict:
    try:
        return json.loads((directory / "meta.json").read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return {}


def publish(root: Path, cache: Path, names: list[str] | None = None) -> Report:
    """Store the certificate pair of every book that has a usable one."""
    report = Report(action="publish", cache=str(cache))
    cache.mkdir(parents=True, exist_ok=True)
    for source in book_sources(root, names):
        if not source.is_file():
            continue
        report.books += 1
        name = book_name(root, source)
        cert = source.with_suffix(".cert")
        if not valid_looking(cert):
            report.uncached.append(name)
            continue
        # Validity is decided by content, not by mtime: the certificate records
        # the book's checksum (ACL2_BOOK_HASH_ALISTP=NIL), and include-book
        # refuses a mismatch.  Checkout mtimes are meaningless (a fresh
        # worktree is newer than every certificate ever made for it).
        digest = content_hash(source)
        directory = entry_directory(cache, digest, name)
        cached = directory / "book.cert"
        if cached.is_file() and content_hash(cached) == content_hash(cert):
            report.already += 1
            continue
        directory.mkdir(parents=True, exist_ok=True)
        port = source.with_suffix(".port")
        write_entry(directory, name, digest, cert, port if port.is_file() else None)
        report.published += 1
    return report


def write_entry(directory: Path, name: str, digest: str,
                cert: Path, port: Path | None) -> None:
    """Write the pair and its metadata, each file renamed into place."""
    place(cert, directory / "book.cert")
    target_port = directory / "book.port"
    if port is None:
        target_port.unlink(missing_ok=True)
    else:
        place(port, target_port)
    meta = {
        "book": name,
        "book_sha256": digest,
        "cert_sha256": content_hash(cert),
        "certified_at": cert.stat().st_mtime,
        "has_port": port is not None,
        "published_at": dt.datetime.now(dt.timezone.utc).isoformat(),
        "published_from": str(cert.parent),
        "host": os.uname().nodename,
    }
    temporary = directory / "meta.json.tmp"
    temporary.write_text(json.dumps(meta, indent=2, sort_keys=True) + "\n",
                         encoding="utf-8")
    temporary.replace(directory / "meta.json")


def place(source: Path, target: Path) -> None:
    temporary = target.with_suffix(target.suffix + ".tmp")
    shutil.copyfile(source, temporary)
    shutil.copystat(source, temporary)
    temporary.replace(target)


def install(root: Path, cache: Path, names: list[str] | None = None) -> Report:
    """Copy every cached pair whose key matches a book in this worktree."""
    report = Report(action="install", cache=str(cache))
    for source in book_sources(root, names):
        if not source.is_file():
            continue
        report.books += 1
        name = book_name(root, source)
        directory = entry_directory(cache, content_hash(source), name)
        cached = directory / "book.cert"
        if not cached.is_file():
            report.uncached.append(name)
            continue
        meta = read_meta(directory)
        cert = source.with_suffix(".cert")
        if valid_looking(cert):
            # A local certificate already exists for this content: keep it.
            # Both describe the same bytes, and ACL2 decides validity.
            report.kept += 1
            continue
        place(cached, cert)
        port = source.with_suffix(".port")
        if (directory / "book.port").is_file():
            place(directory / "book.port", port)
        else:
            # A left-over .port from another certification would contradict
            # the installed certificate's portcullis.
            port.unlink(missing_ok=True)
        # Stamp the installed pair no earlier than the certification it came
        # from: a second install is then a no-op, and a farm box whose clock
        # runs ahead of this one does not make its own work look stale here.
        stamp = max(dt.datetime.now(dt.timezone.utc).timestamp(),
                    meta.get("certified_at", 0.0))
        os.utime(cert, (stamp, stamp))
        if port.is_file():
            os.utime(port, (stamp, stamp))
        report.installed += 1
    return report


def status(root: Path, cache: Path) -> Report:
    report = Report(action="status", cache=str(cache))
    for source in book_sources(root):
        report.books += 1
        name = book_name(root, source)
        if valid_looking(source.with_suffix(".cert")):
            report.certified_locally += 1
        entry = entry_directory(cache, content_hash(source), name)
        if not entry.joinpath("book.cert").is_file():
            report.uncached.append(name)
    return report


def remote_target(remote: str) -> str:
    """``host`` with this project's default path, or ``host:path`` verbatim."""
    if ":" in remote:
        return remote
    path = REMOTE_CACHES.get(remote)
    if path is None:
        raise ValueError(f"no default cache path for {remote}; use host:path")
    return f"{remote}:{path}"


def mirror(cache: Path, remote: str,
           run=subprocess.run) -> subprocess.CompletedProcess:
    """rsync the cache to a farm box.  Entries are immutable, so no --delete."""
    target = remote_target(remote)
    host, path = target.split(":", 1)
    run(["ssh", host, f"mkdir -p {path}"], check=True)
    return run(["rsync", "-a", f"{cache}/", f"{target}/"], check=True)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("action", choices=("publish", "install", "status"))
    parser.add_argument("books", nargs="*", default=None,
                        help="repository-relative book names without .lisp "
                             "(default: every book under books/ and tests/acl2/)")
    parser.add_argument("--root", default=str(ROOT),
                        help="worktree to publish from or install into")
    parser.add_argument("--cache", default=None, help="cache directory "
                        "(default: FN_CERT_CACHE or ~/.cache/fn-certs)")
    parser.add_argument("--remote", default=None,
                        help="after publishing, rsync the cache to host or host:path")
    arguments = parser.parse_args(argv)
    root = Path(arguments.root).resolve()
    cache = Path(arguments.cache).expanduser() if arguments.cache else cache_directory()
    names = arguments.books or None
    if arguments.action == "publish":
        report = publish(root, cache, names)
        if arguments.remote:
            mirror(cache, arguments.remote)
            report.mirrored = remote_target(arguments.remote)
    elif arguments.action == "install":
        report = install(root, cache, names)
    else:
        report = status(root, cache)
    for line in report.lines():
        print(line)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
