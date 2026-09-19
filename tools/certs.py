#!/usr/bin/env python3
"""A cache of ACL2 certificates, keyed by a book's whole include closure.

Every fn tool sets ``ACL2_BOOK_HASH_ALISTP=NIL``, so ACL2 8.7 hashes book
*contents* rather than write dates and absolute paths: a ``.cert``/``.port``
pair is valid in any worktree and on any host whose books are the same bytes.
This tool caches those pairs.  Two rules, both learned by being wrong:

**A pair is published only against a certification manifest.**  A ``.cert``
lying next to a book proves nothing: it may be left over from the source that
was there before a merge, in which case filing it under the *current* book's
key poisons the cache for everyone.  So ``publish`` reads the manifests written
by ``tools/certify_books.py`` and publishes a book only when the source beside
it still hashes to what that run certified (``source_digests_sha256`` and, when
the run recorded it, ``source_digests_sha256_after``) and the certificate
beside it still hashes to what that run produced
(``certificate_digests_sha256``).  There is no other publish path.

**The key is the closure, not the book.**  A certificate is valid only for the
book *and every book it includes*: change a dependency and ACL2 refuses with a
sub-book checksum mismatch.  Keying by the book's own content would report
"cached" for a pair that cannot be used.  The key is therefore the SHA-256 of
the sorted ``<path>:<sha256>`` listing of the book and its whole local include
closure, which also keeps two same-byte books apart, since each listing names
its own path.

What this still does not establish: nothing here proves a book certifies.
``tools/certify_books.py`` does that, with a fresh success marker per book; the
cache only moves its result to another worktree, where ACL2 checks it again.

    python3 tools/certs.py publish [--manifest PATH] [--remote hbox]
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
# One s-expression reader in this project: the ledger's.  It never interns,
# evaluates or macro-expands, so computing a closure cannot run a book.
sys.path.insert(0, str(Path(__file__).resolve().parent))
import ledger  # noqa: E402

BOOK_DIRECTORIES = ("books", "tests/acl2")
DEFAULT_CACHE = "~/.cache/fn-certs"
# Where a farm box keeps its copy.  `--remote host:path` overrides.
REMOTE_CACHES = {"hbox": "/tank/fn/certcache", "persvati": "~/fn-certcache"}
MANIFEST_GLOB = "build/acl2/certify-*/manifest.json"
# An older ACL2 and hand-written fixtures use the textual certificate form.
CERT_MARKERS = (":BEGIN-PORTCULLIS-CMDS", ":END-PORTCULLIS-CMDS")


class UnreadableBook(ValueError):
    """A book, or something it includes, cannot be read from this worktree."""


@dataclass
class Certified:
    """One book as one manifest recorded it: what it was, what it produced."""

    book: str
    source: str
    after: str | None
    cert: str
    evidence: str


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
    unverified: list[str] = field(default_factory=list)
    uncached: list[str] = field(default_factory=list)
    unreadable: list[str] = field(default_factory=list)
    certified_locally: int = 0
    manifests: int = 0
    mirrored: str | None = None

    def lines(self) -> list[str]:
        out = [f"{self.action}: {self.books} books, cache {self.cache}"]
        if self.action == "publish":
            out.append(f"  {self.manifests} manifests; published {self.published}, "
                       f"already cached {self.already}, "
                       f"no manifest-verified pair {len(self.unverified)}")
        elif self.action == "install":
            out.append(f"  installed {self.installed}, kept identical local "
                       f"{self.kept}, no cached pair {len(self.uncached)}")
        else:
            out.append(f"  certified here {self.certified_locally}, "
                       f"in the cache {self.books - len(self.uncached)}, "
                       f"not in the cache {len(self.uncached)}")
        for book in self.unverified:
            out.append(f"  unverified: {book}")
        for book in self.unreadable:
            out.append(f"  unreadable closure: {book}")
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


# --------------------------------------------------------------------------
# the closure key
# --------------------------------------------------------------------------


# One parse and one hash per file per process: `install` computes a closure
# for every book, and the closures overlap heavily.  The memo key is the file
# identity, so an edit during a run is not missed.
_FACTS: dict[tuple[str, int, int], tuple[str, list[str]]] = {}


def book_facts(source: Path) -> tuple[str, list[str]]:
    """``(content hash, local include-book references)`` for one book."""
    stat = source.stat()
    key = (str(source), stat.st_mtime_ns, stat.st_size)
    remembered = _FACTS.get(key)
    if remembered is None:
        analysis = ledger.analyze_book(source, source.name)
        if analysis.read_error:
            raise UnreadableBook(f"{source.name}: {analysis.read_error}")
        remembered = (content_hash(source), list(analysis.includes))
        _FACTS[key] = remembered
    return remembered


def closure(root: Path, name: str) -> dict[str, str]:
    """The book and every book it locally includes, each with its content hash.

    ``(include-book "x")`` resolves relative to the including file's own
    directory, exactly as ACL2 resolves it.  An ``:dir``-qualified include
    selects a system book outside this worktree and is not part of the key:
    the ACL2 installation is a trusted input, named in the run manifest.
    """
    pending = [name]
    found: dict[str, str] = {}
    base = root.resolve()
    while pending:
        book = pending.pop()
        if book in found:
            continue
        source = base / f"{book}.lisp"
        if not source.is_file():
            raise UnreadableBook(f"{book}.lisp: missing")
        digest, references = book_facts(source)
        found[book] = digest
        for reference in references:
            target = (source.parent / reference).with_suffix(".lisp").resolve()
            if not target.is_relative_to(base):
                raise UnreadableBook(
                    f"{book}.lisp: include-book escapes the worktree: {reference}")
            pending.append(target.relative_to(base).with_suffix("").as_posix())
    return found


def closure_listing(books: dict[str, str]) -> list[str]:
    return sorted(f"{book}.lisp:{digest}" for book, digest in books.items())


def closure_key(root: Path, name: str) -> tuple[str, list[str]]:
    """The cache key for one book, and the listing the key hashes."""
    listing = closure_listing(closure(root, name))
    return hashlib.sha256("\n".join(listing).encode("utf-8")).hexdigest(), listing


def entry_directory(cache: Path, key: str) -> Path:
    return cache / key


def read_meta(directory: Path) -> dict:
    try:
        return json.loads((directory / "meta.json").read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return {}


# --------------------------------------------------------------------------
# manifests
# --------------------------------------------------------------------------


def load_manifests(root: Path, path: Path | None = None) -> list[dict]:
    """One named manifest, or every certification manifest under ``root``."""
    paths = [path] if path is not None else sorted(root.glob(MANIFEST_GLOB))
    loaded: list[dict] = []
    for candidate in paths:
        try:
            manifest = json.loads(candidate.read_text(encoding="utf-8"))
        except (OSError, ValueError):
            continue
        if isinstance(manifest, dict):
            manifest.setdefault("evidence", str(candidate))
            loaded.append(manifest)
    return loaded


def certified_books(manifests: list[dict]) -> dict[str, list[Certified]]:
    """What each passing manifest says it certified, by book.

    A manifest that did not pass contributes nothing: the runner's pass rule
    is one fresh success marker and one certificate per requested book, and a
    cache entry may not be built on anything weaker.
    """
    found: dict[str, list[Certified]] = {}
    for manifest in manifests:
        if manifest.get("status") != "passed":
            continue
        sources = manifest.get("source_digests_sha256") or {}
        after = manifest.get("source_digests_sha256_after") or {}
        certificates = manifest.get("certificate_digests_sha256") or {}
        exits = manifest.get("acl2_exit_codes") or {}
        evidence = str(manifest.get("evidence", "<in-memory manifest>"))
        for book in manifest.get("requested_books", []):
            source = sources.get(f"{book}.lisp")
            certificate = certificates.get(book)
            if source is None or certificate is None or exits.get(book, 0) != 0:
                continue
            found.setdefault(book, []).append(Certified(
                book=book, source=source,
                # An absent `_after` map is an older manifest; an `_after` map
                # that exists and does not name this book recorded a closure
                # error, so it must not verify anything.
                after=after.get(f"{book}.lisp", None if not after else ""),
                cert=certificate, evidence=evidence))
    return found


def verified(records: list[Certified], source: str, cert: str) -> Certified | None:
    for record in records:
        if record.source != source or record.cert != cert:
            continue
        if record.after is not None and record.after != source:
            continue
        return record
    return None


# --------------------------------------------------------------------------
# commands
# --------------------------------------------------------------------------


def publish(root: Path, cache: Path, manifests: list[dict] | None = None,
            names: list[str] | None = None) -> Report:
    """Cache every pair a certification manifest still vouches for."""
    report = Report(action="publish", cache=str(cache))
    loaded = load_manifests(root) if manifests is None else list(manifests)
    report.manifests = len(loaded)
    records = certified_books(loaded)
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
        record = verified(records.get(name, []), content_hash(source),
                          content_hash(cert))
        if record is None:
            # Either no manifest certified this book, or the source or the
            # certificate has changed since one did.  This is the poisoning
            # case: publishing here would file a stale pair under a key that
            # describes content it was never produced from.
            report.unverified.append(name)
            continue
        try:
            key, listing = closure_key(root, name)
        except UnreadableBook as error:
            report.unreadable.append(f"{name}: {error}")
            continue
        directory = entry_directory(cache, key)
        cached = directory / "book.cert"
        if cached.is_file() and content_hash(cached) == content_hash(cert):
            report.already += 1
            continue
        directory.mkdir(parents=True, exist_ok=True)
        port = source.with_suffix(".port")
        write_entry(directory, name, key, listing, cert,
                    port if port.is_file() else None, record)
        report.published += 1
    return report


def write_entry(directory: Path, name: str, key: str, listing: list[str],
                cert: Path, port: Path | None, record: Certified) -> None:
    """Write the pair and its metadata, each file renamed into place."""
    place(cert, directory / "book.cert")
    target_port = directory / "book.port"
    if port is None:
        target_port.unlink(missing_ok=True)
    else:
        place(port, target_port)
    meta = {
        "book": name,
        "closure_key": key,
        "closure": listing,
        "cert_sha256": record.cert,
        "source_sha256": record.source,
        "evidence": record.evidence,
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
    """Copy in every cached pair whose closure key matches a book here."""
    report = Report(action="install", cache=str(cache))
    for source in book_sources(root, names):
        if not source.is_file():
            continue
        report.books += 1
        name = book_name(root, source)
        try:
            key, _ = closure_key(root, name)
        except UnreadableBook as error:
            report.unreadable.append(f"{name}: {error}")
            continue
        directory = entry_directory(cache, key)
        cached = directory / "book.cert"
        if not cached.is_file():
            report.uncached.append(name)
            continue
        cert = source.with_suffix(".cert")
        if cert.is_file() and content_hash(cert) == content_hash(cached):
            # The same bytes are already here; a copy would change nothing.
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
        report.installed += 1
    return report


def status(root: Path, cache: Path) -> Report:
    report = Report(action="status", cache=str(cache))
    for source in book_sources(root):
        report.books += 1
        name = book_name(root, source)
        if valid_looking(source.with_suffix(".cert")):
            report.certified_locally += 1
        try:
            key, _ = closure_key(root, name)
        except UnreadableBook as error:
            report.unreadable.append(f"{name}: {error}")
            report.uncached.append(name)
            continue
        if not entry_directory(cache, key).joinpath("book.cert").is_file():
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
    parser.add_argument("--manifest", default=None,
                        help="the certification manifest to publish against "
                             f"(default: every {MANIFEST_GLOB} under --root)")
    parser.add_argument("--remote", default=None,
                        help="after publishing, rsync the cache to host or host:path")
    arguments = parser.parse_args(argv)
    root = Path(arguments.root).resolve()
    cache = Path(arguments.cache).expanduser() if arguments.cache else cache_directory()
    names = arguments.books or None
    if arguments.action == "publish":
        manifest = Path(arguments.manifest).resolve() if arguments.manifest else None
        report = publish(root, cache, load_manifests(root, manifest), names)
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
