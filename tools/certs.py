#!/usr/bin/env python3
"""A cache of ACL2 certificates, keyed by a book's whole include closure.

Every fn tool sets ``ACL2_BOOK_HASH_ALISTP=NIL``, so ACL2 8.7 omits write
dates from book hashes.  The source closure key admits candidates, but it
does not establish that independently certified pairs compose: ACL2 also
hashes certification data and expansion alists.  ``install-partial`` asks
ACL2 to compare candidate post-alists before selecting a mixed set.  This
tool caches those pairs.  Rules learned from measured failures follow:

**A pair is published only against a certification manifest.**  A ``.cert``
lying next to a book proves nothing: it may be left over from the source that
was there before a merge, in which case filing it under the *current* book's
key poisons the cache for everyone.  So ``publish`` reads the manifests written
by ``tools/certify_books.py`` and publishes a book only when the source beside
it still hashes to what that run certified (``source_digests_sha256`` and, when
the run recorded it, ``source_digests_sha256_after``), the certificate
beside it still hashes to what that run produced
(``certificate_digests_sha256``), and *every book in the closure the key is
computed from* still hashes to what that run recorded.  There is no other
publish path.

That last clause is the one a run verdict used to stand in for.  While
publishing happened only after a wholly successful run, the run-wide
"sources unchanged" check covered it; the moment a run's individual passing
books are published -- which is what makes a failed run useful to the next
lane -- the check has to be per book, here, where the key is computed.  A
dependency edited mid-run leaves the book's own source untouched, so nothing
weaker notices.

**The key is the closure, not the book.**  A certificate is valid only for the
book *and every book it includes*: change a dependency and ACL2 refuses with a
sub-book checksum mismatch.  Keying by the book's own content would report
"cached" for a pair that cannot be used.  The key is therefore the SHA-256 of
the sorted ``<path>:<sha256>`` listing of the book and its whole local include
closure, which also keeps two same-byte books apart, since each listing names
its own path.

**A closure may be composed from several snapshot origins.**  An ACL2
certificate's post-alist names every sub-book by the absolute path it was
certified at, which is why this module once installed a closure only from one
origin.  Measured on persvati on 2026-09-23 with ACL2 8.7 and checksum
book-hashes (``planning/evidence/certificate-cache-2026-09-23.md``), ACL2 does
not use those names to decide anything: ``include-book-alist-subsetp``
compares each entry's familiar name, certificate annotations and book-hash
and ignores the full-book-name, and include-book opens only the files beside
the including book.  A parent from origin A over children from origin B
includes without a warning, with A and B on disk, removed, or edited; a new
parent certified over a closure from three origins includes cleanly with all
three removed; editing an event in the target's own child is still refused.
``install-set`` takes one complete origin when there is a compatible one,
and otherwise composes the closure book by book from usable entries with the
same toolchain. It uses the same exact ACL2 post-alist selector as the
incremental runner, and ``proof_artifacts.py acquire`` validates the loaded
roots afterward. A live
worktree that still exists on this machine is still not drawn from.  The
measurement found nothing that requires this exclusion; it stays because no
run needs a live tree's pairs when the farm publishes every certified book
from a snapshot.  ``--require-origin`` keeps the single-origin rule for
a caller that asks for it.  ``install`` remains the legacy per-book
inspection and recovery command; native builds use ``install-set``.

**A run need not find its whole closure cached.**  ``install-partial`` is
what an incremental certification uses (``certify_books.py --incremental``,
the default for a plain-roots farm run): every book of the closure whose pair
exists at its current closure key and toolchain installs, each from its own
newest usable origin whose actual ACL2 post-alist agrees with selected
parents, and the books left over -- roots included -- are what the runner
certifies, dependencies first.  If a child has no compatible cached pair,
its cached parents are recertified too: matching source bytes alone do not
promise that the fresh child will reproduce its former book-hash.

**A snapshot is an origin that is not a worktree.**  A gate directory and a
farm run root are each made from one commit by one run, and nothing edits or
certifies into them afterwards.  So ``publish --origin-kind gate`` (or
``run``) records what the origin tree is, and ``install`` and ``install-set``
accept such an entry wherever they find it.  A snapshot later overwritten
with different books costs nothing either: ACL2 never opens the origin's
files, and the closure key already names the bytes the target holds.

**A cache entry commits as one pair.** Concurrent farm harvests can publish
the same closure and origin. A per-entry file lock covers the certificate,
portcullis and metadata replacement; every replacement uses its own temporary
file, and metadata is written last. Cache readers take the shared lock while
inspecting or copying the selected pair and retry if its metadata changed
since selection. New metadata binds both certificate and port bytes; older
entries without a port digest retain only their original presence check.
Different closure entries remain independent. The destination worktree still
requires its existing single-mutator discipline: its local `.cert`/`.port`
copies are not locked against another installer in that same worktree.

What this still does not establish: nothing here proves a book certifies.
``tools/certify_books.py`` does that, with a fresh success marker per book; the
cache only moves its result to another worktree, where ACL2 checks it again.

    python3 tools/certs.py publish [--manifest PATH] [--remote hbox]
    python3 tools/certs.py publish --origin-kind gate    # from a gate directory
    python3 tools/certs.py --acl2 PATH install-set books/served
    python3 tools/certs.py --acl2 PATH install-partial --toolchain-identity ID books/served
    python3 tools/certs.py status
"""

from __future__ import annotations

import argparse
import cert_alists
from contextlib import contextmanager
from dataclasses import dataclass, field
import datetime as dt
import fcntl
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from typing import Iterable


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
# What the origin tree is, which decides where its pairs may be installed.
# `worktree` is live: someone certifies in it, and a pair whose sub-book paths
# point there must not be followed from another tree on the same machine.
# `gate` (a gate directory) and `run` (a farm run root) are snapshots.
LIVE_ORIGIN = "worktree"
ORIGIN_KINDS = (LIVE_ORIGIN, "gate", "run")
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
    origin: str = ""
    # Every source digest the run recorded, which is the book's whole local
    # include closure and everything else the run touched.  The cache key is
    # the closure, so this is what says the key describes the source the
    # certificate was produced from.
    closure_sources: dict[str, str] = field(default_factory=dict)
    # The ACL2 executable and environment are part of a reusable proof
    # artifact's identity.  Source bytes alone do not say which prover wrote
    # the certificate.
    compatibility: dict[str, object] = field(default_factory=dict)
    certification_provenance: dict[str, object] = field(default_factory=dict)


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
    # Books whose only cached pairs were made in another worktree that still
    # exists on this machine: ACL2 would follow that worktree's sub-books.
    foreign_local: list[str] = field(default_factory=list)
    removed_foreign: int = 0
    # Entries already cached whose recorded origin kind this run corrected.
    relabelled: int = 0
    certified_locally: int = 0
    manifests: int = 0
    mirrored: str | None = None
    artifact_set: str | None = None
    artifact_origin: str | None = None
    source_identity: str | None = None
    toolchain_identity: str | None = None
    rejected_sets: list[str] = field(default_factory=list)
    # Where the installed (or, for `status`, the usable) pairs came from:
    # origin root -> number of books.  More than one is a composed set.
    origins: dict[str, int] = field(default_factory=dict)
    # install-partial: books named to be certified afresh, never installed.
    recertified: list[str] = field(default_factory=list)
    # install-partial: which origin each installed book's pair came from, the
    # roots asked for, and those whose own pair installed (nothing to certify).
    installed_from: dict[str, str] = field(default_factory=dict)
    roots: list[str] = field(default_factory=list)
    roots_installed: list[str] = field(default_factory=list)

    def origin_words(self) -> str:
        """``/a=3,/b=5``: one token, so the identity line stays parseable."""
        return ",".join(f"{origin}={count}" for origin, count
                        in sorted(self.origins.items()))

    def lines(self) -> list[str]:
        out = [f"{self.action}: {self.books} books, cache {self.cache}"]
        if self.action == "publish":
            out.append(f"  {self.manifests} manifests; published {self.published}, "
                       f"already cached {self.already}, "
                       f"relabelled {self.relabelled}, "
                       f"no manifest-verified pair {len(self.unverified)}")
        elif self.action == "install":
            out.append(f"  installed {self.installed}, kept identical local "
                       f"{self.kept}, no cached pair {len(self.uncached)}, "
                       f"foreign-local {len(self.foreign_local)}, "
                       f"removed foreign {self.removed_foreign}")
        elif self.action == "install-set":
            out.append(
                "  artifact-set {} origin {} source {} toolchain {}; "
                "installed {}, kept {}, missing {}, removed {}".format(
                    self.artifact_set or "NONE", self.artifact_origin or "NONE",
                    self.source_identity or "NONE", self.toolchain_identity or "NONE",
                    self.installed, self.kept, len(self.uncached),
                    self.removed_foreign)
                + (f"; origins {self.origin_words()}" if self.origins else ""))
        elif self.action == "install-partial":
            out.append(
                "  toolchain {}; installed {}, kept {}, missing {}, removed {}; "
                "roots installed {} of {}".format(
                    self.toolchain_identity or "NONE", self.installed, self.kept,
                    len(self.uncached), self.removed_foreign,
                    len(self.roots_installed), len(self.roots))
                + (f"; origins {self.origin_words()}" if self.origins else "")
                + (f"; recertify {' '.join(self.recertified)}"
                   if self.recertified else ""))
        else:
            out.append(f"  certified here {self.certified_locally}, "
                       f"usable from the cache "
                       f"{self.books - len(self.uncached) - len(self.foreign_local)}, "
                       f"foreign-local {len(self.foreign_local)}, "
                       f"not in the cache {len(self.uncached)}")
            if self.origins:
                out.append(f"  usable pairs come from {len(self.origins)} "
                           f"origin(s): {self.origin_words()}")
        for book in self.unverified:
            out.append(f"  unverified: {book}")
        for book in self.foreign_local:
            out.append(f"  foreign-local (made in another live worktree): {book}")
        for book in self.unreadable:
            out.append(f"  unreadable closure: {book}")
        for book in self.uncached:
            out.append(f"  uncached: {book}")
        if self.mirrored:
            out.append(f"  mirrored to {self.mirrored}")
        return out


def cache_directory() -> Path:
    return Path(os.environ.get("FN_CERT_CACHE", DEFAULT_CACHE)).expanduser()


def default_origin_kind() -> str:
    """What a publish with no explicit kind says its origin tree is.

    The farm runner is started with ``FN_CERT_ORIGIN_KIND=run``, so the pairs
    it publishes into the box's cache during a run are already labelled when
    the next lane's ``install`` reads them.
    """
    kind = os.environ.get("FN_CERT_ORIGIN_KIND", LIVE_ORIGIN)
    return kind if kind in ORIGIN_KINDS else LIVE_ORIGIN


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


def origin_token(origin: str) -> str:
    """A path-safe, deterministic name for one origin worktree."""
    return hashlib.sha256(origin.encode("utf-8")).hexdigest()[:16]


def stable_identity(value: object) -> str:
    """A short printable identity for structured cache metadata."""
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def manifest_compatibility(manifest: dict) -> dict[str, object]:
    """Inputs which decide whether ACL2 may reuse this certificate.

    Runner and reader hashes are audit provenance: changing either tool's text
    does not change the ACL2 world which wrote a certificate.  The qualified
    fingerprint already binds the launcher chain, saved core, Lisp runtime and
    proof environment.  Older launcher-only manifests intentionally return no
    compatibility identity.
    """
    compatibility = manifest.get("acl2_compatibility")
    return dict(compatibility) if isinstance(compatibility, dict) else {}


def manifest_provenance(manifest: dict) -> dict[str, object]:
    """Per-certification audit facts retained without fragmenting reuse sets."""
    return {
        "acl2_version": manifest.get("acl2_version"),
        "acl2_executable_sha256": manifest.get("acl2_executable_sha256"),
        "acl2_toolchain": manifest.get("acl2_toolchain"),
        "acl2_toolchain_identity": manifest.get("acl2_toolchain_identity"),
        "environment": manifest.get("environment"),
        "runner_sha256": manifest.get("runner_sha256"),
        "reader_sha256": manifest.get("reader_sha256"),
    }


def entry_directory(cache: Path, key: str, origin: str) -> Path:
    return cache / key / origin_token(origin)


@contextmanager
def entry_lock(directory: Path, exclusive: bool):
    """Serialize one cache entry across harvest and install processes."""
    directory.mkdir(parents=True, exist_ok=True)
    with (directory / ".entry.lock").open("a+b") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX if exclusive else fcntl.LOCK_SH)
        try:
            yield
        finally:
            fcntl.flock(lock, fcntl.LOCK_UN)


class EntryChanged(RuntimeError):
    """The selected cache generation changed before it could be copied."""


def entry_matches_meta(directory: Path, meta: dict) -> bool:
    cert = directory / "book.cert"
    if not cert.is_file():
        return False
    expected = meta.get("cert_sha256")
    if expected and content_hash(cert) != expected:
        return False
    if "has_port" in meta and (directory / "book.port").is_file() != meta["has_port"]:
        return False
    # Older entries did not record this digest. They remain readable under
    # their historical contract; new publications bind the port's bytes.
    if "port_sha256" in meta and meta["port_sha256"] is not None:
        port = directory / "book.port"
        if not port.is_file() or content_hash(port) != meta["port_sha256"]:
            return False
    return True


def install_entry(directory: Path, selected: dict, cert: Path, port: Path) -> bool:
    """Copy one selected pair under its reader lock; return whether it moved."""
    with entry_lock(directory, exclusive=False):
        if read_meta(directory) != selected or not entry_matches_meta(directory, selected):
            raise EntryChanged(str(directory))
        cached = directory / "book.cert"
        cert_same = cert.is_file() and content_hash(cert) == content_hash(cached)
        cached_port = directory / "book.port"
        port_same = (port.is_file() and cached_port.is_file()
                     and content_hash(port) == content_hash(cached_port)) or (
                         not port.is_file() and not cached_port.is_file())
        if not cert_same:
            place(cached, cert)
        if cached_port.is_file():
            if not port_same:
                place(cached_port, port)
        else:
            port.unlink(missing_ok=True)
        return not (cert_same and port_same)


def cached_entries(cache: Path, key: str) -> list[tuple[Path, dict]]:
    """Every usable entry for one closure key, with its metadata.

    An entry with no recorded ``origin_root`` predates this rule.  It is kept
    and reported, but never chosen: it cannot be classified, and installing an
    unclassifiable certificate is how a worktree ends up including another
    worktree's books.  Keeping it is what lets `install` recognise, and
    remove, a pair an earlier origin-blind install left behind.
    """
    base = cache / key
    if not base.is_dir():
        return []
    found = []
    for directory in sorted(base.iterdir()):
        if not directory.is_dir():
            continue
        with entry_lock(directory, exclusive=False):
            meta = read_meta(directory)
            if entry_matches_meta(directory, meta):
                found.append((directory, meta))
    return found


def choose_entry(entries: list[tuple[Path, dict]],
                 target: str) -> tuple[Path, dict] | None:
    """The entry this worktree may install, or None when all are foreign-local.

    An ACL2 certificate's post-alist records the *absolute* full-book-name of
    every sub-book.  A pair made in worktree X and installed in worktree Y on
    the same machine makes Y include X's books -- X's paths still resolve --
    and Y's own later certificates then conflict with them.  So: this
    worktree's own pair first; otherwise one whose origin does not exist on
    this machine, where nothing can be followed by mistake.
    """
    own = [entry for entry in entries if entry[1].get("origin_root") == target]
    if own:
        return own[0]
    # An origin not on this machine, or a snapshot (a gate directory or a
    # farm run root: one commit, one run, never certified into again).  An
    # entry with no recorded kind predates the rule and counts as a live
    # worktree.  The newest publication wins, as it does in `install-set`.
    usable = [entry for entry in entries if usable_origin(entry[1], target)]
    return newest(usable)


def newest(entries: list[tuple[Path, dict]]) -> tuple[Path, dict] | None:
    """The most recently published entry; the directory name breaks ties."""
    if not entries:
        return None
    return max(entries, key=lambda entry: (str(entry[1].get("published_at", "")),
                                           str(entry[0])))


@dataclass
class ArtifactSet:
    """One origin/toolchain's current certificates for a requested closure.

    The old installer chose one entry per book.  That can make a parent from
    origin A load a child from origin B, even when every source hash matches.
    An ArtifactSet is the indivisible choice: every selected pair has the same
    toolchain identity, and either one absolute origin or -- a *composed* set,
    ``origin_root == COMPOSED`` -- compatible entries from snapshot origins.
    """

    identity: str
    origin_root: str
    origin_kind: str
    origin_host: str
    toolchain: dict[str, object]
    entries: dict[str, tuple[Path, dict]] = field(default_factory=dict)
    required: tuple[str, ...] = ()
    source_identity: str = ""

    @property
    def missing(self) -> tuple[str, ...]:
        return tuple(name for name in self.required if name not in self.entries)

    @property
    def complete(self) -> bool:
        return not self.missing

    @property
    def origins(self) -> dict[str, int]:
        counts: dict[str, int] = {}
        for _, meta in self.entries.values():
            origin = str(meta.get("origin_root", ""))
            counts[origin] = counts.get(origin, 0) + 1
        return counts

    @property
    def composed(self) -> bool:
        return self.origin_root == COMPOSED


# The `origin_root` of a set drawn from more than one origin.
COMPOSED = "composed"


def required_closure(root: Path, roots: Iterable[str],
                     dependencies_only: bool = False) -> dict[str, str]:
    """The union of the local include closures needed by ``roots``.

    An incremental certification will author each selected root itself, so its
    reusable input set contains only books outside that selected set.  Roots
    which include one another are all excluded: the scheduler will certify the
    selected dependency before its selected parent.
    """
    selected = tuple(roots)
    required: dict[str, str] = {}
    for name in selected:
        required.update(closure(root, name))
    if dependencies_only:
        for name in selected:
            required.pop(name, None)
    return required


def source_set_identity(required: dict[str, str]) -> str:
    """Identity of the exact fn source set an artifact set must cover."""
    return stable_identity(closure_listing(required))


def usable_origin(meta: dict, target: str) -> bool:
    """Whether following this entry's absolute names is allowed here."""
    origin = meta.get("origin_root")
    if not origin:
        return False
    if origin == target or not Path(origin).exists():
        return True
    return meta.get("origin_kind", LIVE_ORIGIN) != LIVE_ORIGIN


def artifact_sets(root: Path, cache: Path, roots: Iterable[str],
                  toolchain_identity: str | None = None,
                  dependencies_only: bool = False,
                  acl2: Path | None = None,
                  pair_checker=None) -> list[ArtifactSet]:
    """Candidate whole sets for ``roots``, ordered by usable coverage.

    Grouping is by origin *and* toolchain. Closure keys bind entries to target
    source bytes; when ``acl2`` is provided, the shared selector also checks
    actual certificate post-alists. Missing toolchain metadata remains visible
    only when no toolchain was requested; deployment supplies its identity.
    """
    needed = required_closure(root, roots, dependencies_only)
    required = tuple(sorted(needed))
    source_id = source_set_identity(needed)
    target = str(root.resolve())
    grouped: dict[tuple[str, str], ArtifactSet] = {}
    # toolchain identity -> book -> every usable entry, for the composed set.
    pooled: dict[str, tuple[dict, dict[str, list[tuple[Path, dict]]]]] = {}
    for name in required:
        key, _ = closure_key(root, name)
        for directory, meta in cached_entries(cache, key):
            if not usable_origin(meta, target):
                continue
            toolchain = meta.get("toolchain") or {}
            found_identity = meta.get("toolchain_identity")
            if toolchain_identity and found_identity != toolchain_identity:
                continue
            origin = str(meta.get("origin_root", ""))
            toolchain_id = stable_identity(toolchain)
            pooled.setdefault(toolchain_id, (toolchain, {}))[1].setdefault(
                name, []).append((directory, meta))
            group_key = (origin, toolchain_id)
            if group_key not in grouped:
                identity = stable_identity({
                    "origin_root": origin,
                    "toolchain": toolchain,
                    "source_identity": source_id,
                })
                grouped[group_key] = ArtifactSet(
                    identity=identity,
                    origin_root=origin,
                    origin_kind=str(meta.get("origin_kind", LIVE_ORIGIN)),
                    origin_host=str(meta.get("origin_host", "")),
                    toolchain=toolchain,
                    required=required,
                    source_identity=source_id)
            grouped[group_key].entries.setdefault(name, (directory, meta))

    candidates = list(grouped.values())
    if acl2 is not None:
        if pair_checker is None:
            pair_checker = cert_alists.acl2_certificate_pairs
        for candidate in candidates:
            if candidate.complete:
                candidate.entries = compatible_partial_choices(
                    root, {name: [entry] for name, entry in candidate.entries.items()},
                    acl2, pair_checker)
    for toolchain_id, (toolchain, by_book) in pooled.items():
        ordered = {name: sorted(entries, key=lambda entry: (
            str(entry[1].get("published_at", "")), str(entry[0])), reverse=True)
                   for name, entries in by_book.items()}
        chosen = (compatible_partial_choices(root, ordered, acl2, pair_checker)
                  if acl2 is not None else
                  {name: newest(entries) for name, entries in by_book.items()})
        origins = {str(meta.get("origin_root", "")) for _, meta in chosen.values()}
        if len(origins) < 2 and (acl2 is None or any(
                candidate.complete and candidate.entries == chosen
                for candidate in candidates)):
            # One origin covers everything it can: that origin's own group
            # already is this set.
            continue
        composed = ArtifactSet(
            identity=stable_identity({
                "composed": sorted(
                    (name, str(meta.get("origin_root", "")),
                     str(meta.get("cert_sha256", "")))
                    for name, (_, meta) in chosen.items()),
                "toolchain": toolchain,
                "source_identity": source_id,
            }),
            origin_root=next(iter(origins)) if len(origins) == 1 else COMPOSED,
            origin_kind=COMPOSED,
            origin_host="",
            toolchain=toolchain,
            entries=chosen,
            required=required,
            source_identity=source_id)
        candidates.append(composed)

    def order(candidate: ArtifactSet) -> tuple[int, int, int, int, str]:
        # Complete first, then the set that covers most of the requested
        # closure; a single origin before a composed one of the same
        # coverage, and among single origins this tree, then a snapshot.
        own = candidate.origin_root == target
        snapshot = candidate.origin_kind != LIVE_ORIGIN
        return (int(candidate.complete), len(candidate.entries),
                int(not candidate.composed),
                int(own) * 2 + int(snapshot), candidate.identity)

    return sorted(candidates, key=order, reverse=True)


def install_artifact_set(root: Path, cache: Path, roots: Iterable[str],
                         toolchain_identity: str | None = None,
                         reject: Iterable[str] = (),
                         require_origin: str | None = None,
                         purge_on_miss: bool = False,
                         dependencies_only: bool = False,
                         acl2: Path | None = None,
                         pair_checker=None,
                         _attempt: int = 0) -> Report:
    """Install one complete set: one origin when one suffices, else composed.

    The selected set's actual ACL2 certificate alists must agree, including
    when all pairs came from one origin. ``require_origin`` constrains the
    origin but does not bypass this compatibility check.
    """
    rejected = set(reject)
    if acl2 is None:
        raise ValueError("install-set needs an ACL2 executable for exact "
                         "certificate-alist compatibility")
    report = Report(action="install-set", cache=str(cache))
    roots = tuple(roots)
    required = required_closure(root, roots, dependencies_only)
    if not required:
        report.books = 0
        report.artifact_set = stable_identity({"empty": True})
        report.artifact_origin = require_origin or str(root.resolve())
        report.source_identity = source_set_identity({})
        report.toolchain_identity = stable_identity({
            "empty": True, "toolchain_identity": toolchain_identity})
        return report
    candidates = [one for one in artifact_sets(
                      root, cache, roots, toolchain_identity,
                      dependencies_only, acl2, pair_checker)
                  if one.identity not in rejected
                  and (require_origin is None
                       or one.origin_root == require_origin)]
    chosen = next((one for one in candidates if one.complete), None)
    if chosen is None:
        report.books = len(required)
        best = candidates[0] if candidates else None
        report.uncached = list(best.missing if best else sorted(required))
        if purge_on_miss:
            # A closure recertification is safe only when it cannot consume a
            # leftover per-book mixture before it has rebuilt the dependency.
            # The certification scheduler orders this exact closure from
            # dependencies to parents, so removing every local pair makes that
            # premise explicit and leaves no ambiguous input behind.
            for name in sorted(required):
                source = root / f"{name}.lisp"
                for suffix in (".cert", ".port"):
                    artifact = source.with_suffix(suffix)
                    if artifact.is_file():
                        artifact.unlink()
                        report.removed_foreign += 1
        return report
    report.books = len(chosen.required)
    report.artifact_set = chosen.identity
    report.artifact_origin = chosen.origin_root
    report.source_identity = chosen.source_identity
    report.toolchain_identity = stable_identity(chosen.toolchain)
    report.rejected_sets = sorted(rejected)
    report.origins = chosen.origins

    # Once a set is chosen, every local pair in its closure comes from that
    # set.  A pair left from a previous attempt may certify different bytes:
    # that, not its origin, is what ACL2 refuses.
    try:
        for name in chosen.required:
            source = root / f"{name}.lisp"
            directory, meta = chosen.entries[name]
            moved = install_entry(directory, meta, source.with_suffix(".cert"),
                                  source.with_suffix(".port"))
            if moved:
                report.installed += 1
            else:
                report.kept += 1
    except EntryChanged:
        if _attempt >= 2:
            raise
        return install_artifact_set(root, cache, roots, toolchain_identity,
                                    reject, require_origin, purge_on_miss,
                                    dependencies_only, acl2, pair_checker,
                                    _attempt + 1)
    return report


def compatible_partial_choices(
    root: Path, options: dict[str, list[tuple[Path, dict]]], acl2: Path,
    pair_checker=cert_alists.acl2_certificate_pairs,
) -> dict[str, tuple[Path, dict]]:
    """Choose a partial set whose ACL2 certificate alists actually agree.

    Source SHA and toolchain identify candidates, but not their book-hash:
    ACL2 also hashes certification data and make-event expansions.  Prefer
    the newest usable pair, switch a conflicting child or parent to a matching
    cached pair when possible, and otherwise recertify the conflicting parent
    and its cached ancestors.  The last step is conservative: a new child's
    book-hash cannot be promised before it is certified.
    """
    indexed: list[tuple[str, Path, dict]] = []
    ids: dict[str, list[int]] = {}
    for name in sorted(options):
        ids[name] = []
        for directory, meta in options[name]:
            ids[name].append(len(indexed))
            indexed.append((name, directory, meta))
    dependencies = {name: set(closure(root, name)) - {name} for name in options}
    pairs = [(p, c) for parent in sorted(options)
             for child in sorted(dependencies[parent]) if child in ids
             for p in ids[parent] for c in ids[child]]
    facts = pair_checker([directory / "book.cert" for _, directory, _ in indexed],
                         pairs, acl2, root)
    if set(facts) != set(pairs):
        raise ValueError("ACL2 certificate-alist probe omitted a candidate pair")
    selected = {name: candidates[0] for name, candidates in ids.items() if candidates}

    def conflicts(chosen: dict[str, int]) -> list[tuple[str, str]]:
        bad = []
        for parent in sorted(chosen):
            for child in sorted(dependencies[parent]):
                if child not in chosen:
                    bad.append((parent, child))
                elif facts[(chosen[parent], chosen[child])] == (True, False):
                    bad.append((parent, child))
                elif facts[(chosen[parent], chosen[child])] == (False, False):
                    raise ValueError("ACL2 could not read a cached certificate alist")
        return bad

    seen: set[tuple[tuple[str, int], ...]] = set()
    steps = 0
    while True:
        bad = conflicts(selected)
        if not bad:
            break
        seen.add(tuple(sorted(selected.items())))
        parent, child = bad[0]
        best: dict[str, int] | None = None
        best_count = len(bad) + 1
        if steps < 8 * len(indexed) + 32:
            for name in (child, parent):
                for candidate in ids.get(name, []):
                    if selected.get(name) == candidate:
                        continue
                    trial = dict(selected)
                    trial[name] = candidate
                    if tuple(sorted(trial.items())) in seen:
                        continue
                    count = len(conflicts(trial))
                    if count < best_count:
                        best, best_count = trial, count
        if best is not None:
            selected = best
            steps += 1
            continue
        # No cached pair can satisfy this parent.  Its cached ancestors must
        # also be authored afresh; their stored hash for it may differ.
        selected = {name: candidate for name, candidate in selected.items()
                    if name != parent and parent not in dependencies[name]}
        steps += 1

    return {name: (indexed[candidate][1], indexed[candidate][2])
            for name, candidate in selected.items()}


def install_partial(root: Path, cache: Path, roots: Iterable[str],
                    toolchain_identity: str, acl2: Path | None = None,
                    pair_checker=None,
                    _attempt: int = 0,
                    recertify: Iterable[str] = ()) -> Report:
    """Install every book of the roots' closure that has a usable pair, and
    name the rest, which the runner then certifies in dependency order.

    ``install-set`` is all or nothing.  Here each book stands alone, but
    candidate cached pairs are selected only after ACL2 compares their actual
    post-alist entries.  If no compatible candidate exists, recertify that
    book and any cached ancestor.  Roots are part of the closure: a root
    whose pair installs is already certified at these bytes, and the runner
    does not certify it again.

    The toolchain identity is required, not optional: this is the one
    installer that mixes origins per book, and it must not mix provers.
    Every uninstalled book loses any local pair, so nothing left from an
    earlier attempt can stand in for the certificate this run will write.

    ``recertify`` names books of the closure that install nothing whatever
    the cache holds, so the runner certifies them fresh and its manifest
    records their digest; their cached dependents follow them, as for any
    uncached child, and their dependencies still install.
    """
    report = Report(action="install-partial", cache=str(cache))
    roots = tuple(roots)
    recertify = tuple(sorted(set(recertify)))
    target = str(root.resolve())
    required = required_closure(root, roots)
    outside = [name for name in recertify if name not in required]
    if outside:
        raise ValueError("a book to recertify is not in the roots' closure: "
                         + ", ".join(outside))
    report.recertified = list(recertify)
    report.books = len(required)
    report.toolchain_identity = toolchain_identity
    options: dict[str, list[tuple[Path, dict]]] = {}
    for name in sorted(required):
        key, _ = closure_key(root, name)
        usable = [(directory, meta) for directory, meta in cached_entries(cache, key)
                  if usable_origin(meta, target)
                  and meta.get("toolchain_identity") == toolchain_identity]
        own = [entry for entry in usable if entry[1].get("origin_root") == target]
        if name in recertify:
            options[name] = []
            continue
        options[name] = ((own[:1] + sorted(
            [entry for entry in usable if entry not in own],
            key=lambda entry: (str(entry[1].get("published_at", "")), str(entry[0])),
            reverse=True)) if own else sorted(
                usable, key=lambda entry: (str(entry[1].get("published_at", "")),
                                           str(entry[0])), reverse=True))
    if acl2 is None:
        raise ValueError("install-partial needs an ACL2 executable for exact "
                         "certificate-alist compatibility")
    if pair_checker is None:
        pair_checker = cert_alists.acl2_certificate_pairs
    selected = compatible_partial_choices(root, options, acl2, pair_checker)
    for name in sorted(required):
        source = root / f"{name}.lisp"
        chosen = selected.get(name)
        cert = source.with_suffix(".cert")
        port = source.with_suffix(".port")
        if chosen is None:
            report.uncached.append(name)
            for artifact in (cert, port):
                if artifact.is_file():
                    artifact.unlink()
                    report.removed_foreign += 1
            continue
        directory, meta = chosen
        try:
            moved = install_entry(directory, meta, cert, port)
        except EntryChanged:
            if _attempt >= 2:
                raise
            return install_partial(root, cache, roots, toolchain_identity, acl2,
                                   pair_checker, _attempt + 1, recertify)
        if moved:
            report.installed += 1
        else:
            report.kept += 1
        origin = str(meta.get("origin_root", ""))
        report.installed_from[name] = origin
        report.origins[origin] = report.origins.get(origin, 0) + 1
    report.roots = list(roots)
    report.roots_installed = sorted(name for name in roots
                                    if name in report.installed_from)
    return report


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


def manifest_origin(manifest: dict, default: str) -> str:
    """The worktree a run happened in, from its evidence path."""
    evidence = str(manifest.get("evidence", ""))
    marker = "/build/acl2/"
    return evidence.split(marker)[0] if marker in evidence else default


def certified_books(manifests: list[dict],
                    default_origin: str = "") -> dict[str, list[Certified]]:
    """What each passing manifest says it certified, by book.

    A manifest that did not pass contributes nothing: the runner's pass rule
    is one fresh success marker and one certificate per requested book, and a
    cache entry may not be built on anything weaker.
    """
    found: dict[str, list[Certified]] = {}
    for manifest in manifests:
        # The unit of trust is one BOOK, not one run: a gate that fails on a
        # single root still certified every other root, and each of those has
        # its own fresh nonce-tagged success marker.  A book counts only when
        # its expected marker was observed in this run and ACL2 exited 0.
        requested = manifest.get("requested_books", [])
        expected = manifest.get("expected_success_markers") or []
        observed = set(manifest.get("observed_success_markers") or [])
        if len(expected) != len(requested):
            # An older or malformed manifest; fall back to the run verdict.
            if manifest.get("status") != "passed":
                continue
            expected = [None] * len(requested)
        sources = manifest.get("source_digests_sha256") or {}
        after = manifest.get("source_digests_sha256_after") or {}
        certificates = manifest.get("certificate_digests_sha256") or {}
        exits = manifest.get("acl2_exit_codes") or {}
        evidence = str(manifest.get("evidence", "<in-memory manifest>"))
        origin = manifest_origin(manifest, default_origin)
        # The runner's own per-book verdict, when the manifest carries one.  An
        # exit code of 0 is not a verdict: the driver's `(quit)` exits 0 after a
        # failed `certify-book` too, so this is the field that separates them.
        results = manifest.get("book_results") or {}
        for book, token in zip(requested, expected):
            if token is not None and token not in observed:
                continue
            if results and results.get(book) != "passed":
                continue
            source = sources.get(f"{book}.lisp")
            certificate = certificates.get(book)
            if source is None or certificate is None or exits.get(book, 0) != 0:
                continue
            found.setdefault(book, []).append(Certified(
                book=book, source=source, closure_sources=sources,
                # An absent `_after` map is an older manifest; an `_after` map
                # that exists and does not name this book recorded a closure
                # error, so it must not verify anything.
                after=after.get(f"{book}.lisp", None if not after else ""),
                cert=certificate, evidence=evidence, origin=origin,
                compatibility=manifest_compatibility(manifest),
                certification_provenance=manifest_provenance(manifest)))
    return found


def closure_drift(listing: list[str], recorded: dict[str, str]) -> list[str]:
    """The books in this key's closure the manifest cannot vouch for.

    `listing` is what the key hashes, one ``<path>.lisp:<sha256>`` per book.
    A book the manifest never recorded is drift too: an unrecorded digest is
    not a matching one, and the runner records the whole closure of every
    requested book, so this only refuses a manifest that really is partial.
    """
    moved = []
    for entry in listing:
        path, _, found = entry.rpartition(":")
        if recorded.get(path) != found:
            moved.append(path)
    return sorted(moved)


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
            names: list[str] | None = None, origin: str | None = None,
            origin_host: str | None = None,
            origin_kind: str | None = None) -> Report:
    """Cache every pair a certification manifest still vouches for.

    ``origin`` is the absolute worktree path the certificates were *produced*
    in, which is what their sub-book paths point at.  It defaults to each
    manifest's own evidence path, then to ``root``; a farm run passes the path
    the run used on the box.  ``origin_kind`` says what that tree is
    (``worktree``, ``gate`` or ``run``), which is what decides whether the
    entry may be installed on a machine where the tree still exists.
    """
    kind = origin_kind or default_origin_kind()
    report = Report(action="publish", cache=str(cache))
    loaded = load_manifests(root) if manifests is None else list(manifests)
    report.manifests = len(loaded)
    records = certified_books(loaded, origin or str(root.resolve()))
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
        if not record.compatibility:
            report.unverified.append(
                f"{name}: no qualified ACL2 launcher/core/runtime fingerprint")
            continue
        try:
            key, listing = closure_key(root, name)
        except UnreadableBook as error:
            report.unreadable.append(f"{name}: {error}")
            continue
        moved = closure_drift(listing, record.closure_sources)
        if moved:
            # The key would describe source this certificate was not produced
            # from: a real pair filed under the wrong closure.
            report.unverified.append(
                f"{name}: closure changed since certification: "
                + ", ".join(moved[:6]))
            continue
        where = origin or record.origin or str(root.resolve())
        directory = entry_directory(cache, key, where)
        port = source.with_suffix(".port")
        port = port if port.is_file() else None
        outcome = write_entry(directory, name, key, listing, cert, port, record,
                              where, origin_host, kind)
        if outcome == "already":
            report.already += 1
        elif outcome == "relabelled":
            report.already += 1
            report.relabelled += 1
        else:
            report.published += 1
    return report


def write_entry(directory: Path, name: str, key: str, listing: list[str],
                cert: Path, port: Path | None, record: Certified,
                origin: str, origin_host: str | None = None,
                origin_kind: str = LIVE_ORIGIN) -> str:
    """Commit a matched pair and provenance under one cache-entry lock."""
    meta = {
        "book": name,
        "closure_key": key,
        "closure": listing,
        "cert_sha256": record.cert,
        "port_sha256": content_hash(port) if port is not None else None,
        "source_sha256": record.source,
        "evidence": record.evidence,
        # The worktree the pair was produced in.  A certificate's post-alist
        # names its sub-books by absolute path, so this is what decides where
        # the pair may be installed; `origin_host` is provenance only.
        "origin_root": origin,
        # `worktree` keeps the pair on its own machine; `gate` and `run` are
        # snapshots, installable wherever the cache reaches.
        "origin_kind": origin_kind,
        "origin_host": origin_host or os.uname().nodename,
        "toolchain": record.compatibility,
        "toolchain_identity": stable_identity(record.compatibility),
        "certification_provenance": record.certification_provenance,
        "has_port": port is not None,
        "published_at": dt.datetime.now(dt.timezone.utc).isoformat(),
        "published_from": str(cert.parent),
        "host": os.uname().nodename,
    }
    with entry_lock(directory, exclusive=True):
        cached = directory / "book.cert"
        target_port = directory / "book.port"
        same_cert = cached.is_file() and content_hash(cached) == record.cert
        same_port = ((port is None and not target_port.is_file()) or
                     (port is not None and target_port.is_file() and
                      content_hash(target_port) == content_hash(port)))
        old_meta = read_meta(directory)
        same_provenance = (
            old_meta.get("book") == name
            and old_meta.get("closure") == listing
            and old_meta.get("origin_kind", LIVE_ORIGIN) == origin_kind
            and old_meta.get("origin_host") == meta["origin_host"]
            and old_meta.get("toolchain") == record.compatibility
            and old_meta.get("certification_provenance")
            == record.certification_provenance
            and old_meta.get("evidence") == record.evidence
            and old_meta.get("cert_sha256") == record.cert
            and old_meta.get("port_sha256") == meta["port_sha256"]
            and old_meta.get("has_port") == meta["has_port"]
            and old_meta.get("source_sha256") == record.source
            and old_meta.get("closure_key") == key
            and old_meta.get("origin_root") == origin
            and old_meta.get("published_from") == str(cert.parent))
        if same_cert and same_port and same_provenance:
            return "already"
        if not same_cert:
            place(cert, cached)
        if port is None:
            target_port.unlink(missing_ok=True)
        elif not same_port:
            place(port, target_port)
        if not entry_matches_meta(directory, meta):
            raise EntryChanged(f"source pair changed while publishing {directory}")
        write_text_atomic(directory / "meta.json",
                          json.dumps(meta, indent=2, sort_keys=True) + "\n")
        return "relabelled" if same_cert else "published"


def place(source: Path, target: Path) -> None:
    target.parent.mkdir(parents=True, exist_ok=True)
    descriptor, name = tempfile.mkstemp(prefix=target.name + ".", suffix=".tmp",
                                       dir=target.parent)
    temporary = Path(name)
    try:
        with os.fdopen(descriptor, "wb") as output, source.open("rb") as input_file:
            shutil.copyfileobj(input_file, output)
        shutil.copystat(source, temporary)
        temporary.replace(target)
    finally:
        temporary.unlink(missing_ok=True)


def write_text_atomic(target: Path, value: str) -> None:
    target.parent.mkdir(parents=True, exist_ok=True)
    descriptor, name = tempfile.mkstemp(prefix=target.name + ".", suffix=".tmp",
                                       dir=target.parent)
    temporary = Path(name)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8") as output:
            output.write(value)
        temporary.replace(target)
    finally:
        temporary.unlink(missing_ok=True)


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
        entries = cached_entries(cache, key)
        cert = source.with_suffix(".cert")
        chosen = choose_entry(entries, str(root.resolve()))
        if chosen is None:
            if entries:
                # Every cached pair belongs to a worktree that still exists
                # here.  Installing one would make this worktree include that
                # worktree's books.  Remove a local pair that is provably one
                # of them, so a tree poisoned by an earlier install recovers.
                report.foreign_local.append(name)
                if cert.is_file() and any(
                        content_hash(cert) == content_hash(entry / "book.cert")
                        for entry, _ in entries):
                    cert.unlink()
                    source.with_suffix(".port").unlink(missing_ok=True)
                    report.removed_foreign += 1
            else:
                report.uncached.append(name)
            continue
        port = source.with_suffix(".port")
        for attempt in range(3):
            directory, meta = chosen
            try:
                moved = install_entry(directory, meta, cert, port)
                break
            except EntryChanged:
                if attempt == 2:
                    raise
                chosen = choose_entry(cached_entries(cache, key), str(root.resolve()))
                if chosen is None:
                    raise EntryChanged(f"cache entry vanished for {name}")
        if moved:
            report.installed += 1
        else:
            report.kept += 1
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
        entries = cached_entries(cache, key)
        chosen = choose_entry(entries, str(root.resolve())) if entries else None
        if not entries:
            report.uncached.append(name)
        elif chosen is None:
            report.foreign_local.append(name)
        else:
            origin = str(chosen[1].get("origin_root", ""))
            report.origins[origin] = report.origins.get(origin, 0) + 1
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
    parser.add_argument("action", choices=("publish", "install", "install-set",
                                           "install-partial", "status"))
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
    parser.add_argument("--origin-kind", default=None, choices=ORIGIN_KINDS,
                        help="what the tree these pairs were produced in is: a "
                             "live worktree (default, or FN_CERT_ORIGIN_KIND), a "
                             "gate directory or a farm run root.  A snapshot's "
                             "pairs install on the machine that holds it too")
    parser.add_argument("--toolchain-identity", default=None,
                        help="for install-set, require this qualified ACL2 "
                             "launcher/core/runtime compatibility identity")
    parser.add_argument("--acl2", default=os.environ.get("FN_ACL2"),
                        help="ACL2 executable used to compare certificate "
                             "alists for install-set and install-partial")
    parser.add_argument("--require-origin", default=None,
                        help="for install-set, require one complete set from this "
                             "exact certificate origin instead of composing one")
    parser.add_argument("--purge-on-miss", action="store_true",
                        help="for install-set, remove every local .cert/.port in "
                             "the requested closure when no complete set exists")
    parser.add_argument("--dependencies-only", action="store_true",
                        help="for install-set, install the requested roots' local "
                             "dependencies but not roots that this run will author")
    parser.add_argument("--recertify", action="append", default=[], metavar="BOOK",
                        help="for install-partial, install nothing for this book of "
                             "the closure (repeatable), so the runner certifies it")
    arguments = parser.parse_args(argv)
    root = Path(arguments.root).resolve()
    cache = Path(arguments.cache).expanduser() if arguments.cache else cache_directory()
    names = arguments.books or None
    if arguments.action == "publish":
        manifest = Path(arguments.manifest).resolve() if arguments.manifest else None
        report = publish(root, cache, load_manifests(root, manifest), names,
                         origin_kind=arguments.origin_kind)
        if arguments.remote:
            mirror(cache, arguments.remote)
            report.mirrored = remote_target(arguments.remote)
    elif arguments.action == "install":
        report = install(root, cache, names)
    elif arguments.action == "install-set":
        if not names:
            parser.error("install-set needs one or more root books")
        if not arguments.acl2:
            parser.error("install-set needs --acl2 to check certificate alists")
        report = install_artifact_set(
            root, cache, names, toolchain_identity=arguments.toolchain_identity,
            require_origin=arguments.require_origin,
            purge_on_miss=arguments.purge_on_miss,
            dependencies_only=arguments.dependencies_only,
            acl2=Path(arguments.acl2).resolve())
    elif arguments.action == "install-partial":
        if not names:
            parser.error("install-partial needs one or more root books")
        if not arguments.toolchain_identity:
            parser.error("install-partial needs --toolchain-identity: it takes "
                         "each book's pair on its own and must not mix provers")
        if not arguments.acl2:
            parser.error("install-partial needs --acl2 to check certificate alists")
        try:
            report = install_partial(root, cache, names, arguments.toolchain_identity,
                                     Path(arguments.acl2).resolve(),
                                     recertify=[name[:-len(".lisp")] if name.endswith(".lisp")
                                                else name for name in arguments.recertify])
        except ValueError as error:
            parser.error(str(error))
    else:
        report = status(root, cache)
    for line in report.lines():
        print(line)
    return 1 if arguments.action == "install-set" and report.artifact_set is None else 0


if __name__ == "__main__":
    raise SystemExit(main())
