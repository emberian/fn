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

**And a certification dependency closure is installed as one set.**  An
ACL2 certificate's post-alist names every sub-book by *absolute* path, so a
parent from worktree X and a child from worktree Y conflict even when both
source closures are byte-identical.  Each entry records the ``origin_root``
and toolchain it was produced with; ``install-set`` chooses one complete
origin/toolchain group for the requested roots or refuses before ACL2 starts.
An incremental certification also requires that origin to be the absolute
tree it will extend.  ``install`` remains the legacy per-book inspection and
recovery command; certification and native builds must use ``install-set``.

**Unless that origin is not a worktree.**  A gate directory and a farm run
root are snapshots: each is made from one commit by one run, and nothing edits
or certifies into them afterwards.  On a box where every gate directory is
still on disk, the rule above would refuse the box's own cache to every lane,
which is what made a lane re-certify a whole dependency closure.  So
``publish --origin-kind gate`` (or ``run``) records what the origin tree is,
and ``install`` accepts such an entry wherever it finds it.  A snapshot later
overwritten with different books costs a loud refusal from ACL2 at include
time -- the sub-book content no longer matches -- never a silent wrong result.

What this still does not establish: nothing here proves a book certifies.
``tools/certify_books.py`` does that, with a fresh success marker per book; the
cache only moves its result to another worktree, where ACL2 checks it again.

    python3 tools/certs.py publish [--manifest PATH] [--remote hbox]
    python3 tools/certs.py publish --origin-kind gate    # from a gate directory
    python3 tools/certs.py install-set books/served # coherent dependency set
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
                    self.removed_foreign))
        else:
            out.append(f"  certified here {self.certified_locally}, "
                       f"usable from the cache "
                       f"{self.books - len(self.uncached) - len(self.foreign_local)}, "
                       f"foreign-local {len(self.foreign_local)}, "
                       f"not in the cache {len(self.uncached)}")
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
        if not (directory / "book.cert").is_file():
            continue
        found.append((directory, read_meta(directory)))
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
    relocatable = [entry for entry in entries
                   if entry[1].get("origin_root")
                   and not Path(entry[1]["origin_root"]).exists()]
    if relocatable:
        return relocatable[0]
    # A gate directory or a farm run root: a tree built from one commit by one
    # run, never certified into again, so nothing here can be followed into a
    # tree that is about to change under it.  An entry with no recorded kind
    # predates this rule and counts as a live worktree.
    snapshot = [entry for entry in entries
                if entry[1].get("origin_root")
                and entry[1].get("origin_kind", LIVE_ORIGIN) != LIVE_ORIGIN]
    return snapshot[0] if snapshot else None


@dataclass
class ArtifactSet:
    """One origin/toolchain's current certificates for a requested closure.

    The old installer chose one entry per book.  That can make a parent from
    origin A load a child from origin B, even when every source hash matches.
    An ArtifactSet is the indivisible choice: every selected pair has the same
    absolute origin and toolchain identity.
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
                  dependencies_only: bool = False) -> list[ArtifactSet]:
    """Candidate whole sets for ``roots``, ordered by usable coverage.

    Grouping is by origin *and* toolchain.  Closure keys already bind every
    entry to the target source bytes.  Missing toolchain metadata is kept
    visible as a candidate only when no toolchain was requested; deployment
    passes the hash of the ACL2 executable it is about to run.
    """
    needed = required_closure(root, roots, dependencies_only)
    required = tuple(sorted(needed))
    source_id = source_set_identity(needed)
    target = str(root.resolve())
    grouped: dict[tuple[str, str], ArtifactSet] = {}
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

    def order(candidate: ArtifactSet) -> tuple[int, int, int, str]:
        # Complete first, then the set that covers most of the requested
        # closure.  Ties prefer this tree, then an immutable snapshot.
        own = candidate.origin_root == target
        snapshot = candidate.origin_kind != LIVE_ORIGIN
        return (int(candidate.complete), len(candidate.entries),
                int(own) * 2 + int(snapshot), candidate.identity)

    return sorted(grouped.values(), key=order, reverse=True)


def install_artifact_set(root: Path, cache: Path, roots: Iterable[str],
                         toolchain_identity: str | None = None,
                         reject: Iterable[str] = (),
                         require_origin: str | None = None,
                         purge_on_miss: bool = False,
                         dependencies_only: bool = False) -> Report:
    """Install one complete origin/toolchain set, never a per-book mixture."""
    rejected = set(reject)
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
                      root, cache, roots, toolchain_identity, dependencies_only)
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

    # Once a set is chosen, every local pair in its closure comes from that
    # set.  Leaving a pair from a previous attempt is exactly how the
    # mixed-absolute-origin failure is reproduced.
    for name in chosen.required:
        source = root / f"{name}.lisp"
        directory, _ = chosen.entries[name]
        cached = directory / "book.cert"
        cert = source.with_suffix(".cert")
        if cert.is_file() and content_hash(cert) == content_hash(cached):
            report.kept += 1
        else:
            place(cached, cert)
            report.installed += 1
        port = source.with_suffix(".port")
        if (directory / "book.port").is_file():
            place(directory / "book.port", port)
        else:
            port.unlink(missing_ok=True)
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
        cached = directory / "book.cert"
        port = source.with_suffix(".port")
        port = port if port.is_file() else None
        if cached.is_file() and content_hash(cached) == content_hash(cert):
            report.already += 1
            old_meta = read_meta(directory)
            if (old_meta.get("origin_kind", LIVE_ORIGIN) != kind
                    or old_meta.get("toolchain") != record.compatibility
                    or old_meta.get("certification_provenance")
                    != record.certification_provenance):
                # The same bytes, published again by a run that knows what its
                # origin tree and toolchain are: these fields are metadata
                # about the artifact, not its certificate bytes, so refresh
                # them in place.
                write_entry(directory, name, key, listing, cert, port, record,
                            where, origin_host, kind)
                report.relabelled += 1
            continue
        directory.mkdir(parents=True, exist_ok=True)
        write_entry(directory, name, key, listing, cert, port, record, where,
                    origin_host, kind)
        report.published += 1
    return report


def write_entry(directory: Path, name: str, key: str, listing: list[str],
                cert: Path, port: Path | None, record: Certified,
                origin: str, origin_host: str | None = None,
                origin_kind: str = LIVE_ORIGIN) -> None:
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
        directory, meta = chosen
        cached = directory / "book.cert"
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
        entries = cached_entries(cache, key)
        if not entries:
            report.uncached.append(name)
        elif choose_entry(entries, str(root.resolve())) is None:
            report.foreign_local.append(name)
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
                                           "status"))
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
    parser.add_argument("--require-origin", default=None,
                        help="for install-set, require this exact certificate "
                             "origin (needed when this run will extend the set)")
    parser.add_argument("--purge-on-miss", action="store_true",
                        help="for install-set, remove every local .cert/.port in "
                             "the requested closure when no complete set exists")
    parser.add_argument("--dependencies-only", action="store_true",
                        help="for install-set, install the requested roots' local "
                             "dependencies but not roots that this run will author")
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
        report = install_artifact_set(
            root, cache, names, toolchain_identity=arguments.toolchain_identity,
            require_origin=arguments.require_origin,
            purge_on_miss=arguments.purge_on_miss,
            dependencies_only=arguments.dependencies_only)
    else:
        report = status(root, cache)
    for line in report.lines():
        print(line)
    return 1 if arguments.action == "install-set" and report.artifact_set is None else 0


if __name__ == "__main__":
    raise SystemExit(main())
