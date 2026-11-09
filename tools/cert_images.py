#!/usr/bin/env python3
"""Certification images: certify a book from a saved ACL2 world that already
holds the part of its closure every chain above a checkpoint shares.

Per book, certification time on this tree is mostly include-book of the
closure, not proving (planning/evidence/image-umbrella-2026-09-28.md's
architect numbers: 0.78 ms per definition, 0.12 ms per theorem loaded).  A
`save-exec` image that has included a checkpoint book X turns every
certification above X into a redundant include of X's closure.

    python3 tools/cert_images.py plan [--images K]   # propose checkpoints
    python3 tools/cert_images.py plan --write         # ... into tools/cert-images.json
    python3 tools/cert_images.py show BOOK            # which image a book uses

What ACL2 does with an image (measured, planning/evidence/cert-images-2026-09-28.md):

* The image's `include-book` commands become the certificate's portcullis.
  certify-book records a portcullis include-book with a RELATIVE name only
  when the directory it was issued from is the book's own directory
  (other-events.lisp make-include-books-absolute-1); otherwise the name is
  absolute and the certificate stops being relocatable.  So an image is
  built per book directory (`books/`, `tests/acl2/`), issuing its includes
  from that directory, in the tree that certifies.
* A plain-world include of such a book executes the portcullis first: the
  image's roots, which are in the book's own non-local closure (the rule
  `image_for` keeps), so an includer loads the same books.  A `local` image
  include would be skipped instead, but certify-book's Step 3 then retracts
  the whole certification world and replays it, which costs the include
  back.  Non-local it is.
* The portcullis is part of ACL2's book-hash, so a certificate made from an
  image is a valid certificate with a different hash from a plain-world one:
  dependents record whichever they were certified against, and the cache's
  post-alist selector (`certs.install_partial`) composes compatible sets.
  The image definition therefore lives in this committed file and changes
  rarely: every book's certificate follows from its sources and the image
  set.
* An attachable stobj's attachment must be made before the stobj is
  defined: `(attach-stobj fn-arena fn-arena-extent)` precedes the include of
  books/payload-arena.  An image that already holds the stobj's defining
  book makes a later `attach-stobj` fail ("The name FN-ARENA is in use, so
  it cannot serve here as an attachable stobj"; batch BB, the image-world
  umbrellas).  So an image is never used for a book whose certification
  world (local includes too, and the book itself) makes, outside the image,
  an attachment of a stobj the image defines (`applicable`).
* SBCL's save-lisp-and-die coalesces numbers, so after restart a bignum
  defconst's value is no longer `eq` to the value ACL2 recorded for it, and
  reloading that book's compiled file (which ACL2 does for a redundant
  include whose certificate names another origin) fails with "Illegal
  attempt to redeclare the constant" and loads the rest of that include
  uncompiled.  `FIXUP` re-links the recorded value to the live one when they
  are EQUAL, before certify-book; nothing logical changes.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(Path(__file__).resolve().parent))
import ledger  # noqa: E402

CONFIG = ROOT / "tools" / "cert-images.json"
# The directories whose books certify from images; each gets its own build of
# every image (see the module docstring: a relative portcullis needs the
# includes issued from the book's own directory).
DIRECTORIES = ("books", "tests/acl2")
# The architect's include-cost model (R^2 0.83 over 18 books).
MS_PER_DEFINITION = 0.78
MS_PER_THEOREM = 0.12

# Raw Lisp run after the image restarts and before certify-book: the defconst
# discriminator values save-exec split from the live constant values.
FIXUP = (
    ':q\n'
    '(let ((n 0)) (do-all-symbols (s) (let ((d (get s (quote acl2::redundant-raw-lisp-discriminator)))) '
    '(when (and (consp d) (eq (car d) (quote acl2::defconst)) (consp (cdr d)) (boundp s) '
    '(not (eq (cddr d) (symbol-value s))) (equal (cddr d) (symbol-value s))) '
    '(incf n) (setf (cddr d) (symbol-value s))))) '
    '(format t "~%FN_CERT_IMAGE_RELINKED ~a~%" n))\n'
    '(lp)\n')


def stobj_events(text: str) -> tuple[frozenset[str], frozenset[str]]:
    """(stobjs a book defines, stobjs it attaches), from the ledger's reader:
    every `defstobj`/`defabsstobj`/`def-generic` and `attach-stobj` form,
    at any depth."""
    defined: set[str] = set()
    attached: set[str] = set()
    try:
        forms = ledger.read_forms(text)
    except ledger.ReadError:
        return frozenset(), frozenset()
    pending = list(forms)
    while pending:
        form = pending.pop()
        if not isinstance(form, list) or not form:
            continue
        # The ledger mirrors def-generic's proof obligations, not the
        # attachable defabsstobj it also creates. Record that definition
        # before following the expansion, or an image can preload the
        # generic and make a later attach-stobj impossible.
        if (form[0] == "def-generic" and len(form) >= 2
                and isinstance(form[1], ledger.Sym)):
            defined.add(str(form[1]))
        expansion = ledger.generated_expansion(form)
        if expansion is not None:
            pending.extend(expansion)
            continue
        head = form[0]
        if isinstance(head, ledger.Sym) and len(form) >= 2 and isinstance(form[1], ledger.Sym):
            if head in ("defstobj", "defabsstobj"):
                defined.add(str(form[1]))
            elif head == "attach-stobj":
                attached.add(str(form[1]))
        pending.extend(item for item in form if isinstance(item, list))
    return frozenset(defined), frozenset(attached)


class UnreadableSource(ValueError):
    """A book the include graph cannot read: absent from the tree, or not
    readable Lisp.  `certs.book_entries` retells it as its own per-book
    unreadable finding, so one parked book over a deleted include reports
    and never aborts the install (FILL-CERTS-INSTALL-DELETED-BOOK)."""


class Graph:
    """The non-local include graph of the tree, from the ledger's reader."""

    def __init__(self, root: Path = ROOT) -> None:
        self.root = root
        self.edges: dict[str, list[str]] = {}
        self.nonlocal_edges: dict[str, list[str]] = {}
        self.cost_ms: dict[str, float] = {}
        # Per book: the stobjs it defines and the stobjs it attaches.
        self.stobjs: dict[str, frozenset[str]] = {}
        self.attaches: dict[str, frozenset[str]] = {}
        self._nonlocal_closure: dict[str, frozenset[str]] = {}
        self._closure: dict[str, frozenset[str]] = {}

    def load(self, book: str) -> None:
        pending = [book]
        while pending:
            name = pending.pop()
            if name in self.edges:
                continue
            source = self.root / f"{name}.lisp"
            if not source.is_file():
                raise UnreadableSource(f"{name}.lisp: missing")
            analysis = ledger.analyze_book(source, source.name)
            if analysis.read_error:
                raise UnreadableSource(f"{name}.lisp: {analysis.read_error}")

            def resolve(reference: str) -> str:
                target = (source.parent / reference).with_suffix(".lisp").resolve()
                return target.relative_to(self.root.resolve()).with_suffix("").as_posix()

            self.edges[name] = [resolve(r) for r in analysis.includes]
            self.nonlocal_edges[name] = [resolve(r) for _, r in analysis.nonlocal_includes]
            theorems = sum(1 for t in analysis.theorems if not getattr(t, "local", False))
            functions = sum(1 for f in analysis.functions if not getattr(f, "local", False))
            self.cost_ms[name] = MS_PER_DEFINITION * functions + MS_PER_THEOREM * theorems
            defined, attached = stobj_events(source.read_text(encoding="latin-1"))
            self.stobjs[name], self.attaches[name] = defined, attached
            pending.extend(self.edges[name])

    def nonlocal_closure(self, book: str) -> frozenset[str]:
        """What `(include-book BOOK)` loads: BOOK and its non-local includes, transitively."""
        found = self._nonlocal_closure.get(book)
        if found is None:
            self.load(book)
            seen: set[str] = set()
            pending = [book]
            while pending:
                name = pending.pop()
                if name in seen:
                    continue
                seen.add(name)
                self.load(name)
                pending.extend(self.nonlocal_edges[name])
            found = frozenset(seen)
            self._nonlocal_closure[book] = found
        return found

    def closure(self, book: str) -> frozenset[str]:
        """BOOK and everything it includes, local includes too: its certification world."""
        found = self._closure.get(book)
        if found is None:
            seen: set[str] = set()
            pending = [book]
            while pending:
                name = pending.pop()
                if name in seen:
                    continue
                seen.add(name)
                self.load(name)
                pending.extend(self.edges[name])
            found = frozenset(seen)
            self._closure[book] = found
        return found

    def attached(self, book: str) -> frozenset[str]:
        """Every stobj an attach-stobj in BOOK's certification world names."""
        return frozenset().union(*(self.attaches[name] for name in self.closure(book)))

    def defines(self, books: frozenset[str]) -> frozenset[str]:
        for name in books:
            self.load(name)
        return frozenset().union(*(self.stobjs[name] for name in books))

    def include_cost(self, books: frozenset[str]) -> float:
        return sum(self.cost_ms.get(book, 0.0) for book in books)


def load_config(root: Path = ROOT) -> list[dict]:
    """ROOT's committed image set, a list of {"name", "roots"}; [] when absent.

    An image whose roots are not books of ROOT is dropped (a fixture tree)."""
    path = root / CONFIG.relative_to(ROOT)
    if not path.is_file():
        return []
    value = json.loads(path.read_text(encoding="utf-8"))
    images = value.get("images") if isinstance(value, dict) else None
    return [image for image in images or []
            if isinstance(image, dict) and image.get("name") and image.get("roots")
            and all((root / f"{book}.lisp").is_file() for book in image["roots"])]


def book_directory(book: str) -> str | None:
    parent = book.rpartition("/")[0]
    return parent if parent in DIRECTORIES else None


PLAIN = "plain"


def world_id(image: dict, directory: str) -> str:
    """What a certificate made from IMAGE for a book in DIRECTORY was made in.

    Part of the certificate cache key (`certs.closure_key`): the image's
    include-books are the certificate's portcullis, which a plain-world
    includer replays, so an image-made pair is never filed with plain ones."""
    return f"{image['name']}@{directory}:{','.join(image['roots'])}"


def applicable(book: str, images: list[dict], graph: Graph) -> list[dict]:
    """The images BOOK may certify from, costliest first.

    An image qualifies when every root is in BOOK's non-local closure (so a
    plain-world include of BOOK loads exactly the books its portcullis
    names), it does not hold BOOK, and it defines no stobj that BOOK's
    certification world attaches (an attachment must precede the stobj)."""
    if book_directory(book) is None:
        return []
    reach = graph.nonlocal_closure(book)
    world = graph.closure(book)
    found = []
    for image in images:
        roots = image["roots"]
        if book in roots or not all(root in reach for root in roots):
            continue
        closure = image_closure(image, graph)
        if book in closure:
            continue
        # The attachments this certification would make on top of the image
        # (by books the image does not already hold) must not name a stobj
        # the image has defined.  An image that holds the attaching book made
        # the attachment itself, first (composed-owner-3 at ae64a5c42 found the
        # same defect and allows exactly that case).
        attached = frozenset().union(*(graph.attaches[name] for name in world - closure))
        if attached & graph.defines(closure):
            continue
        found.append((-graph.include_cost(closure), image["name"], image))
    return [image for _, _, image in sorted(found, key=lambda item: item[:2])]


def image_for(book: str, images: list[dict], graph: Graph) -> dict | None:
    """The costliest image BOOK may certify from (`applicable`), or None."""
    found = applicable(book, images, graph)
    return found[0] if found else None


def worlds(root: Path, book: str) -> list[str]:
    """Every world a certificate of BOOK may validly have been made in under
    ROOT's image set: plain, and each applicable image.  `certs` looks a book
    up under each."""
    graph = _GRAPHS.get(str(root))
    if graph is None:
        graph = _GRAPHS[str(root)] = Graph(root)
        _CONFIGS[str(root)] = load_config(root)
    directory = book_directory(book)
    return [PLAIN] + [world_id(image, directory)
                      for image in applicable(book, _CONFIGS[str(root)], graph)]


_GRAPHS: dict[str, Graph] = {}
_CONFIGS: dict[str, list[dict]] = {}


def image_closure(image: dict, graph: Graph) -> frozenset[str]:
    return frozenset().union(*(graph.nonlocal_closure(r) for r in image["roots"]))


def build_script(image: dict, directory: str, core: Path) -> str:
    """The ACL2 session that builds IMAGE for books in DIRECTORY and saves CORE.

    The includes are issued from DIRECTORY so each becomes a relative
    portcullis command of the books certified from it.
    """
    depth = directory.count("/") + 1
    up = "../" * depth
    lines = [f'(set-cbd "{directory}/")']
    for root in image["roots"]:
        lines.append(f'(include-book "{up}{root}")' if not root.startswith(directory + "/")
                     else f'(include-book "{root[len(directory) + 1:]}")')
    lines.append(f'(value-triple (cw "~%FN_CERT_IMAGE_BUILT {image["name"]}~%"))')
    lines.append(":q")
    lines.append(f'(save-exec "{core.with_suffix("")}-saved" "fn certification image '
                 f'{image["name"]} for {directory}")')
    return "\n".join(lines) + "\n"


def launcher_for(acl2: Path, core: Path) -> str:
    """The toolchain's launcher with its --core replaced: same SBCL flags
    (save-exec's own launcher would reset the TLS limit and heap size)."""
    text = acl2.read_text(encoding="utf-8")
    new, count = re.subn(r'--core "[^"]+"', f'--core "{core}"', text)
    if count != 1:
        raise ValueError(f"{acl2}: no single --core argument to replace")
    return new


class Runner:
    """The images one certification run builds and hands out.

    An image is built, per book directory, once every book of its closure is
    certified (installed before the run, or passed in it) and some book still
    to start would use it; at most `builders` builds run at once.  A book
    certifies from the costliest image that `image_for`'s rule allows and
    that is already built -- it never waits for one -- so the image a
    certificate names is recorded per book (`record`).  Its portcullis says
    the same thing in the certificate itself.
    """

    def __init__(self, root: Path, run_dir: Path, acl2: Path, books: list[str],
                 run, slot, images: list[dict] | None = None,
                 builders: int = 2, timeout: int = 900) -> None:
        import concurrent.futures
        import threading
        self.root, self.acl2, self.run, self.slot = root, acl2, run, slot
        self.images = load_config(root) if images is None else images
        self.directory = run_dir / "images"
        self.graph = Graph(root)
        self.pending = set(books)          # not yet started
        self.unfinished = set(books)       # not yet passed (failed stays here)
        self.failed: set[str] = set()
        self.lock = threading.Lock()
        self.pool = concurrent.futures.ThreadPoolExecutor(max_workers=builders)
        self.timeout = timeout
        self.builds: dict[tuple[str, str], dict] = {}
        self.futures: dict[tuple[str, str], object] = {}
        self.used: dict[str, str] = {}
        by_name = {image["name"]: image for image in self.images}
        self.by_name = by_name
        self.closures = {name: image_closure(image, self.graph) for name, image in by_name.items()}
        self.cost = {name: self.graph.include_cost(c) for name, c in self.closures.items()}
        # book -> applicable image names, costliest first
        self.applicable: dict[str, list[str]] = {}
        for book in books:
            self.applicable[book] = [image["name"] for image
                                     in applicable(book, self.images, self.graph)]
        self.kick()

    def _wanted(self) -> list[tuple[str, str]]:
        """(image, directory) builds some pending book would use, ready to build."""
        wanted = []
        for book in self.pending:
            directory = book_directory(book)
            for name in self.applicable.get(book, []):
                key = (name, directory)
                if key in self.futures or key in wanted:
                    continue
                closure = self.closures[name]
                if closure & self.failed or closure & self.unfinished:
                    continue
                wanted.append(key)
        return wanted

    def kick(self) -> None:
        with self.lock:
            for key in self._wanted():
                self.futures[key] = self.pool.submit(self._build, *key)

    def _build(self, name: str, directory: str) -> None:
        import time
        image = self.by_name[name]
        flat = directory.replace("/", "--")
        self.directory.mkdir(parents=True, exist_ok=True)
        core = self.directory / f"{flat}--{name}.core"
        saved = Path(f"{core.with_suffix('')}-saved.core")
        record: dict = {"image": name, "directory": directory, "roots": image["roots"]}
        started = time.monotonic()
        try:
            with self.slot(f"cert image {name} {directory}"):
                result = self.run(self.acl2, build_script(image, directory, core),
                                  self.timeout)
            output = result.stdout.decode("utf-8", errors="replace")
            (self.directory / f"{flat}--{name}.build.log").write_text(output, encoding="utf-8")
            if f"FN_CERT_IMAGE_BUILT {name}" not in output or not saved.is_file():
                raise RuntimeError("the build did not include its roots and save")
            saved.replace(core)
            Path(f"{core.with_suffix('')}-saved").unlink(missing_ok=True)
            launcher = core.with_suffix("")
            launcher.write_text(launcher_for(self.acl2, core), encoding="utf-8")
            launcher.chmod(0o755)
            record.update({"ok": True, "launcher": str(launcher),
                           "core_bytes": core.stat().st_size})
        except Exception as error:  # the run goes on without this image
            record.update({"ok": False, "error": f"{type(error).__name__}: {error}"})
        record["seconds"] = round(time.monotonic() - started, 3)
        with self.lock:
            self.builds[(name, directory)] = record

    def choose(self, book: str) -> tuple[Path, int, str] | None:
        """(launcher, portcullis command count, label) for BOOK, or None: plain."""
        with self.lock:
            self.pending.discard(book)
            directory = book_directory(book)
            for name in self.applicable.get(book, []):
                built = self.builds.get((name, directory))
                if built and built.get("ok"):
                    label = world_id(self.by_name[name], directory)
                    self.used[book] = label
                    return Path(built["launcher"]), len(self.by_name[name]["roots"]), label
            self.used[book] = PLAIN
            return None

    def finished(self, book: str, passed: bool) -> None:
        with self.lock:
            if passed:
                self.unfinished.discard(book)
            else:
                self.failed.add(book)
        self.kick()

    def close(self, keep: bool = False) -> dict:
        self.pool.shutdown(wait=True)
        if not keep:
            for core in self.directory.glob("*.core"):
                core.unlink(missing_ok=True)
        return {
            "definition": definition_identity(self.images),
            "images": [{"name": i["name"], "roots": i["roots"]} for i in self.images],
            "builds": sorted(self.builds.values(), key=lambda r: (r["image"], r["directory"])),
            "book_images": dict(sorted(self.used.items())),
        }


def plan(graph: Graph, books: list[str], count: int) -> list[dict]:
    """Greedy checkpoints: each step adds the single-root image that most
    reduces the summed include cost over BOOKS, given those already chosen."""
    for book in books:
        graph.load(book)
    candidates = sorted(b for b in graph.edges if book_directory(b) == "books")
    reach = {book: graph.nonlocal_closure(book) for book in books}
    cost = {c: graph.include_cost(graph.nonlocal_closure(c)) for c in candidates}
    users = {c: [b for b in books if c in reach[b] and b != c
                 and book_directory(b) is not None] for c in candidates}
    current = {book: 0.0 for book in books}
    chosen: list[dict] = []
    for _ in range(count):
        best, gain = None, 0.0
        for c in candidates:
            g = sum(max(0.0, cost[c] - current[b]) for b in users[c])
            if g > gain:
                best, gain = c, g
        if best is None:
            break
        for b in users[best]:
            current[b] = max(current[b], cost[best])
        chosen.append({"name": best.rpartition("/")[2], "roots": [best],
                       "closure_books": len(graph.nonlocal_closure(best)),
                       "include_ms": round(cost[best]),
                       "users": len(users[best]), "gain_ms": round(gain)})
    return chosen


def definition_identity(images: list[dict]) -> str:
    """What a certificate made from these images depends on besides sources."""
    wanted = [{"name": i["name"], "roots": i["roots"]} for i in images]
    return hashlib.sha256(json.dumps(wanted, sort_keys=True).encode()).hexdigest()[:16]


# ---------------------------------------------------------------------------
# fn2: saved world images for cert.pl (tools/certify.sh, tools/box_certify_bb2.sh)
#
# fn2 certifies with cert.pl, which runs the ACL2 a book's `<book>.image` file
# names.  An image here is the toolchain's ACL2 after
# `(include-book "<root>" :dir :fn)` of one certified root, saved by
# `save-exec` into a shared store on the box (`~/fn2-images/<name>-<key>/`)
# and used by every tree whose closure has the same key.
#
# Honesty, in four parts:
#
# * The key.  ACL2 treats an include of a book already in the world's
#   include-book-alist as redundant by name alone (other-events.lisp
#   include-book-fn1): it never looks at the file again.  So an image must
#   only serve a tree whose files for the root's non-local closure are the
#   ones the image loaded.  `world_key` hashes, for every book of that
#   closure, the source and the certificate bytes (a book-hash, which every
#   includer records, is a function of both: the source's events and the
#   certificate's portcullis commands, expansion alist and cert data), plus
#   the toolchain's content identity (`acl2_toolchain.fingerprint`: launcher,
#   saved core, runtime), the system books directory and the project map.
#   Equal key, equal world.  A tree whose key differs is not served (`select`
#   writes no `.image` for it, and removes any it wrote before): it certifies
#   plain, or from a smaller image whose key does match.
# * The build.  `build` includes the root from certified books only
#   (`:uncertified-okp nil :defaxioms-okp nil :skip-proofs-okp nil`, no
#   ttags), refuses a world whose include-book-alist is not exactly the
#   closure the key hashed or that has seen skip-proofs, a ttag or
#   redefinition, saves, and checks that the saved image starts and already
#   holds the root.  It records the command, the key inputs and ACL2's own list
#   of included books in `meta.json`, then writes `DONE`.  Images are rebuilt by
#   that command, never edited.
# * The certificate.  The image's include-book is a command of the
#   certification world, so certify-book records it as a portcullis command
#   (in sysfile form, `:dir :fn`, so it relocates) with its pre-alist entry,
#   and records every included book with its book-hash in the post-alist, as
#   a plain certification does.  A plain-world includer executes that
#   portcullis first; `applicable` only lets a book use an image whose root is
#   in its own non-local closure, so the includer loads the same books it
#   would have loaded anyway.  The certificate differs from a plain one in its
#   portcullis (hence in its own book-hash), not in what it includes.
# * Freshness.  The roots certify first (`world-roots`), so a root's
#   certificate is current before `select` keys it; cert.pl then never
#   rewrites a root under a book that is using its image.
#
# What is trusted: the toolchain identity of `acl2_toolchain` (content hashes)
# and that /tank/fn/acl2-8.7/books is the immutable system books tree the
# launcher was built with (its path is in the key, its content is not).

WORLD_BUILDER = "fn2-world-image-v1"
WORLD_KEEP = 2                        # generations kept per image name
WORLD_MIN_FREE_BYTES = 15 * 1024 ** 3  # refuse to build below this much free disk
WORLD_STORE = Path.home() / "fn2-images"
# Where cert.pl may find books: select clears every `.image` under these.
WORLD_DIRECTORIES = ("books", "tests", "sim", "meta")
_FN_NAME = re.compile(r'\(:FN \. "([^"]+)\.lisp"\)')


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


_TOOLCHAIN: dict[str, str] = {}


def toolchain_identity(acl2: Path) -> str:
    """`acl2_toolchain`'s content identity of ACL2 (launcher, core, runtime)."""
    found = _TOOLCHAIN.get(str(acl2))
    if found is None:
        import acl2_toolchain
        fingerprint = acl2_toolchain.fingerprint(acl2)
        if not fingerprint.qualified:
            raise ValueError(f"{acl2}: unqualified ACL2 launcher: {fingerprint.reason}")
        found = _TOOLCHAIN[str(acl2)] = fingerprint.identity
    return found


def world_key(tree: Path, root: str, acl2: Path, system_books: str,
              graph: Graph | None = None) -> tuple[str, dict]:
    """(key, inputs) of ROOT's world in TREE; ValueError when a book of its
    non-local closure has no certificate (nothing to key yet)."""
    graph = graph or Graph(tree)
    books = sorted(graph.nonlocal_closure(root))
    files = []
    for book in books:
        source, cert = tree / f"{book}.lisp", tree / f"{book}.cert"
        if not cert.is_file():
            raise ValueError(f"{book}.cert: absent")
        files.append([book, _sha256(source), _sha256(cert)])
    inputs = {
        "builder": WORLD_BUILDER,
        "root": root,
        "toolchain": toolchain_identity(acl2),
        "system_books": system_books,
        "projects": (tree / "acl2-projects").read_text(encoding="utf-8"),
        "books": files,
    }
    digest = hashlib.sha256(json.dumps(inputs, sort_keys=True).encode()).hexdigest()
    return digest[:20], inputs


def world_build_script(root: str, saved: Path, label: str) -> str:
    """The ACL2 session that includes ROOT from certificates and saves SAVED."""
    return "\n".join([
        "(set-ld-error-action '(:exit 1) state)",
        f'(include-book "{root}" :dir :fn :uncertified-okp nil :defaxioms-okp nil '
        ':skip-proofs-okp nil)',
        ":q",
        "(let ((w (acl2::w acl2::*the-live-state*))) "
        "(dolist (e (acl2::global-val 'acl2::include-book-alist w)) "
        '(format t "~&FN_WORLD_IMAGE_BOOK ~s~%" (car e))) '
        '(format t "~&FN_WORLD_IMAGE_SEEN ~s ~s ~s~%" '
        "(acl2::global-val 'acl2::skip-proofs-seen w) "
        "(acl2::global-val 'acl2::ttags-seen w) "
        "(acl2::global-val 'acl2::redef-seen w)))",
        f'(acl2::save-exec "{saved}" "{label}")',
        ""])


def world_check_script(root: str) -> str:
    """Run in a built image: the root is already there (the include is redundant)."""
    return "\n".join([
        ":q",
        "(format t \"~&FN_WORLD_IMAGE_HOLDS ~s~%\" (not (null (assoc-equal "
        f"(quote (:fn . \"{root}.lisp\")) "
        "(acl2::global-val 'acl2::include-book-alist (acl2::w acl2::*the-live-state*))))))",
        ""])


def _proof_env(tree: Path, system_books: str) -> dict:
    import os
    env = dict(os.environ)
    env.update({"ACL2_PROJECTS": str(tree / "acl2-projects"),
                "ACL2_SYSTEM_BOOKS": system_books,
                "ACL2_BOOK_HASH_ALISTP": "NIL",
                "ACL2_CUSTOMIZATION": "NONE"})
    return env


def world_images(store: Path, name: str) -> list[tuple[float, Path, dict]]:
    """(built_at, directory, meta) of every image this builder made for NAME."""
    found = []
    for directory in store.glob(f"{name}-*"):
        meta_path = directory / "meta.json"
        try:
            meta = json.loads(meta_path.read_text(encoding="utf-8"))
        except (OSError, ValueError):
            continue
        if meta.get("builder") == WORLD_BUILDER and meta.get("name") == name:
            found.append((float(meta.get("built_at", 0)), directory, meta))
    return sorted(found, key=lambda item: item[0])


def world_prune(store: Path, name: str, keep: int = WORLD_KEEP) -> list[Path]:
    """Remove all but the KEEP newest finished images of NAME (only ours)."""
    import shutil
    finished = [item for item in world_images(store, name) if (item[1] / "DONE").is_file()]
    removed = []
    for _, directory, _ in finished[:-keep] if keep else finished:
        shutil.rmtree(directory)
        removed.append(directory)
    return removed


def world_build(tree: Path, image: dict, store: Path, acl2: Path, system_books: str,
                timeout: int, source_rev: str = "") -> int:
    """Build IMAGE from TREE's certificates into STORE (foreground)."""
    import os
    import shutil
    import subprocess
    import time
    name, root = image["name"], image["roots"][0]
    if len(image["roots"]) != 1:
        raise ValueError(f"{name}: a world image has exactly one root")
    key, inputs = world_key(tree, root, acl2, system_books)
    target = store / f"{name}-{key}"
    if (target / "DONE").is_file():
        print(f"world-image: {name}-{key} already built")
        return 0
    store.mkdir(parents=True, exist_ok=True)
    free = shutil.disk_usage(store).free
    if free < WORLD_MIN_FREE_BYTES:
        print(f"world-image: refused: {free / 1024 ** 3:.1f} GB free on {store}, "
              f"below {WORLD_MIN_FREE_BYTES / 1024 ** 3:.0f} GB")
        return 3
    lock = store / f".{name}-{key}.lock"
    try:
        lock.mkdir()
    except FileExistsError:
        print(f"world-image: {lock} is held: another build of this key is running")
        return 75
    try:
        if target.exists():          # an unfinished build of ours: start over
            shutil.rmtree(target)
        target.mkdir()
        saved = target / "saved"
        label = f"fn2 world image {name} {key}"
        script = world_build_script(root, saved, label)
        (target / "build.lsp").write_text(script, encoding="utf-8")
        started = time.monotonic()
        with (target / "build.log").open("wb") as log:
            result = subprocess.run([str(acl2)], input=script.encode(), stdout=log,
                                    stderr=subprocess.STDOUT, cwd=tree, timeout=timeout,
                                    env=_proof_env(tree, system_books))
        seconds = round(time.monotonic() - started, 1)
        output = (target / "build.log").read_text(encoding="utf-8", errors="replace")
        # A marker may follow the loop's prompt on its line ("* FN_...").
        marked = [line[line.index("FN_WORLD_IMAGE_"):] for line in output.splitlines()
                  if "FN_WORLD_IMAGE_" in line]
        loaded = sorted(set(_FN_NAME.findall(
            "\n".join(line for line in marked if line.startswith("FN_WORLD_IMAGE_BOOK")))))
        seen = [line.strip() for line in marked if line.startswith("FN_WORLD_IMAGE_SEEN")]
        keyed = [book for book, _, _ in inputs["books"]]
        problems = []
        if not (target / "saved.core").is_file():
            problems.append(f"no saved core (ACL2 exit {result.returncode})")
        if loaded != keyed:
            problems.append(f"ACL2 included {len(loaded)} fn books, the key hashed "
                            f"{len(keyed)}: only ACL2 {sorted(set(loaded) - set(keyed))[:5]}, "
                            f"only key {sorted(set(keyed) - set(loaded))[:5]}")
        if seen != ["FN_WORLD_IMAGE_SEEN NIL NIL NIL"]:
            problems.append(f"skip-proofs/ttags/redef seen: {seen}")
        if problems:
            print(f"world-image: {name}-{key} refused: " + "; ".join(problems))
            return 1
        (target / "saved").unlink(missing_ok=True)   # save-exec's own launcher
        launcher = target / "acl2"
        launcher.write_text(launcher_for(acl2, target / "saved.core"), encoding="utf-8")
        launcher.chmod(0o755)
        check = subprocess.run([str(launcher)], input=world_check_script(root).encode(),
                               capture_output=True, cwd=tree, timeout=600,
                               env=_proof_env(tree, system_books))
        if b"FN_WORLD_IMAGE_HOLDS T" not in check.stdout:
            (target / "check.log").write_bytes(check.stdout + check.stderr)
            print(f"world-image: {name}-{key} refused: the saved image does not hold {root}")
            return 1
        meta = {
            "builder": WORLD_BUILDER, "name": name, "root": root, "key": key,
            "built_at": time.time(), "build_seconds": seconds,
            "core_bytes": (target / "saved.core").stat().st_size,
            "tree": str(tree), "source_rev": source_rev,
            "command": f"python3 tools/cert_images.py world-build {name} "
                       f"--acl2 {acl2} --store {store}",
            "launcher": str(launcher), "included": loaded, "inputs": inputs,
        }
        (target / "meta.json").write_text(json.dumps(meta, indent=1) + "\n", encoding="utf-8")
        (target / "DONE").write_text(f"{key}\n", encoding="utf-8")
        print(f"world-image: built {name}-{key}: {len(loaded)} books, {seconds} s, "
              f"{meta['core_bytes'] / 1024 ** 3:.2f} GB")
        for removed in world_prune(store, name):
            print(f"world-image: removed old generation {removed}")
        return 0
    finally:
        lock.rmdir()


def world_targets(tree: Path, arguments: list[str]) -> list[str]:
    """The books named by certify.sh-style arguments (`books/x.lisp`, `fn2/...`)."""
    books = []
    for argument in arguments:
        argument = argument.removeprefix("fn2/")
        for suffix in (".lisp", ".cert"):
            if argument.endswith(suffix) and (tree / argument).with_suffix(".lisp").is_file():
                books.append(argument[:-len(suffix)])
    return books


def world_applicable(book: str, images: list[dict], graph: Graph) -> list[dict]:
    """`applicable` without fn1's per-directory rule: a `:dir :fn` portcullis
    relocates, so one image serves every directory."""
    reach, world = graph.nonlocal_closure(book), graph.closure(book)
    found = []
    for image in images:
        closure = image_closure(image, graph)
        if book in closure or not all(root in reach for root in image["roots"]):
            continue
        attached = frozenset().union(*(graph.attaches[name] for name in world - closure))
        if attached & graph.defines(closure):
            continue
        found.append((-len(closure), image["name"], image))
    return [image for _, _, image in sorted(found, key=lambda item: item[:2])]


def world_roots(tree: Path, arguments: list[str], store: Path) -> list[str]:
    """Image roots in the closure of the named books that the store has some
    image for, smallest first: certify these before `select`."""
    graph = Graph(tree)
    closure = frozenset().union(*(graph.closure(b) for b in world_targets(tree, arguments)))
    roots = [(len(image_closure(image, graph)), image["roots"][0])
             for image in load_config(tree)
             if image["roots"][0] in closure and world_images(store, image["name"])]
    return [f"{root}.lisp" for _, root in sorted(roots)]


def _write_image_file(tree: Path, book: str, launcher: str) -> None:
    """Name LAUNCHER in BOOK's `.image` without making the certificate stale.

    cert.pl makes `<book>.image` a prerequisite of `<book>.cert`
    (Certlib.pm find_deps), so a fresh mtime would recertify a current
    certificate, and a recertified root changes its bytes and so the key of
    every image above it.  Which valid world a certificate is made in is not a
    reason to remake it: an unchanged file is left alone, a new one gets its
    source's mtime (already a prerequisite)."""
    import os
    path = tree / f"{book}.image"
    text = launcher + "\n"
    if path.is_file() and path.read_text(encoding="utf-8") == text:
        return
    path.write_text(text, encoding="utf-8")
    source = (tree / f"{book}.lisp").stat()
    os.utime(path, ns=(source.st_atime_ns, source.st_mtime_ns))


def world_select(tree: Path, arguments: list[str], store: Path, acl2: Path,
                 system_books: str, enabled: bool = True) -> dict[str, str]:
    """Write `<book>.image` for each book the run may certify that has a
    current image; remove every other `.image` in TREE.  Returns book -> image."""
    existing = {path for directory in WORLD_DIRECTORIES
                for path in (tree / directory).rglob("*.image")}
    if not enabled:
        for stale in existing:
            stale.unlink()
        print("world-image: off (plain world for every book)")
        return {}
    graph = Graph(tree)
    images = load_config(tree)
    available = []
    for image in images:
        name, root = image["name"], image["roots"][0]
        try:
            key, _ = world_key(tree, root, acl2, system_books, graph)
        except (ValueError, UnreadableSource) as error:
            print(f"world-image: {name}: not keyed ({error})")
            continue
        built = store / f"{name}-{key}"
        if (built / "DONE").is_file():
            available.append(image)
            image = dict(image, launcher=str(built / "acl2"))
            available[-1] = image
            print(f"world-image: {name}-{key} current")
        else:
            others = [d.name for _, d, _ in world_images(store, name)]
            print(f"world-image: {name}: no image for this tree's key {key}"
                  + (f" (store has {', '.join(others)}: not served)" if others else ""))
    chosen: dict[str, str] = {}
    books = frozenset().union(*(graph.closure(b) for b in world_targets(tree, arguments)))
    for book in sorted(books):
        found = world_applicable(book, available, graph)
        if found:
            _write_image_file(tree, book, found[0]["launcher"])
            existing.discard(tree / f"{book}.image")
            chosen[book] = found[0]["name"]
    for stale in existing:
        stale.unlink()
    counts: dict[str, int] = {}
    for name in chosen.values():
        counts[name] = counts.get(name, 0) + 1
    print("world-image: " + (", ".join(f"{n} for {c} books" for n, c in sorted(counts.items()))
                             or "no book of this run has a current image"))
    return chosen


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("action", choices=("plan", "show", "world-key", "world-build",
                                           "world-roots", "world-select"))
    parser.add_argument("books", nargs="*",
                        help="world-build: image names; world-roots/world-select: "
                             "certify.sh arguments (non-book arguments are ignored)")
    parser.add_argument("--images", type=int, default=4)
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--tree", type=Path, default=ROOT)
    parser.add_argument("--store", type=Path, default=WORLD_STORE)
    parser.add_argument("--acl2", type=Path, help="the toolchain launcher (default $ACL2)")
    parser.add_argument("--system-books", help="default $ACL2_SYSTEM_BOOKS")
    parser.add_argument("--off", action="store_true", help="world-select: remove every .image")
    parser.add_argument("--timeout", type=int, default=1800)
    parser.add_argument("--rev", default="", help="world-build: the source revision, recorded")
    arguments, extra = parser.parse_known_args(argv)
    if arguments.action.startswith("world-"):
        import os
        tree = arguments.tree.resolve()
        books = arguments.books + extra
        if arguments.action == "world-roots":
            print("\n".join(world_roots(tree, books, arguments.store)))
            return 0
        acl2 = (arguments.acl2 or Path(os.environ["ACL2"])).resolve()
        system_books = arguments.system_books or os.environ["ACL2_SYSTEM_BOOKS"]
        if arguments.action == "world-select":
            world_select(tree, books, arguments.store, acl2, system_books,
                         enabled=not arguments.off)
            return 0
        by_name = {image["name"]: image for image in load_config(tree)}
        status = 0
        for name in books or list(by_name):
            if arguments.action == "world-key":
                key, _ = world_key(tree, by_name[name]["roots"][0], acl2, system_books)
                print(f"{name}-{key}")
            else:
                status = max(status, world_build(tree, by_name[name], arguments.store, acl2,
                                                 system_books, arguments.timeout,
                                                 arguments.rev))
        return status
    if extra:
        parser.error(f"unrecognized arguments: {' '.join(extra)}")
    sys.path.insert(0, str(ROOT / "tools"))
    import certify_books  # noqa: E402
    graph = Graph(ROOT)
    if arguments.action == "plan":
        roots = arguments.books or certify_books.default_books()
        books = sorted(certify_books.local_closure(roots))
        chosen = plan(graph, books, arguments.images)
        for image in chosen:
            print(f"{image['roots'][0]}: closure {image['closure_books']} books, "
                  f"include ~{image['include_ms']} ms, used by {image['users']}, "
                  f"adds {image['gain_ms'] / 1000:.1f} s of summed include")
        if arguments.write:
            CONFIG.write_text(json.dumps(
                {"comment": "tools/cert_images.py plan --write; see that module",
                 "images": [{"name": i["name"], "roots": i["roots"]} for i in chosen]},
                indent=2) + "\n", encoding="utf-8")
        return 0
    images = load_config()
    for book in arguments.books:
        image = image_for(book, images, graph)
        print(f"{book}: {image['name'] if image else 'plain'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
