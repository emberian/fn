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
    every `defstobj`/`defabsstobj` and `attach-stobj` form, at any depth."""
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
            analysis = ledger.analyze_book(source, source.name)
            if analysis.read_error:
                raise ValueError(f"{name}.lisp: {analysis.read_error}")

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


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("action", choices=("plan", "show"))
    parser.add_argument("books", nargs="*")
    parser.add_argument("--images", type=int, default=4)
    parser.add_argument("--write", action="store_true")
    arguments = parser.parse_args(argv)
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
