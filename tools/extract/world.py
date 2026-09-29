#!/usr/bin/env python3
"""tools/extract/world.py -- the image's world, and the extractor's, is one book.

Reads each native build script (host/native/build.lisp and its variants)
and writes, from its forms before its first trust tag:
  books/image-world.lisp          (and -dtn, -store-test for the variants)
                                  the UMBRELLA: every book the script
                                  includes, in its order, then the books its
                                  host files include themselves (their lds
                                  followed).  A certified root; the script
                                  includes it first and then turns the
                                  compiler off, so every later include-book
                                  (its own and its host files') is redundant
                                  and loads nothing;
  tools/extract/world.lisp        the extractor's world from build.lisp: the
                                  same umbrella first, then the same list
                                  (redundant, and what the extraction
                                  manifest names; proof_repl starts from it);
  tools/extract/world-host.lisp   every `ld' of a host :program file, in
                                  order, then the closure check.

WHY ONE BOOK (lane image-umbrella; planning/evidence/arena-store-8-tls.md).
A top-level include-book loads the compiled file of every book in its
closure even when the include is redundant (ACL2 8.7 include-book-fn calls
include-book-raw-top before the redundancy check), and each load of a
constrained or non-executable function's raw stub declares a fresh special
(throw-or-attach's gensym), whose thread-local-storage index SBCL never
frees.  With ~600 top-level includes the developer image used 60% of the
65536-slot TLS and b1 (history pages under store-files) exhausted it.  Under
one umbrella each compiled file loads once.  `--check' fails if any file is
not what the build scripts say today; tools/tls_check.py checks that each
script includes its umbrella first.
"""
import os
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "tools" / "extract"

# Each native build script and the umbrella book it includes first.
UMBRELLAS = {
    "host/native/build.lisp": "books/image-world",
    "host/native/build-dtn.lisp": "books/image-world-dtn",
    "host/native/build-store-test.lisp": "books/image-world-store-test",
}
EXTRACT_BUILD = "host/native/build.lisp"

# The forms each script puts right after its umbrella's include, and the
# check before its trust tag.  tools/tls_check.py requires both verbatim.
PROLOGUE = ("(assign fn-image-world-books (len (global-val 'include-book-alist (w state))))",
            "(assign fn-image-world-compiler (@ compiler-enabled))",
            "(set-compiler-enabled nil state)")
EPILOGUE = ("(assert-event (equal (len (global-val 'include-book-alist (w state)))",
            "                     (@ fn-image-world-books))",
            "              :msg \"an include-book after the image's umbrella added a book\")",
            "(set-compiler-enabled (@ fn-image-world-compiler) state)",
            "(value-triple (if (equal (len (global-val 'include-book-alist (w state)))",
            "                         (@ fn-image-world-books))",
            "                  (cw \"FN_IMAGE_WORLD_CLOSED ~x0~%\" (@ fn-image-world-books))",
            "                (cw \"FN_IMAGE_WORLD_OPEN~%\")))")

# world-host.lisp's own prologue: when world.lisp ran first (world_image.sh,
# the extraction) its PROLOGUE already assigned these and nothing changes;
# ld'd alone into a session over the umbrella (coverage.py dump, proof_repl
# start cov books/image-world) it assigns them itself, so the closure check
# at its end has its reference (coverage-crawler's ask, 2026-09-29).
HOST_PROLOGUE = (
    "(if (boundp-global 'fn-image-world-books state)",
    "    (value :fn-image-world-prologue-already-run)",
    "  (pprogn (f-put-global 'fn-image-world-books",
    "                        (len (global-val 'include-book-alist (w state))) state)",
    "          (f-put-global 'fn-image-world-compiler (@ compiler-enabled) state)",
    "          (set-compiler-enabled nil state)",
    "          (value :fn-image-world-prologue)))")


def prefix_text(build):
    text = (ROOT / build).read_text()
    match = re.search(r"^\(defttag :", text, re.M)
    return text[:match.start()] if match else text


def forms(build):
    """(books, hosts) of BUILD's prefix: its include-books but its umbrella,
    and its host `ld's, in order."""
    text = prefix_text(build)
    umbrella = UMBRELLAS.get(build)
    books = [b for b in re.findall(r'^\(include-book "([^"]+)"\)', text, re.M) if b != umbrella]
    hosts = re.findall(r'^\(ld "([^"]+)" :ld-error-action :error\)', text, re.M)
    return books, hosts


def host_books(hosts):
    """The include-books the host files make themselves (their lds followed)."""
    out, seen = [], set()

    def visit(rel):
        path = (ROOT / rel).resolve()
        if path in seen or not path.exists():
            return
        seen.add(path)
        text = path.read_text()
        for m in re.finditer(r'^\s*\((include-book|ld) "([^"]+)"', text, re.M):
            target = (path.parent / m.group(2)).resolve()
            if m.group(1) == "include-book":
                out.append(str(target.relative_to(ROOT)))
            else:
                visit(str(target.relative_to(ROOT)))

    for h in hosts:
        visit(h)
    return out


def world_books(build, extra_hosts=()):
    books, hosts = forms(build)
    hosts = hosts + [h for h in extra_hosts if h not in hosts]
    for b in host_books(hosts):
        if b not in books:
            books.append(b)
    return books, hosts


# The extracted program's own host files, which the image does not load (yet):
# the read-only store open as ACL2 :program code over the host primitives.
# They include no book (world-host.lisp's closure check fails if one does).
EXTRA_HOSTS = ["host/store-open-host.lisp",
               # the writable store verbs (lane extract-writable)
               "host/store-write-host.lisp",
               # the extraction roots' declarations (definterface; lane generators)
               "host/interfaces-extract.lisp"]


def relative_to_books(book):
    return Path(os.path.relpath(ROOT / book, ROOT / "books")).as_posix()


def render_umbrella(build, umbrella):
    books, _ = world_books(build)
    head = ("; GENERATED by tools/extract/world.py from\n"
            ";   %s\n"
            "; the image's certified books, in its order, then the books its host files\n"
            "; include.  Do not edit; regenerate.  The script includes this book first\n"
            "; and then turns the compiler off, so each compiled file of the image loads\n"
            "; once: a top-level include-book reloads its whole closure, and every load\n"
            "; of a constrained stub takes a TLS index SBCL never frees (world.py).\n"
            % build)
    return head + '(in-package "ACL2")\n' + "".join(
        '(include-book "%s")\n' % relative_to_books(b) for b in books)


def render():
    out = {}
    for build, umbrella in UMBRELLAS.items():
        out[ROOT / (umbrella + ".lisp")] = render_umbrella(build, umbrella)
    books, hosts = world_books(EXTRACT_BUILD, EXTRA_HOSTS)
    head = ("; GENERATED by tools/extract/world.py from host/native/build.lisp: the image's\n"
            "; certified books, in its order.  Do not edit; regenerate.\n")
    umbrella = UMBRELLAS[EXTRACT_BUILD]
    world = (head + '(in-package "ACL2")\n'
             + '(include-book "../../%s")\n' % umbrella
             + "".join(line + "\n" for line in PROLOGUE)
             + "".join('(include-book "../../%s")\n' % b for b in books))
    host = (head.replace("certified books", "host :program files (ld)") + '(in-package "ACL2")\n'
            + "".join(line + "\n" for line in HOST_PROLOGUE)
            + "".join('(ld "../../%s" :ld-error-action :error)\n' % h for h in hosts)
            + "".join(line + "\n" for line in EPILOGUE))
    out[OUT / "world.lisp"] = world
    out[OUT / "world-host.lisp"] = host
    return out


def lds_followed(root, rel):
    """REL and every file its `ld's reach, in first-visit order."""
    out, seen = [], set()

    def visit(path):
        path = path.resolve()
        if path in seen or not path.is_file():
            return
        seen.add(path)
        out.append(path)
        for m in re.finditer(r'^\s*\(ld "([^"]+)"', path.read_text(), re.M):
            visit(path.parent / m.group(1))

    visit(root / rel)
    return out


def included_books(root, rel):
    """The books a world file includes, with their include closures (names)."""
    sys.path.insert(0, str(ROOT / "tools"))  # this tool's own certs.py; ROOT may differ
    import certs  # noqa: E402
    path = root / rel
    names = []
    for m in re.finditer(r'^\(include-book "([^"]+)"\)', path.read_text(), re.M):
        target = (path.parent / m.group(1)).resolve()
        name = target.relative_to(root.resolve()).as_posix()
        for one in certs.closure(root, name):
            if one not in names:
                names.append(one)
    return names


def digest(root, acl2=None):
    """The world's cache key (world_image.sh): SHA-256 over the two world
    files, every host file they load (lds followed), and the certificate and
    compiled file of every book in their include closure, with the ACL2 the
    image is saved under.  A changed book, certificate or host file is a new
    key.  A missing certificate is keyed as missing (the load then fails)."""
    import hashlib
    root = Path(root).resolve()
    h = hashlib.sha256()

    def add(label, path):
        h.update(label.encode() + b"\0")
        h.update(path.read_bytes() if path.is_file() else b"<missing>")
        h.update(b"\0")

    files = []
    for world in ("tools/extract/world.lisp", "tools/extract/world-host.lisp"):
        for path in lds_followed(root, world):
            if path not in files:
                files.append(path)
    for path in files:
        add("file " + path.relative_to(root).as_posix(), path)
    for name in included_books(root, "tools/extract/world.lisp"):
        for suffix in (".cert", ".fasl"):
            add("artifact " + name + suffix, root / (name + suffix))
    if acl2:
        h.update(b"acl2 " + str(acl2).encode())
    return h.hexdigest()


if __name__ == "__main__":
    if "--digest" in sys.argv:
        # tools/extract/world.py --digest TREE [--acl2 PATH]: print the key;
        # never write (before 2026-09-29 world_image.sh called this flag,
        # which did not exist, and the call REGENERATED the world files).
        rest = [a for a in sys.argv[1:] if a != "--digest"]
        acl2 = None
        if "--acl2" in rest:
            i = rest.index("--acl2")
            acl2 = rest[i + 1]
            del rest[i:i + 2]
        print(digest(Path(rest[0]) if rest else ROOT, acl2))
        sys.exit(0)
    check = "--check" in sys.argv
    bad = 0
    for path, text in render().items():
        if check:
            if not path.exists() or path.read_text() != text:
                print("world.py: %s is not what the native build scripts say; run tools/extract/world.py"
                      % path.relative_to(ROOT))
                bad = 1
        else:
            path.write_text(text)
    sys.exit(bad)
