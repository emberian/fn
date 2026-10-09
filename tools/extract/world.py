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

# THE CHAIN (lane n-tls-chain).  Certifying an umbrella runs one top-level
# include-book per line, and each reloads its whole closure, so the certify
# process spends ~140 TLS slots per line (the SBCL leak above): 71917 of the
# 65536 allowed for books/image-world, 67781 for books/image-world-dtn, at dev
# 697c03398 (n-tls, hbox, ACL2 8.7 / SBCL 2.6.8, load-only launcher tls256k,
# 2026-10-08; the certify at tls64k died at store-identity and at
# ../host/page-window-executor-host).  An umbrella is therefore a chain of
# links, books/<umbrella>-part-1 .. -part-N: part k includes part k-1, then its
# own slice of the umbrella's include lines, in the umbrella's exact order; the
# umbrella itself includes only the last link.  Including the umbrella loads
# each file once, as before (measured: a thin book over two links certified at
# 4360 slots).  An umbrella whose estimate fits one link has no chain.
#
# Where each link ends is decided by a measured slot budget, not a number of
# lines.  SLOT_COSTS is tools/extract/world_slots.json, the slots a top-level
# include of each book cost in that measurement (tools/extract/world_slots.py
# files it; mean 140, max 627); a book it lacks costs UNMEASURED_COST, above
# every measured one, so a new book makes a link smaller, never a certify red.
# A table, not a model: the stubs are made by macros the sources do not show
# (tls_check counts 101 where 2215 live ones exist), and a cost per line from
# the closure size fits only r=0.86.  The table ages, but only toward the
# conservative side or by a book's closure growing; LINK_FRACTION leaves 40%
# for that and for the unmeasured, and a link that still went over is a red
# certify (the first include past 65536), not a silent one: re-measure then.
SLOT_LIMIT = 65536            # --tls-limit of the certify launcher (tls64k)
LINK_FRACTION = 0.60          # each link stays under about 60% of SLOT_LIMIT
SLOT_BASE = 1667              # a fresh ACL2 image (measured 1666.5)
CERTIFY_MARGIN = 200          # certify-book's own bindings (measured ~100)
PREV_LINK_COST = 4000         # including the previous link (measured 1915 for
                              # a 251-include link; its closure is every earlier file once)
UNMEASURED_COST = 640         # above the largest measured include (627)
LINK_INCLUDE_BUDGET = (int(SLOT_LIMIT * LINK_FRACTION) - SLOT_BASE
                       - CERTIFY_MARGIN - PREV_LINK_COST)
SLOT_COSTS_PATH = ROOT / "tools" / "extract" / "world_slots.json"

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
# The carried rows' owed writers, checked once every host file is loaded
# (books/def-carried.lisp def-carried-host-check), as the image drivers do.
CARRIED_HOST_CHECK = "(def-carried-host-check)"

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
    """The include-books the host files make themselves (their lds and their
    host-sibling include-books followed: a sibling included as a book loads
    its own edges with its certificate, so the umbrella names them the same
    way an ld'd sibling's books are named)."""
    out, seen = [], set()

    def visit(rel):
        path = (ROOT / rel).resolve()
        if path in seen or not path.exists():
            return
        seen.add(path)
        text = path.read_text()
        for m in re.finditer(r'^\s*\((include-book|ld) "([^"]+)"', text, re.M):
            target = (path.parent / m.group(2)).resolve()
            trell = str(target.relative_to(ROOT))
            if m.group(1) == "ld":
                visit(trell)
                continue
            out.append(trell)
            source = target if target.suffix == ".lisp" else target.with_name(target.name + ".lisp")
            if trell.startswith("host/") and source.is_file():
                # a host sibling included as a book: walk it like an ld.  A
                # books/ target's own closure arrives through its
                # certificate, not this list.
                visit(str(source.relative_to(ROOT)))

    for h in hosts:
        visit(h)
    return out


def world_books(build):
    books, hosts = forms(build)
    for b in host_books(hosts):
        if b not in books:
            books.append(b)
    return books, hosts


def relative_to_books(book):
    return Path(os.path.relpath(ROOT / book, ROOT / "books")).as_posix()


def books_last(books: list[str]) -> list[str]:
    """Pure books in their order, then the host :program books in theirs.

    A host book replays its wrapper defuns unverified, and ACL2 refuses a
    book's guard-verified definition over an existing unverified one while
    the identical-defun skip works in the other direction; the extracted
    aliases (books/store-octet-entry.lisp of host/store-host.lisp's
    fn-store-octets->string, carried by books/owner-connection-callbacks)
    must therefore precede every host book.  Interleaving them by first
    visit put ../host/store-host before owner-connection-callbacks in both
    umbrellas and the umbrella would not certify (native-admin-host hit the
    same refusal before its includes were ordered; certify run
    certify-20261006T140212Z-12860)."""
    pure = [b for b in books if not b.startswith("host/")]
    hosts = [b for b in books if b.startswith("host/")]
    return pure + hosts


def slot_costs():
    import json
    return json.loads(SLOT_COSTS_PATH.read_text())


def split_links(books, costs=None, budget=LINK_INCLUDE_BUDGET):
    """BOOKS (include names in umbrella order) cut into the fewest slices whose
    estimated cost each fits BUDGET, balanced by cost; the slices concatenate
    to BOOKS exactly (asserted: the order is the image's, tests/test_extract_world.py).
    A book the table lacks costs UNMEASURED_COST."""
    costs = slot_costs() if costs is None else costs
    cost = [costs.get(b, UNMEASURED_COST) for b in books]
    total = sum(cost)
    if max(cost, default=0) > budget:
        raise ValueError("one include exceeds the link budget %d" % budget)
    count = max(1, -(-total // budget))
    while True:
        target = total / count
        slices, current, spent = [], [], 0
        for book, c in zip(books, cost):
            if current and (spent + c > budget or spent + c / 2 > target and len(slices) < count - 1):
                slices.append(current)
                current, spent = [], 0
            current.append(book)
            spent += c
        slices.append(current)
        if len(slices) <= count or count >= len(books):
            break
        count += 1
    flat = [b for one in slices for b in one]
    assert flat == list(books), "split_links changed the include order"
    for one in slices:
        assert sum(costs.get(b, UNMEASURED_COST) for b in one) <= budget
    return slices


def link_name(umbrella, k):
    return "%s-part-%d" % (umbrella, k)


def render_umbrella(build, umbrella):
    """{path: text} of UMBRELLA: itself, and its links when it needs more than one."""
    books, _ = world_books(build)
    books = books_last(books)
    incs = ['(include-book "%s")\n' % relative_to_books(b) for b in books]
    slices = split_links([relative_to_books(b) for b in books])
    head = ("; GENERATED by tools/extract/world.py from\n"
            ";   %s\n"
            "; the image's certified books, in its order, then the books its host files\n"
            "; include, the host :program books last (their wrapper defuns are admitted\n"
            "; unverified; an extracted guard-verified alias must come first).\n"
            "; Do not edit; regenerate.  The script includes this book first\n"
            "; and then turns the compiler off, so each compiled file of the image loads\n"
            "; once: a top-level include-book reloads its whole closure, and every load\n"
            "; of a constrained stub takes a TLS index SBCL never frees (world.py).\n"
            % build)
    out = {}
    if len(slices) == 1:
        out[ROOT / (umbrella + ".lisp")] = head + '(in-package "ACL2")\n' + "".join(incs)
        return out
    name = umbrella.split("/")[-1]
    for k, one in enumerate(slices, 1):
        chain = ('(include-book "%s")\n' % link_name(name, k - 1)) if k > 1 else ""
        text = ("; GENERATED by tools/extract/world.py: link %d of %d of %s\n"
                ";   (%s)\n"
                "; %s the next slice of its include lines in the umbrella's order.\n"
                "; Certifying one book of the whole umbrella exhausts the thread-local\n"
                "; storage of the certify launcher (a top-level include-book reloads its\n"
                "; closure at each line, world.py CHAIN); a link certifies a slice.\n"
                "; Do not edit; regenerate.\n"
                % (k, len(slices), umbrella, build,
                   "It includes the previous link, then" if k > 1 else "It is"))
        out[ROOT / ("books/%s.lisp" % link_name(name, k))] = (
            text + '(in-package "ACL2")\n' + chain + "".join(
                '(include-book "%s")\n' % b for b in one))
    out[ROOT / (umbrella + ".lisp")] = (
        head + "; It is the thin end of a chain of %d links (world.py CHAIN): the slices\n"
        "; of the include lines are books/%s-part-1 .. -part-%d, in this order.\n"
        % (len(slices), name, len(slices))
        + '(in-package "ACL2")\n' + '(include-book "%s")\n' % link_name(name, len(slices)))
    flat = [m for k in range(1, len(slices) + 1)
            for m in re.findall(r'^\(include-book "([^"]+)"\)\n?', out[ROOT / ("books/%s.lisp" % link_name(name, k))], re.M)
            if m != link_name(name, k - 1)]
    assert flat == [relative_to_books(b) for b in books], "the chain changed the include order"
    return out


def stale_links(generated):
    """Link books on disk that no umbrella renders now (a shorter chain)."""
    names = {path for path in generated}
    out = []
    for umbrella in UMBRELLAS.values():
        base = umbrella.split("/")[-1]
        for path in sorted((ROOT / "books").glob(base + "-part-*.lisp")):
            if path not in names:
                out.append(path)
    return out


def world_paths(variant="default"):
    if variant not in ("default", "dtn"):
        raise ValueError("unsupported extraction variant: " + variant)
    suffix = "" if variant == "default" else "-dtn"
    return ("tools/extract/world" + suffix + ".lisp",
            "tools/extract/world-host" + suffix + ".lisp")


def render(variant="default"):
    build = EXTRACT_BUILD if variant == "default" else "host/native/build-dtn.lisp"
    out = {}
    for native_build, umbrella in UMBRELLAS.items():
        out.update(render_umbrella(native_build, umbrella))
    books, hosts = world_books(build)
    books = books_last(books)
    head = ("; GENERATED by tools/extract/world.py from host/native/build.lisp: the image's\n"
            "; certified books, in its order, the host :program books last.\n"
            "; Do not edit; regenerate.\n")
    umbrella = UMBRELLAS[build]
    world = (head + '(in-package "ACL2")\n'
             + '(include-book "../../%s")\n' % umbrella
             + "".join(line + "\n" for line in PROLOGUE)
             + "".join('(include-book "../../%s")\n' % b for b in books))
    host = (head.replace("the image's\n; certified books, in its order, the host :program books last.",
                         "the image's\n; host :program files (ld), in its order.")
            + '(in-package "ACL2")\n'
            + "".join(line + "\n" for line in HOST_PROLOGUE)
            + "".join('(ld "../../%s" :ld-error-action :error)\n' % h for h in hosts)
            + CARRIED_HOST_CHECK + "\n"
            + "".join(line + "\n" for line in EPILOGUE))
    world = world.replace("from host/native/build.lisp:", "from " + build + ":")
    host = host.replace("from host/native/build.lisp:", "from " + build + ":")
    paths = world_paths(variant)
    out[ROOT / paths[0]] = world
    out[ROOT / paths[1]] = host
    return out


def lds_followed(root, rel):
    """REL and every file its `ld's and host-sibling include-books reach, in
    first-visit order (the digest's file set: a host file reached only
    through an include-book is loaded all the same, so its bytes must key
    the cache; a books/ include's bytes arrive below as its certificate and
    compiled artifacts, not as a source file)."""
    out, seen = [], set()

    def under_host(path):
        try:
            path.resolve().relative_to(Path(root).resolve().joinpath("host"))
            return True
        except ValueError:
            return False

    def visit(path):
        path = path.resolve()
        if path in seen or not path.is_file():
            return
        seen.add(path)
        out.append(path)
        for m in re.finditer(r'^\s*\((ld|include-book) "([^"]+)"', path.read_text(), re.M):
            target = path.parent / m.group(2)
            if m.group(1) == "include-book":
                if target.suffix != ".lisp":
                    target = target.with_name(target.name + ".lisp")
                if not under_host(target):
                    continue
            visit(target)

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


def digest(root, acl2=None, variant="default", toolchain_identity=None):
    """The world's cache key (world_image.sh): SHA-256 over the two world
    files selected by VARIANT, every host file they load (lds followed), and the certificate and
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
    for world in world_paths(variant):
        for path in lds_followed(root, world):
            if path not in files:
                files.append(path)
    for path in files:
        add("file " + path.relative_to(root).as_posix(), path)
    for name in included_books(root, world_paths(variant)[0]):
        for suffix in (".cert", ".fasl"):
            add("artifact " + name + suffix, root / (name + suffix))
    if acl2:
        h.update(b"acl2 " + str(acl2).encode())
    if toolchain_identity:
        h.update(b"\0toolchain " + toolchain_identity.encode())
    return h.hexdigest()


if __name__ == "__main__":
    if "--digest" in sys.argv:
        # tools/extract/world.py --digest TREE [--acl2 PATH]: print the key;
        # never write (before 2026-09-29 world_image.sh called this flag,
        # which did not exist, and the call REGENERATED the world files).
        rest = [a for a in sys.argv[1:] if a != "--digest"]
        variant = "default"
        if "--variant" in rest:
            i = rest.index("--variant")
            variant = rest[i + 1]
            del rest[i:i + 2]
        toolchain_identity = None
        if "--toolchain-identity" in rest:
            i = rest.index("--toolchain-identity")
            toolchain_identity = rest[i + 1]
            del rest[i:i + 2]
        acl2 = None
        if "--acl2" in rest:
            i = rest.index("--acl2")
            acl2 = rest[i + 1]
            del rest[i:i + 2]
        print(digest(Path(rest[0]) if rest else ROOT, acl2, variant, toolchain_identity))
        sys.exit(0)
    # Only --check and no argument are modes: any other argument (--help
    # included) used to fall through and REGENERATE every umbrella, which hid a
    # stale one from the --check that followed.
    unknown = [a for a in sys.argv[1:] if a != "--check"]
    if unknown:
        print("usage: tools/extract/world.py [--check | --digest TREE [--variant V] "
              "[--acl2 PATH] [--toolchain-identity ID]]  (unrecognised: %s)" % " ".join(unknown),
              file=sys.stderr)
        sys.exit(2)
    check = "--check" in sys.argv
    bad = 0
    generated = render()
    generated.update(render("dtn"))
    for path in stale_links(generated):
        if check:
            print("world.py: %s is a link no umbrella renders now; run tools/extract/world.py"
                  % path.relative_to(ROOT))
            bad = 1
        else:
            path.unlink()
    for path, text in generated.items():
        if check:
            if not path.exists() or path.read_text() != text:
                print("world.py: %s is not what the native build scripts say; run tools/extract/world.py"
                      % path.relative_to(ROOT))
                bad = 1
        else:
            path.write_text(text)
    sys.exit(bad)
