#!/usr/bin/env python3
"""The native image loads each compiled file once, and its stubs fit its TLS.

SBCL never frees a thread-local-storage index, and ACL2 8.7 declares a fresh
special (throw-or-attach's gensym) in the raw stub of every constrained or
non-executable function each time that stub's compiled file loads.  A
top-level include-book loads the compiled file of every book in its closure,
even when the include is redundant.  So an image's TLS use is (stubs in its
world) x (top-level includes that reach them): ~600 of them took the
developer image to 60% of the 65536-slot TLS and b1 past it
(planning/evidence/arena-store-8-tls.md).  Each build script therefore
includes one umbrella book first and turns the compiler off, so the rest
load nothing (tools/extract/world.py).

Static, no ACL2 (make check):
  umbrella   every host/native/*.lisp that calls save-exec is a key of
             world.UMBRELLAS; each includes its umbrella as its FIRST
             include-book, followed at once by world.PROLOGUE, and has
             world.EPILOGUE after its last host `ld' and before its trust
             tag, and prints FN_NATIVE_TLS;
  generated  the umbrellas and tools/extract/world*.lisp are what world.py
             renders today;
  stubs      each umbrella's non-local closure (fn's own books; the system
             books ACL2 ships are not counted) has at most STUB_BUDGET raw
             stubs: 2 per constrained function (an encapsulate or
             partial-encapsulate signature, a defstub) and 1 per
             non-executable definition (defun-nx, defund-nx, :non-executable
             t).  A macro that expands to one is invisible here; the image
             build's FN_NATIVE_TLS line (tools/build_native_host.sh refuses
             over its budget) is the measured figure.

--measure BUILD (on a box with ACL2 and the certificates installed; FN_ACL2
or --acl2 names the image launcher): runs BUILD's prefix (to its trust tag)
with a probe around each compiled-file load (ACL2's load-compiled) and prints
each book's own TLS cost, the largest first, and the total.  It is the
diagnosis when an image build is refused over its TLS budget.
"""
from __future__ import annotations

import argparse
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parent / "extract"))
import ledger  # noqa: E402
import world  # noqa: E402

# Raw stubs the umbrella closure of the default image may hold.  A book's
# TLS cost is one slot for each special its compiled code references for the
# first time (a defconst's name, once per process) plus one per raw stub each
# time its compiled file loads (the leak): tls_check --measure at the lane's
# head read 24188 of 524288 units for the whole developer world loaded once,
# with 101 stubs counted here (assumptions' 40 measured exactly 40 slots).  A
# slot is TLS_UNITS_PER_STUB units.  The budget is twenty times today's count:
# past it, measure (--measure) before growing the world's stubs further.
STUB_BUDGET = 2000
TLS_UNITS_PER_STUB = 8

CONSTRAINED = {"encapsulate", "partial-encapsulate"}
NONEXEC = {"defun-nx", "defund-nx"}


def sym(x) -> str | None:
    return str(x).lower() if isinstance(x, ledger.Sym) else None


def signature_names(signatures) -> list[str]:
    names = []
    if not isinstance(signatures, list):
        return names
    for sig in signatures:
        if not isinstance(sig, list) or not sig:
            continue
        head = sig[0]
        if isinstance(head, list) and head and sym(head[0]):     # ((f x) => *)
            names.append(sym(head[0]))
        elif sym(head):                                          # (f (x) t ...)
            names.append(sym(head))
    return names


def declares_nonexec(form) -> bool:
    for item in form[3:]:
        if isinstance(item, list) and item and sym(item[0]) == "declare":
            for decl in item[1:]:
                if isinstance(decl, list) and decl and sym(decl[0]) == "xargs":
                    plist = decl[1:]
                    for i in range(0, len(plist) - 1):
                        if sym(plist[i]) == ":non-executable" and sym(plist[i + 1]) not in (None, "nil"):
                            return True
    return False


def stubs_in(forms) -> int:
    count = 0
    for form in forms:
        if not isinstance(form, list) or not form:
            continue
        head = sym(form[0])
        if head in ("local", "quote", "defmacro", "defthm", "defthmd"):
            continue
        if head in CONSTRAINED and len(form) >= 2:
            count += 2 * len(signature_names(form[1]))
            count += stubs_in(form[2:])
        elif head == "defstub":
            count += 2
        elif head in NONEXEC:
            count += 1
        elif head in ("defun", "defund") and declares_nonexec(form):
            count += 1
        elif head in ("progn", "encapsulate", "with-output", "make-event", "defsection"):
            count += stubs_in(form[1:])
    return count


def closure_stubs(umbrella: str, root: Path = ROOT) -> tuple[int, list[tuple[int, str]]]:
    """(total, [(stubs, book)]) over UMBRELLA's non-local closure of fn books."""
    seen: set[Path] = set()
    rows: list[tuple[int, str]] = []
    pending = [(root / (umbrella + ".lisp")).resolve()]
    while pending:
        path = pending.pop()
        if path in seen or not path.is_file():
            continue
        seen.add(path)
        rel = path.relative_to(root.resolve()).as_posix()
        forms = [f for f, _ in ledger.Reader(path.read_text(encoding="utf-8")).top_level()]
        rows.append((stubs_in(forms), rel))
        book = ledger.analyze_book(path, rel)
        for _, reference in book.nonlocal_includes:
            pending.append((path.parent / (reference + ".lisp")).resolve())
    rows.sort(reverse=True)
    return sum(n for n, _ in rows), rows


def build_scripts(root: Path = ROOT) -> list[str]:
    out = []
    for path in sorted((root / "host" / "native").glob("*.lisp")):
        text = re.sub(r";[^\n]*", "", path.read_text(encoding="utf-8"))
        if re.search(r"^\(save-exec\b", text, re.M):
            out.append(path.relative_to(root).as_posix())
    return out


def structure_problems(build: str, umbrella: str, root: Path = ROOT) -> list[str]:
    problems = []
    text = (root / build).read_text(encoding="utf-8")
    code = re.sub(r";[^\n]*", "", text)
    tag = re.search(r"^\(defttag :", code, re.M)
    prefix = code[:tag.start()] if tag else code
    first = re.search(r'^\(include-book "([^"]+)"', prefix, re.M)
    if not first or first.group(1) != umbrella:
        problems.append(f"{build}: its first include-book is {first.group(1) if first else 'absent'}, "
                        f"not its umbrella {umbrella}")
    else:
        after = [line.strip() for line in prefix[first.end():].split("\n")[1:] if line.strip()]
        if after[:len(world.PROLOGUE)] != list(world.PROLOGUE):
            problems.append(f"{build}: the umbrella is not followed at once by world.PROLOGUE "
                            "(the compiler turned off)")
    epilogue = "\n".join(world.EPILOGUE)
    at = prefix.find(epilogue)
    last_ld = max((m.end() for m in re.finditer(r"^\(ld ", prefix, re.M)), default=0)
    last_include = max((m.end() for m in re.finditer(r"^\(include-book ", prefix, re.M)), default=0)
    if at < 0:
        problems.append(f"{build}: world.EPILOGUE (the closure check) is not before its trust tag")
    elif at < max(last_ld, last_include):
        problems.append(f"{build}: an include-book or ld follows the closure check")
    if "FN_NATIVE_TLS" not in code:
        problems.append(f"{build}: prints no FN_NATIVE_TLS line before its save")
    return problems


def static_check(root: Path = ROOT, verbose: bool = False) -> int:
    problems = []
    scripts = build_scripts(root)
    for build in scripts:
        if build not in world.UMBRELLAS:
            problems.append(f"{build}: saves an image and is not a key of world.UMBRELLAS "
                            "(tools/extract/world.py): its includes would each reload their closure")
    for build, umbrella in world.UMBRELLAS.items():
        if not (root / build).is_file():
            problems.append(f"{build}: named in world.UMBRELLAS and absent")
            continue
        problems.extend(structure_problems(build, umbrella, root))
    if root == ROOT:
        for path, text in world.render().items():
            if not path.exists() or path.read_text(encoding="utf-8") != text:
                problems.append(f"{path.relative_to(ROOT)}: not what tools/extract/world.py renders; run it")
    total, rows = closure_stubs(world.UMBRELLAS[world.EXTRACT_BUILD], root)
    over = total > STUB_BUDGET
    print(f"tls_check: {len(world.UMBRELLAS)} build scripts, each through its umbrella; "
          f"{total} raw stubs in the default image's closure ({len(rows)} books), budget {STUB_BUDGET} "
          f"(~{total * TLS_UNITS_PER_STUB} of 524288 TLS units, loaded once)")
    for n, book in rows[:5 if not verbose else 40]:
        if n:
            print(f"  {n:5d} {book}")
    if over:
        problems.append(f"{total} raw stubs exceed the budget {STUB_BUDGET}: move constrained and "
                        "non-executable functions out of the image's closure, or raise the budget "
                        "with the measured FN_NATIVE_TLS")
    for problem in problems:
        print("tls_check: " + problem)
    return 1 if problems else 0


PROBE = r""":q
(defvar cl-user::*fn-tls-depth* 0)
(let ((old (symbol-function 'acl2::load-compiled)))
  (setf (symbol-function 'acl2::load-compiled)
        (lambda (&rest args)
          (let ((before sb-vm::*free-tls-index*)
                (cl-user::*fn-tls-depth* (1+ cl-user::*fn-tls-depth*)))
            (declare (special cl-user::*fn-tls-depth*))
            (multiple-value-prog1 (apply old args)
              (format t "~&FNTLS ~d ~a ~d~%" cl-user::*fn-tls-depth*
                      (namestring (car args))
                      (- sb-vm::*free-tls-index* before)))))))
(format t "~&FNTLS-START ~d~%" sb-vm::*free-tls-index*)
(lp)
"""


def measure(build: str, acl2: str, timeout: int, top: int) -> int:
    text = (ROOT / build).read_text(encoding="utf-8")
    tag = re.search(r"^\(defttag :", text, re.M)
    prefix = text[:tag.start()] if tag else text
    driver = (PROBE + prefix + '\n:q\n(format t "~&FNTLS-END ~d ~d~%" sb-vm::*free-tls-index* '
              '(floor (sb-alien:extern-alien "dynamic_values_bytes" (sb-alien:unsigned 32)) 2))\n'
              "(sb-ext:exit)\n")
    import acl2_slots  # noqa: PLC0415 (tools/ is on sys.path above)
    env = dict(acl2_slots.acl2_environment(), ACL2_CUSTOMIZATION="NONE")
    env.pop("ACL2_SYSTEM_BOOKS", None)
    # The machine's ACL2 pool and heap cap (PKT-162), as proof_artifacts' load.
    with acl2_slots.tree_slot("tls_check measure"):
        done = subprocess.run([acl2], cwd=ROOT, input=driver.encode(), stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, env=env, timeout=timeout, check=False)
    out = done.stdout.decode("utf-8", "replace")
    start = re.search(r"FNTLS-START (\d+)", out)
    end = re.search(r"FNTLS-END (\d+) (\d+)", out)
    # A book's own cost: its delta less its children's (loads nest).
    stack: list[list] = []
    own: dict[str, int] = {}
    for m in re.finditer(r"^FNTLS (\d+) (\S+) (-?\d+)$", out, re.M):
        depth, book, delta = int(m.group(1)), m.group(2), int(m.group(3))
        children = 0
        while stack and stack[-1][0] > depth:
            children += stack.pop()[1]
        stack.append([depth, delta])
        book = os.path.relpath(book, ROOT) if book.startswith(str(ROOT)) else book
        own[book] = own.get(book, 0) + delta - children
    if not (start and end):
        print(f"tls_check --measure: {build} did not finish (no FNTLS-START/END); "
              "the session's output tail:\n" + "\n".join(out.splitlines()[-15:]))
        return 4
    used, cap = int(end.group(1)), int(end.group(2))
    print(f"tls_check --measure {build}: TLS index {int(start.group(1))} -> {used} of {cap} "
          f"({100 * used // cap}%), {len(own)} compiled-file loads")
    for book, n in sorted(own.items(), key=lambda kv: -kv[1])[:top]:
        print(f"  {n:7d} {book}")
    loads: dict[str, int] = {}
    for m in re.finditer(r"^FNTLS \d+ (\S+) ", out, re.M):
        loads[m.group(1)] = loads.get(m.group(1), 0) + 1
    # (the full paths: two system books can share a file name)
    loaded_twice = [b for b, n in loads.items() if n > 1]
    if loaded_twice:
        print(f"tls_check --measure: {len(loaded_twice)} books loaded more than once, e.g. "
              + ", ".join(loaded_twice[:5]))
        return 1
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--measure", metavar="BUILD")
    parser.add_argument("--acl2", default=os.environ.get("FN_ACL2", "acl2"))
    parser.add_argument("--timeout", type=int, default=1800)
    parser.add_argument("--top", type=int, default=25)
    parser.add_argument("--verbose", action="store_true")
    args = parser.parse_args(argv)
    if args.measure:
        return measure(args.measure, args.acl2, args.timeout, args.top)
    return static_check(verbose=args.verbose)


if __name__ == "__main__":
    sys.exit(main())
