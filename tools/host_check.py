#!/usr/bin/env python3
"""The host files load, in the order and world each image loads them.

    python3 tools/host_check.py                 # both images' ld prefixes, build order
    python3 tools/host_check.py --load          # the raw files, build order, bare ACL2
    python3 tools/host_check.py --tables        # static: global hash tables
    python3 tools/host_check.py --world         # static: counterparts in the image world
    python3 tools/host_check.py --alone FILE... # one file alone (a diagnosis, not a gate)

THE DEFAULT (lane lane-tools-2, 2026-09-28) is the ACL2-mode prefix of
host/native/build.lisp and of host/native/build-dtn.lisp -- every
include-book and host `ld`, in the script's order -- translated by
tools/host_translate_check.py, one ACL2 per image.  It replaced loading each
host file ALONE, which was vacuous twice over: without FN_ACL2 it printed
SKIPPED and exited 0 (every `make check' until batch AY), and with ACL2 it
failed 39 of 80 files in a certified tree, because a host file may use what
an earlier `ld` in the build defined -- the order the image really loads is
the one that decides.  No ACL2, or a book the prefix includes without an
installed certificate, is NOT RUN, exit 2, and `make check' counts it as a
failed step: evidence that did not run is not a pass.  `--alone FILE...`
keeps the old per-file load as a diagnosis tool.

What follows describes `--alone`, then the other modes.

The host files are never certified: they are `ld`ed by the Python bridges
(tools/run_store.py and its siblings) and `load`ed, in raw mode, by
host/native/build.lisp.  Nothing else reads them, so a host file that uses a
name a *sibling* host file defines is green under one bridge's load order and
broken under another's, and broken outright for any tool that loads it alone.
tools/ledger.py's `host_names` lint reports that statically.  This is the
dynamic half: one fresh ACL2 per host file, that file and nothing else, and
the file must load without an error and leave the session in the logic mode
and at the `ACL2 !>` prompt it found.

Three kinds of host file, decided from host/native/build.lisp rather than a
list typed here:

  ld    the interpreted `:program` wrappers, `(ld "<file>")`.
  raw   the raw Common Lisp the image loads under its trust tag, checked with
        the same `(progn! (set-raw-mode t) (load "<file>"))` the build uses.
  skip  host/native/build.lisp itself: it ends in `:q` and `save-exec`, so
        loading it is building the image.  tools/build_native_host.sh is its
        check.

Certificates for the books a host file includes must already be installed
(`python3 tools/certs.py install`), because `ld` of an `include-book` reads a
certificate it will not produce.

`--load` (lane tooling-leftovers, 2026-09-27) is the raw files' load check
without an image build.  A raw host file's only load check was the native
image build, about ten minutes (history-columns-2), and the build does not
even see most of what goes wrong there: ACL2 compiles under SBCL's
`inhibit-warnings 3`, so an undefined function, a call with the wrong number
of arguments, or a macro used above its definition (batch AW's
`fnn-log-with-kernel`, which compiled `(log)` as a call of CL:LOG) is
silent and faults at run time.  `--load` starts one bare ACL2 (no book, so
it takes seconds, not the certified world), lowers `inhibit-warnings` to 1,
and inside one `with-compilation-unit` reads and evaluates every form of
the files build.lisp `load`s, in build.lisp's order.  It then reports:

  FAIL  a form that signals an error; a call with the wrong number of
        arguments; a macro used before its definition ("redefined as a
        macro when it was previously assumed to be a function"); a
        function or special variable still undefined at the end whose name
        no book and no ACL2-mode host file defines (a typo, a deleted
        helper, a sibling file build.lisp does not load);
  world an undefined name the books or the `ld` host files do define: the
        bare image lacks the certified world by design, so these are
        counted, never failed, and a load-time call of one is skipped
        (`return-value' restart) so the rest of the file still loads.

It first runs tools/extract/world.py --check (the umbrellas against the
build scripts; a stale umbrella is a FAIL: limits-live-5's host include-book
passed --load and died in the image build's acquire).  `make
host-convert-check FILE=...` (tools/host_convert_check.py) runs this with
every other pre-image gate, including the certified-world class check.
THE WORLD (obstructions-6 item 40): when the build script's include-books
have certificates in the tree -- or `certs.py install-set` can install them
from FN_CERT_CACHE / the box's farm cache -- --load first runs the build's
ACL2-mode prefix (image-world and the host `ld`s, where definterface checks
each declaration and generates its `-by-definition` equations) and loads the
raw files over it; an error in the prefix is a FAIL naming its host file.
Its first line says which world it ran in: `WORLD CERTIFIED UMBRELLA ...` or
`WORLD BARE ACL2 -- ...` with the reason.  `--bare` forces the seconds-scale
bare load (make check's, whose default step runs the prefix already);
`--require-world` makes an unavailable umbrella NOT RUN (exit 2).
In a bare load it cannot see: the arity of a call into a book function (the bare image
does not know it), anything the FFI initializers do (`fnn-crypto-initialize'
and its siblings are build.lisp's calls, not the files'), and translate
errors in the ACL2-mode host files (tools/host_translate_check.py).  Exit 0
clean, 1 with each finding named, 2 NOT RUN (no ACL2).

    FN_ACL2=/path/to/acl2 python3 tools/host_check.py --load [--build host/native/build-dtn.lisp] [FILE ...]

FN_ACL2 is REQUIRED (an `acl2` on PATH is the fallback): without an ACL2 the
check prints NOT RUN and exits 2, which `make check' reports as a failed
step, never a pass (host-lints' check-lane skipped it for lack of FN_ACL2).

with FILEs, the order is loaded through the last of them.

`--tables` (lane host-lints, 2026-09-27) is a static rule, no ACL2: every
`make-hash-table` in host/ whose table can outlive one call -- at top level,
in a defvar/defparameter/defglobal initializer, a defstruct slot's initform,
or a `setq`/`setf` of an earmuffed global inside a function -- is
`:synchronized t`, or its line or the line before declares one of

  ;; thread-confined: <which thread, and why no other reaches it>
  ;; guarded-by: <lock>   (the lock a `with-mutex`/`with-recursive-lock` in
                           the same file takes)

Anything else is refused by file:line and name.  entry-guards-2 found the
reason by luck: two lazily filled tables in host/native/io.lisp were shared
by served threads, the owner and control workers without synchronization,
and two first calls at once stopped the owner (fixed by 6137e36c3).  A
table local to one call (a `let` in a defun) is not a global and is not
checked.  What it cannot see: whether every access really holds the named
lock -- the declaration names the lock; the review reads the accesses.

    python3 tools/host_check.py --tables [FILE ...]
"""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import acl2_slots  # noqa: E402

HOST_DIRS = ("host", "host/native")
BUILD_SCRIPT = "host/native/build.lisp"
# The image build script names its own raw files; reading them from it keeps
# this tool from carrying a second copy of that decision.
RAW_LOAD = re.compile(r'\(load\s+"([^"]+\.lisp)"')
# Two markers, because one is not enough.  A failed `ld` does not end a
# session reading from a pipe: ACL2 reports the error, abandons that form and
# reads the next one, so a marker on its own line prints for a file that did
# not load.  Measured: host/config-host.lisp with its `ld` edge deleted
# reported `ACL2 Error [Translate]` for an undefined function and the marker
# still appeared.  LD_OK is printed from inside an `er-progn` with the load,
# which short-circuits, and MARKER by the next top-level form, whose prompt
# is the one the loaded file left behind.
LD_OK = "FN_HOST_CHECK_LD_OK"
MARKER = "FN_HOST_CHECK_LOADED"
PROMPT = "ACL2 !>"
ERRORS = ("ACL2 Error", "HARD ACL2 ERROR")
DEFAULT_TIMEOUT_SECONDS = 600


def executable() -> Path | None:
    configured = os.environ.get("FN_ACL2", "")
    if not configured:
        return None
    if os.sep in configured:
        candidate = Path(configured).expanduser()
        return candidate.resolve() if candidate.is_file() and os.access(candidate, os.X_OK) else None
    found = shutil.which(configured)
    return Path(found).resolve() if found else None


def raw_files() -> set[str]:
    text = (ROOT / BUILD_SCRIPT).read_text(encoding="utf-8")
    return {name for name in RAW_LOAD.findall(text) if (ROOT / name).is_file()}


def host_files() -> list[str]:
    found: list[str] = []
    for directory in HOST_DIRS:
        for path in sorted((ROOT / directory).glob("*.lisp")):
            found.append(path.relative_to(ROOT).as_posix())
    return found


def driver_for(relative: str, raw: bool) -> str:
    """The whole session: this one file, then one marker at the prompt.

    `:ld-error-action :error` turns any failure inside the file into a failed
    `ld`, and the marker is printed by a form read at the top level *after*
    it, so its prompt is the prompt the file left behind.  A file that ended
    in `(program)` prints `ACL2 p>` there and fails this check; every host
    file that switches mode restores it (host/anchor-host.lisp is the one
    that switches).
    """
    load = (f'(progn! (set-raw-mode t) (load "{relative}"))' if raw
            else f'(ld "{relative}" :ld-error-action :error)')
    return ("(defttag :fn-host-check)\n" if raw else "") \
        + f'(er-progn {load}\n' \
        + f'          (value-triple (cw "{LD_OK} ~s0~%" "{relative}")))\n' \
        + ("(defttag nil)\n" if raw else "") \
        + f'(cw "{MARKER} ~s0~%" "{relative}")\n(good-bye)\n'


def loaded_at_logic_prompt(output: str) -> tuple[bool, str]:
    """Did the load succeed, and did the prompt after it say `ACL2 !>`?

    ACL2 prints its prompt before reading each form and does not echo a form
    that came from a pipe, so a marker's own output follows the prompt on one
    line.  An error reported while the file was loading fails the check even
    if the session recovered from it.
    """
    lines = output.splitlines()
    end = next((i for i, line in enumerate(lines) if LD_OK in line), len(lines))
    for line in lines[:end]:
        if any(marker in line for marker in ERRORS):
            return False, f"error while loading: {line.strip()}"
    if end == len(lines):
        return False, "the load did not complete"
    for line in lines[end:]:
        if MARKER not in line:
            continue
        before = line.split(MARKER, 1)[0].strip()
        if before.endswith(PROMPT):
            return True, ""
        return False, f"loaded, but the prompt after it was {before!r}, not {PROMPT!r}"
    return False, "loaded, but the session did not reach a prompt after it"


def check(acl2: Path, relative: str, raw: bool, timeout: int) -> tuple[bool, str, str]:
    try:
        # The machine's ACL2 pool and heap cap, as every fn launcher (PKT-162).
        result = acl2_slots.run(
            [str(acl2)], f"host_check {relative}", cwd=ROOT,
            input=driver_for(relative, raw).encode(),
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            timeout=timeout, check=False)
    except subprocess.TimeoutExpired as error:
        partial = (error.output or b"").decode("utf-8", "replace")
        return False, f"timed out after {timeout}s", partial
    output = result.stdout.decode("utf-8", "replace")
    ok, reason = loaded_at_logic_prompt(output)
    return ok, reason, output


# --- --load: the raw files in one bare ACL2 ---------------------------------

LOAD_TAG = "FNLC"
# Definition heads whose next symbol is a name the ACL2 world (books and the
# `ld` host files) defines.  A generated name (a stobj's accessors, a
# `defrec`'s fields) is covered by the second test in `world_names`: the
# token appears in those files at all.
WORLD_DEF = re.compile(r"\(\s*(?:local\s+\(\s*)?def[a-z0-9*$-]*\s+\(?\s*([^\s()'`\"]+)",
                       re.IGNORECASE)
WORLD_DIRS = ("books", "host")


def raw_load_order(build: str = BUILD_SCRIPT) -> list[str]:
    """The raw files BUILD `load`s, in its order (each once)."""
    text = (ROOT / build).read_text(encoding="utf-8")
    text = re.sub(r";[^\n]*", "", text)
    order: list[str] = []
    for name in RAW_LOAD.findall(text):
        if name not in order and (ROOT / name).is_file():
            order.append(name)
    return order


def world_text() -> str:
    """Every book and ACL2-mode host file, lower-cased: the certified world's source."""
    parts = []
    for directory in WORLD_DIRS:
        base = ROOT / directory
        paths = base.rglob("*.lisp") if directory == "books" else base.glob("*.lisp")
        for path in sorted(paths):
            parts.append(path.read_text(encoding="utf-8", errors="replace").lower())
    return "\n".join(parts)


def world_names(text: str) -> set[str]:
    return {name.lower() for name in WORLD_DEF.findall(text)}


def in_world(name: str, defined: set[str], text: str) -> bool:
    """Does the certified world define NAME (or generate it from a definition)?"""
    name = name.lower()
    if name in defined:
        return True
    if name.startswith("acl2_*1*_"):
        return in_world(name.split("::", 1)[-1], defined, text)
    return re.search(r"(?<![\w*+$-])" + re.escape(name) + r"(?![\w*+$-])", text) is not None


def load_driver(files: list[str]) -> str:
    """The raw-mode session: every FILE's forms evaluated in one compilation unit.

    Each line the driver prints starts with FNLC- and one word, so the
    parser never reads ACL2's own output.  A form's error is caught and the
    next form read, so one failure does not hide the rest of the file; a
    load-time call of an undefined function takes the `return-value`
    restart with NIL, and the name is reported for classification.
    """
    listed = " ".join(f'"{name}"' for name in files)
    tag = LOAD_TAG
    return f"""(in-package "ACL2")
(proclaim '(optimize (sb-ext:inhibit-warnings 1)))
(defun fnlc-line (x) (substitute #\\Space #\\Newline (princ-to-string x)))
(defun fnlc-head (form)
  (fnlc-line (if (consp form)
                 (list (car form) (if (consp (cdr form)) (cadr form) nil))
                 form)))
(let ((sb-ext:*muffled-warnings* nil))
  (handler-bind ((warning
                   (lambda (w)
                     (format t "~&{tag}-WARN ~a~%" (fnlc-line w))
                     (muffle-warning w))))
    (with-compilation-unit ()
      (dolist (file '({listed}))
        (format t "~&{tag}-FILE ~a~%" file)
        (with-open-file (s file)
          (let ((*package* (find-package "ACL2"))
                (*load-pathname* (pathname file))
                (*load-truename* (truename file))
                (index 0))
            (loop
              (let ((form (handler-case (read s nil s)
                            (error (e)
                              (format t "~&{tag}-READ-ERROR ~a #~d ~a~%" file (1+ index)
                                      (fnlc-line e))
                              s))))
                (when (eq form s) (return))
                (incf index)
                (handler-case
                    (handler-bind
                        ((undefined-function
                           (lambda (e)
                             (let ((restart (find-restart 'return-value e)))
                               (format t "~&{tag}-CALLED ~a #~d ~a ~a~%" file index
                                       (package-name (symbol-package (cell-error-name e)))
                                       (symbol-name (cell-error-name e)))
                               (when restart (invoke-restart restart nil))))))
                      (eval form))
                  (undefined-function (e)
                    ;; The form needs a function the bare image lacks; what
                    ;; the form defines is named so its later uses classify.
                    (format t "~&{tag}-NEEDS ~a #~d ~a ~a ~a~%" file index
                            (package-name (symbol-package (cell-error-name e)))
                            (symbol-name (cell-error-name e))
                            (if (and (consp form) (consp (cdr form)) (symbolp (cadr form))
                                     (cadr form))
                                (symbol-name (cadr form))
                                "-")))
                  (error (e)
                    (format t "~&{tag}-ERROR ~a #~d ~a: ~a~%" file index (fnlc-head form)
                            (fnlc-line e)))))))))
      (dolist (u sb-c::*undefined-warnings*)
        (let ((name (sb-c::undefined-warning-name u))
              (kind (sb-c::undefined-warning-kind u)))
          (when (and (symbolp name)
                     (not (if (eq kind :function) (fboundp name) (boundp name))))
            (format t "~&{tag}-UNDEFINED ~(~a~) ~a ~a~%" kind
                    (package-name (symbol-package name)) (symbol-name name))))))))
(format t "~&{tag}-DONE~%")
"""


# SBCL's words for the findings that fail the check.  "undefined" warnings
# are the end-of-unit summary of the UNDEFINED lines, classified there.
FAILING_WARNINGS = (
    ("is called with", "arity"),
    ("redefined as a macro when it was previously assumed to be a function",
     "macro used before its definition"),
    ("redefining", "redefinition"),
)


RAW_DEF = re.compile(r"^\((?:defun|defmacro|defvar|defparameter|defconstant|defgeneric)\s+"
                     r"([^\s()]+)", re.IGNORECASE | re.MULTILINE)


def raw_definers() -> dict[str, str]:
    """name -> the host/native file that defines it (first wins)."""
    found: dict[str, str] = {}
    for path in sorted((ROOT / "host" / "native").glob("*.lisp")):
        text = path.read_text(encoding="utf-8", errors="replace")
        for name in RAW_DEF.findall(text):
            found.setdefault(name.lower(), path.relative_to(ROOT).as_posix())
    return found


def nowhere(kind: str, name: str, definers: dict[str, str] | None) -> str:
    where = (definers or {}).get(name.lower())
    if where:
        return (f"undefined {kind} {name.lower()}: defined in {where}, which this build "
                "does not load (a call reaching it faults at run time)")
    return f"undefined {kind} {name.lower()}: no raw file, book or ld host file defines it"


# A load-alone ERROR line: "FILE #N (DEFCONSTANT NAME): The variable X is
# unbound."  Group 1 is the name the form defines, group 2 the unbound one.
WORLD_UNBOUND = re.compile(r"\(DEF[A-Z-]*\s+([^\s()]+)\):\s+The variable ([^\s]+) is unbound",
                           re.IGNORECASE)


def classify_load(output: str, world_defined: set[str], world_source: str,
                  definers: dict[str, str] | None = None
                  ) -> tuple[list[str], dict[str, int], bool]:
    """(findings, counts, completed) from a --load transcript.

    A name a raw host/native file defines is the world's only when a book or
    `ld` host file defines it too: `in_world`'s fallback, the name spelled
    anywhere in those files, also matches a comment that mentions a raw
    function, and it hid four of the DTN image's undefined control-socket
    calls (fnn-control-live-status among them) until batch AX.
    """
    def worlds(name: str) -> bool:
        lowered = name.lower()
        if definers and lowered in definers and lowered not in world_defined:
            return False
        return in_world(name, world_defined, world_source)

    findings: list[str] = []
    counts = {"files": 0, "world": 0, "world_calls": 0, "warnings": 0}
    completed = False
    current = "?"
    # Names a form would have defined, had the world function it calls at
    # load time been there: their later uses are the world's too.
    world_shadowed: set[str] = set()
    for line in output.splitlines():
        if line.startswith(LOAD_TAG + "-NEEDS "):
            parts = line.split()
            if len(parts) >= 6 and in_world(parts[4], world_defined, world_source):
                world_shadowed.add(parts[5].lower())
        elif line.startswith((LOAD_TAG + "-ERROR ")):
            unbound = WORLD_UNBOUND.search(line)
            if unbound and in_world(unbound.group(2), world_defined, world_source):
                world_shadowed.add(unbound.group(1).lower())
    for line in output.splitlines():
        if not line.startswith(LOAD_TAG + "-"):
            continue
        word, _, rest = line[len(LOAD_TAG) + 1:].partition(" ")
        if word == "DONE":
            completed = True
        elif word == "FILE":
            current = rest.strip()
            counts["files"] += 1
        elif word in ("ERROR", "READ-ERROR"):
            unbound = WORLD_UNBOUND.search(line) if word == "ERROR" else None
            if unbound and in_world(unbound.group(2), world_defined, world_source):
                # A load-time form reads a constant of the certified world
                # (host/native/mux.lisp's +fnn-mux-loops+ is
                # books/profile-limits.lisp's *fn-heap-mux-loops*, lane
                # generators G5): the world's, like a load-time call of it.
                counts["world_calls"] += 1
            else:
                findings.append(f"{word.lower()}: {rest.strip()}")
        elif word == "NEEDS":
            continue  # its CALLED line (printed first) classified the call
        elif word == "CALLED":
            parts = rest.split()
            name = parts[-1] if parts else "?"
            if worlds(name):
                counts["world_calls"] += 1
            else:
                where = (definers or {}).get(name.lower())
                findings.append(f"load-time call of undefined {name.lower()} "
                                f"({' '.join(parts[:2])}), "
                                + (f"defined in {where}, which this build does not load"
                                   if where else "defined nowhere in the tree"))
        elif word == "UNDEFINED":
            kind, _, qualified = rest.strip().partition(" ")
            name = qualified.split()[-1] if qualified.split() else "?"
            if name.lower() in world_shadowed or worlds(name):
                counts["world"] += 1
            else:
                findings.append(nowhere(kind, name, definers))
        elif word == "WARN":
            text = rest.strip()
            lowered = text.lower()
            if lowered.startswith(("undefined function", "undefined variable",
                                   "undefined type", "undefined alien")):
                continue  # the summary of UNDEFINED lines, classified there
            label = next((label for words, label in FAILING_WARNINGS
                          if words in lowered), None)
            if label:
                findings.append(f"{label} (in or before {current}): {text}")
            else:
                counts["warnings"] += 1
    return findings, counts, completed


# --- --load's world (obstructions-6 item 40) ---------------------------------
#
# A bare ACL2 never evaluates the ACL2-mode prefix of the build script: the
# include of books/image-world and the host `ld`s, where definterface checks
# each declaration against the certified world and generates its
# `-by-definition` equations.  decision-keystones-3's `::ideal` declaration of
# five common-lisp-compliant entries passed a bare --load and failed the
# 25-minute hbox image build.  So --load runs the raw files OVER that prefix
# whenever its certificates are here or in the box's certificate cache, and
# says which world it ran in; --bare keeps the seconds-scale check.

WORLD_OK = LOAD_TAG + "-WORLD-OK"
WORLD_LD = LOAD_TAG + "-LD"


def world_prefix(build: str) -> list[object]:
    import host_translate_check
    return host_translate_check.prefix(ROOT / build)


def world_missing(forms: list[object]) -> list[str]:
    import host_translate_check
    return host_translate_check.uncertified(forms)


def world_session(forms: list[object]) -> str:
    """The build's ACL2-mode prefix as a piped session, each `ld` announced so
    an error inside it names its host file, then the world marker."""
    import host_translate_check
    from ledger import head
    lines = []
    for form in forms:
        if head(form) == "ld" and len(form) >= 2 and isinstance(form[1], str):
            lines.append(f'(value-triple (cw "{WORLD_LD} ~s0~%" "{form[1]}"))')
        lines.append(host_translate_check.text(form))
    lines.append(f'(value-triple (cw "{WORLD_OK}~%"))')
    return "\n".join(lines) + "\n"


def world_findings(output: str) -> tuple[list[str], bool]:
    """(the prefix's errors, each naming the host `ld` it was in; did the
    prefix reach its end marker)."""
    import host_translate_check
    findings, current, reached = [], "the include-books", False
    lines = output.splitlines()
    for index, line in enumerate(lines):
        if line.startswith(WORLD_LD + " ") or (WORLD_LD + " ") in line:
            current = line.split(WORLD_LD + " ", 1)[1].strip()
        elif WORLD_OK in line:
            reached = True
            break
        elif any(marker in line for marker in host_translate_check.ERRORS):
            detail = " ".join(part.strip() for part in lines[index:index + 3])
            findings.append(f"world: in {current}: {detail[:400]}")
    return findings, reached


def certificate_cache() -> Path | None:
    """FN_CERT_CACHE, else this box's farm cache, else ~/.cache/fn-certs."""
    candidates = [os.environ.get("FN_CERT_CACHE", "")]
    try:
        import farm
        candidates += [host["cache"] for host in farm.HOSTS.values()]
    except Exception:  # noqa: BLE001  farm imports the world of tools; optional here
        pass
    candidates.append("~/.cache/fn-certs")
    for candidate in candidates:
        if candidate and Path(candidate).expanduser().is_dir():
            return Path(candidate).expanduser()
    return None


def install_world(forms: list[object], acl2: Path, runner=None) -> str:
    """Install the prefix's books from the certificate cache; '' or why not."""
    from ledger import head
    cache = certificate_cache()
    if cache is None:
        return "no certificate cache on this machine (FN_CERT_CACHE unset)"
    roots = [form[1] for form in forms
             if head(form) == "include-book" and len(form) >= 2 and isinstance(form[1], str)]
    argv = [sys.executable, str(ROOT / "tools" / "certs.py"), "--root", str(ROOT),
            "--cache", str(cache), "--acl2", str(acl2), "install-set", *roots]
    if runner is None:
        runner = lambda argv: subprocess.run(argv, cwd=ROOT, capture_output=True, text=True)
    done = runner(argv)
    missing = world_missing(forms)
    if missing:
        tail = " ".join((done.stdout + done.stderr).split()[-30:])
        return (f"{len(missing)} of its books have no certificate here or in {cache} "
                f"(e.g. {missing[0]}; certs.py install-set said: {tail})")
    return ""


def choose_world(build: str, acl2: Path, bare: bool, install: bool = True,
                 runner=None) -> tuple[list[object] | None, str]:
    """(the prefix forms to load first, or None; the sentence naming the world)."""
    if bare:
        return None, "BARE ACL2 (--bare): definterface's checks NOT evaluated"
    forms = world_prefix(build)
    from ledger import head as _head
    if not any(_head(form) == "include-book" for form in forms):
        return None, f"BARE ACL2 -- {build} includes no book (no certified world to load)"
    if world_missing(forms):
        why = install_world(forms, acl2, runner) if install else "certificates not installed"
        if why:
            return None, (f"BARE ACL2 -- the certified umbrella is not available: {why}; "
                          "definterface's checks and the -by-definition equations were "
                          "NOT evaluated")
    from ledger import head
    includes = [form[1] for form in forms if head(form) == "include-book"]
    lds = sum(1 for form in forms if head(form) == "ld")
    return forms, (f"CERTIFIED UMBRELLA -- {', '.join(includes)} and {lds} host lds "
                   f"of {build}, in order (definterface's checks evaluated)")


def load_check(acl2: Path, files: list[str], timeout: int,
               log_dir: Path | None = None, world: list[object] | None = None,
               world_note: str = "BARE ACL2") -> int:
    import tempfile
    with tempfile.TemporaryDirectory(prefix="fn-host-load-") as scratch:
        driver = Path(scratch) / "driver.lsp"
        driver.write_text(load_driver(files), encoding="utf-8")
        session = ((world_session(world) if world is not None else "")
                   + "(defttag :fn-host-load-check)\n"
                   f'(progn! (set-raw-mode t) (load "{driver}"))\n(good-bye)\n')
        started = time.monotonic()
        try:
            result = acl2_slots.run(
                [str(acl2)], "host_check --load", cwd=ROOT, input=session.encode(),
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                timeout=timeout, check=False)
            output = result.stdout.decode("utf-8", "replace")
        except subprocess.TimeoutExpired as error:
            output = (error.output or b"").decode("utf-8", "replace")
            output += f"\n(host_check --load: timed out after {timeout}s)\n"
        elapsed = time.monotonic() - started
    if log_dir is not None:
        (log_dir / "load.log").write_text(output)
    source = world_text()
    findings, counts, completed = classify_load(output, world_names(source), source,
                                                raw_definers())
    if world is not None:
        prefix_findings, reached = world_findings(output)
        findings = prefix_findings + findings
        if not reached:
            findings.insert(0, "world: the build's ACL2-mode prefix did not reach its end "
                               "marker (see the transcript's tail)")
    print(f"host_check --load: WORLD {world_note}")
    for finding in findings:
        print(f"FAIL {finding}")
    if not completed:
        print("FAIL the load did not reach its end marker (ACL2 aborted or timed out); "
              "the transcript's tail:")
        print("\n".join(output.splitlines()[-25:]))
    print(f"host_check --load: {counts['files']} of {len(files)} raw files loaded in one "
          f"{'bare ' if world is None else ''}{acl2.name}"
          f"{'' if world is None else ' over the certified umbrella'} in {elapsed:.1f} s; "
          f"{len(findings)} finding(s); "
          f"{counts['world']} undefined names and {counts['world_calls']} load-time calls "
          f"belong to the certified world"
          f"{' (not loaded here)' if world is None else ''}; {counts['warnings']} other "
          "compiler warnings")
    return 1 if findings or not completed else 0


# --- --tables: unsynchronised global mutable tables ----------------------

TABLE_HEAD = "make-hash-table"
# Forms whose body runs per call: a table made inside one is local to that
# call unless it is assigned to an earmuffed global (checked separately).
LOCAL_HEADS = frozenset({"defun", "defmacro", "defmethod", "lambda", "flet", "labels",
                         "macrolet", "defun-inline", "define-compiler-macro"})
GLOBAL_DEFINERS = frozenset({"defvar", "defparameter", "defglobal",
                             "define-load-time-global"})
ASSIGNERS = frozenset({"setq", "setf", "psetq", "psetf"})
SYNCHRONIZED = re.compile(r":synchronized\s+t(?![\w*+-])", re.IGNORECASE)
CONFINED = re.compile(r";+\s*thread-confined:\s*\S", re.IGNORECASE)
GUARDED = re.compile(r";+\s*guarded-by:\s*([^\s()]+)", re.IGNORECASE)
TOKEN = re.compile(r"[^\s()'`\",;]+")


def _bare(token: str) -> str:
    """TOKEN lower-cased without its package prefix."""
    return token.lower().rsplit(":", 1)[-1]


def table_sites(text: str) -> list[tuple[int, str, bool, str]]:
    """(line, name, synchronized, form text) for each make-hash-table in code
    whose table can outlive one call."""
    import must_fail_check  # the one Lisp comment/string mask in tools/
    mask = must_fail_check.code_mask(text)
    stack: list[tuple[int, str, str]] = []  # (open position, head, second token)
    sites = []
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if not mask[i]:
            i += 1
            continue
        if c == "(":
            head = TOKEN.match(text, i + 1)
            head_s = head.group(0) if head else ""
            second = ""
            if head:
                m = re.compile(r"\s*\(?\s*([^\s()'`\",;]+)").match(text, head.end())
                second = m.group(1) if m else ""
            if _bare(head_s) == TABLE_HEAD:
                depth, j = 0, i
                while j < n:
                    if mask[j] and text[j] == "(":
                        depth += 1
                    elif mask[j] and text[j] == ")":
                        depth -= 1
                        if depth == 0:
                            break
                    j += 1
                form = text[i:j + 1]
                heads = [_bare(h) for _, h, _ in stack]
                parent = stack[-1] if stack else None
                name = None
                if not stack:
                    name = "<top level>"
                elif heads[0] in GLOBAL_DEFINERS:
                    name = stack[0][2]
                elif heads[0] == "defstruct":
                    slot = stack[1][1] if len(stack) > 1 else "?"
                    name = f"{stack[0][2]} slot {slot}"
                elif (parent and _bare(parent[1]) in ASSIGNERS
                      and parent[2].startswith("*") and parent[2].endswith("*")):
                    name = parent[2]
                elif not any(h in LOCAL_HEADS for h in heads):
                    name = f"<top-level {heads[0]}>"
                if name is not None:
                    line = text.count("\n", 0, i) + 1
                    sites.append((line, name, bool(SYNCHRONIZED.search(form)), form))
            stack.append((i, head_s, second))
        elif c == ")" and stack:
            stack.pop()
        i += 1
    return sites


def lock_taken(text: str, lock: str) -> bool:
    """Does a with-mutex / with-recursive-lock in TEXT take LOCK (a variable,
    or an accessor applied to an object)?"""
    return re.search(r"with-(?:mutex|recursive-lock)\s*\(\s*\(?\s*" + re.escape(lock)
                     + r"(?=[\s)])", text, re.IGNORECASE) is not None


def tables_check(files: list[Path], root: Path = ROOT) -> tuple[list[str], list[str]]:
    """(refusals, accepted) over FILES: one line each, file:line name why."""
    refused, accepted = [], []
    for path in files:
        text = path.read_text(encoding="utf-8", errors="replace")
        lines = text.split("\n")
        try:
            rel = path.resolve().relative_to(root).as_posix()
        except ValueError:
            rel = path.as_posix()
        for line, name, synchronized, _ in table_sites(text):
            where = f"{rel}:{line} {name}"
            if synchronized:
                accepted.append(f"{where}: :synchronized t")
                continue
            near = lines[line - 1] + "\n" + (lines[line - 2] if line >= 2 else "")
            guarded = GUARDED.search(near)
            if CONFINED.search(near):
                accepted.append(f"{where}: thread-confined")
            elif guarded and lock_taken(text, guarded.group(1)):
                accepted.append(f"{where}: guarded-by {guarded.group(1)}")
            elif guarded:
                refused.append(f"{where}: guarded-by {guarded.group(1)}, but no "
                               "with-mutex/with-recursive-lock in this file takes it")
            else:
                refused.append(f"{where}: a global hash table that is neither "
                               ":synchronized t nor declared `;; thread-confined: "
                               "<reason>` or `;; guarded-by: <lock>`")
    return refused, accepted


def table_files() -> list[Path]:
    return sorted((ROOT / "host").rglob("*.lisp"))


def tables_main(names: list[str]) -> int:
    files = [Path(name) if Path(name).is_absolute() else ROOT / name for name in names] \
        or table_files()
    refused, accepted = tables_check(files)
    for site in accepted:
        print(f"ok   {site}")
    for site in refused:
        print(f"FAIL {site}")
    print(f"host_check --tables: {len(files)} file(s), {len(accepted) + len(refused)} "
          f"global table(s), {len(refused)} refused")
    return 1 if refused else 0


# --world (lane lane-tools-2, 2026-09-28): the names a raw file hands to the
# image's executable counterparts must be defined in that image's world.
WORLD_BUILDS = ("host/native/build.lisp", "host/native/build-dtn.lisp")
WORLD_CALLERS = {"fnn-call", "fnn-counterpart"}  # and every fnn-core*


def world_caller(name: object) -> bool:
    return isinstance(name, str) and (name in WORLD_CALLERS or name.startswith("fnn-core"))


def world_resolve(root: Path, base: Path, reference: str) -> Path:
    """REFERENCE (an include-book or ld string) as a file under ROOT, relative
    to BASE, the directory ACL2's connected book directory is at."""
    target = base / reference
    if target.suffix != ".lisp":
        target = target.with_name(target.name + ".lisp")
    return Path(os.path.normpath(target))


# --- the ld host files' forward references (item 14, obstructions-3) --------
#
# ACL2 translates each `ld` host file's definitions in the order the image
# `ld`s them, and refuses a call of a function no earlier event defined.
# `--load` loads only the raw files, so twice on 2026-09-29 (online-reclaim-4,
# limits-live-4) a forward reference in host/owner-host.lisp passed it and
# the image build refused it ten minutes later.  This is the static half,
# seconds and no ACL2: every call in an ld host file, in build order, of a
# name that only a LATER top-level form of the ld files defines and no book
# of the image's world defines.  A mutual-recursion (one top-level form) may
# call its own members.  The dynamic half is the default mode (the ld prefix
# through ACL2 in the certified world), which hbox_native runs before it
# builds an image.

def _callers():
    try:
        from tools import callers
    except ImportError:
        import callers
    return callers


def ld_sequence(build: str = BUILD_SCRIPT, root: Path = ROOT) -> list[str]:
    """The ld host files BUILD loads, in its order (an ld inside one in place)."""
    import ledger
    order: list[str] = []

    def walk(form, base: Path) -> None:
        if not isinstance(form, list) or not form or form[0] in ("quote", "quasiquote"):
            return
        if form[0] == "ld" and len(form) >= 2 and isinstance(form[1], str) \
                and not isinstance(form[1], ledger.Sym):
            path = world_resolve(root, base, form[1])
            relative = path.relative_to(root).as_posix() if path.is_relative_to(root) \
                else path.as_posix()
            if relative in order or not path.is_file():
                return
            order.append(relative)
            for inner, _ in ledger.Reader(path.read_text(encoding="utf-8")).top_level():
                walk(inner, path.parent)
            return
        if form[0] in ("defun", "defmacro", "defund", "include-book", "load"):
            return
        for item in form[1:]:
            walk(item, base)

    script = root / build
    for form, _ in ledger.Reader(script.read_text(encoding="utf-8")).top_level():
        walk(form, root)
    return order


def top_level_facts(text: str) -> list[tuple[set[str], list[tuple[str, int]], list[str]]]:
    """Per top-level form of TEXT: the names it defines (at any depth), the
    (name, line) of every call in it (an atom in a list's first position,
    not quoted), and the files it `ld`s, in order."""
    callers = _callers()
    facts: list[tuple[set[str], list[tuple[str, int]], list[str]]] = []
    line, index, depth = 1, 0, 0
    after_open = False
    stack: list[list] = []   # [head, name, position]
    while index < len(text):
        match = callers.TOKEN.match(text, index)
        kind, value, index = match.lastgroup, match.group(), match.end()
        if kind == "nl":
            line += 1
            continue
        if kind in ("comment", "space", "other", "quote", "function"):
            continue
        if kind == "block":
            end = callers.skip_block(text, index)
            line += text.count("\n", index, end)
            index = end
            continue
        if kind in ("string", "char"):
            line += value.count("\n")
            after_open = False
            if stack:
                if (kind == "string" and stack[-1][0] == "ld" and stack[-1][2] == 1
                        and not stack[-1][3]):
                    facts[-1][2].append(value[1:-1])
                stack[-1][2] += 1
            continue
        if kind == "open":
            if not stack:
                facts.append((set(), [], []))
            quoted = text[match.start() - 1:match.start()] in ("'", "`")
            stack.append([None, None, 0, quoted or (bool(stack) and stack[-1][3])])
            after_open = True
            continue
        if kind == "close":
            if stack:
                head, name, _, _ = stack.pop()
                if head in callers.DEFINERS and name and facts:
                    facts[-1][0].add(name)
                if stack:
                    stack[-1][2] += 1
            after_open = False
            continue
        name = callers.bare(value)
        if stack:
            frame = stack[-1]
            if frame[2] == 0:
                frame[0] = name
                if after_open and not frame[3]:
                    facts[-1][1].append((name, line))
            elif frame[2] == 1 and frame[1] is None:
                frame[1] = name
            frame[2] += 1
        after_open = False
    return facts


def forward_references(build: str = BUILD_SCRIPT, root: Path = ROOT) -> list[str]:
    """`FILE:LINE: NAME is called before its definition (FILE:LINE of it)`."""
    callers = _callers()
    book_defined, _, _ = world_of(build, root, ld_definitions=False)
    book_defined = {name.lower() for name in book_defined}
    first: dict[str, tuple[int, str]] = {}      # name -> (form ordinal, file:line)
    per_file = []
    seen: set[str] = set()

    def visit(relative: str) -> None:
        # An `ld` inside a file runs where it stands: its forms come before
        # the rest of the file's (host/native-admin-host.lisp lds owner-host).
        seen.add(relative)
        path = root / relative
        text = path.read_text(encoding="utf-8", errors="replace")
        spans = {}
        for defined, first_line, _ in callers.definitions(text):
            spans.setdefault(defined, first_line)
        for defined, calls, loads in top_level_facts(text):
            ordinal = len(per_file)
            for name in defined:
                first.setdefault(name, (ordinal, f"{relative}:{spans.get(name, '?')}"))
            per_file.append((ordinal, relative, defined, calls))
            for target in loads:
                inner = world_resolve(root, path.parent, target)
                inner_relative = (inner.relative_to(root).as_posix()
                                  if inner.is_relative_to(root) else inner.as_posix())
                if inner.is_file() and inner_relative not in seen:
                    visit(inner_relative)

    for relative in ld_sequence(build, root):
        if relative not in seen:
            visit(relative)
    found = []
    for ordinal, relative, defined, calls in per_file:
        for name, line in calls:
            if name in defined or name in book_defined or name not in first:
                continue
            later, where = first[name]
            if later > ordinal:
                found.append(f"{relative}:{line}: {name} is called before its definition "
                             f"({where}); ACL2 refuses the call when it translates this form")
    return found


def world_of(build: str, root: Path = ROOT,
             ld_definitions: bool = True) -> tuple[set[str], list[str], list[str]]:
    """(defined names, raw files loaded, problems) of BUILD's image.

    The world is every book BUILD includes and everything those books include
    NON-locally, plus each `ld` host file's own definitions and includes
    (resolved from that file's directory, as `ld' binds the connected book
    directory).  A book's local definitions and local includes are not in an
    includer's world and are not counted."""
    import ledger
    defined: set[str] = set()
    problems: list[str] = []
    raw: list[str] = []
    books: list[Path] = []
    seen_books: set[Path] = set()
    seen_lds: set[Path] = set()

    def rel(path: Path) -> str:
        try:
            return path.relative_to(root).as_posix()
        except ValueError:
            return path.as_posix()

    def text(item) -> bool:  # a Lisp string literal, not a symbol
        return isinstance(item, str) and not isinstance(item, ledger.Sym)

    def walk(form, base: Path, where: str) -> None:
        if not isinstance(form, list) or not form:
            return
        head = form[0]
        if head in ("quote", "quasiquote"):
            return
        if head == "include-book" and len(form) >= 2 and text(form[1]):
            if ":dir" not in [str(x) for x in form[2:]]:
                books.append(world_resolve(root, base, form[1]))
            return
        if head == "ld" and len(form) >= 2 and text(form[1]):
            path = world_resolve(root, base, form[1])
            if path in seen_lds:
                return
            seen_lds.add(path)
            if not path.is_file():
                problems.append(f"{where}: ld of {form[1]}, which does not exist")
                return
            host = ledger.analyze_host(path, rel(path))
            if host.read_error:
                problems.append(f"{rel(path)}: unreadable: {host.read_error}")
            if ld_definitions:
                defined.update(host.defines)
            for inner, _ in host.forms:
                walk(inner, path.parent, rel(path))
            return
        if head == "load" and len(form) >= 2 and text(form[1]):
            if (root / form[1]).is_file() and form[1] not in raw:
                raw.append(form[1])
            return
        if head in ("defun", "defmacro", "defund"):
            return
        for item in form[1:]:
            walk(item, base, where)

    script = root / build
    for form, _ in ledger.Reader(script.read_text(encoding="utf-8")).top_level():
        walk(form, root, build)
    while books:
        path = books.pop()
        if path in seen_books:
            continue
        seen_books.add(path)
        if not path.is_file():
            problems.append(f"{build}: includes {rel(path)}, which does not exist")
            continue
        book = ledger.analyze_book(path, rel(path))
        if book.read_error:
            problems.append(f"{rel(path)}: unreadable: {book.read_error}")
        local = {f.name for f in book.functions if f.local}
        defined.update(book.definitions - local)
        defined.update(stobj_names(path))
        for _, reference in book.nonlocal_includes:
            books.append(world_resolve(root, path.parent, reference))
    return defined, raw, problems


def stobj_names(path: Path) -> set[str]:
    """The callable names a `defstobj' / `defabsstobj' / `defevent' introduces
    that the ledger does not record: the exports, creator and recognizer, and a
    concrete stobj's field accessors and updaters (by ACL2's naming)."""
    import ledger
    found: set[str] = set()
    try:
        forms = ledger.Reader(path.read_text(encoding="utf-8")).top_level()
    except ledger.ReadError:
        return found

    def visit(form) -> None:
        if not isinstance(form, list) or not form:
            return
        head = form[0]
        if head in ("defstobj", "defabsstobj") and len(form) >= 2 and isinstance(form[1], str):
            name = str(form[1])
            found.update({name + "p", "create-" + name})
            rest = form[2:]
            for i, item in enumerate(rest):
                if isinstance(item, str) and item.startswith(":"):
                    value = rest[i + 1] if i + 1 < len(rest) else None
                    if item in (":recognizer", ":creator") and isinstance(value, list) and value:
                        found.add(str(value[0]))
                    elif item == ":exports" and isinstance(value, list):
                        for spec in value:
                            if isinstance(spec, list) and spec:
                                found.add(str(spec[0]))
                            elif isinstance(spec, str):
                                found.add(spec)
                    elif item == ":renaming" and isinstance(value, list):
                        for pair in value:
                            if isinstance(pair, list) and len(pair) == 2:
                                found.add(str(pair[1]))
                elif isinstance(item, list) and item and head == "defstobj":
                    field = str(item[0])
                    found.update({field, "update-" + field, field + "p",
                                  field + "-length", "resize-" + field,
                                  field + "i", "update-" + field + "i"})
            return
        if head == "defevent" and len(form) >= 2:
            # books/defevent.lisp (lane generators G6): the encoder, the
            # decoder and the recognizer it names are defuns it expands to.
            rest = form[2:]
            for i, item in enumerate(rest[:-1]):
                if item in (":encode", ":decode", ":recognizer") and \
                        isinstance(rest[i + 1], str):
                    found.add(str(rest[i + 1]))
            return
        if head in ("local",):
            return
        for item in form[1:]:
            visit(item)

    for form, _ in forms:
        visit(form)
    return found


def world_sites(path: Path) -> tuple[list[tuple[int, str]], int]:
    """([(line, name)], dynamic): every quoted name a `fnn-core*'/`fnn-call'
    form in PATH passes as the counterpart to run, and the number of calls
    whose name is computed (a variable: not checkable here).  The wrappers
    themselves (a definition of a caller) are skipped."""
    import ledger
    text = path.read_text(encoding="utf-8")
    lines = text.split("\n")
    sites: list[tuple[int, str]] = []
    dynamic = 0

    def quoted(form) -> list[str]:
        if isinstance(form, list) and len(form) == 2 and form[0] == "quote" \
                and isinstance(form[1], str) and not isinstance(form[1], list):
            return [str(form[1])] if isinstance(form[1], ledger.Sym) else []
        if isinstance(form, list):
            out: list[str] = []
            for item in form:
                out += quoted(item)
            return out
        return []

    def locate(name: str, start: int) -> int:
        pattern = re.compile(r"'" + re.escape(name) + r"(?![\w*+$<>=/-])", re.IGNORECASE)
        for number in range(start, len(lines)):
            if pattern.search(lines[number]):
                return number + 1
        return start + 1

    def visit(form, line: int) -> None:
        nonlocal dynamic
        if not isinstance(form, list) or not form:
            return
        head = form[0]
        if head == "quote":
            return
        if head in ("defun", "defmacro") and len(form) >= 2 and world_caller(form[1]):
            return
        if world_caller(head) and len(form) >= 2:
            names = quoted(form[1])
            if not names:
                dynamic += 1
            for name in names:
                sites.append((locate(name, line - 1), name))
        for item in form[1:]:
            visit(item, line)

    for form, line in ledger.Reader(text).top_level():
        visit(form, line)
    return sites, dynamic


def world_check(builds=WORLD_BUILDS, root: Path = ROOT) -> tuple[list[str], list[str]]:
    """(refusals, notes): each counterpart name a raw file of BUILD passes to
    `fnn-core'/`fnn-call' that BUILD's world does not define, by file:line."""
    import build_lists_check
    # The DTN image omits host files by declaration, each name it cannot
    # reach with its reason (tools/build_lists_check.py DTN_OMITTED, which
    # `make check' holds to "still omitted, still reached"); that register is
    # read here, not a second list kept.
    dtn_excused = {name: reason for _, (_, names) in build_lists_check.DTN_OMITTED.items()
                   for name, reason in names.items()}
    refused: list[str] = []
    notes: list[str] = []
    for build in builds:
        defined, raw, problems = world_of(build, root)
        refused += [f"{build}: {problem}" for problem in problems]
        excused = dtn_excused if build == build_lists_check.DTN_BUILD else {}
        checked = dynamic = waived = 0
        for name in raw:
            sites, computed = world_sites(root / name)
            dynamic += computed
            for line, symbol in sites:
                checked += 1
                if symbol not in defined and symbol in excused:
                    waived += 1
                elif symbol not in defined:
                    refused.append(f"{name}:{line} {symbol}: {build}'s image world does not "
                                   "define it (no book the build includes, no ld host file); "
                                   "the counterpart is missing at run time")
        notes.append(f"{build}: {len(raw)} raw file(s), {checked} named counterpart(s) "
                     f"checked against {len(defined)} world name(s); {dynamic} computed "
                     "name(s) not checkable statically"
                     + (f"; {waived} unreachable in this image by build_lists_check's "
                        "DTN_OMITTED" if waived else ""))
    return refused, notes


def world_main(builds: list[str]) -> int:
    refused, notes = world_check(tuple(builds) or WORLD_BUILDS)
    for note in notes:
        print(f"host_check --world: {note}")
    for line in refused:
        print(f"FAIL {line}")
    print(f"host_check --world: {len(refused)} refused")
    return 1 if refused else 0


def build_order_main(timeout: int) -> int:
    """Each image's ACL2-mode prefix in its build order (host_translate_check):
    0 all translated, 1 an ACL2 error in any, else 2 NOT RUN."""
    codes = []
    for build in WORLD_BUILDS:
        result = subprocess.run(
            [sys.executable, str(ROOT / "tools/host_translate_check.py"), "--build", build,
             "--timeout", str(timeout),
             "--log", f"build/host-translate/{Path(build).stem}.log"],
            cwd=ROOT)
        codes.append(result.returncode)
        verdict = {0: "ok", 1: "FAIL", 2: "NOT RUN"}.get(result.returncode,
                                                         f"exit {result.returncode}")
        print(f"host_check: {verdict} {build} (its include-books and host lds, in order)")
    if any(code == 1 for code in codes):
        return 1
    return 0 if all(code == 0 for code in codes) else 2


def world_stale(runner=None) -> list[str]:
    """tools/extract/world.py --check's findings (the umbrellas books/image-world*
    against what the build scripts include), printed as FAIL lines.

    `--load` runs it (obstructions-5 item 34): limits-live-5's host
    include-book passed --load and died in the image build's acquire step
    (FN_IMAGE_WORLD_OPEN) because the umbrellas were not regenerated.
    """
    if runner is None:
        def runner():
            done = subprocess.run([sys.executable, str(ROOT / "tools/extract/world.py"),
                                   "--check"], cwd=ROOT, capture_output=True, text=True)
            return done.returncode, done.stdout + done.stderr
    code, output = runner()
    found = [line.strip() for line in output.splitlines() if line.strip()] if code else []
    for line in found:
        print(f"FAIL {line}")
    print(f"host_check --load: world.py --check "
          + ("current" if not found else f"STALE ({len(found)}): run python3 tools/extract/world.py"))
    return found


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("files", nargs="*",
                        help="host files to check (default: every one)")
    parser.add_argument("--timeout-seconds", type=int, default=DEFAULT_TIMEOUT_SECONDS)
    parser.add_argument("--log-dir", default=None,
                        help="write each session's transcript here")
    parser.add_argument("--load", action="store_true",
                        help="load the raw host/native files in the build's order into one "
                             "bare ACL2 and report errors, arity, macro order and names "
                             "nothing defines (seconds; no image build).  Requires FN_ACL2 "
                             "(or acl2 on PATH): exit 2 NOT RUN without it")
    parser.add_argument("--tables", action="store_true",
                        help="static: refuse a global make-hash-table in host/ that is "
                             "neither :synchronized t nor declared thread-confined or "
                             "guarded-by a lock (no ACL2)")
    parser.add_argument("--alone", action="store_true",
                        help="load each FILE (default: every host file) alone in its own "
                             "ACL2: a diagnosis, not the gate (build order is the gate)")
    parser.add_argument("--world", action="store_true",
                        help="static: every name a raw host/native file passes to fnn-core* "
                             "or fnn-call is defined in the world of the image that loads it "
                             "(build.lisp, build-dtn.lisp; FILEs name other build scripts)")
    parser.add_argument("--forward", action="store_true",
                        help="static: a call in an ld host file of a name only a later "
                             "form of the ld files defines (no ACL2; --load runs it too)")
    parser.add_argument("--build", default=None,
                        help="with --load: the build script whose raw load order to use")
    parser.add_argument("--bare", action="store_true",
                        help="with --load: a bare ACL2 (seconds), not the build's "
                             "certified prefix; definterface's checks are NOT evaluated")
    parser.add_argument("--require-world", action="store_true",
                        help="with --load: exit 2 NOT RUN when the certified umbrella is "
                             "not available, rather than falling back to a bare ACL2")
    args = parser.parse_args(argv)

    if args.tables:
        return tables_main(args.files)
    if args.world:
        return world_main(args.files)
    if args.forward or args.load:
        forward = []
        for build in ([args.build] if args.build else WORLD_BUILDS):
            forward += [one for one in forward_references(build) if one not in forward]
        for one in forward:
            print(f"FAIL {one}")
        print(f"host_check --forward: {len(forward)} forward reference(s) in the ld host "
              "files, in build order")
        if args.forward:
            return 1 if forward else 0
    stale = world_stale() if args.load else []
    acl2 = executable()
    if args.load:
        if acl2 is None:
            found = shutil.which("acl2")
            acl2 = Path(found).resolve() if found else None
        if acl2 is None:
            print("host_check --load: NOT RUN -- no ACL2 (FN_ACL2 unset and no acl2 on "
                  "PATH).  Set FN_ACL2 to the ACL2 executable (on hbox and persvati "
                  "/tank/fn/toolchains/w28/acl2-literal-4g-tls64k); make check "
                  "counts this as a failed step", file=sys.stderr)
            return 2
        order = raw_load_order(args.build or BUILD_SCRIPT)
        unknown = [name for name in args.files if name not in order]
        if unknown:
            print("host_check --load: not loaded by " + (args.build or BUILD_SCRIPT) + ": " + ", ".join(unknown),
                  file=sys.stderr)
            return 2
        # A raw file needs the ones before it: FILEs load the order through
        # the last of them.
        last = max((order.index(name) for name in args.files), default=len(order) - 1)
        files = order[:last + 1]
        log_dir = Path(args.log_dir).resolve() if args.log_dir else None
        if log_dir is not None:
            log_dir.mkdir(parents=True, exist_ok=True)
        build = args.build or BUILD_SCRIPT
        world, note = choose_world(build, acl2, args.bare)
        if world is None and args.require_world and not args.bare:
            print(f"host_check --load: NOT RUN -- {note}", file=sys.stderr)
            return 2
        if world is not None and os.environ.get("FN_IMAGE_ACL2"):
            # The image's launcher (tls64k): the production prefix exhausts
            # SBCL's default thread-local storage (host_translate_check).
            image = Path(os.environ["FN_IMAGE_ACL2"])
            if image.is_file():
                acl2 = image
        loaded = load_check(acl2, files, args.timeout_seconds, log_dir, world, note)
        return 1 if (forward or stale) and loaded == 0 else loaded
    if not args.alone:
        if args.files:
            print("host_check: FILEs without a mode: use --alone FILE... (a diagnosis) "
                  "or --load FILE... (build order)", file=sys.stderr)
            return 2
        return build_order_main(args.timeout_seconds)
    if acl2 is None:
        print("host_check --alone: NOT RUN -- FN_ACL2 is unset or does not name an "
              "executable, so no host file was loaded.", file=sys.stderr)
        return 2

    raw = raw_files()
    targets = args.files or host_files()
    log_dir = Path(args.log_dir).resolve() if args.log_dir else None
    if log_dir is not None:
        log_dir.mkdir(parents=True, exist_ok=True)

    failures: list[tuple[str, str]] = []
    checked = 0
    for relative in targets:
        if relative == BUILD_SCRIPT:
            print(f"skip     {relative} -- image build script, ends in `:q` and "
                  "`save-exec`; tools/build_native_host.sh is its check")
            continue
        checked += 1
        ok, reason, output = check(acl2, relative, relative in raw, args.timeout_seconds)
        if log_dir is not None:
            (log_dir / (relative.replace("/", "_") + ".log")).write_text(output)
        kind = "raw " if relative in raw else "ld  "
        print(f"{'ok  ' if ok else 'FAIL'} {kind}{relative}" + ("" if ok else f" -- {reason}"))
        if not ok:
            failures.append((relative, reason))
            tail = "\n".join(output.splitlines()[-25:])
            print(tail, file=sys.stderr)
    print(f"host_check: {checked - len(failures)}/{checked} host files load "
          f"alone with {acl2}")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
