#!/usr/bin/env python3
"""Load each host file alone, in its own ACL2, and require it to succeed.

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

What it cannot see: the arity of a call into a book function (the bare image
does not know it), anything the FFI initializers do (`fnn-crypto-initialize'
and its siblings are build.lisp's calls, not the files'), and translate
errors in the ACL2-mode host files (tools/host_translate_check.py).  Exit 0
clean, 1 with each finding named, 2 NOT RUN (no ACL2).

    python3 tools/host_check.py --load [--build host/native/build-dtn.lisp] [FILE ...]

with FILEs, the order is loaded through the last of them.
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


def classify_load(output: str, world_defined: set[str], world_source: str,
                  definers: dict[str, str] | None = None
                  ) -> tuple[list[str], dict[str, int], bool]:
    """(findings, counts, completed) from a --load transcript."""
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
            findings.append(f"{word.lower()}: {rest.strip()}")
        elif word == "NEEDS":
            continue  # its CALLED line (printed first) classified the call
        elif word == "CALLED":
            parts = rest.split()
            name = parts[-1] if parts else "?"
            if in_world(name, world_defined, world_source):
                counts["world_calls"] += 1
            else:
                findings.append(f"load-time call of undefined {name.lower()} "
                                f"({' '.join(parts[:2])}), defined nowhere in the tree")
        elif word == "UNDEFINED":
            kind, _, qualified = rest.strip().partition(" ")
            name = qualified.split()[-1] if qualified.split() else "?"
            if name.lower() in world_shadowed or in_world(name, world_defined, world_source):
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


def load_check(acl2: Path, files: list[str], timeout: int,
               log_dir: Path | None = None) -> int:
    import tempfile
    with tempfile.TemporaryDirectory(prefix="fn-host-load-") as scratch:
        driver = Path(scratch) / "driver.lsp"
        driver.write_text(load_driver(files), encoding="utf-8")
        session = ("(defttag :fn-host-load-check)\n"
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
    for finding in findings:
        print(f"FAIL {finding}")
    if not completed:
        print("FAIL the load did not reach its end marker (ACL2 aborted or timed out); "
              "the transcript's tail:")
        print("\n".join(output.splitlines()[-25:]))
    print(f"host_check --load: {counts['files']} of {len(files)} raw files loaded in one "
          f"bare {acl2.name} in {elapsed:.1f} s; {len(findings)} finding(s); "
          f"{counts['world']} undefined names and {counts['world_calls']} load-time calls "
          f"belong to the certified world (not loaded here); {counts['warnings']} other "
          "compiler warnings")
    return 1 if findings or not completed else 0


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
                             "nothing defines (seconds; no image build)")
    parser.add_argument("--build", default=BUILD_SCRIPT,
                        help="with --load: the build script whose raw load order to use")
    args = parser.parse_args(argv)

    acl2 = executable()
    if args.load:
        if acl2 is None:
            found = shutil.which("acl2")
            acl2 = Path(found).resolve() if found else None
        if acl2 is None:
            print("host_check --load: NOT RUN -- no ACL2 (FN_ACL2 unset and no acl2 on "
                  "PATH)", file=sys.stderr)
            return 2
        order = raw_load_order(args.build)
        unknown = [name for name in args.files if name not in order]
        if unknown:
            print("host_check --load: not loaded by " + args.build + ": " + ", ".join(unknown),
                  file=sys.stderr)
            return 2
        # A raw file needs the ones before it: FILEs load the order through
        # the last of them.
        last = max((order.index(name) for name in args.files), default=len(order) - 1)
        files = order[:last + 1]
        log_dir = Path(args.log_dir).resolve() if args.log_dir else None
        if log_dir is not None:
            log_dir.mkdir(parents=True, exist_ok=True)
        return load_check(acl2, files, args.timeout_seconds, log_dir)
    if acl2 is None:
        # Loudly, not silently: an unset FN_ACL2 is a check that did not run.
        print("host_check: SKIPPED -- FN_ACL2 is unset or does not name an "
              "executable, so no host file was loaded.  This check is not "
              "evidence until it runs with a real ACL2.", file=sys.stderr)
        return 0

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
