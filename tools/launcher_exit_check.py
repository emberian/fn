#!/usr/bin/env python3
"""Every launcher path classifies a child's failure; none forwards it as a refusal.

AGENTS.md: "Uncertain, refused and accepted stay distinct at every boundary,
exit codes and test expectations included."  fn's exit codes are ACL2's
(books/outcome-class.lisp): 0 accepted, 1 refused, 3 uncertain, 4 fault,
5 usage.  A launcher that runs a child and passes the child's status on
unread breaks that: a runtime that never reached ACL2 exits with ITS OWN
code, and 1 -- SBCL's code for "the core would not map" -- reads as ACL2's
refusal.  Lane openbsd-datasize found exactly that (fb12148f8): under a
datasize limit below the image's own mappings the heap probe died with
ENOMEM, exit 1, and packaging/fn's `[ "$status" -eq 0 ] || exit "$status"'
told the operator "refused".

The rule, with no waivers: every exit site that follows a child is a known
classification.

  shell (every `#!/bin/sh' launcher in packaging/)
    * `exit "$S"' / `exit $?' / `return $S', where S holds a child's status
      (`S=$?', `|| S=$?'), is refused unless it sits in a `case' arm whose
      pattern names the child's decision (`refused\\ *)'): the child said
      what it decided, so its code is its classification.  A bare `*)' arm
      is not a decision.
    * `|| exit 1' (or `|| { ...; exit 1; }') after a command, and `exit 1'
      in the `||' / `then' of a test on a status variable, map the child's
      unknown failure to the refusal code.  Refused.
  raw Lisp (every host/**/*.lisp, read with tools/ledger.py's non-evaluating
  reader)
    * a STATUS SOURCE is `(sb-ext:process-exit-code ...)', or a call of a
      function whose tail returns one (transitively).  Each status source
      outside a status function's tail must be a `let'/`let*' binding
      whose variable a `cond' in the binding's body classifies, and the
      cond's UNKNOWN arm -- the first clause that is `t' or tests only
      "not success" (`(not (eql v 0))', `(/= v 0)', `(plusp v)', `(not
      (zerop v))') -- must not refuse (`fnn-refuse', `+fnn-exit-refused+',
      the literal 1).  A fault or an uncertain outcome is a classification;
      a refusal is ACL2's word and no child's crash earns it.

Output: one line per refusal, `FILE:LINE: reason'.  Exit 0 clean, 1 refused.

What it cannot see: `exec' hands the process to the image, so the image's
own runtime failure after the launcher is gone (an ENOMEM mapping the main
heap after the probe succeeded) is the runtime's exit code; a Python tool
that forwards an fn client's return code (tools/fn_agent.py) is not a
launcher of the image and is not read here.

    python3 tools/launcher_exit_check.py [FILE ...]
"""
from __future__ import annotations

import argparse
from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import ledger  # noqa: E402
from ledger import Sym, head  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]

# ---------------------------------------------------------------- shell ----

STATUS_ASSIGN = re.compile(r"\b([A-Za-z_][A-Za-z0-9_]*)=\$\?")
FORWARD = re.compile(r"\b(?:exit|return)\s+\"?\$(?:\{)?([A-Za-z_][A-Za-z0-9_]*|\?)\}?\"?")
OR_EXIT_ONE = re.compile(r"\|\|\s*(?:\{[^}]*;\s*)?exit\s+1\b")
EXIT_ONE = re.compile(r"\bexit\s+1\b")
CASE_OPEN = re.compile(r"^\s*case\b.*\bin\s*$")
CASE_ARM = re.compile(r"^\s*([^()#]*?)\)(?!\))")


def shell_launchers(root: Path = ROOT) -> list[Path]:
    """packaging/'s shell scripts, a symlink read once (fn-native -> fn)."""
    found, seen = [], set()
    for path in sorted((root / "packaging").iterdir()):
        if not path.is_file():
            continue
        real = path.resolve()
        if real in seen:
            continue
        try:
            first = path.read_text(encoding="utf-8", errors="replace").split("\n", 1)[0]
        except OSError:
            continue
        if first.startswith("#!") and re.search(r"\b(?:sh|bash|ksh|dash)\b", first):
            seen.add(real)
            found.append(path)
    return found


def strip_comment(line: str) -> str:
    """The line without a trailing `# comment' (quotes respected)."""
    quote = None
    for i, c in enumerate(line):
        if quote:
            if c == quote:
                quote = None
        elif c in "'\"":
            quote = c
        elif c == "#" and (i == 0 or line[i - 1].isspace()):
            return line[:i]
    return line


def shell_check(path: Path, relative: str) -> list[str]:
    refused: list[str] = []
    statuses: set[str] = set()
    # One entry per open `case': the pattern of the arm we are in, or None
    # between `in' and the first arm.
    arms: list[str | None] = []
    for number, raw in enumerate(path.read_text(encoding="utf-8", errors="replace").splitlines(), 1):
        line = strip_comment(raw)
        if not line.strip():
            continue
        statuses |= set(STATUS_ASSIGN.findall(line))
        body = line
        if CASE_OPEN.match(line):
            arms.append(None)
            continue
        if re.match(r"^\s*esac\b", line):
            if arms:
                arms.pop()
            continue
        if arms:
            arm = CASE_ARM.match(line)
            if arm and not re.match(r"^\s*(?:if|while|until|for)\b", line):
                arms[-1] = arm.group(1).strip()
                body = line[arm.end():]
        where = f"{relative}:{number}"
        for match in FORWARD.finditer(body):
            name = match.group(1)
            if name != "?" and name not in statuses:
                continue
            arm = arms[-1] if arms else None
            if arm is None or arm.strip() in ("*", "''|*", ""):
                refused.append(
                    f"{where}: forwards the child's status ${name} unclassified: a child "
                    f"that never reached its decision (SBCL's own exit 1 under ENOMEM) "
                    f"would read as refused; classify it (a decision arm) or report a "
                    f"fault, exit 4")
        if OR_EXIT_ONE.search(body):
            refused.append(f"{where}: `|| exit 1' maps a child's unknown failure to the "
                           f"refusal code; an unknown failure is a fault, exit 4")
        elif EXIT_ONE.search(body) and any(
                re.search(r"\$\{?" + re.escape(s) + r"\b", body) for s in statuses | {"?"}):
            refused.append(f"{where}: exit 1 on a child's status: a refusal is the "
                           f"child's decision, never the launcher's reading of a failure")
    return refused


# ----------------------------------------------------------------- lisp ----

SOURCE_HEADS = {"sb-ext:process-exit-code", "process-exit-code"}
REFUSAL = {"fnn-refuse", "+fnn-exit-refused+"}
BINDERS = {"let", "let*"}


def lisp_files(root: Path = ROOT) -> list[Path]:
    return sorted((root / "host").rglob("*.lisp"))


def definitions(forms: list) -> list[tuple[str, list, int]]:
    """(name, body forms, line) of every defun, through progn-like wrappers."""
    out = []

    def visit(form, line):
        name = head(form)
        if name in ("progn", "progn!", "eval-when", "local", "when", "unless"):
            for item in form[1:]:
                visit(item, line)
        elif name in ("defun", "defmacro") and len(form) >= 4 and isinstance(form[1], Sym):
            out.append((str(form[1]), list(form[3:]), line))

    for form, line in forms:
        visit(form, line)
    return out


def tails(body: list) -> list:
    """The forms whose value is the body's value."""
    if not body:
        return []
    last = body[-1]
    name = head(last)
    if name in BINDERS and len(last) >= 3:
        return tails(list(last[2:]))
    if name in ("progn", "unwind-protect", "prog1"):
        return tails([last[1]] if name in ("unwind-protect", "prog1") else list(last[1:]))
    return [last]


def is_source(form, sources: set[str]) -> bool:
    return isinstance(form, list) and bool(form) and head(form) in sources


def status_functions(defs) -> set[str]:
    sources = set(SOURCE_HEADS)
    while True:
        more = {name for name, body, _ in defs
                if name not in sources and any(is_source(t, sources) for t in tails(body))}
        if not more:
            return sources
        sources |= more


def unknown_arm_test(test, var: str) -> bool:
    if test == Sym("t"):
        return True
    if not isinstance(test, list) or not test:
        return False
    h = head(test)
    if h == "not" and len(test) == 2 and isinstance(test[1], list):
        inner = test[1]
        if head(inner) in ("eql", "=", "equal", "eq") and var in inner[1:] and 0 in inner[1:]:
            return True
        if head(inner) == "zerop" and inner[1:] == [var]:
            return True
    if h == "/=" and var in test[1:] and 0 in test[1:]:
        return True
    if h == "plusp" and test[1:] == [var]:
        return True
    return False


def mentions(form, names: set[str]) -> bool:
    if isinstance(form, Sym):
        return str(form) in names
    if isinstance(form, list):
        return any(mentions(item, names) for item in form)
    return False


def refuses(forms) -> bool:
    for form in forms:
        if form == 1 or mentions(form, REFUSAL):
            return True
    return False


def classification(body: list, var: str) -> str | None:
    """None when a cond in BODY classifies VAR with a non-refusing unknown
    arm; else the reason it does not."""
    found = [None]

    def visit(form):
        if not isinstance(form, list):
            return
        if head(form) == "cond" and any(isinstance(c, list) and c and mentions(c[0], {var})
                                        for c in form[1:]):
            for clause in form[1:]:
                if isinstance(clause, list) and clause and unknown_arm_test(clause[0], var):
                    found[0] = found[0] or ("refused" if refuses(clause[1:]) else "ok")
                    return
            found[0] = found[0] or "no-unknown-arm"
            return
        for item in form:
            visit(item)

    for form in body:
        visit(form)
    verdict = found[0]
    if verdict == "ok":
        return None
    if verdict == "refused":
        return "its unknown arm refuses: a child's unclassified failure is a fault or uncertain, never refused"
    if verdict == "no-unknown-arm":
        return "the cond that reads it has no arm for an unknown nonzero status"
    return "no cond classifies it"


def lisp_check(path: Path, relative: str, sources: set[str] | None = None) -> list[str]:
    try:
        forms = ledger.Reader(path.read_text(encoding="utf-8")).top_level()
    except ledger.ReadError as exc:
        return [f"{relative}:1: unreadable: {exc}"]
    defs = definitions(forms)
    sources = status_functions(defs) if sources is None else sources
    refused: list[str] = []

    def walk(form, line, allowed: set[int]):
        if not isinstance(form, list) or not form:
            return
        if head(form) == "quote":
            return
        if head(form) in BINDERS and len(form) >= 3 and isinstance(form[1], list):
            for binding in form[1]:
                if (isinstance(binding, list) and len(binding) == 2
                        and isinstance(binding[0], Sym) and is_source(binding[1], sources)):
                    reason = classification(list(form[2:]), str(binding[0]))
                    if reason:
                        refused.append(f"{relative}:{line}: the status of "
                                       f"({head(binding[1])} ...) bound to {binding[0]}: {reason}")
                    allowed = allowed | {id(binding[1])}
        if is_source(form, sources) and id(form) not in allowed:
            refused.append(f"{relative}:{line}: ({head(form)} ...) used unclassified: bind it "
                           f"and classify it in a cond whose unknown arm is a fault or uncertain")
        for item in form:
            walk(item, line, allowed)

    for form, line in forms:
        name = head(form)
        tail_ids: set[int] = set()
        if name in ("defun", "defmacro") and len(form) >= 4:
            tail_ids = {id(t) for t in tails(list(form[3:])) if is_source(t, sources)}
        walk(form, line, tail_ids)
    return refused


def check(files: list[Path] | None = None) -> list[str]:
    shells = shell_launchers() if files is None else [p for p in files if p.suffix != ".lisp"]
    lisps = lisp_files() if files is None else [p for p in files if p.suffix == ".lisp"]
    refused: list[str] = []
    for path in shells:
        refused += shell_check(path, rel(path))
    # Status functions are named across files: one file's wrapper is
    # another's source.
    parsed = []
    for path in lisps:
        try:
            parsed += definitions(ledger.Reader(path.read_text(encoding="utf-8")).top_level())
        except ledger.ReadError:
            pass
    sources = status_functions(parsed)
    for path in lisps:
        refused += lisp_check(path, rel(path), sources)
    return refused


def rel(path: Path) -> str:
    try:
        return path.resolve().relative_to(ROOT).as_posix()
    except ValueError:
        return str(path)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("files", nargs="*", type=Path,
                        help="shell launchers and .lisp files (default: packaging/ and host/)")
    arguments = parser.parse_args(argv)
    refused = check(arguments.files or None)
    for line in refused:
        print(line)
    scope = "the named files" if arguments.files else "packaging/ launchers and host/"
    print(f"launcher_exit_check: {len(refused)} unclassified child-status path(s) in {scope}")
    return 1 if refused else 0


if __name__ == "__main__":
    sys.exit(main())
