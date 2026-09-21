#!/usr/bin/env python3
"""Find the repository paths this tree cites that no file in it answers.

On 2026-09-21 a lane reading `books/stx-lace.lisp` for an unrelated reason
found that its header said `books/stx-transit.lisp` "names the composition and
proves it satisfies the predicate", and that `tests/acl2/stx-lace-tests.lisp`
"exhibits a run where it holds".  Neither file has ever existed on any ref of
this repository.  `books/stx-policy.lisp` cited the same absent book for a
theorem-subject obligation.  So `fn-stx-acceptedp` was an assumption wearing a
citation, and four keystones that hypothesise it were preservation under a
hypothesis nothing established.  Nothing in the tree could have caught that:
`tools/ledger.py` reads the forms a book DEFINES, and a citation lives in the
prose around them.

So this tool reads the prose.  It finds every token shaped like a path into
this repository, in every tracked text file, and reports the ones no file
answers.  It separates the two questions a reader of such a report has:

  * WHERE is the citation?  A citation inside `books/` or `tests/acl2/` is a
    claim about EVIDENCE, made where a reader is deciding whether to trust a
    theorem; it is reported as LOAD-BEARING.  The same token in `planning/` is
    a stale handoff.  A spec is in between: it is a design the tree owes.
  * HAS the target EVER existed?  `git log --all` answers this mechanically.
    A path with history is DRIFT -- something was renamed, folded or removed
    and the citation was not updated, and the repair is a new path.  A path
    with no history anywhere is a PHANTOM: the citation was written for a file
    that was never written, and there is nothing to point it at.

A third class is neither: ANNOTATED, a citation whose own prose says the file
is not there and what that means, or where it went.  When there is nothing to
point at, that disclosure IS the repair AGENTS.md asks for -- the claim is not
deleted to make the citation go away -- and `make check` counts them rather
than raising them, so the number of disclosed gaps stays readable.

This is a report.  It prints counts and a list; it never prints a verdict of
correctness, and the spec, tool and planning counts are reported, not failed.
`--strict` fails on an undisclosed load-bearing finding, and `make check`
passes it because this tree has none: see the Makefile.

WHY NOT A `ledger.py` LINT.  The ledger's docstring promises that "nothing is
interned, evaluated, or macro-expanded, so reading a book cannot run a book",
and a text scan would keep that promise.  Two other things decide it.  The
ledger's subject is the s-expressions of `books/`, `tests/acl2/` and the
`ld`ed host files, and its `--check` is a gate that FAILS; more than half of
what this tool reads -- `specs/`, `docs/`, `planning/`, `tools/`, the Makefile
-- it never opens, and the answer here is a count, not a gate.  Folding a
whole-tree text sweep into a 2300-line book reader would have made the ledger
two tools sharing a file.  `tools/teeth_check.py`, `tools/transcribe_check.py`
and `tools/session_depth.py` are the precedent: one question, one file, wired
into `make check` beside the ledger.

    python3 tools/cite_check.py              # the report `make check` prints
    python3 tools/cite_check.py --all        # every class, including benign
    python3 tools/cite_check.py --json
    python3 tools/cite_check.py --strict     # fail on an undisclosed one

WHAT IT CANNOT SEE.  Every line below is a question for a reader.

* It checks that a path EXISTS.  It cannot check that the file says what the
  citation says it says: `books/stx-policy.lisp` could have cited a book that
  exists and does not contain the named theorem, and this tool would be
  silent.  `tools/teeth_check.py` checks cited THEOREM names; nothing checks a
  cited section number, a line number, or a claim about a file's contents.
* "Ever existed" is `git log --all` in the worktree it runs in.  A path on a
  branch this checkout has never fetched reads as a phantom, and a path that
  existed only inside an uncommitted working tree reads as a phantom too.
* A phantom in a spec is usually deliberate -- a design names the book a
  packet will add.  The tool marks such a line `forward?` when it carries a
  word like "proposed" or "new", and that mark is a hint from one regex, not
  a judgement.  A forward-looking citation in a `books/` source is not
  forward-looking; it is a claim about evidence that is not there.
* PHANTOM is a fact about the PATH, not about the work.  `books/tcpcl.lisp`
  was a phantom while the convergence layer it names was certified, under
  four other names.  The tool compares paths; only a reader can say whether
  the deliverable landed.
* It does not read `build/`.  A lane worktree is not a repository path: it is
  gitignored, it is removed when the lane lands, and a citation of one
  (`build/lanes/w3-native-host/host/native/io.lisp`) is stale by design.
* ANNOTATED is a regex over the prose around the citation.  A comment that
  says "never existed" silences the raise, so the class is a convention held
  by review, not a proof; the count is printed for exactly that reason.
* It reads tokens, not sentences.  A citation spelled in prose ("the transit
  book"), split across a line break, or given only by theorem name is
  invisible to it.
* The fixture, record and catalogue classes are exclusions with reasons, not
  proofs of innocence: a genuine stale citation inside a unit test's fixture
  data, inside an evidence record, or inside this file is classed with them
  and not raised.  The tree's number is the same before and after this tool
  was tracked, which is the point of the catalogue list and its only defence.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

# The tracked top-level names a citation can start with.  A token that starts
# with anything else is not a path into this repository.
TOPS = ("books", "tests", "tools", "specs", "docs", "host", "planning",
        "packaging", "bin")

TOKEN = re.compile(
    r"(?<![\w./-])((?:" + "|".join(TOPS) + r")/[A-Za-z0-9_.*<>{}?%/-]+)")

# Extensions a citation can name and the tree can answer.
SOURCE_EXTENSIONS = (".lisp", ".py", ".md", ".json", ".txt", ".sh", ".lsp",
                     ".acl2", ".toml", ".cfg", ".yaml", ".yml", ".service",
                     ".csv", ".html", ".mk", ".conf")
# Extensions naming a file a run PRODUCES.  `books/wire.cert` is answered by
# `books/wire.lisp`; certificates are gitignored and a checkout has none.
PRODUCED_EXTENSIONS = (".cert", ".port", ".fasl", ".log", ".out", ".certdep",
                       ".lx64fsl", ".dx64fsl")
# What an extensionless citation can mean: a book root, a Python module, a
# document.  `books/wire` is the Makefile's spelling of `books/wire.lisp`.
IMPLIED_EXTENSIONS = ("", ".lisp", ".py", ".md")

PLACEHOLDER_CHARS = set("*<>{}?%")

# The Python unit tests of `tools/`.  Every one builds a tree in a
# `TemporaryDirectory` and names files in it -- `books/mid.lisp`,
# `books/leaf-a`, `tools/run_peer.py` (which is
# `tests/twonode_gate_fake/tools/run_peer.py` copied into the fixture) -- so
# their path strings are data for a fake tree, not citations of this one.  A
# COMMENT line in such a file is prose and is read normally.
FIXTURE_FILES = re.compile(r"^tests/test_[a-z0-9_]+\.py$")

# Records of a run that happened.  Every book that was certified appears as a
# key with its source digest, so a book removed since is named here forever
# and MUST stay named: rewriting an evidence file to match today's tree is
# falsifying the record.  Reported, never repaired.
RECORD_FILES = re.compile(r"^(tests|planning)/evidence/")

# A load-bearing citer: a source file a reader consults while deciding whether
# to trust a theorem.
LOAD_BEARING = re.compile(r"^(books/|tests/acl2/)")

# Files whose SUBJECT is absent paths.  This checker's own examples, its
# tests, and the triage that reads its output all name paths that are not
# there, on purpose; counting them would make the tree's number a measure of
# how much has been written ABOUT the tree's number.  Add a file here only
# when enumerating absent paths is what it is for, and say so in one line.
CATALOGUE = {
    "tools/cite_check.py": "the checker, whose rules are named in examples",
    "tests/test_cite_check.py": "its cases, which are absent paths",
    "planning/lanes/HANDOFF-w11-phantom-cites.md":
        "the triage of every finding this tool reported",
}

# A citation the surrounding prose already says is empty.  Disclosure is the
# repair AGENTS.md asks for when there is nothing to point at ("Never conceal
# proof gaps"): the claim stays, and the reader is told the evidence named for
# it is not there.  An annotated citation is COUNTED and listed under `--all`,
# so the number of disclosed gaps can be read and cannot grow unseen; it is
# not raised, so `--strict` is about UNDISCLOSED ones.
# For a DRIFT citation the disclosure is different and just as good: prose
# that says where the file went, so a reader following the old name is not
# left at a dead end.
DISCLOSURE = re.compile(
    r"(never existed|never been written|has ever existed|does not exist|"
    r"no such (?:file|book|directory)|no longer exists|was removed|"
    r"folded into|renamed to)", re.IGNORECASE)
DISCLOSURE_WINDOW = (2, 8)      # lines before, lines after

# One regex, one hint.  See WHAT IT CANNOT SEE.
FORWARD = re.compile(
    r"\b(proposed|propose|new book|will (?:add|exist|be)|would|planned|"
    r"packet|future|not yet|to be added|once .* exists|until .* exists)\b",
    re.IGNORECASE)


@dataclass(frozen=True)
class Finding:
    token: str
    citer: str
    line: int
    text: str
    klass: str          # phantom | drift | fixture | record | system | ...
    tier: str           # load-bearing | spec | tool | planning | record
    forward: bool

    def as_dict(self) -> dict:
        return {"token": self.token, "citer": self.citer, "line": self.line,
                "class": self.klass, "tier": self.tier,
                "forward_hint": self.forward, "text": self.text}

    def __str__(self) -> str:
        hint = " forward?" if self.forward else ""
        return (f"{self.klass.upper()} [{self.tier}]{hint} {self.token}\n"
                f"    {self.citer}:{self.line}: {self.text}")


def run(*argv: str) -> str:
    return subprocess.run(argv, cwd=ROOT, capture_output=True, text=True,
                          check=True).stdout


def tracked() -> list[str]:
    return [p for p in run("git", "ls-files").split("\n") if p]


def ever_existed() -> set[str]:
    """Every path any commit on any ref of this checkout touched."""
    return {p for p in run("git", "log", "--all", "--pretty=format:",
                           "--name-only").split("\n") if p}


def resolves(token: str, present: set[str]) -> bool:
    """Does some file in the tree answer this citation?"""
    if token in present or (ROOT / token).exists():
        return True
    base = token.rstrip("/")
    if base != token and (base in present or (ROOT / base).is_dir()):
        return True
    stem, dot, extension = base.rpartition(".")
    extension = ("." + extension) if dot else ""
    if extension in PRODUCED_EXTENSIONS:
        # A produced file is answered by the source that produces it.
        return any(stem + e in present or (ROOT / (stem + e)).exists()
                   for e in IMPLIED_EXTENSIONS)
    if extension and extension not in SOURCE_EXTENSIONS:
        # `tools/bpa_dtn7.BpaDtn7Client' is a module attribute, not a file.
        return any(stem + e in present or (ROOT / (stem + e)).exists()
                   for e in (".py", ".lisp"))
    if not extension:
        return any(base + e in present or (ROOT / (base + e)).exists()
                   for e in IMPLIED_EXTENSIONS)
    return False


def benign(token: str, citer: str, line_text: str, column: int) -> str | None:
    """A class for a token no reader should be asked about, or None.

    Each branch is a false positive a cruder sweep produced, with the reason
    it is not a citation of a file this tree owes.
    """
    if any(c in token for c in PLACEHOLDER_CHARS):
        # `books/X.lisp', `tests/acl2/*-tests.lisp', `books/{a,b}'.
        return "placeholder"
    if token.endswith("-") and line_text.rstrip().endswith(token):
        # A hyphenated line wrap in Markdown: `books/anchor-` + `invariants`.
        return "wrapped"
    stem = token.rstrip("/").rsplit("/", 1)[-1].split(".")[0]
    if len(stem) <= 1:
        # `books/a.lisp', `host/h.lisp': a one-character name is an example.
        return "placeholder"
    if token.startswith("books/") and token.count("/") > 1:
        # This repository's `books/' is FLAT.  `books/arithmetic/top',
        # `books/kestrel/crypto/sha-2/' are ACL2 community books, reached
        # with `:dir :system' and living in the ACL2 installation.
        return "system"
    before = line_text[:column]
    if re.search(r'\(include-book\s+"[^"]*$', before) and ":dir :system" in line_text:
        # `(include-book "tools/flag" :dir :system)': an ACL2 community book,
        # named by a path into the ACL2 installation, not into this tree.
        return "system"
    if "." not in token.rsplit("/", 1)[-1] and not delimited(token, line_text, column):
        # An extension is an author saying "this is a file".  Without one, a
        # slash in running prose is a slash in running prose: `host/grammar
        # work', `planning/structural checks', `host/process/fault tests'.
        # A book root really cited -- `books/nntp-probe', "books/store-node"
        # -- is written in backticks or quotes, and that is what is read.
        return "prose"
    return None


def delimited(token: str, line_text: str, column: int) -> bool:
    """Is the token marked as a path by the character on each side of it?"""
    opening = line_text[column - 1] if column else " "
    rest = line_text[column + len(token):]
    closing = rest[0] if rest else " "
    # ("`", "'") is the Lisp comment convention this tree writes in books:
    # `books/stx-transit.lisp' .  Markdown writes ("`", "`").
    return (opening, closing) in (("`", "`"), ("`", "'"), ('"', '"'),
                                  ("'", "'"), ("(", ")"), ("[", "]"))


def disclosed(lines: list[str], number: int) -> bool:
    """Does the prose around this line say the cited file is not there?"""
    before, after = DISCLOSURE_WINDOW
    window = lines[max(0, number - 1 - before):number + after]
    prose = " ".join(line.lstrip().lstrip(";#*-").strip() for line in window)
    return bool(DISCLOSURE.search(prose))


def scan(present: set[str], history: set[str],
         files: list[str] | None = None) -> list[Finding]:
    findings: list[Finding] = []
    for citer in (tracked() if files is None else files):
        if re.match(r"^rfc\d+\.txt$", citer):
            continue          # the supplied RFCs are not ours to cite-check
        try:
            text = (ROOT / citer).read_text(errors="replace")
        except (OSError, UnicodeDecodeError):
            continue
        fixture = bool(FIXTURE_FILES.match(citer))
        record = bool(RECORD_FILES.match(citer))
        catalogue = citer in CATALOGUE
        lines = text.splitlines()
        for number, line in enumerate(lines, 1):
            comment = line.lstrip().startswith("#")
            for match in TOKEN.finditer(line):
                token = match.group(1).rstrip(".,;:)\"'`]")
                if resolves(token, present):
                    continue
                klass = benign(token, citer, line, match.start(1))
                if klass is None:
                    if catalogue:
                        klass = "catalogue"
                    elif fixture and not comment:
                        klass = "fixture"
                    elif record:
                        klass = "record"
                    elif disclosed(lines, number):
                        klass = "annotated"
                    else:
                        klass = "drift" if token in history or any(
                            token + e in history
                            for e in IMPLIED_EXTENSIONS) else "phantom"
                tier = ("catalogue" if klass == "catalogue" else
                        "record" if record else
                        "fixture" if klass == "fixture" else
                        "load-bearing" if LOAD_BEARING.match(citer) else
                        "planning" if citer.startswith("planning/") else
                        "spec" if citer.startswith(("specs/", "docs/"))
                        or citer in ("README.md", "AGENTS.md") else "tool")
                findings.append(Finding(
                    token=token, citer=citer, line=number,
                    text=line.strip()[:110], klass=klass, tier=tier,
                    forward=bool(FORWARD.search(line))))
    return findings


RAISED = ("phantom", "drift")
BENIGN = ("annotated", "catalogue", "placeholder", "wrapped", "prose",
          "system", "fixture", "record")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--all", action="store_true",
                        help="list the benign classes too")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--summary", action="store_true",
                        help="the counts only, as `make check` prints them")
    parser.add_argument("--strict", action="store_true",
                        help="exit non-zero on any load-bearing finding")
    args = parser.parse_args(argv)

    present = set(tracked())
    findings = scan(present, ever_existed())
    raised = [f for f in findings if f.klass in RAISED]
    load_bearing = [f for f in raised if f.tier == "load-bearing"]

    if args.json:
        print(json.dumps({
            "findings": [f.as_dict() for f in findings],
            "by_class": {k: sum(1 for f in findings if f.klass == k)
                         for k in RAISED + BENIGN},
            "by_tier": {t: sum(1 for f in raised if f.tier == t)
                        for t in ("load-bearing", "spec", "tool", "planning")},
            "distinct_targets": len({f.token for f in raised}),
            "load_bearing": len(load_bearing),
        }, indent=2))
        return 1 if args.strict and load_bearing else 0

    if not args.summary:
        order = {"load-bearing": 0, "spec": 1, "tool": 2, "planning": 3}
        for finding in sorted(raised, key=lambda f: (order.get(f.tier, 4),
                                                     f.klass, f.token, f.citer)):
            print(finding)
        if args.all:
            for finding in sorted(findings, key=lambda f: (f.klass, f.token)):
                if finding.klass in BENIGN:
                    print(finding)

    counts = {k: sum(1 for f in findings if f.klass == k) for k in RAISED}
    tiers = {t: sum(1 for f in raised if f.tier == t)
             for t in ("load-bearing", "spec", "tool", "planning")}
    print(f"cite_check: {len(raised)} citations of "
          f"{len({f.token for f in raised})} absent paths "
          f"({counts['phantom']} phantom, {counts['drift']} drift); "
          f"by citer: {tiers['load-bearing']} load-bearing, "
          f"{tiers['spec']} spec, {tiers['tool']} tool, "
          f"{tiers['planning']} planning; "
          + ", ".join(f"{sum(1 for f in findings if f.klass == k)} {k}"
                      for k in BENIGN) + " not raised.")
    return 1 if args.strict and load_bearing else 0


if __name__ == "__main__":
    raise SystemExit(main())
