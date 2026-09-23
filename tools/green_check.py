#!/usr/bin/env python3
"""Is this book certified AT ITS CURRENT SOURCE DIGEST, in any manifest we hold?

On 2026-09-21 `dev` had been red for a day in `books/stx-evidence-records`,
`books/checkpoint-compaction`, `books/hybrid-store` and `books/feed-connection`.
Each was committed by a lane that never certified it, and every reader after
that took `git log` for certification.  The evidence was already on disk: the
archived manifests recorded those failures at exactly the digests the tree
carries.  What did not exist was an instrument that asked the question, so
nobody asked it.

    python3 tools/green_check.py --summary   # the three lines `make check` prints
    python3 tools/green_check.py --table     # every book, red first, then never
    python3 tools/green_check.py --json      # the same records, machine-readable
    python3 tools/green_check.py --strict    # exit 1 on a book red at its digest
    python3 tools/green_check.py --changed-since dev --strict
                                             # the merge gate: the books this
                                             # branch changed, every book that
                                             # includes one, and each one's
                                             # verdict; exit 1 unless all green

WHAT IT MEASURES.  Every root in the Makefile's `ACL2_BOOKS` and every book
in those roots' local include closure, read through the one closure walker
(`tools/certs.py`) and the one root list (`tools/ledger.py`) the certification
runner uses, so this cannot disagree with `make certify` about what a book is.
For each book it hashes the `.lisp` beside it now and searches every manifest
under `planning/evidence/manifests/` plus this worktree's unarchived
`build/acl2/certify-*/manifest.json` for the NEWEST run, by run-id timestamp,
that recorded a verdict for it:

  green   the newest passing verdict for this book and its CURRENT include
          closure satisfies `certs.certified_books`' pass rule -- that run's
          fresh success marker, a certificate digest, and ACL2 exit 0.
  red     a failure for this book and current closure is newer than its
          matching green. A failure lacking closure digests remains a
          conservative red; a known different closure is not this verdict.
  never   no run vouches either way at this digest.  The record still names
          the newest green at ANY digest, so `last green 2026-09-21T09:50Z at
          an older digest` reads differently from `never green at all`.
  absent  the book was never a requested root in any manifest we hold.  Being
          only a closure member of some other run's request is not a verdict.

WHAT IT DOES NOT SHOW, and none of these is a small caveat.  A green manifest
is one run, on one host, with one ACL2 toolchain identity and one Lisp: it
does NOT mean a certificate exists in THIS worktree, and it says nothing
whatever about images, saved cores, or whether ACL2 would accept the installed
pair at include time (`tools/certs.py` decides that, and ACL2 decides it
again).  A green here is a claim that those bytes once certified somewhere we
have the record of, which is the weakest useful thing and strictly more than
`git log` says. For a pass, it prefers a run matching the book's full current
include closure; same book bytes over changed dependencies are a different
certificate key. If none matches, the latest pass at the book's own bytes is
still shown with `deps_moved`, and the merge gate rejects it as stale. A
failure with a known different closure does not override a matching pass;
one with missing closure digests is conservatively retained. A handful of
the archived manifests
failed without per-book attribution and without usable success markers, so a
failure inside one of those is invisible here and is counted as
`unattributed`.  And a book absent from every manifest is unmeasured, not
clean. The `--changed-since` merge gate additionally rejects these stale
dependency closures; its `stale` verdict is distinct from a failed proof.

Deliberately generates no committed table: every archived manifest and every
edited book would put one out of date, and both inputs are there to be read at
the moment the question is asked.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass, field
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(Path(__file__).resolve().parent))
import certs  # noqa: E402
import evidence_manifests  # noqa: E402
import ledger  # noqa: E402

STAMP = re.compile(r"certify-(\d{8}T\d{6}Z)-\d+")
ORDER = {"red": 0, "never": 1, "absent": 2, "green": 3}


def when(run_id: str) -> str:
    """A `certify-<YYYYMMDD>T<HHMMSS>Z-<pid>` stamp as a UTC minute.

    A pattern, not an example: `evidence_manifests.py check` reads a run-id
    literal in a tracked file as a certification claim and wants a manifest.
    """
    match = STAMP.match(run_id)
    if not match:
        return "unknown-time"
    stamp = match.group(1)
    return f"{stamp[:4]}-{stamp[4:6]}-{stamp[6:8]}T{stamp[9:11]}:{stamp[11:13]}Z"


@dataclass
class Run:
    """One manifest, reduced to what a green/red question needs."""

    run_id: str
    where: str
    archived: bool
    sources: dict[str, str] = field(default_factory=dict)

    @property
    def stamp(self) -> str:
        match = STAMP.match(self.run_id)
        return match.group(1) if match else ""

    @property
    def when(self) -> str:
        return when(self.run_id)

    def cite(self) -> str:
        place = self.where if self.archived else f"{self.where}, local unarchived"
        return f"{self.when} {self.run_id} ({place})"


def host_of(manifest: dict) -> str:
    """The box a run happened on: `archived_from` first, then its own name."""
    archived = str(manifest.get("archived_from") or "")
    if archived:
        return archived.split(":", 1)[0]
    return str(manifest.get("hostname") or "unknown-host")


def manifests(root: Path = ROOT) -> list[tuple[Run, dict]]:
    """Every manifest a reader at this revision can open, newest last.

    The archive under `planning/evidence/manifests/` is the committed claim
    (`tools/evidence_manifests.py`); the unarchived runs under `build/acl2/`
    are this worktree's own and are labelled so, because a reader elsewhere
    cannot see them.  Both are read through `certs.load_manifests`, which
    skips an unreadable or non-object file and records the evidence path.
    """
    found: list[tuple[Run, dict]] = []
    archive = root / evidence_manifests.ARCHIVE_REL
    paths = [(path, True) for path in sorted(archive.glob("certify-*.json"))]
    paths += [(path, False)
              for path in sorted(root.glob(certs.MANIFEST_GLOB))]
    seen: set[str] = set()
    for path, archived in paths:
        for manifest in certs.load_manifests(root, path):
            run_id = (evidence_manifests.run_id_of(path)
                      or str(manifest.get("run_id") or ""))
            if not run_id or run_id in seen:
                continue
            seen.add(run_id)
            found.append((Run(
                run_id=run_id, where=host_of(manifest), archived=archived,
                sources=manifest.get("source_digests_sha256") or {}), manifest))
    return sorted(found, key=lambda pair: pair[0].stamp)


def failed_books(manifest: dict) -> set[str]:
    """The books ONE manifest says did not certify, by that run's own words.

    `book_results` is the runner's per-book verdict and `book_failures` its
    reasons; both arrived later than the oldest manifests here.  Failing that,
    a run whose expected success markers line up with its requested books
    attributes a missing marker to its book.  A run that carries neither
    attributes nothing: its failure is real and unreadable, and the caller
    counts it rather than guessing.
    """
    requested = manifest.get("requested_books") or []
    results = manifest.get("book_results") or {}
    reasons = manifest.get("book_failures") or {}
    if results or reasons:
        named = {book for book in requested
                 if book in results and results[book] != "passed"}
        return named | {book for book in reasons}
    expected = manifest.get("expected_success_markers") or []
    observed = set(manifest.get("observed_success_markers") or [])
    if expected and len(expected) == len(requested):
        return {book for book, token in zip(requested, expected)
                if token not in observed}
    return set()


@dataclass
class Record:
    """One book's standing: what it hashes to now and what vouches for it."""

    book: str
    digest: str
    verdict: str = "absent"
    green: Run | None = None
    exact_green: Run | None = None
    red: Run | None = None
    last_green: Run | None = None
    deps_moved: list[str] = field(default_factory=list)

    def note(self) -> str:
        if self.verdict == "green":
            moved = (f"; {len(self.deps_moved)} deps moved since"
                     if self.deps_moved else "")
            return f"certified {self.green.cite()}{moved}"
        if self.verdict == "red":
            older = (f"; last green {self.last_green.when} at an older digest"
                     if self.last_green else "; never green at all")
            return f"FAILED {self.red.cite()}{older}"
        if self.verdict == "never":
            if self.last_green:
                return ("NEVER at this digest; last green "
                        f"{self.last_green.cite()} at an older digest")
            return "NEVER at this digest; never green at all"
        return "not a requested root in any manifest we hold"


def audit(root: Path = ROOT, roots: list[str] | None = None) -> dict:
    """Every root and every book those roots include, judged at its digest.

    `roots` defaults to the Makefile's `ACL2_BOOKS`, read by the one parser
    `make certify` reads it with, and is passed explicitly only by a test
    standing up a synthetic tree with no Makefile in it.
    """
    roots = list(roots) if roots is not None else ledger.makefile_roots()
    digests: dict[str, str] = {}
    for name in roots:
        digests.update(certs.closure(root, name))
    records = {book: Record(book=book, digest=digest)
               for book, digest in digests.items()}
    listings = {book: certs.closure_listing(certs.closure(root, book))
                for book in records}

    read = manifests(root)
    runs = {run.run_id: run for run, _ in read}
    unattributed: list[str] = []
    requested_somewhere: set[str] = set()
    for run, manifest in read:
        requested_somewhere.update(manifest.get("requested_books") or [])
        failed = failed_books(manifest)
        if not failed and manifest.get("status") != "passed":
            unattributed.append(run.run_id)
        for book in failed:
            record = records.get(book)
            if record is None or run.sources.get(f"{book}.lisp") != record.digest:
                continue
            # A failure against a known different closure does not refute a
            # pass at the current bytes. Older manifests that omit closure
            # digests remain conservative: their failure is not dismissed.
            paths = [item.rpartition(":")[0] for item in listings[book]]
            if all(path in run.sources for path in paths) and certs.closure_drift(
                    listings[book], run.sources):
                continue
            if record.red is None or run.stamp >= record.red.stamp:
                record.red = run

    # The pass rule is `certs.certified_books`', unchanged: this tool decides
    # WHICH run answers for a book, never what counts as certified.
    for book, certified in certs.certified_books([m for _, m in read]).items():
        record = records.get(book)
        if record is None:
            continue
        for entry in certified:
            run = runs.get(evidence_manifests.run_id_of(Path(entry.evidence)) or "")
            if run is None:
                continue
            # `certs.verified`'s rule: a source that moved WHILE the run was
            # certifying it vouches for neither set of bytes.
            if entry.after is not None and entry.after != entry.source:
                continue
            if record.last_green is None or run.stamp >= record.last_green.stamp:
                record.last_green = run
            if entry.source != record.digest:
                continue
            if record.green is None or run.stamp >= record.green.stamp:
                record.green = run
            if not certs.closure_drift(listings[book], entry.closure_sources):
                if record.exact_green is None or run.stamp >= record.exact_green.stamp:
                    record.exact_green = run

    for record in records.values():
        if record.exact_green is not None:
            record.green = record.exact_green
        if record.red is not None and (record.green is None
                                       or record.red.stamp > record.green.stamp):
            record.verdict = "red"
        elif record.green is not None:
            record.verdict = "green"
            record.deps_moved = certs.closure_drift(
                listings[record.book],
                record.green.sources)
        elif record.book in requested_somewhere:
            record.verdict = "never"
    counts = {name: sum(1 for record in records.values() if record.verdict == name)
              for name in ("green", "red", "never", "absent")}
    return {
        "schema": "fn-green-check-v1",
        "roots": len(roots),
        "books": len(records),
        "manifests": len(read),
        "manifests_archived": sum(1 for run, _ in read if run.archived),
        "manifests_unattributed_failures": unattributed,
        "newest_green": max((record.green.stamp, record.green.when)
                            for record in records.values()
                            if record.green is not None)[1]
        if counts["green"] else None,
        "greens_with_a_moved_dependency": sum(
            1 for record in records.values()
            if record.verdict == "green" and record.deps_moved),
        "counts": counts,
        "books_by_verdict": {
            record.book: {
                "verdict": record.verdict,
                "digest_sha256": record.digest,
                "note": record.note(),
                "certified_at_digest": record.green.run_id if record.green else None,
                "failed_at_digest": record.red.run_id if record.red else None,
                "last_green_any_digest": (record.last_green.run_id
                                          if record.last_green else None),
                "deps_moved_since": record.deps_moved,
            }
            for record in sorted(records.values(),
                                 key=lambda r: (ORDER[r.verdict], r.book))
        },
    }


def changed_books(root: Path, rev: str) -> list[str]:
    """The books and test books whose bytes differ from `rev`'s merge base.

    Working tree against the merge base, so an uncommitted edit counts: the
    question is what a merge would carry, and a lane's tree is what it has.
    """
    base = subprocess.run(["git", "merge-base", rev, "HEAD"], cwd=root,
                          capture_output=True, text=True, check=True).stdout.strip()
    names = subprocess.run(["git", "diff", "--name-only", base, "--",
                            "books", "tests/acl2"], cwd=root,
                           capture_output=True, text=True, check=True).stdout.split()
    return sorted(name[:-5] for name in names if name.endswith(".lisp"))


def dependents(root: Path, report: dict, changed: list[str]) -> dict[str, list[str]]:
    """Every audited book whose include closure reaches a changed book.

    Read through the one closure walker the runner uses, so "depends on" here
    is exactly what `include-book` will ask a certificate for.
    """
    wanted = set(changed)
    found: dict[str, list[str]] = {}
    for book in report["books_by_verdict"]:
        # Host include files contribute dependency bytes to a certifiable
        # book, but certify_books cannot request them as independent roots.
        if not book.startswith(("books/", "tests/acl2/")):
            continue
        if book in wanted:
            continue
        reached = sorted(wanted & set(certs.closure(root, book)))
        if reached:
            found[book] = reached
    return found


def gate(report: dict, changed: list[str], deps: dict[str, list[str]]) -> dict:
    """The merge gate's answer: each changed book and dependent with its verdict.

    Finding F4 of planning/review-2026-09-22-proof-engineering.md: on
    2026-09-21 five commits changed the machine under invariant books nobody
    recertified, and `git log` read as green.  A branch that touched a book
    merges when that book and everything that includes it are green at the
    bytes the merge will carry, or it waits.  A book not in the audit's
    closure (a test book no root names) is reported as `unaudited`, which is
    not green.
    """
    verdicts = report["books_by_verdict"]

    def verdict(book: str) -> str:
        entry = verdicts.get(book)
        if entry is None:
            return "unaudited"
        if entry["verdict"] == "green" and entry.get("deps_moved_since"):
            return "stale"
        return entry["verdict"]

    rows = [{"book": book, "role": "changed", "verdict": verdict(book), "via": []}
            for book in changed]
    rows += [{"book": book, "role": "dependent", "verdict": verdict(book), "via": via}
             for book, via in sorted(deps.items())]
    for row in rows:
        row["deps_moved_since"] = verdicts.get(row["book"], {}).get("deps_moved_since", [])
    not_green = [row["book"] for row in rows if row["verdict"] != "green"]
    return {"schema": "fn-green-gate-v1", "changed": changed,
            "dependents": len(deps), "rows": rows, "not_green": not_green}


def gate_lines(answer: dict) -> list[str]:
    lines = [f"green-gate: {len(answer['changed'])} changed books, "
             f"{answer['dependents']} books include one; "
             f"{len(answer['not_green'])} not green at the bytes a merge would carry."]
    width = max((len(row["book"]) for row in answer["rows"]), default=4)
    for row in answer["rows"]:
        via = (" <- " + " ".join(row["via"])) if row["via"] else ""
        drift = ("; changed or unrecorded dependency bytes: " +
                 " ".join(row["deps_moved_since"])) if row.get("deps_moved_since") else ""
        lines.append(f"  {row['verdict']:9} {row['role']:9} {row['book']:{width}}{via}{drift}")
    if not answer["rows"]:
        lines.append("  no book or test book differs from the merge base")
    return lines


def worklist(report: dict) -> list[str]:
    """The books the certification lanes owe a run, red first."""
    return [book for book, entry in report["books_by_verdict"].items()
            if entry["verdict"] in ("red", "never", "absent")]


def summary(report: dict) -> list[str]:
    counts = report["counts"]
    owed = worklist(report)
    shown = " ".join(owed[:8]) or "none"
    more = f" (+{len(owed) - 8} more; --table for all)" if len(owed) > 8 else ""
    unattributed = len(report["manifests_unattributed_failures"])
    return [
        f"green-check: {report['books']} books in the closure of "
        f"{report['roots']} Makefile roots -- {counts['green']} green at their "
        f"current digest, {counts['red']} RED at digest, {counts['never']} never "
        f"at this digest, {counts['absent']} never a requested root in any manifest.",
        f"green-check: owed a certification: {shown}{more}",
        f"green-check: {report['manifests']} manifests read "
        f"({report['manifests_archived']} archived, "
        f"{report['manifests'] - report['manifests_archived']} local unarchived, "
        f"{unattributed} failed without per-book attribution); newest green at a "
        f"current digest {report['newest_green'] or 'none at all'}; "
        f"{report['greens_with_a_moved_dependency']} greens have a dependency "
        f"that moved since their run.  A green manifest is one host and one "
        f"toolchain identity, not a certificate in this tree, and says nothing "
        f"about images.",
    ]


def table(report: dict) -> list[str]:
    width = max((len(book) for book in report["books_by_verdict"]), default=4)
    lines = [f"{'VERDICT':7}  {'BOOK':{width}}  DIGEST    EVIDENCE"]
    for book, entry in report["books_by_verdict"].items():
        lines.append(f"{entry['verdict']:7}  {book:{width}}  "
                     f"{entry['digest_sha256'][:8]}  {entry['note']}")
    return lines


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Which books are certified at the digest they carry now.")
    parser.add_argument("--summary", action="store_true",
                        help="the three lines `make check` prints")
    parser.add_argument("--table", action="store_true",
                        help="every book, red first, then never, then green")
    parser.add_argument("--json", action="store_true",
                        help="the whole audit as one JSON object")
    parser.add_argument("--strict", action="store_true",
                        help="exit 1 when a book is RED at its current digest "
                             "in a run newer than any green for those bytes; "
                             "with --changed-since, exit 1 unless every changed "
                             "book and every book that includes one is green")
    parser.add_argument("--changed-since", metavar="REV", default=None,
                        help="the merge gate: the books this tree changed since "
                             "its merge base with REV, the books that include "
                             "them, and each one's verdict")
    args = parser.parse_args(argv)

    try:
        report = audit()
    except (certs.UnreadableBook, ValueError, OSError) as error:
        print(f"green-check: cannot read this tree: {error}", file=sys.stderr)
        return 2

    if args.changed_since:
        try:
            changed = changed_books(ROOT, args.changed_since)
        except subprocess.CalledProcessError as error:
            print(f"green-check: git cannot resolve {args.changed_since}: "
                  f"{error.stderr.strip()}", file=sys.stderr)
            return 2
        answer = gate(report, changed, dependents(ROOT, report, changed))
        if args.json:
            print(json.dumps(answer, indent=1, sort_keys=True))
        else:
            print("\n".join(gate_lines(answer)))
        return 1 if args.strict and answer["not_green"] else 0

    if args.json:
        print(json.dumps(report, indent=1, sort_keys=True))
    elif args.table:
        print("\n".join(table(report)))
    if args.summary or not (args.json or args.table):
        print("\n".join(summary(report)))
    return 1 if args.strict and report["counts"]["red"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
