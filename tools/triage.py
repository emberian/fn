#!/usr/bin/env python3
"""Every independent red in a book closure, in as few farm runs as its
dependency graph allows.

**A triage run is evidence of nothing but the list of reds it prints.**  It
certifies a tree whose sources have been substituted, on the box only; its
certificates are never published to the box's cache or to this worktree's,
its manifest is never archived under `planning/evidence/manifests/`, and its
certify run id is deliberately absent from the report it writes, because
naming one would read as a certification claim.  Nothing here certifies
anything.  It finds out what is broken.

    python3 tools/triage.py persvati books/checkpoint tests/acl2/checkpoint-tests \\
        --remote-root /home/ember/fn-gates/w32-triage \\
        --acl2 /home/ember/fn-gates/toolchains/w25/acl2-literal \\
        --cache /home/ember/fn-certcache --budget-seconds 300 --rounds 4

WHY.  `include-book` refuses an uncertified dependency, so a closure run
stops at the first book that fails and every book above it reads "There is no
certificate on file".  One run therefore reveals one *layer* of independent
reds.  The image closure is about ten deep, and on 2026-09-22 it took three
lanes and thirty-nine certification runs across nine hours to reach 140 of
164 green, each run costing the slowest book in it
(`planning/review-2026-09-22-proof-engineering.md`, finding F1).

WHAT A ROUND DOES.  Certify the closure on the farm with a short per-book
budget; read each failed book's own log and call it one of

  cascade      its log carries only ACL2's "There is no certificate on file"
               for a book below it.  Nothing is known about this book.
  timeout      the runner's per-book budget expired.  A proof that stops
               returning burns the whole budget, so this is a finding in its
               own right (F2) and not a lesser kind of red.
  independent  an ACL2 Error of its own.  The first one and its key
               checkpoint are what the report carries.
  unexplained  it failed with no error and no timeout.  Reported verbatim.

Then, for every independent or timed-out book, find the newest source bytes
that ever certified (`tools/green_check.py`'s audit names the run; that run's
manifest names the digest; `git log --all` and `git show` hold the bytes),
write those bytes into the *remote* tree only, and run the closure again.
The books that were hiding behind it now fail on their own account or pass.
Repeat to `--rounds`.

WHAT IT COSTS.  A round is a whole-closure certification.  `certs.py
install-set --purge-on-miss`, which `--closure` implies, removes every local
pair in the closure before the runner starts, and a substituted source has no
cached set anywhere, so there is nothing to reuse between rounds: the price
of a round is the closure's critical path, not the layer's.  The saving is in
the number of rounds, which is the point -- a ten-deep chain is triaged in
two or three.  Set `--budget-seconds` above the closure's slowest honest book
or that book becomes a timeout finding and hides everything above it again.

WHAT IT DOES NOT SHOW.  A book that passes under a substitution is not green:
it is green *over a dependency this tree does not have*.  A book with no
recorded green at any digest cannot be substituted and is reported as
untriageable, and so is a book whose newest green is at the digest it already
carries -- its failure is dependency drift, not its own bytes.  The
assumption stack in the report is the honest name for all of this.

EXIT CODES.  0 the closure answered with no red left in it, 1 the report
names reds or books it could not triage, 2 the triage could not be made at
all -- a box that refused, a manifest that did not come back.  A 1 is not a
verdict on the tree; it is the tool saying it has a list.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass, field
import datetime as dt
import hashlib
import json
from pathlib import Path
import re
import secrets
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(Path(__file__).resolve().parent))
import certs  # noqa: E402
import farm  # noqa: E402
import green_check  # noqa: E402

SCHEMA = "fn-triage-v1"
OUT_REL = "build/triage"
# ACL2 wraps its error text at about 70 columns, so "There is no certificate
# on file" arrives with a newline anywhere inside it and a phrase match has to
# be made on whitespace-collapsed text.
NO_CERTIFICATE = "There is no certificate on file"
# `\b` after the optional `[Failure]` would backtrack past it -- `]` and the
# space that follows are both non-word -- and the report would then print
# every error as a plain `ACL2 Error`.
ERROR_START = re.compile(
    r"^(?:ACL2 Error(?: \[[^\]]*\])?|HARD ACL2 ERROR)(?=[ :]|$)")
CHECKPOINT_START = re.compile(r"^\*\*\* Key checkpoint.*\*\*\*$")
MISSING_FOR = re.compile(NO_CERTIFICATE + r' for "([^"]+)"')
CHECKPOINT_LINES = 24
# The verdict names, in the order the report presents them.
KINDS = ("independent", "timeout", "unexplained", "blocked", "cascade")
# Create and Complete skip proofs and take seconds a book; only Convert needs
# a real budget, and that is what `--budget-seconds` bounds.  This is the
# ceiling for the other two, large enough to be no constraint and small
# enough that a wave which hangs is a finding rather than a night.
WAVE_TIMEOUT_SECONDS = 600


class TriageError(Exception):
    """A triage run that could not be made, reported instead of half-run."""


# --------------------------------------------------------------------------
# reading one book's log
# --------------------------------------------------------------------------


def collapse(text: str) -> str:
    """`text` with every run of whitespace as one space, for phrase matching."""
    return " ".join(text.split())


def repository_book(path: str) -> str:
    """The repository-relative book name inside an absolute path ACL2 printed.

    ACL2 names the uncertified dependency by the absolute path it has on the
    box, which is the remote root, not this worktree.  The repository part is
    what a reader here can act on.
    """
    text = path[:-len(".lisp")] if path.endswith(".lisp") else path
    for directory in certs.BOOK_DIRECTORIES:
        marker = f"/{directory}/"
        at = text.rfind(marker)
        if at >= 0:
            return text[at + 1:]
    return Path(text).name


@dataclass
class AclError:
    """One `ACL2 Error` block in a book's log, as the report needs it."""

    line: int
    head: str
    form: str
    message: str
    cascade_of: str | None = None
    wrapper: bool = False
    restatement: bool = False

    @property
    def news(self) -> bool:
        """Is this block the book's own first word about its own failure?"""
        return (self.cascade_of is None and not self.wrapper
                and not self.restatement)

    def text(self) -> str:
        where = f" in ({self.form})" if self.form else ""
        return collapse(f"{self.head}{where}: {self.message}")


def acl2_errors(log: str) -> list[AclError]:
    """Every error block in `log`, in order, each classified by its own text.

    ACL2 prints an error as a run of non-blank lines starting with `ACL2
    Error`, wrapped at the pretty-printer margin, so both the form and the
    message can be split across lines.  Four kinds appear in a failed
    certification and only one of them is news: the certify-book wrapper at
    the end, which restates the failure; an include-book of a book with no
    certificate, which is a cascade; ACL2's own `[Failure] ... See :DOC
    failure` restatement of a form it has already complained about, which
    carries none of the reason and which made every cascade here look like
    an independent red until it was given a name; and the book's own error.
    """
    lines = log.splitlines()
    found: list[AclError] = []
    by_form: dict[str, AclError] = {}
    index = 0
    while index < len(lines):
        if not ERROR_START.match(lines[index]):
            index += 1
            continue
        start = index
        block: list[str] = []
        while index < len(lines) and lines[index].strip():
            block.append(lines[index])
            index += 1
        whole = collapse(" ".join(block))
        form = ""
        parenthesised = re.search(r"\(\s*([^()]*?)\s*\)", whole)
        if parenthesised:
            form = parenthesised.group(1)
        _, separator, rest = whole.partition("): ")
        if not separator:
            _, separator, rest = whole.partition(": ")
        message = rest.strip() if separator else whole
        cascade_of = None
        if NO_CERTIFICATE in whole:
            named = MISSING_FOR.search(whole)
            cascade_of = (repository_book(named.group(1)) if named
                          else repository_book(form.split('"')[1])
                          if '"' in form else "an unnamed book")
        earlier = by_form.get(form) if form else None
        error = AclError(
            line=start + 1, head=ERROR_START.match(lines[start]).group(0),
            form=form, message=message,
            cascade_of=cascade_of or (earlier.cascade_of if earlier else None),
            wrapper=form.upper().startswith("CERTIFY-BOOK"),
            restatement=earlier is not None)
        if form and earlier is None:
            by_form[form] = error
        found.append(error)
    return found


def key_checkpoint(log: str, limit: int = CHECKPOINT_LINES) -> str | None:
    """ACL2's last key checkpoint, the goal it could not prove, truncated.

    The checkpoint is the one part of a failed proof a reader can act on
    without the log, so the report carries it; it is also unbounded, so it is
    cut at `limit` lines with the cut declared.
    """
    lines = log.splitlines()
    starts = [number for number, line in enumerate(lines)
              if CHECKPOINT_START.match(line.strip())]
    if not starts:
        return None
    start = starts[-1]
    body: list[str] = []
    for line in lines[start + 1:]:
        if ERROR_START.match(line) or line.startswith(("Summary", "********")):
            break
        body.append(line)
    while body and not body[0].strip():
        body.pop(0)
    while body and not body[-1].strip():
        body.pop()
    shown = body[:limit]
    if len(body) > limit:
        shown.append(f"... ({len(body) - limit} more lines, in the run log "
                     f"on the box)")
    return "\n".join([lines[start].strip()] + shown)


@dataclass
class Finding:
    """One book's standing in one round, with everything the report prints."""

    book: str
    kind: str
    round: int
    wall_seconds: float | None = None
    exit_code: object = None
    first_error: str | None = None
    error_line: int | None = None
    checkpoint: str | None = None
    blocked_by: list[str] = field(default_factory=list)
    assumptions: list[str] = field(default_factory=list)
    # Under `--pcert`, the last provisional wave this book finished.  A book
    # that reached `convert` has had every one of its proofs done, so a
    # `blocked` finding hides nothing: it is waiting on a certificate.
    reached: str | None = None

    @property
    def proofs_done(self) -> bool:
        return self.reached in ("convert", "complete")

    def as_json(self) -> dict:
        return {
            "book": self.book, "kind": self.kind, "round": self.round,
            "wall_seconds": self.wall_seconds, "acl2_exit_code": self.exit_code,
            "first_error": self.first_error, "error_log_line": self.error_line,
            "key_checkpoint": self.checkpoint, "blocked_by": self.blocked_by,
            "assuming": self.assumptions, "pcert_reached": self.reached,
            "proofs_done": self.proofs_done,
        }


def classify(book: str, log: str, exit_code: object, round_number: int,
             wall_seconds: float | None, assumptions: list[str]) -> Finding:
    """Which of the four kinds this failed book is, from its own log.

    The exit code decides a timeout and nothing else: a book whose
    certification failed in 0.2 s still exits 0, because the driver ends in
    `(quit)` and ACL2 reaches it either way (`tools/certify_books.py`,
    `book_result`).  Everything else is read out of the log.
    """
    finding = Finding(book=book, kind="unexplained", round=round_number,
                      wall_seconds=wall_seconds, exit_code=exit_code,
                      assumptions=list(assumptions))
    if isinstance(exit_code, str) and exit_code.startswith("timed out"):
        finding.kind = "timeout"
        return finding
    errors = acl2_errors(log)
    own = [error for error in errors if error.news]
    cascades = [error for error in errors if error.cascade_of is not None]
    if own:
        finding.kind = "independent"
        finding.first_error = own[0].text()
        finding.error_line = own[0].line
        finding.checkpoint = key_checkpoint(log)
    elif cascades:
        finding.kind = "cascade"
        finding.blocked_by = sorted({error.cascade_of for error in cascades
                                     if error.cascade_of})
    elif errors:
        # Only the certify-book wrapper: the book failed with no error of its
        # own recorded above it.  That is unusual and is not smoothed over.
        finding.first_error = errors[0].text()
        finding.error_line = errors[0].line
    return finding


def classify_pcert(book: str, evidence: Path, manifest: dict, round_number: int,
                   assumptions: list[str]) -> Finding:
    """One book's standing after a three-wave provisional run.

    The manifest's `pcert_reached` says which wave the book last finished,
    and that is the whole difference from a closure run.  A book that reached
    `convert` proved everything it contains and only lacks a certificate
    because a book below it lacks one -- `blocked`, and nothing is hidden
    behind it.  A book whose Convert failed has its own red, whatever is
    below it.  Only a Create failure can still hide another book's proofs,
    because Create is the one wave that is dependency-ordered, and that is
    the one case the substitution loop is still for.
    """
    reached = (manifest.get("pcert_reached") or {}).get(book)
    waves = (manifest.get("book_wave_seconds") or {}).get(book) or {}
    wall = round(sum(float(value) for value in waves.values()), 3) or None
    code = (manifest.get("acl2_exit_codes") or {}).get(book)
    if reached == "convert":
        finding = Finding(book=book, kind="blocked", round=round_number,
                          wall_seconds=wall, exit_code=code,
                          assumptions=list(assumptions), reached=reached)
        cascades = [error for error in
                    acl2_errors(wave_log(evidence, book, "complete"))
                    if error.cascade_of]
        finding.blocked_by = sorted({error.cascade_of for error in cascades
                                     if error.cascade_of})
        return finding
    wave = "create" if reached is None else "convert"
    finding = classify(book, wave_log(evidence, book, wave), code,
                       round_number, wall, assumptions)
    finding.reached = reached
    return finding


# --------------------------------------------------------------------------
# the last source that ever certified
# --------------------------------------------------------------------------


def git(root: Path, *arguments: str) -> bytes:
    """One git command in `root`, raising the tool's own error on failure."""
    result = subprocess.run(["git", "-C", str(root), *arguments],
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if result.returncode != 0:
        raise TriageError(f"git {' '.join(arguments)}: "
                          f"{result.stderr.decode('utf-8', 'replace').strip()}")
    return result.stdout


@dataclass
class Substitution:
    """A book's last green bytes, and where the claim that they were green is."""

    book: str
    digest: str
    revision: str
    subject: str
    green_run: str
    green_when: str

    def sentence(self) -> str:
        return (f"assuming {self.book} at its last green digest "
                f"{self.digest[:12]} from commit {self.revision[:12]} "
                f"({self.subject}), green in the {self.green_when} run")

    def as_json(self) -> dict:
        return {"book": self.book, "source_digest_sha256": self.digest,
                "revision": self.revision, "subject": self.subject,
                "green_manifest": self.green_run, "green_when": self.green_when}


def last_green(audit: dict, runs: dict[str, green_check.Run],
               book: str) -> tuple[str, green_check.Run] | None:
    """The digest this book last certified at, and the run that says so."""
    entry = audit["books_by_verdict"].get(book)
    if entry is None:
        return None
    run_id = entry.get("last_green_any_digest")
    if not run_id or run_id not in runs:
        return None
    run = runs[run_id]
    digest = run.sources.get(f"{book}.lisp")
    return (digest, run) if digest else None


def source_at_digest(root: Path, book: str, digest: str,
                     limit: int = 400) -> tuple[str, str, bytes] | None:
    """The revision whose `book.lisp` hashes to `digest`, and those bytes.

    `--all` because a green manifest can come from a lane branch that never
    merged, which is exactly where a freeze lane's repairs live.  Renames are
    not followed: a book that moved has a different name and is a different
    book to every tool here.
    """
    path = f"{book}.lisp"
    revisions = git(root, "log", "--all", "--format=%H", "--",
                    path).decode().split()
    for revision in revisions[:limit]:
        try:
            blob = git(root, "show", f"{revision}:{path}")
        except TriageError:
            continue
        if hashlib.sha256(blob).hexdigest() == digest:
            subject = git(root, "log", "-1", "--format=%s",
                          revision).decode().strip()
            return revision, subject, blob
    return None


def substitution_for(root: Path, audit: dict, runs: dict[str, green_check.Run],
                     book: str, current_digest: str
                     ) -> tuple[Substitution, bytes] | str:
    """This book's last green source, or the sentence saying why there is none."""
    green = last_green(audit, runs, book)
    if green is None:
        return "never green at any digest in any manifest we hold"
    digest, run = green
    if digest == current_digest:
        return (f"its newest green is at the digest it already carries "
                f"({digest[:12]}, {run.when}); the failure is not in these "
                f"bytes")
    found = source_at_digest(root, book, digest)
    if found is None:
        return (f"no commit in this repository has {book}.lisp at digest "
                f"{digest[:12]}, which {run.when} recorded as green")
    revision, subject, blob = found
    return (Substitution(book=book, digest=digest, revision=revision,
                         subject=subject, green_run=run.run_id,
                         green_when=run.when), blob)


# --------------------------------------------------------------------------
# the rounds
# --------------------------------------------------------------------------


def run_id() -> str:
    stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    return f"triage-{stamp}-{secrets.token_hex(2)}"


def closure_of(root: Path, roots: list[str]) -> dict[str, str]:
    """Every book those roots include, with the digest it carries here."""
    digests: dict[str, str] = {}
    for name in roots:
        digests.update(certs.closure(root, name))
    return digests


def read_manifest(directory: Path) -> dict:
    try:
        manifest = json.loads((directory / "manifest.json").read_text())
    except (OSError, ValueError) as error:
        raise TriageError(f"no readable manifest under {directory}: {error}")
    if not isinstance(manifest, dict):
        raise TriageError(f"the manifest under {directory} is not an object")
    return manifest


def wave_log(directory: Path, book: str, wave: str) -> str:
    """One provisional wave's own log for one book, or the empty string."""
    return book_log(directory, book, f".pcert-{wave}")


def book_log(directory: Path, book: str, part: str = "") -> str:
    path = directory / (book.replace("/", "--") + part + ".certify.log")
    try:
        return path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return ""


def apply_substitutions(sources: dict[str, bytes], staging: Path):
    """The `farm.submit` prepare hook: write these books into the box's tree.

    The bytes go to `staging`, which is under `build/` and so is excluded
    from the mirror, and from there to the box one file at a time.  Nothing
    is written to the worktree's own `books/`: a triage substitution must not
    survive the run, must not be committed by accident, and must not be what
    another lane in this worktree is reading.
    """
    def prepare(host: str, remote: Path) -> None:
        for book, blob in sorted(sources.items()):
            local = staging / f"{book}.lisp"
            local.parent.mkdir(parents=True, exist_ok=True)
            local.write_bytes(blob)
            copied = farm.run(["rsync", "-a", str(local),
                               f"{host}:{remote}/{book}.lisp"], check=False)
            if copied.returncode != 0:
                raise TriageError(
                    f"{host}: cannot substitute {book}.lisp into {remote}: "
                    f"rsync exited {copied.returncode}: "
                    f"{copied.stdout.strip()}")
    return prepare


def one_round(host: str, root: Path, roots: list[str], number: int,
              sources: dict[str, bytes], out: Path, *, remote_root: str,
              acl2: str | None, cache: str | None, budget_seconds: int,
              jobs: int, wait_seconds: int, poll_seconds: int,
              pcert: bool = True) -> dict:
    """Submit one closure certification with these substitutions, and read it."""
    staging = out / "sources"
    into = out / f"round-{number}"
    identifier = farm.submit(
        host, root, list(roots), jobs,
        WAVE_TIMEOUT_SECONDS if pcert else budget_seconds, [],
        remote=Path(remote_root), closure=True, cache=cache, acl2=acl2,
        no_publish=True, prepare=apply_substitutions(sources, staging),
        pcert=pcert, budget_seconds=budget_seconds if pcert else None)
    code = farm.wait(
        host, identifier, root, poll_seconds, wait_seconds, cache,
        collect=lambda box, run, tree, remote, where: farm.fetch_logs(
            box, run, tree, remote, into))
    directories = sorted(path for path in into.glob("certify-*")
                         if path.is_dir())
    if not directories:
        raise TriageError(
            f"{host}: {identifier} brought back no certification evidence; "
            f"see {into}/{identifier}.log")
    return {"farm_run": identifier, "exit_code": code,
            "evidence": directories[-1]}


def triage(host: str, roots: list[str], *, root: Path = ROOT,
           remote_root: str, acl2: str | None = None, cache: str | None = None,
           budget_seconds: int = 300, rounds: int = 4, jobs: int = 8,
           wait_seconds: int = farm.DEFAULT_WAIT_SECONDS,
           poll_seconds: int = farm.POLL_SECONDS,
           out: Path | None = None, pcert: bool = True) -> dict:
    """Run the rounds and return the report, which is the tool's whole output."""
    identifier = run_id()
    out = out or (root / OUT_REL / identifier)
    out.mkdir(parents=True, exist_ok=True)
    digests = closure_of(root, roots)
    books = sorted(digests)
    report = green_check.audit(root, roots)
    runs = {run.run_id: run for run, _ in green_check.manifests(root)}

    substitutions: dict[str, Substitution] = {}
    sources: dict[str, bytes] = {}
    findings: dict[str, Finding] = {}
    untriageable: dict[str, str] = {}
    performed: list[dict] = []
    # The books that were still hiding behind something when the rounds
    # stopped: the last round's cascades, which never said a word of their own.
    hiding: list[str] = []

    for number in range(1, rounds + 1):
        assumed = [substitutions[book].sentence()
                   for book in sorted(substitutions)]
        outcome = one_round(
            host, root, roots, number, sources, out, remote_root=remote_root,
            acl2=acl2, cache=cache, budget_seconds=budget_seconds, jobs=jobs,
            wait_seconds=wait_seconds, poll_seconds=poll_seconds, pcert=pcert)
        evidence = outcome.pop("evidence")
        manifest = read_manifest(evidence)
        results = manifest.get("book_results") or {}
        walls = manifest.get("book_wall_seconds") or {}
        codes = manifest.get("acl2_exit_codes") or {}
        failed = sorted(book for book, verdict in results.items()
                        if verdict != "passed")
        provisional = bool(manifest.get("pcert"))
        this_round = []
        for book in failed:
            finding = (classify_pcert(book, evidence, manifest, number, assumed)
                       if provisional else
                       classify(book, book_log(evidence, book), codes.get(book),
                                number, walls.get(book), assumed))
            this_round.append(finding)
            if finding.kind != "cascade" and book not in findings:
                findings[book] = finding
        hiding = [one.book for one in this_round if one.kind == "cascade"]
        outcome.update({
            "round": number, "books_requested": len(results),
            "books_failed": len(failed),
            "assumptions": assumed,
            "kinds": {kind: sum(1 for one in this_round if one.kind == kind)
                      for kind in KINDS},
            "certify_wall_seconds": manifest.get("certify_wall_seconds"),
            "timeout_seconds": manifest.get("timeout_seconds"),
        })
        performed.append(outcome)
        if not failed:
            break
        # Only a book that never produced a `.pcert0` can still be hiding
        # another book's proofs: Create is the one dependency-ordered wave.
        # A Convert failure hides nothing, so a provisional round has no
        # second round to run unless Create failed somewhere.  Without
        # `--pcert` every red hides its dependents and every one is a
        # candidate.
        wanted = [one.book for one in this_round
                  if one.kind in ("independent", "timeout", "unexplained")
                  and not (provisional and one.proofs_done)
                  and not (provisional and one.reached is not None)
                  and one.book not in substitutions
                  and one.book not in untriageable]
        added = 0
        for book in wanted:
            answer = substitution_for(root, report, runs, book,
                                      digests.get(book, ""))
            if isinstance(answer, str):
                untriageable[book] = answer
                continue
            substitution, blob = answer
            substitutions[book] = substitution
            sources[book] = blob
            added += 1
        if not added:
            break

    hidden = sorted(book for book in hiding if book not in findings)
    return {
        "schema": SCHEMA,
        "triage_run": identifier,
        "host": host,
        "remote_root": remote_root,
        "roots": list(roots),
        "books_in_closure": len(books),
        "budget_seconds": budget_seconds,
        "rounds_requested": rounds,
        "provisional": pcert,
        "rounds": performed,
        "findings": [findings[book].as_json() for book in sorted(findings)],
        "substitutions": [substitutions[book].as_json()
                          for book in sorted(substitutions)],
        "untriageable": untriageable,
        "still_unanswered": hidden,
        "directory": str(out),
        "evidence_disclaimer":
            "A triage run certifies a tree whose sources were substituted on "
            "the box. Its certificates are published nowhere, its manifest is "
            "not archived, and nothing in this report is a certification "
            "claim about this revision.",
    }


# --------------------------------------------------------------------------
# the report
# --------------------------------------------------------------------------


def markdown(report: dict) -> str:
    """The report a lane reads: every independent red, and what it rests on."""
    mode = ("ACL2 provisional certification: a Create wave, one parallel "
            "Convert wave that does every book's proofs, and a Complete wave"
            if report.get("provisional") else
            "ordinary dependency-ordered certification, one layer of "
            "independent reds per round")
    lines = [f"# Triage {report['triage_run']} -- {report['host']}", ""]
    lines += [
        "**This is not evidence of certification.** " +
        report["evidence_disclaimer"] + " The certify run ids are left out "
        "for that reason; the farm run ids below locate the logs on the box.",
        "",
        f"Closure: {report['books_in_closure']} books under "
        f"{len(report['roots'])} root"
        f"{'' if len(report['roots']) == 1 else 's'} "
        f"({', '.join(report['roots'])}), "
        f"per-book budget {report['budget_seconds']} s, remote root "
        f"`{report['remote_root']}`.",
        "",
        f"Mode: {mode}.",
        "",
        "## Rounds",
        "",
    ]
    for entry in report["rounds"]:
        kinds = ", ".join(f"{count} {kind}"
                          for kind, count in entry["kinds"].items() if count)
        lines.append(
            f"- Round {entry['round']} ({entry['farm_run']}, exit "
            f"{entry['exit_code']}): {entry['books_failed']} of "
            f"{entry['books_requested']} books failed"
            + (f" -- {kinds}" if kinds else "")
            + (f"; {entry['certify_wall_seconds']} s of certification wall"
               if entry.get("certify_wall_seconds") else "")
            + (f"; {len(entry['assumptions'])} substitutions in effect"
               if entry["assumptions"] else "; the tree as committed")
            + ".")
    lines.append("")

    if not (report["findings"] or report["untriageable"]
            or report["still_unanswered"]):
        lines += ["No book in this closure failed on its own account in the "
                  "rounds above.", ""]
    by_kind = {kind: [one for one in report["findings"] if one["kind"] == kind]
               for kind in KINDS}
    titles = {
        "independent": "Independent reds",
        "timeout": "Timeouts (each is a finding in its own right)",
        "unexplained": "Failed with no ACL2 error and no timeout",
        "blocked": ("Proved, not certified -- every proof in these books "
                    "succeeded and a book below them has no certificate"),
    }
    for kind in ("independent", "timeout", "unexplained", "blocked"):
        entries = by_kind[kind]
        if not entries:
            continue
        lines += [f"## {titles[kind]} ({len(entries)})", ""]
        for one in entries:
            lines.append(f"### {one['book']} -- round {one['round']}")
            lines.append("")
            if one["wall_seconds"] is not None:
                lines.append(f"Wall {one['wall_seconds']} s; ACL2 exit "
                             f"{one['acl2_exit_code']!r}.")
                lines.append("")
            if one["first_error"]:
                lines += ["```", one["first_error"], "```", ""]
            if one["key_checkpoint"]:
                lines += [f"Key checkpoint (log line {one['error_log_line']} "
                          f"is the error above):", "```",
                          one["key_checkpoint"], "```", ""]
            if one["blocked_by"]:
                lines.append("Waiting on: "
                             + ", ".join(f"`{name}`"
                                         for name in one["blocked_by"]))
                lines.append("")
            if one["assuming"]:
                lines.append("Assuming:")
                lines += [f"- {sentence}" for sentence in one["assuming"]]
            else:
                lines.append("Assuming: nothing; the tree as committed.")
            lines.append("")

    if report["untriageable"]:
        lines += [f"## Could not be triaged ({len(report['untriageable'])})", "",
                  "No source to substitute, so nothing above these books "
                  "could be reached this run.", ""]
        for book, why in sorted(report["untriageable"].items()):
            lines.append(f"- `{book}`: {why}")
        lines.append("")
    if report["still_unanswered"]:
        lines += [f"## Still unanswered ({len(report['still_unanswered'])})", "",
                  "These books never got a verdict of their own: they "
                  "cascaded every round, or the rounds ran out.", "",
                  ", ".join(f"`{book}`" for book in report["still_unanswered"]),
                  ""]
    return "\n".join(lines) + "\n"


def write_report(report: dict) -> tuple[Path, Path]:
    out = Path(report["directory"])
    out.mkdir(parents=True, exist_ok=True)
    document = out / "report.md"
    data = out / "report.json"
    document.write_text(markdown(report), encoding="utf-8")
    data.write_text(json.dumps(report, indent=1, sort_keys=True) + "\n",
                    encoding="utf-8")
    return document, data


def plan(root: Path, roots: list[str]) -> list[str]:
    """What a run would do, read off this tree, with no farm and no ACL2."""
    digests = closure_of(root, roots)
    report = green_check.audit(root, roots)
    runs = {run.run_id: run for run, _ in green_check.manifests(root)}
    counts = report["counts"]
    lines = [f"triage: {len(digests)} books under {len(roots)} root"
             f"{'' if len(roots) == 1 else 's'}; "
             f"{counts['green']} green at their digest, {counts['red']} red, "
             f"{counts['never']} never, {counts['absent']} absent."]
    for book, entry in report["books_by_verdict"].items():
        if entry["verdict"] == "green":
            continue
        answer = substitution_for(root, report, runs, book, digests[book])
        if isinstance(answer, str):
            lines.append(f"triage: {book}: cannot substitute -- {answer}")
        else:
            lines.append(f"triage: {book}: {answer[0].sentence()}")
    return lines


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("host")
    parser.add_argument("roots", nargs="+",
                        help="book roots whose closure to triage")
    parser.add_argument("--remote-root", required=False, default=None,
                        help="the path to use on the box; required unless "
                             "--dry-run")
    parser.add_argument("--acl2", default=None,
                        help="exact ACL2 executable path ON THE HOST")
    parser.add_argument("--cache", default=None,
                        help="the certificate cache to READ on the host; a "
                             "triage run never writes to it")
    parser.add_argument("--budget-seconds", type=int, default=300,
                        help="per-book ACL2 budget (default 300; a book that "
                             "needs more is reported as a timeout finding)")
    parser.add_argument("--rounds", type=int, default=4)
    parser.add_argument("--no-pcert", dest="pcert", action="store_false",
                        help="use ordinary certification instead of ACL2's "
                             "provisional waves; then one round reports one "
                             "layer of reds and the substitution loop does "
                             "the rest")
    parser.add_argument("--jobs", type=int, default=8)
    parser.add_argument("--wait-seconds", type=int,
                        default=farm.DEFAULT_WAIT_SECONDS)
    parser.add_argument("--poll-seconds", type=int, default=farm.POLL_SECONDS)
    parser.add_argument("--root", default=str(ROOT))
    parser.add_argument("--out", default=None,
                        help=f"where to write the report (default: "
                             f"{OUT_REL}/<triage-run>)")
    parser.add_argument("--dry-run", action="store_true",
                        help="print what a run would substitute, read off "
                             "this tree; no farm, no ACL2")
    arguments = parser.parse_args(argv)
    root = Path(arguments.root).resolve()
    try:
        if arguments.dry_run:
            print("\n".join(plan(root, list(arguments.roots))))
            return 0
        if not arguments.remote_root:
            parser.error("--remote-root is required for a real run")
        report = triage(
            arguments.host, list(arguments.roots), root=root,
            remote_root=arguments.remote_root, acl2=arguments.acl2,
            cache=arguments.cache, budget_seconds=arguments.budget_seconds,
            rounds=arguments.rounds, jobs=arguments.jobs, pcert=arguments.pcert,
            wait_seconds=arguments.wait_seconds,
            poll_seconds=arguments.poll_seconds,
            out=Path(arguments.out) if arguments.out else None)
    except (TriageError, farm.FarmError, certs.UnreadableBook,
            ValueError, OSError) as error:
        print(f"triage: {error}", file=sys.stderr)
        return 2
    document, data = write_report(report)
    print(markdown(report))
    print(f"triage: {document}\ntriage: {data}", file=sys.stderr)
    return 1 if report["findings"] or report["untriageable"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
