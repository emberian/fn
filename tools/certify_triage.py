#!/usr/bin/env python3
"""Which of a certify run's failures are real, from the run directory alone.

On 2026-10-04 a raw `grep -l "FAILED\\|ACL2 Error"` over the per-book logs of
`certify-20261004T022302Z-3294774` said 297.  The truth was 3 real reds, 262
books refused only because an include had no certificate, and 31 books that
PASSED whose echoed source merely contains the word `:FAILED` (the 297th hit is
the run's combined `certify.log`).  The manifest could not say so: it records
`passed` / `failed` per book and a reason list, never *why* a book failed.

    python3 tools/certify_triage.py build/acl2/certify-... [--tsv OUT.tsv]

Every per-book log (`*.certify.log`, not the combined `certify.log`) lands in
exactly one kind:

  clean      no failure text at all.
  echo       the book PASSED and the only "FAILED"/"ACL2 Error" text is echoed
             source (`:FAILED`, `FN-PULL-FAIL`, a comment).  The false positive
             a substring grep cannot avoid; an error is only a line that
             *starts* with `ACL2 Error` / `HARD ACL2 ERROR`, or the banner
             `******** FAILED ********`.
  must-fail  the book PASSED and the log holds a real ACL2 error line: an
             error some form caught by design.  `must-fail` normally prints
             nothing, so this is rare; it is never a red.
  real       the book failed with an error of its own (a defthm, defun or
             verify-guards refused).  The first error and the last key
             checkpoint are printed.
  cascade    the book failed and every error is an `include-book` of a book
             with no certificate (or Complete's "no .cert file at least as
             recent").  Nothing is wrong in this book; the cause is the named
             book, which is itself `real` or a `cascade` of something.
  limit      the book failed on a prover step limit, a time limit, or a
             `timed out` exit.
  killed     the book's ACL2 was killed (exit 143, 137, -9, -15): earlyoom or
             the cgroup, not a proof.
  other      failed with none of the above; read the log.

The verdict a book "passed" is the manifest's `book_results` when
`manifest.json` is in the directory, else this book's own
`FN_CERTIFY_SUCCESS <nonce> <digest>` marker line.  The exit code comes from
the manifest's `acl2_exit_codes`, else the book's `*.active.json`.

The classification of an individual error block is `tools/triage.py`'s
`acl2_errors` (wrapped-line aware); this tool only decides what a *run* of
logs adds up to.  Exit 0 when nothing is real, limit, killed or other; 1
otherwise; 2 when the directory has no logs.
"""

from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import triage  # noqa: E402

KINDS = ("real", "cascade", "must-fail", "limit", "killed", "other")
ALL_KINDS = KINDS + ("echo", "clean")
LOG_SUFFIX = ".certify.log"
SUCCESS_LINE = re.compile(r"^FN_CERTIFY_SUCCESS [0-9a-f]{32} [0-9a-f]{12}\s*$", re.M)
# A line ACL2 itself printed, as opposed to source echoed back to the log.
REAL_ERROR_LINE = re.compile(r"^(?:ACL2 Error|HARD ACL2 ERROR)", re.M)
REAL_FAILED_BANNER = re.compile(r"^\*{8} FAILED \*{8}", re.M)
LIMIT_TEXT = re.compile(r"step-limit|time-limit|prover steps? .*exceeded", re.I)
KILLED_CODES = {143, 137, -9, -15}
CHECKPOINT_LINES = 12


def book_name(log: Path) -> str:
    return log.name.removesuffix(LOG_SUFFIX).replace("--", "/")


def read_json(path: Path) -> dict:
    try:
        value = json.loads(path.read_text())
    except (OSError, ValueError):
        return {}
    return value if isinstance(value, dict) else {}


def checkpoint(text: str, limit: int = CHECKPOINT_LINES) -> str | None:
    """The last `*** Key checkpoint...` block, cut at `limit` lines.

    Looser than `triage.key_checkpoint`, which wants the whole header on one
    line: ACL2 wraps "...at the top level / before a :DO-NOT-INDUCT hint
    stopped the proof attempt: ***" over two, and a one-line match found
    nothing for `books/consumer-reason`.
    """
    lines = text.splitlines()
    starts = [n for n, line in enumerate(lines) if line.startswith("*** Key checkpoint")]
    if not starts:
        return None
    body = []
    for line in lines[starts[-1]:]:
        if body and (triage.ERROR_START.match(line) or line.startswith(("Summary", "********"))):
            break
        body.append(line.rstrip())
    while body and not body[-1]:
        body.pop()
    if len(body) > limit:
        body = body[:limit] + [f"... ({len(body) - limit} more lines in the log)"]
    return "\n".join(body)


def exit_code(directory: Path, log: Path, book: str, manifest: dict):
    codes = manifest.get("acl2_exit_codes") or {}
    if book in codes:
        return codes[book]
    return read_json(directory / (log.name.removesuffix(LOG_SUFFIX) + ".active.json")).get("exit_code")


def passed(book: str, text: str, manifest: dict) -> bool:
    results = manifest.get("book_results") or {}
    if book in results:
        return results[book] == "passed"
    return bool(SUCCESS_LINE.search(text))


def classify(book: str, text: str, code, manifest: dict | None = None) -> dict:
    """One book's kind and detail, from its log text and ACL2 exit code."""
    manifest = manifest or {}
    row = {"book": book, "kind": "clean", "detail": "", "checkpoint": None}
    has_error = bool(REAL_ERROR_LINE.search(text) or REAL_FAILED_BANNER.search(text))
    suspicious = has_error or re.search(r"FAILED|ACL2 Error", text)
    if passed(book, text, manifest):
        if has_error:
            row.update(kind="must-fail", detail="passed; error text caught by design")
        elif suspicious:
            row.update(kind="echo", detail="passed; failure words only in echoed source")
        return row
    if isinstance(code, str) and code.startswith("timed out"):
        row.update(kind="limit", detail=code)
        return row
    if code in KILLED_CODES or (isinstance(code, str) and code.lstrip("-").isdigit()
                                and int(code) in KILLED_CODES):
        row.update(kind="killed", detail=f"ACL2 exit {code}")
        return row
    errors = triage.acl2_errors(text)
    own = [error for error in errors if error.news]
    cascades = [error for error in errors if error.cascade_of]
    if own:
        first = own[0].text()
        if any(LIMIT_TEXT.search(error.text()) for error in own):
            row.update(kind="limit", detail=first)
        else:
            row.update(kind="real", detail=first,
                       checkpoint=checkpoint(text))
    elif cascades:
        blockers = sorted({error.cascade_of for error in cascades if error.cascade_of})
        row.update(kind="cascade", detail="blocked by " + ", ".join(blockers))
    else:
        row.update(kind="other",
                   detail=errors[0].text() if errors else "failed with no ACL2 error text")
    return row


def triage_run(directory: Path) -> list[dict]:
    manifest = read_json(directory / "manifest.json")
    rows = []
    for log in sorted(directory.glob("*" + LOG_SUFFIX)):
        book = book_name(log)
        text = log.read_text(encoding="utf-8", errors="replace")
        row = classify(book, text, exit_code(directory, log, book, manifest), manifest)
        row["log"] = log.name
        rows.append(row)
    return rows


def write_tsv(rows: list[dict], path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    lines = ["log\tbook\tkind\tdetail"]
    for row in rows:
        detail = " ".join(row["detail"].split())
        lines.append(f"{row['log']}\t{row['book']}\t{row['kind']}\t{detail}")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def report(directory: Path, rows: list[dict]) -> list[str]:
    counts = Counter(row["kind"] for row in rows)
    lines = [f"== certify triage {directory.name}: {len(rows)} book logs"]
    lines.append("   " + " / ".join(f"{kind} {counts[kind]}" for kind in KINDS))
    lines.append(f"   (not failures: echo {counts['echo']}, clean {counts['clean']})")
    for kind in ("real", "limit", "killed", "other"):
        for row in (r for r in rows if r["kind"] == kind):
            lines.append(f"-- {kind.upper()} {row['book']}: {row['detail']}")
            if row["checkpoint"]:
                lines += ["   | " + line for line in row["checkpoint"].splitlines()]
    roots = Counter(blocker for row in rows if row["kind"] == "cascade"
                    for blocker in row["detail"].removeprefix("blocked by ").split(", "))
    if roots:
        lines.append("-- cascades directly blocked by: " + ", ".join(
            f"{book} ({count})" for book, count in roots.most_common(8)))
    return lines


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("run_dir", type=Path, help="a certify run directory of *.certify.log")
    parser.add_argument("--tsv", type=Path, help="also write the per-log table here")
    arguments = parser.parse_args(argv)
    rows = triage_run(arguments.run_dir)
    if not rows:
        print(f"no *{LOG_SUFFIX} under {arguments.run_dir}", file=sys.stderr)
        return 2
    if arguments.tsv:
        write_tsv(rows, arguments.tsv)
    print("\n".join(report(arguments.run_dir, rows)))
    counts = Counter(row["kind"] for row in rows)
    return 1 if any(counts[kind] for kind in ("real", "limit", "killed", "other")) else 0


if __name__ == "__main__":
    raise SystemExit(main())
