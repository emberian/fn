#!/usr/bin/env python3
"""Rank the rules a book EXPORTS by the frames its includers waste on them.

proof_profile.py profiles one form of one book.  The fan it finds is usually
not the book's own: it is a rule some included book exports, which the
rewriter tries on almost every goal of every includer and which never
helps (lane d26-books, 2026-09-28: `fn-nntp-article-idp-is-consp` alone was
1.73M frames of books/nntp-post; docs/proof-style.md section 8 forbids
exporting `consp`/`true-listp` backchaining rules for that reason).  A local
`in-theory` in each slow includer is the workaround; the fix is at the
source, and this tool says which sources.

    python3 tools/rule_cost.py run persvati --remote-root /home/ember/fn-gates/X \\
        --jobs 16 [BOOK ...]          # default: every book of the Makefile roots
    python3 tools/rule_cost.py wait persvati <run-id> --remote-root ...
    python3 tools/rule_cost.py rank build/rule-cost/<run-id> \\
        --json planning/evidence/rule-cost-<date>.json --top 40

`run` needs a remote root that holds the certificates of the tree it
profiles (`tools/farm.py submit BOX --remote-root R` installs or makes them;
the books this run profiles are then `ld`ed there, not certified).  For each
book it writes a driver

    (accumulated-persistence t)
    (ld "<book>.lisp")                  ; from the book's directory
    (show-accumulated-persistence :frames)

and runs the drivers `--jobs` at a time, detached, under the box's wrap
(swarm-build on hbox), each with the certify runner's environment and a
timeout.  `wait` blocks on the run's `status` file (never on a process
pattern) and fetches the logs to build/rule-cost/<run-id>/.

`withdraw RANKING` appends a non-local `(in-theory (disable ...))` at the
END of each defining book for the selected rows (`--min-useless`,
`--max-useful-books`, `--min-useful-books` for a later tranche).  Then
certify; a book whose proof fails gets a local enable after its header
includes (`enable_in`).  `restore RUNE` takes a rune back out of every block
when its withdrawal breaks something an enable does not repair (a rule
whose being enabled keeps another pair from looping; docs/proof-style.md
section 8).

`rank` reads those logs.  Each rune's frames are split by ACL2 into useful
and useless (`[useful]`/`[useless]` under each rune of the `:frames`
listing).  A rune is attributed to the book whose source defines its name
(the ledger's reader, `local` included); a rune is EXPORTED into a profiled
book when that is another book.  The ranking is by useless frames summed
over every book the rune was tried in, and each row says in how many books
it was useful at all: those are the books that would need an explicit
enable if the rule were withdrawn at its source.

Frames are ACL2's per-rune cost proxy; ACL2 attributes no time per rune,
and this tool invents none.  The per-book wall time in the report is the
whole `ld` under accumulated persistence, which is slower than certifying.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
import datetime as dt
import json
import os
from pathlib import Path
import re
import secrets
import shlex
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(Path(__file__).resolve().parent))
import certs  # noqa: E402
import farm  # noqa: E402
import ledger  # noqa: E402

MARKER = "FN-RULE-COST-SECTION frames"
BOOK_LINE = re.compile(r"^FN-RULE-COST-BOOK (\S+)$", re.M)
WALL_LINE = re.compile(r"FN-RULE-COST-WALL (\S+) (\d+)$", re.M)
# `   2602     1036 (    2.51) (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND)` then
# `   2000      800    [useful]` and `    602      236    [useless]`.
RUNE_LINE = re.compile(
    r"^\s*(\d+)\s+(\d+)\s+\(\s*[\d.]+\)\s+\((:[A-Z-]+)\s+([^\s()]+)(?:\s+\.\s+(\d+))?\)\s*$")
SPLIT_LINE = re.compile(r"^\s*(\d+)\s+(\d+)\s+\[(useful|useless)\]\s*$")
STEPS = re.compile(r"^Prover steps counted:\s+(\d+)", re.M)
POLL_SECONDS = 20
USEFUL_KEPT = 20


class RuleCostError(Exception):
    pass


# --------------------------------------------------------------------------
# drivers and the remote run
# --------------------------------------------------------------------------


def driver(book: str) -> str:
    """The profile of one whole book, run from the book's directory."""
    name = Path(book).name
    return "".join([
        "(set-fmt-hard-right-margin 100000 state)\n",
        "(set-fmt-soft-right-margin 100000 state)\n",
        # The proof output is not what this run reads; the summaries (and
        # their step counts) and any error are kept.
        "(set-inhibit-output-lst '(prove proof-tree proof-builder event "
        "history observation warning warning!))\n",
        f'(cw "~%FN-RULE-COST-BOOK {book}~%")\n',
        "(accumulated-persistence t)\n",
        f'(ld "{name}.lisp" :ld-error-action :return)\n',
        f'(cw "~%{MARKER}~%")\n',
        "(show-accumulated-persistence :frames)\n",
        "(accumulated-persistence nil)\n",
        "(quit)\n",
    ])


def run_script(host: str, remote: str, run_dir: str, jobs: int, timeout: int,
               acl2: str) -> str:
    """The detached runner: xargs over the book list, a status file at the end."""
    one = (
        f'b="$1"; d=$(dirname "$b"); n=$(echo "$b" | tr / _); '
        f's=$(date +%s); cd {shlex.quote(remote)}/"$d" && '
        f'ACL2_CUSTOMIZATION=NONE ACL2_BOOK_HASH_ALISTP=NIL '
        f'SBCL_USER_ARGS="--dynamic-space-size 8000" '
        f'timeout {timeout} {shlex.quote(acl2)} < {shlex.quote(run_dir)}/drivers/"$n".lsp '
        f'> {shlex.quote(run_dir)}/logs/"$n".log 2>&1; e=$?; '
        f'echo "FN-RULE-COST-WALL $b $(( $(date +%s) - s ))" >> {shlex.quote(run_dir)}/logs/"$n".log; '
        f'echo "$b $e" >> {shlex.quote(run_dir)}/done'
    )
    body = (f"cd {shlex.quote(run_dir)} && : > done && "
            f"xargs -a books.txt -P {jobs} -n 1 sh -c {shlex.quote(one)} sh; "
            f"echo finished > status")
    wrap = farm.HOSTS[host].get("wrap") or ""
    inner = f"{wrap} sh -c {shlex.quote(body)}" if wrap else f"sh -c {shlex.quote(body)}"
    return (f"mkdir -p {shlex.quote(run_dir)} && cd {shlex.quote(run_dir)} && "
            f"setsid nohup {inner} > runner.log 2>&1 < /dev/null & echo started")


def default_books() -> list[str]:
    books: set[str] = set()
    for name in ledger.makefile_roots():
        books.update(certs.closure(ROOT, name))
    return sorted(books)


def run(host: str, remote: str, books: list[str], jobs: int, timeout: int,
        acl2: str | None) -> str:
    identifier = "rule-cost-" + dt.datetime.now(dt.timezone.utc).strftime(
        "%Y%m%dT%H%M%SZ") + "-" + secrets.token_hex(2)
    run_dir = f"{remote}/build/rule-cost/{identifier}"
    with tempfile.TemporaryDirectory() as scratch:
        base = Path(scratch)
        (base / "drivers").mkdir()
        (base / "logs").mkdir()
        for book in books:
            (base / "drivers" / (book.replace("/", "_") + ".lsp")).write_text(
                driver(book), encoding="utf-8")
        (base / "books.txt").write_text("".join(b + "\n" for b in books),
                                        encoding="utf-8")
        subprocess.run(["ssh", "-n", host, f"mkdir -p {shlex.quote(run_dir)}"],
                       check=True)
        subprocess.run(["rsync", "-a", f"{scratch}/", f"{host}:{run_dir}/"],
                       check=True)
    executable = acl2 or farm.HOSTS[host]["acl2"]
    print(identifier, flush=True)
    try:
        # ssh can hold the channel open until the detached runner ends (it
        # did on both boxes); the runner is setsid'd, so leaving is safe.
        subprocess.run(["ssh", "-n", host,
                        run_script(host, remote, run_dir, jobs, timeout, executable)],
                       check=True, timeout=60, stdout=subprocess.DEVNULL)
    except subprocess.TimeoutExpired:
        pass
    return identifier


def wait(host: str, remote: str, identifier: str, total: int | None) -> Path:
    run_dir = f"{remote}/build/rule-cost/{identifier}"
    while True:
        answer = subprocess.run(
            ["ssh", "-n", host,
             f"cat {shlex.quote(run_dir)}/status 2>/dev/null; "
             f"wc -l < {shlex.quote(run_dir)}/done 2>/dev/null; "
             f"wc -l < {shlex.quote(run_dir)}/books.txt"],
            stdout=subprocess.PIPE, text=True, check=False).stdout.split()
        if answer and answer[0] == "finished":
            break
        if len(answer) >= 2:
            print(f"{identifier}: {answer[0]} of {answer[1]} books", flush=True)
        time.sleep(POLL_SECONDS)
    local = ROOT / "build" / "rule-cost" / identifier
    local.mkdir(parents=True, exist_ok=True)
    subprocess.run(["rsync", "-a", f"{host}:{run_dir}/logs/", f"{local}/"],
                   check=True)
    subprocess.run(["rsync", "-a", f"{host}:{run_dir}/done", f"{local}/done.txt"],
                   check=True)
    return local


# --------------------------------------------------------------------------
# parsing and ranking
# --------------------------------------------------------------------------


def parse_log(text: str) -> dict:
    """One book's log: its runes' frames and tries, useful and useless."""
    book = BOOK_LINE.search(text)
    wall = WALL_LINE.search(text)
    head, marker, listing = text.partition(MARKER)
    runes: dict[str, dict[str, int]] = {}
    current: str | None = None
    for line in listing.splitlines():
        match = RUNE_LINE.match(line)
        if match:
            frames, tries, kind, name, index = match.groups()
            current = f"({kind} {name}" + (f" . {index})" if index else ")")
            runes[current] = {"frames": int(frames), "tries": int(tries),
                              "useful": 0, "useless": 0}
            continue
        split = SPLIT_LINE.match(line)
        if split and current is not None:
            runes[current][split.group(3)] = int(split.group(1))
    errors = head.count("ACL2 Error")
    return {
        "book": book.group(1) if book else None,
        "wall": int(wall.group(2)) if wall else None,
        "steps": sum(int(value) for value in STEPS.findall(head)),
        "complete": bool(marker),
        "errors": errors,
        "runes": runes,
    }


def rune_name(rune: str) -> str:
    return rune[1:-1].split()[1].lower()


def definers(books: list[str]) -> dict[str, list[str]]:
    """Rule name (lower case) -> the books whose source defines it.

    Usually one; two books may define the same function identically (one is
    then redundant where both are included: fn-scc-le-digits in the
    checkpoint arena and codec books), and neither is exported into the
    other."""
    owner: dict[str, list[str]] = {}
    for book in books:
        path = ROOT / (book + ".lisp")
        if not path.exists():
            continue
        parsed = ledger.analyze_book(path, book)
        # Only a non-local event exports its rules: a `local` lemma of the
        # same name in another book is not where an includer got it (and a
        # disable of it at that book's end would fail on include).
        for event in parsed.theorems + parsed.functions:
            if not event.local:
                names = owner.setdefault(str(event.name).lower(), [])
                if book not in names:
                    names.append(book)
    return owner


def rank(logs: list[Path], owner: dict[str, list[str]]) -> dict:
    per_book: dict[str, dict] = {}
    totals: dict[str, dict] = defaultdict(lambda: {
        "useless": 0, "useful": 0, "frames": 0, "tries": 0,
        "books_tried": 0, "books_useful": 0, "useful_in": [],
        "worst": []})
    for log in logs:
        parsed = parse_log(log.read_text(encoding="utf-8", errors="replace"))
        book = parsed["book"]
        if not book:
            continue
        frames_all = sum(r["frames"] for r in parsed["runes"].values())
        exported = 0
        for rune, value in parsed["runes"].items():
            sources = owner.get(rune_name(rune)) or []
            if not sources or book in sources:
                continue
            source = sources[0]
            exported += value["useless"]
            row = totals[rune]
            row["definer"] = source
            for key in ("useless", "useful", "frames", "tries"):
                row[key] += value[key]
            row["books_tried"] += 1
            if value["useful"]:
                row["books_useful"] += 1
                row["useful_in"].append(book)
            row["worst"].append((value["useless"], book))
        per_book[book] = {"wall": parsed["wall"], "steps": parsed["steps"],
                          "complete": parsed["complete"], "errors": parsed["errors"],
                          "frames": frames_all, "exported_useless": exported}
    ranked = []
    for rune, row in totals.items():
        row["worst"] = [[book, useless] for useless, book in
                        sorted(row["worst"], reverse=True)[:5]]
        row["useful_in"] = sorted(row["useful_in"])
        ranked.append({"rune": rune, **row})
    ranked.sort(key=lambda row: -row["useless"])
    return {"books": dict(sorted(per_book.items())), "runes": ranked}


def summary_lines(result: dict, top: int) -> list[str]:
    books = result["books"]
    frames = sum(book["frames"] for book in books.values())
    exported = sum(book["exported_useless"] for book in books.values())
    incomplete = sorted(b for b, v in books.items() if not v["complete"] or v["errors"])
    lines = [f"{len(books)} books profiled; {frames:,} frames in all, of which "
             f"{exported:,} useless frames on rules exported by another fn book",
             f"incomplete or erroring logs: {len(incomplete)}"
             + (f" ({', '.join(incomplete[:8])}{' ...' if len(incomplete) > 8 else ''})"
                if incomplete else ""),
             "",
             f"{'useless':>12} {'useful':>10} {'tried':>5} {'usefl':>5}  rune  <- definer"]
    for row in result["runes"][:top]:
        lines.append(f"{row['useless']:>12,} {row['useful']:>10,} {row['books_tried']:>5} "
                     f"{row['books_useful']:>5}  {row['rune']}  <- {row['definer']}")
    return lines


WITHDRAW_HEAD = ";; Withdrawn from includers (lane rule-hygiene, tools/rule_cost.py)."


def select(result: dict, *, max_useful_books: int, min_useless: int,
           kinds: tuple[str, ...], min_useful_books: int = 0) -> list[dict]:
    """The rows to withdraw: costly, useful in at most `max_useful_books`."""
    return [row for row in result["runes"]
            if row["useless"] >= min_useless
            and min_useful_books <= row["books_useful"] <= max_useful_books
            and row["rune"].split()[0][1:] in kinds
            and row["definer"].startswith("books/")]


def rune_designator(rune: str) -> str:
    """`(:REWRITE FN-X . 1)` -> `(:rewrite fn-x . 1)`, as an in-theory reads it."""
    return rune.lower()


def withdraw(rows: list[dict], root: Path = ROOT) -> dict[str, list[str]]:
    """Append one non-local `(in-theory (disable ...))` to each definer book.

    At the END of the book, so the book's own proofs keep the rule; every
    includer inherits it disabled.  A book that already carries a withdrawal
    block gets the new runes added to it.
    """
    by_book: dict[str, list[dict]] = defaultdict(list)
    for row in rows:
        by_book[row["definer"]].append(row)
    written: dict[str, list[str]] = {}
    for book, entries in sorted(by_book.items()):
        path = root / (book + ".lisp")
        text = path.read_text(encoding="utf-8")
        runes = [rune_designator(row["rune"]) for row in entries]
        prior: list[str] = []
        if WITHDRAW_HEAD in text:
            text, _, block = text.partition(WITHDRAW_HEAD)
            prior = re.findall(r"\(:[a-z-]+ [^()]+\)", block)
            text = text.rstrip() + "\n"
        runes = sorted(set(prior) | set(runes))
        lines = [WITHDRAW_HEAD,
                 ";; Each is tried in includers' proofs and pays for its frames in",
                 ";; almost none (planning/evidence/rule-cost-*.json has the counts;",
                 ";; docs/proof-style.md section 8).  An includer that needs one",
                 ";; enables it where it is used.",
                 "(in-theory (disable " + ("\n                    ".join(runes)) + "))"]
        path.write_text(text.rstrip() + "\n\n" + "\n".join(lines) + "\n",
                        encoding="utf-8")
        written[book] = runes
    return written


ENABLE_HEAD = ";; Rules withdrawn at their source that this book's proofs use"


def after_last_include(text: str) -> int:
    """The offset just past the include-book forms that open the book.

    The header's includes, not the last in the file: a book that includes
    arithmetic/top half-way down (books/store-node-invariants-base) needs
    the enables for the events above it too."""
    end = 0
    for form, line in ledger.Reader(text).top_level():
        inner = form[1] if (ledger.head(form) == "local" and len(form) > 1) else form
        if ledger.head(inner) == "include-book":
            end = line
        elif ledger.head(inner) != "in-package" and end:
            break
    if not end:
        raise RuleCostError("no top-level include-book")
    lines = text.splitlines(keepends=True)
    # The form starts on line `end`; it ends at the first line whose parens
    # balance from there (an include-book is short and holds no strings with
    # parens).
    depth, index = 0, end - 1
    while True:
        depth += lines[index].count("(") - lines[index].count(")")
        index += 1
        if depth <= 0:
            return sum(len(line) for line in lines[:index])


def enable_in(book: str, runes: list[str], root: Path = ROOT) -> None:
    """Add `(local (in-theory (enable RUNES)))` after the book's includes."""
    path = root / (book + ".lisp")
    text = path.read_text(encoding="utf-8")
    runes = [rune.lower() for rune in runes]
    if ENABLE_HEAD in text:
        before, _, rest = text.partition(ENABLE_HEAD)
        block, _, after = rest.partition(")))\n")
        runes = sorted(set(runes) | set(re.findall(r"\(:[a-z-]+ [^()]+\)", block)))
        text = before.rstrip("\n") + "\n\n" + after.lstrip("\n")
    at = after_last_include(text)
    block = (f"\n{ENABLE_HEAD}\n;; (lane rule-hygiene, tools/rule_cost.py).\n"
             "(local (in-theory (enable " + "\n                          ".join(sorted(runes))
             + ")))\n")
    rest = text[at:]
    if rest and not rest.startswith("\n"):
        block += "\n"
    path.write_text(text[:at] + block + rest, encoding="utf-8")


def restore(rune: str, root: Path = ROOT) -> list[str]:
    """Take one rune back out of every withdrawal and enable block.

    For a rune whose withdrawal broke something no enable repairs (a rule
    whose being enabled kept another pair from looping: the definition of
    fn-lg-declared-len, 2026-09-28).  Empty blocks are removed whole."""
    rune = rune.lower()
    touched = []
    for path in sorted(list((root / "books").glob("**/*.lisp"))
                       + list((root / "tests" / "acl2").glob("*.lisp"))):
        text = path.read_text(encoding="utf-8")
        if rune not in text or ("lane rule-hygiene" not in text):
            continue
        new = text
        for head, opener, closer in ((WITHDRAW_HEAD, "(in-theory (disable ", "))"),
                                     (ENABLE_HEAD, "(local (in-theory (enable ", ")))")):
            if head not in new:
                continue
            before, _, rest = new.partition(head)
            start = rest.index(opener)
            end = rest.index(closer + "\n", start) + len(closer) + 1
            runes = re.findall(r"\(:[a-z-]+ [^()]+\)", rest[start:end])
            if rune not in runes:
                continue
            runes.remove(rune)
            pad = " " * len(opener)
            if runes:
                block = opener + ("\n" + pad).join(runes) + closer + "\n"
                new = before + head + rest[:start] + block + rest[end:]
            else:
                new = before.rstrip("\n") + "\n" + rest[end:]
                if not new.endswith("\n"):
                    new += "\n"
        if new != text:
            path.write_text(new, encoding="utf-8")
            touched.append(str(path.relative_to(root)))
    return touched


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = parser.add_subparsers(dest="action", required=True)
    start = sub.add_parser("run")
    start.add_argument("host", choices=sorted(farm.HOSTS))
    start.add_argument("books", nargs="*")
    start.add_argument("--remote-root", required=True)
    start.add_argument("--jobs", type=int, default=12)
    start.add_argument("--timeout", type=int, default=1800)
    start.add_argument("--acl2")
    block = sub.add_parser("wait")
    block.add_argument("host", choices=sorted(farm.HOSTS))
    block.add_argument("identifier")
    block.add_argument("--remote-root", required=True)
    order = sub.add_parser("rank")
    order.add_argument("logs", nargs="+", help="directories of logs, or log files")
    order.add_argument("--json", type=Path, help="write the ranking here")
    order.add_argument("--top", type=int, default=40)
    order.add_argument("--keep", type=int, default=400,
                       help="runes kept in the JSON (the ranking's head)")
    pull = sub.add_parser("withdraw", help="append the disable blocks to the definers")
    pull.add_argument("ranking", type=Path, help="a `rank --json` file")
    pull.add_argument("--max-useful-books", type=int, default=1)
    pull.add_argument("--min-useful-books", type=int, default=0,
                      help="a later tranche: leave the rows an earlier one withdrew")
    pull.add_argument("--min-useless", type=int, default=300_000)
    pull.add_argument("--kinds", default="REWRITE,LINEAR,FORWARD-CHAINING,DEFINITION")
    pull.add_argument("--dry-run", action="store_true")
    pull.add_argument("--enable-in", choices=("none", "useful", "failed"), default="none",
                      help="add local enables: none (default; certify, then enable "
                           "where a proof fails), in every book where a withdrawn "
                           "rule was useful (over-enables: 216 of 309 such blocks "
                           "were not needed, and a book-wide enable can turn on a "
                           "rule an intermediate book disabled), or in the "
                           "useful books a certify manifest (--manifest) did not pass")
    pull.add_argument("--manifest", type=Path)
    back = sub.add_parser("restore", help="take runes back out of every block")
    back.add_argument("runes", nargs="+", help="e.g. '(:definition fn-x)'")
    args = parser.parse_args(argv)
    try:
        if args.action == "restore":
            for rune in args.runes:
                print(rune, " ".join(restore(rune)))
            return 0
        if args.action == "withdraw":
            result = json.loads(args.ranking.read_text(encoding="utf-8"))
            rows = select(result, max_useful_books=args.max_useful_books,
                          min_useless=args.min_useless,
                          min_useful_books=args.min_useful_books,
                          kinds=tuple(":" + kind for kind in args.kinds.split(",")))
            for row in rows:
                print(f"{row['useless']:>12,} {row['books_useful']:>3} {row['rune']} "
                      f"<- {row['definer']}")
            needs: dict[str, list[str]] = defaultdict(list)
            passed: set[str] = set()
            if args.enable_in == "failed":
                if not args.manifest:
                    parser.error("--enable-in failed needs --manifest")
                results = json.loads(args.manifest.read_text())["book_results"]
                passed = {book for book, verdict in results.items() if verdict == "passed"}
            if args.enable_in != "none":
                for row in rows:
                    for book in row["useful_in"]:
                        if book not in passed:
                            needs[book].append(row["rune"])
            if not args.dry_run:
                written = withdraw(rows)
                for book, runes in sorted(needs.items()):
                    enable_in(book, runes)
                print(f"withdrew {sum(map(len, written.values()))} rune(s) in "
                      f"{len(written)} book(s); enabled {sum(map(len, needs.values()))} "
                      f"where useful, in {len(needs)} book(s)")
            return 0
        if args.action == "run":
            books = [b.removesuffix(".lisp") for b in args.books] or default_books()
            identifier = run(args.host, args.remote_root, books, args.jobs,
                             args.timeout, args.acl2)
            print(f"{identifier}: {len(books)} books on {args.host}; "
                  f"`rule_cost.py wait {args.host} {identifier} --remote-root "
                  f"{args.remote_root}`", file=sys.stderr)
            return 0
        if args.action == "wait":
            print(wait(args.host, args.remote_root, args.identifier, None))
            return 0
        logs: list[Path] = []
        for item in args.logs:
            path = Path(item)
            logs.extend(sorted(path.glob("*.log")) if path.is_dir() else [path])
        result = rank(logs, definers(default_books()))
        print("\n".join(summary_lines(result, args.top)))
        if args.json:
            kept = dict(result)
            # useful_in is what `withdraw` enables from; past USEFUL_KEPT books
            # a rule is not a withdrawal candidate, and the count says how many.
            kept["runes"] = [dict(row, useful_in=row["useful_in"][:USEFUL_KEPT])
                             for row in result["runes"][:args.keep]]
            kept["about"] = ("Generated by python3 tools/rule_cost.py rank: rules "
                             "exported by one fn book into another, by useless "
                             "accumulated-persistence frames summed over every "
                             "profiled book (the whole book ld'ed under "
                             "(accumulated-persistence t)). useful_in names the "
                             "books where the rule contributed at all.")
            args.json.write_text(json.dumps(kept, indent=1) + "\n", encoding="utf-8")
        return 0
    except (RuleCostError, subprocess.CalledProcessError, OSError) as error:
        print(f"rule_cost: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
