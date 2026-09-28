#!/usr/bin/env python3
"""Measure what the tau system costs each book, and turn it off where it pays.

Tau's work is invisible to the numbers every other tool reads: it is not
rewriting, so ACL2 counts no prover steps for it, and proof_profile and
rule_cost (which read accumulated-persistence frames) see nothing.  Only
time shows it.  Lane d26-books-2 (2026-09-28) found it was half the proof
time of three books over the ten-second line, steps unchanged.

    python3 tools/tau_cost.py run persvati --remote-root /home/ember/fn-gates/X \\
        --jobs 2 [BOOK ...]           # default: every book of the Makefile roots
    python3 tools/tau_cost.py wait persvati <run-id> --remote-root ...
    python3 tools/tau_cost.py rank build/tau-cost/<run-id> [...] \\
        --json planning/evidence/tau-cost-<date>.json
    python3 tools/tau_cost.py apply planning/evidence/tau-cost-<date>.json \\
        [--min-seconds 1 --min-fraction 0.2]

`run` needs a remote root holding the certificates of the tree
(`tools/farm.py submit BOX --all --remote-root R`).  Each book is `ld`ed
twice from its own directory, one job after the other so both variants see
the same load:

    on   (time$ (ld "<book>.lisp" :ld-error-action :continue))
    off  the same, on a copy of the book with
         (local (in-theory (disable (tau-system))))
         inserted after the header's include-books

`--variant applied` pairs the remote's text (as it was) with this worktree's
(after `apply`): the confirmation, measured again, of what was applied, and
the forms of it that still fail.  `--variant local` `ld`s this worktree's
text alone.  The time is `time$`'s
runtime of the whole `ld` (includes and all; CPU time, which load moves less
than wall), with the realtime beside it.  `:continue` runs every form, so an
off log names each form that fails without tau; a failure the on log shares
(a must-fail, an error of the book's own) is not counted.

`rank` pairs the logs and ranks books by runtime saved.  For each book it
also lists the forms that FAIL with tau off and the forms that got slower
(`--slower-seconds`), the forms `apply` turns tau back on for.

`apply` writes the tau-off block after the header includes of every book
that saves at least `--min-seconds` or `--min-fraction` of its on-runtime,
and wraps each failing or slower top-level form in a local enable/disable
pair.  The theorem set is unchanged: every event is `local` (the block) or
an `in-theory` (the pairs, also local).  Then certify; `run --variant local`
on the applied books finds any form still failing (a failure can hide
behind an earlier one it cascaded from).
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
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
import farm  # noqa: E402
import ledger  # noqa: E402
import rule_cost  # noqa: E402

BOOK_LINE = re.compile(r"^FN-TAU-COST-BOOK (\S+) (\S+)$", re.M)
WALL_LINE = re.compile(r"FN-TAU-COST-WALL (\S+) (\S+) (\d+) (\S+) (\S+)$", re.M)
TIME_LINE = re.compile(
    r"took\s*\n?;?\s*([\d.]+) seconds realtime, ([\d.]+) seconds runtime", re.M)
SUMMARY = re.compile(
    r"^Summary\nForm:\s+\(\s*([A-Z0-9*$!<>=?/+:.-]+)\s*([^\s()]*)[^\n]*\n"
    r"(?:.*\n)*?Time:\s+([\d.]+) seconds[^\n]*\n(?:Prover steps counted:\s+(\d+))?",
    re.M)
ERROR = re.compile(r"^ACL2 Error(?: \[([A-Za-z-]+)\])? in \(\s*([A-Z0-9*$!<>=?/+:.-]+)\s*"
                   r"([^\s()]*)", re.M)
# A form that fails only because an earlier one did: it names what that one
# would have defined ([Translate]), or it is a theory or grouping form.
CASCADE_KINDS = {"deftheory", "progn", "in-theory", "local"}
OFF_PREFIX = "fn-tau-off--"
OFF_HEAD = ";; The tau system is off in this book (lane tau-pass, tools/tau_cost.py)."
OFF_BLOCK = (OFF_HEAD + "\n"
             ";; Its work is proof time no prover step counts (docs/proof-style.md\n"
             ";; 9.1); planning/evidence/tau-cost-*.json has this book's figures.\n"
             "(local (in-theory (disable (tau-system))))\n")
ON_OPEN = "(local (in-theory (enable (tau-system)))) ; tau-cost: this form needs tau\n"
ON_CLOSE = "(local (in-theory (disable (tau-system))))\n"
ALREADY = re.compile(r"\(in-theory \(disable \(tau-system\)\)\)")
POLL_SECONDS = 20


class TauCostError(Exception):
    pass


# --------------------------------------------------------------------------
# sources
# --------------------------------------------------------------------------


def forms_with_spans(text: str) -> list[tuple[object, int, int]]:
    """Every top-level form with its start and end offsets."""
    reader = ledger.Reader(text)
    spans = []
    while True:
        reader.skip_space()
        if reader.pos >= len(text):
            return spans
        start = reader.pos
        form = reader.form()
        spans.append((form, start, reader.pos))


def header_end(text: str) -> int:
    """The offset just past the header's include-books (or its in-package)."""
    try:
        return rule_cost.after_last_include(text)
    except rule_cost.RuleCostError:
        for form, _start, end in forms_with_spans(text):
            if ledger.head(form) == "in-package":
                return end + (1 if text[end:end + 1] == "\n" else 0)
        return 0


def tau_off(text: str) -> str:
    """The book with tau off after its header includes (unchanged if already)."""
    if ALREADY.search(text):
        return text
    at = header_end(text)
    rest = text[at:]
    return text[:at] + "\n" + OFF_BLOCK + ("" if rest.startswith("\n") else "\n") + rest


def event_names(form: object) -> set[str]:
    """Lower-case names of the events a top-level form defines (nested too)."""
    names: set[str] = set()

    def walk(node: object) -> None:
        if not isinstance(node, list) or not node:
            return
        head = ledger.head(node)
        if head in ("local", "encapsulate", "progn", "defsection", "with-output",
                    "must-fail-checked", "make-event"):
            for child in node[1:]:
                walk(child)
            return
        if head and len(node) > 1 and not isinstance(node[1], list):
            names.add(str(node[1]).lower())
        for child in node[1:]:
            if isinstance(child, list):
                walk(child)

    walk(form)
    return names


def enable_around(text: str, names: set[str]) -> tuple[str, set[str]]:
    """Wrap each top-level form that defines one of `names` in a tau-on pair."""
    spans = forms_with_spans(text)
    found: set[str] = set()
    edits: list[tuple[int, int]] = []
    for form, start, end in spans:
        hit = event_names(form) & names
        if hit and ON_OPEN not in text[max(0, start - len(ON_OPEN) - 1):start]:
            found |= hit
            edits.append((start, end))
    for start, end in reversed(edits):
        line_start = text.rfind("\n", 0, start) + 1
        after = end + (1 if text[end:end + 1] == "\n" else 0)
        text = (text[:line_start] + ON_OPEN + text[line_start:after]
                + ("" if text[after - 1:after] == "\n" else "\n") + ON_CLOSE + text[after:])
    return text, found


# --------------------------------------------------------------------------
# the remote run
# --------------------------------------------------------------------------


def driver(book: str, variant: str) -> str:
    name = Path(book).name
    target = name if variant == "on" else OFF_PREFIX + name
    return "".join([
        "(set-fmt-hard-right-margin 100000 state)\n",
        "(set-fmt-soft-right-margin 100000 state)\n",
        "(set-inhibit-output-lst '(prove proof-tree proof-builder event "
        "history observation warning warning!))\n",
        "(set-inhibited-summary-types '(rules hint-events warnings splitter-rules value))\n",
        f'(cw "~%FN-TAU-COST-BOOK {book} {variant}~%")\n',
        f'(time$ (ld "{target}.lisp" :ld-error-action :continue))\n',
        "(quit)\n",
    ])


def run_script(remote: str, run_dir: str, jobs: int, timeout: int, acl2: str,
               wrap: str, off_timeout: int | None = None) -> str:
    """Tasks `book variant`, xargs -P jobs; a status file at the end."""
    one = (
        'b="$1"; v="$2"; d=$(dirname "$b"); n=$(basename "$b"); '
        'f=$(echo "$b" | tr / _); '
        f'cd {shlex.quote(remote)}/"$d" || exit 0; '
        f'if [ "$v" != on ]; then cp {shlex.quote(run_dir)}/sources/"$f".lisp '
        f'"{OFF_PREFIX}$n.lisp"; fi; '
        f't={timeout}; if [ "$v" = off ]; then t={off_timeout or timeout}; fi; '
        'l=$(cut -d" " -f1 /proc/loadavg); s=$(date +%s); '
        'ACL2_CUSTOMIZATION=NONE ACL2_BOOK_HASH_ALISTP=NIL '
        'SBCL_USER_ARGS="--dynamic-space-size 8000" '
        f'timeout "$t" {shlex.quote(acl2)} < {shlex.quote(run_dir)}/drivers/"$f.$v".lsp '
        f'> {shlex.quote(run_dir)}/logs/"$f.$v".log 2>&1; e=$?; '
        f'if [ "$v" != on ]; then rm -f "{OFF_PREFIX}$n".*; fi; '
        f'echo "FN-TAU-COST-WALL $b $v $(( $(date +%s) - s )) $e $l/$(cut -d" " -f1 /proc/loadavg)" '
        f'>> {shlex.quote(run_dir)}/logs/"$f.$v".log; '
        f'echo "$b $v $e" >> {shlex.quote(run_dir)}/done'
    )
    body = (f"cd {shlex.quote(run_dir)} && : > done && "
            f"xargs -a tasks.txt -P {jobs} -n 2 sh -c {shlex.quote(one)} sh; "
            f"echo finished > status")
    inner = f"{wrap} sh -c {shlex.quote(body)}" if wrap else f"sh -c {shlex.quote(body)}"
    return (f"cd {shlex.quote(run_dir)} && "
            f"setsid nohup {inner} > runner.log 2>&1 < /dev/null & echo started")


def run(host: str, remote: str, books: list[str], jobs: int, timeout: int,
        acl2: str | None, variant: str, off_timeout: int | None = None) -> str:
    identifier = ("tau-cost-" + dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
                  + "-" + secrets.token_hex(2))
    run_dir = f"{remote}/build/tau-cost/{identifier}"
    tasks: list[str] = []
    skipped: list[str] = []
    with tempfile.TemporaryDirectory() as scratch:
        base = Path(scratch)
        for sub in ("drivers", "logs", "sources"):
            (base / sub).mkdir()
        for book in books:
            flat = book.replace("/", "_")
            text = (ROOT / (book + ".lisp")).read_text(encoding="utf-8")
            if variant == "local":
                pairs = [("local", text)]
            elif variant == "applied":
                # The remote tree holds the book as it was; this worktree's
                # text (after `apply`) is the off variant, measured beside it.
                pairs = [("on", None), ("off", text)]
            elif ALREADY.search(text):
                skipped.append(book)
                continue
            else:
                pairs = [("on", None), ("off", tau_off(text))]
            for name, source in pairs:
                (base / "drivers" / f"{flat}.{name}.lsp").write_text(
                    driver(book, name), encoding="utf-8")
                if source is not None:
                    (base / "sources" / f"{flat}.lisp").write_text(source, encoding="utf-8")
                tasks.append(f"{book} {name}\n")
        (base / "tasks.txt").write_text("".join(tasks), encoding="utf-8")
        (base / "skipped.txt").write_text("".join(b + "\n" for b in skipped),
                                          encoding="utf-8")
        subprocess.run(["ssh", "-n", host, f"mkdir -p {shlex.quote(run_dir)}"], check=True)
        subprocess.run(["rsync", "-a", f"{scratch}/", f"{host}:{run_dir}/"], check=True)
    executable = acl2 or farm.HOSTS[host]["acl2"]
    print(f"{identifier}: {len(tasks)} tasks; {len(skipped)} books already tau-off",
          flush=True)
    try:
        subprocess.run(["ssh", "-n", host,
                        run_script(remote, run_dir, jobs, timeout, executable,
                                   farm.HOSTS[host].get("wrap") or "", off_timeout)],
                       check=True, timeout=60, stdout=subprocess.DEVNULL)
    except subprocess.TimeoutExpired:
        pass
    return identifier


def wait(host: str, remote: str, identifier: str) -> Path:
    run_dir = f"{remote}/build/tau-cost/{identifier}"
    while True:
        answer = subprocess.run(
            ["ssh", "-n", host,
             f"cat {shlex.quote(run_dir)}/status 2>/dev/null; "
             f"wc -l < {shlex.quote(run_dir)}/done 2>/dev/null; "
             f"wc -l < {shlex.quote(run_dir)}/tasks.txt"],
            stdout=subprocess.PIPE, text=True, check=False).stdout.split()
        if answer and answer[0] == "finished":
            break
        if len(answer) >= 2:
            print(f"{identifier}: {answer[0]} of {answer[1]} tasks", flush=True)
        time.sleep(POLL_SECONDS)
    local = ROOT / "build" / "tau-cost" / identifier
    local.mkdir(parents=True, exist_ok=True)
    subprocess.run(["rsync", "-a", f"{host}:{run_dir}/logs/", f"{local}/"], check=True)
    subprocess.run(["rsync", "-a", f"{host}:{run_dir}/skipped.txt",
                    f"{local}/skipped.txt"], check=True)
    return local


# --------------------------------------------------------------------------
# parsing and ranking
# --------------------------------------------------------------------------


def parse_log(text: str) -> dict:
    book = BOOK_LINE.search(text)
    wall = WALL_LINE.search(text)
    timed = TIME_LINE.search(text)
    forms: list[dict] = []
    seen: dict[str, int] = {}
    for match in SUMMARY.finditer(text):
        kind, name, seconds, steps = match.groups()
        key = f"{kind} {name}".strip().lower()
        seen[key] = seen.get(key, 0) + 1
        if seen[key] > 1:
            key = f"{key} #{seen[key]}"
        forms.append({"form": key, "seconds": float(seconds),
                      "steps": int(steps) if steps else None})
    tags: dict[str, set[str]] = {}
    for tag, kind, name in ERROR.findall(text):
        tags.setdefault(f"{kind} {name}".strip().lower(), set()).add(tag or "")
    errors = list(tags)  # log order: the first is the one the rest may follow from
    primary = list(form for form, seen in tags.items()
                     if "Translate" not in seen and form.split()[0] not in CASCADE_KINDS)
    return {
        "book": book.group(1) if book else None,
        "variant": book.group(2) if book else None,
        "wall": int(wall.group(3)) if wall else None,
        "exit": int(wall.group(4)) if wall else None,
        "load": wall.group(5) if wall else None,
        "realtime": float(timed.group(1)) if timed else None,
        "runtime": float(timed.group(2)) if timed else None,
        "steps": sum(f["steps"] or 0 for f in forms),
        "forms": forms,
        "errors": errors,
        "primary": primary,
        # The form after the last summary is the one a timeout cut.
        "last_form": forms[-1]["form"] if forms else None,
    }


def rank(logs: list[Path], slower_seconds: float) -> dict:
    by_book: dict[str, dict[str, dict]] = {}
    for log in logs:
        parsed = parse_log(log.read_text(encoding="utf-8", errors="replace"))
        if parsed["book"]:
            by_book.setdefault(parsed["book"], {})[parsed["variant"]] = parsed
    rows = []
    incomplete = []
    local = {book: {"errors": v["local"]["primary"], "runtime": v["local"]["runtime"],
                    "exit": v["local"]["exit"]}
             for book, v in sorted(by_book.items()) if "local" in v}
    for book, variants in sorted(by_book.items()):
        if "local" in variants:
            continue
        on, off = variants.get("on"), variants.get("off")
        if not on or not off or on["runtime"] is None or off["runtime"] is None:
            incomplete.append(book)
            continue
        on_times = {f["form"]: f["seconds"] for f in on["forms"]}
        slower = []
        for f in off["forms"]:
            before = on_times.get(f["form"])
            if before is not None and f["seconds"] - before >= slower_seconds:
                slower.append([f["form"], before, f["seconds"]])
        failing = [e for e in off["primary"] if e not in on["errors"]]
        cascaded = sorted(e for e in off["errors"] if e not in on["errors"] and e not in failing)
        saved = round(on["runtime"] - off["runtime"], 3)
        rows.append({
            "book": book, "on_runtime": on["runtime"], "off_runtime": off["runtime"],
            "saved": saved,
            "fraction": round(saved / on["runtime"], 3) if on["runtime"] else 0.0,
            "on_realtime": on["realtime"], "off_realtime": off["realtime"],
            "on_steps": on["steps"], "off_steps": off["steps"],
            "failing": failing, "cascaded": len(cascaded), "slower": slower,
            "on_errors": on["errors"],
            "timed_out": off["exit"] == 124, "load": [on["load"], off["load"]],
        })
    rows.sort(key=lambda row: -row["saved"])
    return {"books": rows, "incomplete": incomplete, "local": local,
            "on_runtime": round(sum(r["on_runtime"] for r in rows), 1),
            "off_runtime": round(sum(r["off_runtime"] for r in rows), 1)}


def selected(result: dict, min_seconds: float, min_fraction: float) -> list[dict]:
    return [row for row in result["books"]
            if row["saved"] >= min_seconds or (row["fraction"] >= min_fraction
                                               and row["saved"] > 0)]


def summary_lines(result: dict, top: int, min_seconds: float,
                  min_fraction: float) -> list[str]:
    rows = result["books"]
    chosen = selected(result, min_seconds, min_fraction)
    lines = [f"LOCAL {book}: exit {v['exit']} runtime {v['runtime']} errors {v['errors']}"
             for book, v in result.get("local", {}).items() if v["errors"] or v["exit"]]
    lines += [f"{len(rows)} books paired; runtime tau on {result['on_runtime']:,} s, "
             f"tau off {result['off_runtime']:,} s; incomplete {len(result['incomplete'])}",
             f"selected (saved >= {min_seconds:g} s or >= {min_fraction:.0%}): {len(chosen)}, "
             f"saving {sum(r['saved'] for r in chosen):,.1f} s runtime; "
             f"{sum(1 for r in chosen if r['failing'])} with forms failing tau off",
             "", f"{'saved':>7} {'frac':>6} {'on':>7} {'off':>7}  book  [failing]"]
    for row in rows[:top]:
        lines.append(f"{row['saved']:>7.2f} {row['fraction']:>6.0%} {row['on_runtime']:>7.2f} "
                     f"{row['off_runtime']:>7.2f}  {row['book']}"
                     + (f"  FAIL {', '.join(row['failing'])}" if row["failing"] else ""))
    return lines


def apply(result: dict, min_seconds: float, min_fraction: float,
          root: Path = ROOT) -> list[str]:
    """Tau off in each selected book; tau on around its FIRST failing form
    (the others usually fail because that one did: `repair` takes the next
    after a `run --variant local`) and around every slower form."""
    out = []
    for row in selected(result, min_seconds, min_fraction):
        path = root / (row["book"] + ".lisp")
        text = tau_off(path.read_text(encoding="utf-8"))
        wanted = {form.split()[1] for form in row["failing"][:1] if len(form.split()) > 1}
        wanted |= {form[0].split()[1] for form in row["slower"]
                   if len(form[0].split()) > 1}
        text, found = enable_around(text, wanted)
        path.write_text(text, encoding="utf-8")
        missing = sorted(wanted - found)
        out.append(f"{row['book']}: tau off, saved {row['saved']:.2f} s"
                   + (f"; tau on around {', '.join(sorted(found))}" if found else "")
                   + (f"; NOT FOUND {', '.join(missing)}" if missing else ""))
    return out


def repair(result: dict, ranking: dict, root: Path = ROOT) -> list[str]:
    """After `run --variant local`: tau on around each book's first failing
    form that did not fail with tau on too (a must-fail)."""
    expected = {row["book"]: set(row.get("on_errors", [])) for row in ranking["books"]}
    out = []
    found_errors = dict(result.get("local", {}))
    for row in result["books"]:  # an applied run: its off variant is the local text
        if row["failing"]:
            found_errors[row["book"]] = {"errors": row["failing"]}
    for book, value in found_errors.items():
        new = [form for form in value["errors"] if form not in expected.get(book, set())]
        first = [form for form in new[:1] if len(form.split()) > 1]
        if not first:
            continue
        path = root / (book + ".lisp")
        text, found = enable_around(path.read_text(encoding="utf-8"),
                                    {first[0].split()[1]})
        path.write_text(text, encoding="utf-8")
        out.append(f"{book}: tau on around {first[0]}" + ("" if found else " NOT FOUND"))
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = parser.add_subparsers(dest="action", required=True)
    start = sub.add_parser("run")
    start.add_argument("host", choices=sorted(farm.HOSTS))
    start.add_argument("books", nargs="*")
    start.add_argument("--remote-root", required=True)
    start.add_argument("--jobs", type=int, default=2)
    start.add_argument("--timeout", type=int, default=900)
    start.add_argument("--off-timeout", type=int, default=120,
                       help="the off variant's: a book tau off makes this slow is no "
                            "candidate (bp-app-handoff-time ran 900 s against 1 s on)")
    start.add_argument("--exclude", type=Path, action="append", default=[],
                       help="a run's `done` file: skip the books both of whose variants ran")
    start.add_argument("--acl2")
    start.add_argument("--variant", choices=("pair", "applied", "local"), default="pair",
                       help="pair: as is against tau off; applied: the remote's text "
                            "against this worktree's (a confirmation after apply); "
                            "local: this worktree's text alone")
    start.add_argument("--shard", help="K/N: every Nth book from the Kth (0-based)")
    block = sub.add_parser("wait")
    block.add_argument("host", choices=sorted(farm.HOSTS))
    block.add_argument("identifier")
    block.add_argument("--remote-root", required=True)
    order = sub.add_parser("rank")
    order.add_argument("logs", nargs="+", type=Path)
    order.add_argument("--json", type=Path)
    order.add_argument("--top", type=int, default=40)
    order.add_argument("--slower-seconds", type=float, default=0.5)
    order.add_argument("--min-seconds", type=float, default=1.0)
    order.add_argument("--min-fraction", type=float, default=0.2)
    put = sub.add_parser("apply")
    put.add_argument("ranking", type=Path)
    put.add_argument("--min-seconds", type=float, default=1.0)
    put.add_argument("--min-fraction", type=float, default=0.2)
    fix = sub.add_parser("repair", help="tau on around each first local failure")
    fix.add_argument("ranking", type=Path, help="the pair ranking (its on-errors are expected)")
    fix.add_argument("logs", nargs="+", type=Path)
    args = parser.parse_args(argv)
    try:
        if args.action == "run":
            books = args.books or rule_cost.default_books()
            if args.shard:
                k, n = (int(x) for x in args.shard.split("/"))
                books = books[k::n]
            for done in args.exclude:
                seen: dict[str, int] = {}
                for line in done.read_text(encoding="utf-8").splitlines():
                    if line.split():
                        seen[line.split()[0]] = seen.get(line.split()[0], 0) + 1
                books = [book for book in books if seen.get(book, 0) < 2]
            print(run(args.host, args.remote_root, books, args.jobs, args.timeout,
                      args.acl2, args.variant,
                      args.off_timeout))
            return 0
        if args.action == "wait":
            print(wait(args.host, args.remote_root, args.identifier))
            return 0
        if args.action == "rank":
            files: list[Path] = []
            for item in args.logs:
                files += sorted(item.glob("*.log")) if item.is_dir() else [item]
            result = rank(files, args.slower_seconds)
            print("\n".join(summary_lines(result, args.top, args.min_seconds,
                                          args.min_fraction)))
            if args.json:
                args.json.write_text(json.dumps(result, indent=1) + "\n", encoding="utf-8")
            return 0
        if args.action == "repair":
            files = []
            for item in args.logs:
                files += sorted(item.glob("*.log")) if item.is_dir() else [item]
            ranking = json.loads(args.ranking.read_text(encoding="utf-8"))
            print("\n".join(repair(rank(files, 0.5), ranking)))
            return 0
        result = json.loads(args.ranking.read_text(encoding="utf-8"))
        print("\n".join(apply(result, args.min_seconds, args.min_fraction)))
        return 0
    except (TauCostError, rule_cost.RuleCostError, OSError) as error:
        print(f"tau_cost: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
