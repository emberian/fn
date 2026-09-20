#!/usr/bin/env python3
"""Profile one slow ACL2 form: which rules are burning frames, and where it stops.

This is the first thing to run on a form that is slow or does not close.  The
tree has paid for that lesson four times in one cycle --- the C2, checkpoint,
reader-profile and article-exports lanes each spent hours on a proof whose
cost turned out to be a handful of rules backchaining into a recognizer, and
each found it the same way, with `accumulated-persistence` (BOARD 2026-09-20;
`planning/deputies/BOARD.md` records 921k of 921k frames of one rule fan).
Running it should not require rediscovering the incantation.

    python3 tools/proof_profile.py books/scheduler \\
        fn-sched-step-preserves-statep --host hbox

builds a scratch driver in the lane's remote root: the book's own source up to
(but not including) the named form --- so the form is profiled in exactly the
theory the book builds for it, with the book's dependencies coming from the
box's certificate cache rather than being replayed --- then

    (accumulated-persistence t)
    (set-prover-step-limit <steps>)
    <the form>
    (show-accumulated-persistence :frames-a)
    (show-accumulated-persistence :useless)
    (show-accumulated-persistence :tries-a)

and reports: the top rules by frames that never contributed a useful
application (the fan), the top rules by frames overall, the top by tries, the
form's own Summary line, and the first checkpoint if it did not close.

What ACL2 does not give, and this tool therefore does not invent: prover time
is not attributed per rune.  ACL2 accumulates frames and tries per rule and
reports time only for the form as a whole, which is what `SUMMARY` below
carries.  Frames are the per-rule cost proxy; a rune with a large frame count
and no useful application is the thing to withdraw.

The remote root must already hold the box's certificates for the book's
dependencies; `python3 tools/farm.py submit <host> ... --closure` installs
them, which every lane does before it starts.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import os
from pathlib import Path
import re
import shlex
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(Path(__file__).resolve().parent))
import ledger  # noqa: E402

HOSTS = {
    "persvati": {"acl2": "$HOME/fn-tools/acl2-8.7/saved_acl2",
                 "root": "/home/ember/fn-lanes", "wrap": ""},
    "hbox": {"acl2": "/tank/fn/acl2-8.7/saved_acl2",
             "root": "/tank/fn/lanes", "wrap": "swarm-build"},
}
NAMED_EVENTS = ("defthm", "defthmd", "defun", "defund", "defun-nx", "defun-sk",
                "verify-guards", "defrule")
DEFAULT_STEPS = 4_000_000

# Seams: the tests drive command construction and load probing through these.
RUN = subprocess.run


class ProfileError(Exception):
    """A profile run that could not be built or started."""


# --------------------------------------------------------------------------
# the parser
# --------------------------------------------------------------------------
#
# ACL2 8.7 prints, for each `show-accumulated-persistence`, a header that does
# NOT name the sort key --- `Accumulated Persistence (2282 :tries useful, 1683
# :tries not useful)` --- and then one line per rune,
#
#       2602     1036 (    2.51) (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND)
#
# separated by dashes and terminated by `NIL`.  So the driver prints its own
# marker before each listing and the parser keys on that; a log without
# markers falls back to the order the driver issues them in.  A rune line is
# recognised by its shape: a rune at end of line, at least two numbers before
# it, of which the first is the frame count.

RUNE = re.compile(r"\((:[A-Za-z-]+)\s+([^()\s]+)(?:\s+[^()]*)?\)\s*$")
NUMBER = re.compile(r"-?\d+(?:\.\d+)?")
MARKER = re.compile(r"^FN-PROFILE-SECTION (\S+)", re.M)
HEADER = re.compile(r"^Accumulated Persistence\b")
SECTION_ORDER = ("frames-a", "useless", "tries-a")
SUMMARY_TIME = re.compile(r"^Time:\s+(.*)$", re.M)
STEPS = re.compile(r"^Prover steps counted:\s+(\d+)", re.M)


@dataclass(frozen=True)
class Entry:
    rune: str
    numbers: tuple[float, ...]

    @property
    def frames(self) -> float:
        return self.numbers[0] if self.numbers else 0.0


def parse_sections(text: str) -> dict[str, list[Entry]]:
    """Every `show-accumulated-persistence` listing in a log, by sort key.

    A section runs from its header to the next header or to the end.  A
    listing ACL2 declines to print (no rule fired) yields an empty list, which
    is a real answer and not a parse failure.
    """
    sections: dict[str, list[Entry]] = {}
    current: str | None = None
    marked = False
    seen = 0
    for line in text.splitlines():
        marker = MARKER.match(line)
        if marker:
            current, marked = marker.group(1).lower(), True
            sections.setdefault(current, [])
            continue
        if HEADER.match(line):
            if not marked:
                # A log with no markers: label the listings in the order the
                # driver issues them.
                current = (SECTION_ORDER[seen] if seen < len(SECTION_ORDER)
                           else f"listing-{seen}")
                sections.setdefault(current, [])
            seen += 1
            continue
        if current is None:
            continue
        match = RUNE.search(line)
        if not match:
            continue
        prefix = line[: match.start()]
        numbers = tuple(float(value) for value in NUMBER.findall(prefix))
        if len(numbers) < 2:
            continue
        sections[current].append(
            Entry(rune=f"({match.group(1)} {match.group(2)})", numbers=numbers))
    return sections


def useless_runes(sections: dict[str, list[Entry]]) -> set[str]:
    """The runes ACL2 reports as never having contributed a useful application."""
    return {entry.rune for entry in sections.get("useless", [])}


def before_listings(text: str) -> str:
    """The log up to the first listing: the profiled form is the last thing in it."""
    marker = MARKER.search(text)
    return text[: marker.start()] if marker else text


def checkpoint(text: str) -> str | None:
    """The first key checkpoint ACL2 printed, if the form did not close."""
    lines = before_listings(text).splitlines()
    for index, line in enumerate(lines):
        if "Key checkpoint" in line:
            return "\n".join(lines[index:index + 30]).rstrip()
    return None


def summary(text: str) -> dict[str, str]:
    """The profiled form's own Summary: the last one before the listings."""
    head_text = before_listings(text)
    result: dict[str, str] = {}
    times = SUMMARY_TIME.findall(head_text)
    if times:
        result["time"] = times[-1].strip()
    steps = STEPS.findall(head_text)
    if steps:
        result["steps"] = steps[-1]
    return result


def report(text: str, top: int = 10) -> str:
    """The whole report, from a log: this is what `--log` re-renders."""
    sections = parse_sections(text)
    useless = useless_runes(sections)
    frames = sections.get("frames-a") or sections.get("frames") or []
    tries = sections.get("tries-a") or sections.get("tries") or []
    lines: list[str] = []

    fan = [entry for entry in frames if entry.rune in useless]
    lines.append(f"top {top} by frames with no useful application "
                 f"({len(fan)} such runes; these are the fan)")
    if not fan:
        lines.append("  (none: every rule that fired contributed somewhere)")
    for entry in fan[:top]:
        lines.append(f"  {entry.frames:12,.0f}  {entry.rune}")

    lines.append("")
    lines.append(f"top {top} by frames, all")
    for entry in frames[:top]:
        mark = "  useless" if entry.rune in useless else ""
        lines.append(f"  {entry.frames:12,.0f}  {entry.rune}{mark}")
    if not frames:
        lines.append("  (no accumulated-persistence listing in this log)")

    lines.append("")
    lines.append(f"top {top} by tries")
    for entry in tries[:top]:
        # `:tries-a` prints the same columns, sorted differently: frames first,
        # tries second.
        count = entry.numbers[1] if len(entry.numbers) > 1 else entry.numbers[0]
        lines.append(f"  {count:12,.0f}  {entry.rune}")
    if not tries:
        lines.append("  (no :tries-a listing in this log)")

    facts = summary(text)
    lines.append("")
    lines.append("SUMMARY  " + ("time " + facts["time"] if "time" in facts
                                else "no Time line"))
    if "steps" in facts:
        lines.append(f"         prover steps {int(facts['steps']):,}")
    lines.append("ACL2 attributes frames and tries per rune, never time; the "
                 "time above is the whole form's.")

    stop = checkpoint(text)
    lines.append("")
    if stop:
        lines.append("CHECKPOINT")
        lines.append(stop)
    else:
        lines.append("CHECKPOINT  none printed: the form closed, or it was cut "
                     "by the step limit or the timeout.")
    return "\n".join(lines)


# --------------------------------------------------------------------------
# building the driver
# --------------------------------------------------------------------------


def book_source(book: str) -> Path:
    path = ROOT / (book if book.endswith(".lisp") else book + ".lisp")
    if not path.exists():
        raise ProfileError(f"no such book: {path}")
    return path


def split_at_form(source: str, form_name: str) -> tuple[str, str]:
    """(everything above the named event, the event itself), from the source.

    Reading with the ledger's own reader rather than a regexp: the name of an
    event is its second element, and a `defthm` whose name also occurs in a
    comment or a hint must not be matched.
    """
    forms = ledger.Reader(source).top_level()
    lines = source.splitlines(keepends=True)
    for index, (form, line) in enumerate(forms):
        head = ledger.head(form)
        if head not in NAMED_EVENTS or len(form) < 2:
            continue
        if not isinstance(form[1], ledger.Sym) or str(form[1]) != form_name:
            continue
        start = line - 1
        end = (forms[index + 1][1] - 1) if index + 1 < len(forms) else len(lines)
        return "".join(lines[:start]), "".join(lines[start:end])
    raise ProfileError(f"no top-level {'/'.join(NAMED_EVENTS)} named {form_name}")


def driver(prefix: str, form: str, steps: int) -> str:
    return "".join([
        prefix,
        "\n; ---- proof_profile.py ----\n",
        "(accumulated-persistence t)\n",
        f"(set-prover-step-limit {steps})\n",
        form,
        '\n(cw "~%FN-PROFILE-SECTION frames-a~%")\n',
        "(show-accumulated-persistence :frames-a)\n",
        '(cw "~%FN-PROFILE-SECTION useless~%")\n',
        "(show-accumulated-persistence :useless)\n",
        '(cw "~%FN-PROFILE-SECTION tries-a~%")\n',
        "(show-accumulated-persistence :tries-a)\n",
        "(accumulated-persistence nil)\n",
        "(quit)\n",
    ])


def host_load(host: str) -> float:
    """The host's one-minute load average, from one `ssh host uptime`."""
    answer = RUN(["ssh", "-n", host, "uptime"], stdout=subprocess.PIPE,
                 stderr=subprocess.STDOUT, text=True, check=False)
    match = re.search(r"load averages?:\s*([\d.]+)", answer.stdout or "")
    if answer.returncode != 0 or not match:
        return float("inf")
    return float(match.group(1))


def quieter_host() -> str:
    """The less loaded farm box.  persvati and hbox are co-tenant with other
    work (hbox with codex's HOL build), so a profile run goes to whichever is
    idle rather than to a hard-coded default."""
    loads = {host: host_load(host) for host in HOSTS}
    ranked = sorted(loads.items(), key=lambda item: item[1])
    print("  ".join(f"{host} load {load}" for host, load in loads.items()),
          file=sys.stderr)
    if ranked[0][1] == float("inf"):
        raise ProfileError("neither farm box answered `uptime`")
    return ranked[0][0]


def remote_command(host: str, remote_root: str, name: str, timeout: int) -> str:
    settings = HOSTS[host]
    inner = (f"ACL2_CUSTOMIZATION=NONE ACL2_BOOK_HASH_ALISTP=NIL "
             f"timeout {timeout} {settings['acl2']} < {shlex.quote(name)}")
    if settings["wrap"]:
        inner = f"{settings['wrap']} sh -c {shlex.quote(inner)}"
    return f"cd {shlex.quote(remote_root)} && {inner}"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("book", nargs="?", help="books/scheduler, or a path")
    parser.add_argument("form", nargs="?", help="the name of the event to profile")
    parser.add_argument("--host", choices=sorted(HOSTS),
                        help="default: the less loaded of the two")
    parser.add_argument("--remote-root",
                        help="default: <host's lane root>/<this worktree's name>")
    parser.add_argument("--steps", type=int, default=DEFAULT_STEPS)
    parser.add_argument("--timeout", type=int, default=900)
    parser.add_argument("--top", type=int, default=10)
    parser.add_argument("--log", help="re-render a saved log instead of running")
    parser.add_argument("--save", help="write the raw log here")
    parser.add_argument("--dry-run", action="store_true",
                        help="print the driver and the remote command, run nothing")
    args = parser.parse_args()

    if args.log:
        print(report(Path(args.log).read_text(encoding="utf-8"), args.top))
        return 0
    if not args.book or not args.form:
        parser.error("book and form are required unless --log is given")

    source = book_source(args.book).read_text(encoding="utf-8")
    prefix, form = split_at_form(source, args.form)
    text = driver(prefix, form, args.steps)

    host = args.host or quieter_host()
    remote_root = args.remote_root or f"{HOSTS[host]['root']}/{ROOT.name}"
    name = f"proof-profile-{args.form}.lsp"
    command = remote_command(host, remote_root, name, args.timeout)

    if args.dry_run:
        print(f"# {host}:{remote_root}/{name}")
        print(f"# {command}")
        print(text)
        return 0

    scratch = Path(os.environ.get("TMPDIR", "/tmp")) / name
    scratch.write_text(text, encoding="utf-8")
    copy = RUN(["scp", "-q", str(scratch), f"{host}:{remote_root}/{name}"],
               stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
               check=False)
    if copy.returncode != 0:
        raise ProfileError(f"{host}: cannot place the driver: {copy.stdout}")
    answer = RUN(["ssh", "-n", host, command], stdout=subprocess.PIPE,
                 stderr=subprocess.STDOUT, text=True, check=False)
    log = answer.stdout or ""
    if args.save:
        Path(args.save).write_text(log, encoding="utf-8")
    print(f"# {host}:{remote_root}/{name}, exit {answer.returncode}")
    print(report(log, args.top))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except ProfileError as error:
        print(f"proof_profile: {error}", file=sys.stderr)
        sys.exit(2)
