#!/usr/bin/env python3
"""Which of a book's exported names anything downstream actually uses.

    python3 tools/rule_usage.py RUN_DIR [RUN_DIR ...] --summary [--min-dependents 200]
    python3 tools/rule_usage.py RUN_DIR --book books/config [--unused]
    python3 tools/rule_usage.py RUN_DIR --includers books/records-invariants
    python3 tools/rule_usage.py RUN_DIR --summary --json

RUN_DIR is a certification run directory (`build/acl2/certify-*`) whose logs
cover the books whose use you want to know.  A provisional run
(`certify_books.py --pcert`) leaves `<book>.pcert-convert.certify.log`, the
wave where the proofs are; an ordinary run leaves `<book>.certify.log`, which
prints the same summaries.  Either works; given several directories, the
newest log per book wins.  A full-tree map needs one run over every root with
nothing installed from the cache (`--closure`): an installed book has no log.

**What "used" means.**  ACL2 ends every event's summary with `Rules:` (every
rune the proof applied, `(:REWRITE NAME)`, `(:DEFINITION FN)`, ...) and, when
a hint named events, `Hint-events:` (`(:USE NAME)`, ...).  A name exported by
book B is

  used        when some dependent of B lists it in a summary;
  mentioned   when no dependent's proof applied it but some dependent's
              source names it (an `in-theory`, a `:use` in a `local` proof the
              log did not reach, a `deftheory`): making it local would break
              that source, so it is not a candidate;
  registered  when planning/proof-events.json, planning/proofs.json, host/,
              tools/ or tests/*.py name it (the registries key on names);
  unused      otherwise: no dependent's proof applied it and nothing outside
              the book names it.  A candidate to make `local` or to move to a
              leaf book; certification is the check, because a rule can be
              load-bearing without ever being applied (docs/proof-style.md
              section 8: `fn-lg-declared-len` keeps two rules from looping).

**`--includers HUB`** is the finder for the architect's leaf cuts
(planning/architecture-recommendation-2026-09-28.md, the UTF-8 decoder out of
`wildmat`): for each direct includer X of HUB, how many of HUB's own names X
uses (its source's tokens and its log's runes), and how many of HUB's
dependents would stop depending on HUB if X included something else instead.
An includer that uses three helpers and carries half the hub's dependents is
the cut.

Books are read with tools/ledger.py's reader (never the Lisp reader); the
graph is tools/certify_books.py's `local_closure` over the Makefile roots,
the one the farm and tools/shape_books.py walk.  What this cannot see: names
a macro generates (a record's accessors are exported by `defrecord`'s
expansion, not by a top-level form), so it reports only top-level `defthm`,
`defthmd`, `defun`-family, `defmacro` and `defconst` names; and the log is
the run's, so a book edited since the run is reported with the run's usage.
"""
from __future__ import annotations

import argparse
import collections
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import certify_books  # noqa: E402
import ledger  # noqa: E402
import shape_books  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]

THEOREM_HEADS = {"defthm", "defthmd"}
DEFINITION_HEADS = {"defun", "defund", "defun-nx", "defun-inline", "defun-sk",
                    "defmacro", "defconst", "defstobj", "defabsstobj", "deftheory"}
TRANSPARENT = {"progn", "encapsulate", "defsection", "with-output"}

RUNE = re.compile(r"\(:[A-Z-]+\s+([^\s()]+)")
TOKEN = re.compile(r"[^\s()'`,\"#;|]+")
SUMMARY_END = r"\n(?=\S)"
RULES = re.compile(r"^Rules:\s*(\(.*?\)|NIL)" + SUMMARY_END, re.S | re.M)
HINTS = re.compile(r"^Hint-events:\s*(\(.*?\))" + SUMMARY_END, re.S | re.M)
LOG_SUFFIXES = (".pcert-convert.certify.log", ".certify.log")


def exported(book: str, root: Path = ROOT) -> tuple[list[str], list[str]]:
    """(theorems, definitions) a book exports: non-local top-level names, in order."""
    theorems: list[str] = []
    definitions: list[str] = []

    def walk(form: object) -> None:
        if not isinstance(form, list) or not form:
            return
        head = str(form[0]).lower()
        if head == "local":
            return
        if head in TRANSPARENT:
            start = 2 if head == "encapsulate" else 1
            if head == "encapsulate" and len(form) > 1 and isinstance(form[1], list):
                for signature in form[1]:
                    if isinstance(signature, list) and signature:
                        name = signature[0]
                        definitions.append(str(name[0] if isinstance(name, list) else name).lower())
            for item in form[start:]:
                walk(item)
            return
        if head == "mutual-recursion":
            for item in form[1:]:
                walk(item)
            return
        if len(form) > 1 and isinstance(form[1], str):
            name = str(form[1]).lower()
            if head in THEOREM_HEADS:
                theorems.append(name)
            elif head in DEFINITION_HEADS:
                definitions.append(name)

    text = (root / f"{book}.lisp").read_text(encoding="utf-8", errors="replace")
    for form, _ in ledger.Reader(text).top_level():
        walk(form)
    return theorems, definitions


def source_tokens(path: Path) -> set[str]:
    try:
        text = path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return set()
    text = re.sub(r";[^\n]*", "", text)
    return {token.lower() for token in TOKEN.findall(text)}


def log_names(text: str) -> set[str]:
    """Every name a log's event summaries report as applied or hinted."""
    names: set[str] = set()
    for match in RULES.finditer(text):
        names.update(name.lower() for name in RUNE.findall(match.group(1)))
    for match in HINTS.finditer(text):
        names.update(name.lower() for name in RUNE.findall(match.group(1)))
    return names


def run_logs(run_dirs: list[Path]) -> dict[str, Path]:
    """book -> its log across the run directories: a Convert log before an
    ordinary one, then the newest."""
    found: dict[str, tuple[int, float, Path]] = {}
    for directory in run_dirs:
        for rank, suffix in enumerate(LOG_SUFFIXES):
            for path in directory.glob(f"*{suffix}"):
                stem = path.name[:-len(suffix)]
                if ".pcert-" in stem:
                    continue
                key = (-rank, path.stat().st_mtime, path)
                book = stem.replace("--", "/")
                if book not in found or key[:2] > found[book][:2]:
                    found[book] = key
    return {book: key[2] for book, key in found.items()}


class Map:
    def __init__(self, run_dirs: list[Path], root: Path = ROOT) -> None:
        self.root = root
        roots = certify_books.default_books()
        self.graph = certify_books.local_closure(roots)
        self.included_by: dict[str, set[str]] = collections.defaultdict(set)
        for book, includes in self.graph.items():
            for dependency in includes:
                self.included_by[dependency].add(book)
        self.logs = run_logs(run_dirs)
        self._used: dict[str, set[str]] = {}
        self._tokens: dict[str, set[str]] = {}
        self._exports: dict[str, tuple[list[str], list[str]]] = {}
        self._external: set[str] | None = None

    def dependents(self, book: str, graph_by: dict[str, set[str]] | None = None) -> set[str]:
        by = self.included_by if graph_by is None else graph_by
        seen = {book}
        stack = [book]
        while stack:
            for parent in by.get(stack.pop(), ()):
                if parent not in seen:
                    seen.add(parent)
                    stack.append(parent)
        return seen - {book}

    def used(self, book: str) -> set[str] | None:
        """Names the book's own proofs applied, or None when the run has no log for it."""
        if book not in self._used:
            path = self.logs.get(book)
            if path is None:
                return None
            self._used[book] = log_names(path.read_text(encoding="utf-8", errors="replace"))
        return self._used[book]

    def tokens(self, book: str) -> set[str]:
        if book not in self._tokens:
            self._tokens[book] = source_tokens(self.root / f"{book}.lisp")
        return self._tokens[book]

    def exports(self, book: str) -> tuple[list[str], list[str]]:
        if book not in self._exports:
            self._exports[book] = exported(book, self.root)
        return self._exports[book]

    def external(self) -> set[str]:
        """Names the registries, host code, tools and Python tests mention."""
        if self._external is None:
            names: set[str] = set()
            paths = [self.root / "planning" / "proof-events.json",
                     self.root / "planning" / "proofs.json"]
            paths += sorted((self.root / "host").rglob("*.lisp"))
            paths += sorted((self.root / "tools").glob("*.py"))
            paths += sorted((self.root / "tests").glob("*.py"))
            for path in paths:
                if path.name == "rule_usage.py":
                    continue
                try:
                    text = path.read_text(encoding="utf-8", errors="replace")
                except OSError:
                    continue
                names.update(token.lower() for token in re.findall(r"[A-Za-z0-9*+<>=/!?$%&_.:-]+", text))
            self._external = names
        return self._external

    def classify(self, book: str) -> dict:
        """Per exported theorem: users (dependents whose proofs applied it),
        mentioners (dependents whose source names it), registered."""
        theorems, _ = self.exports(book)
        dependents = self.dependents(book)
        logged = [d for d in dependents if self.used(d) is not None]
        external = self.external()
        rows = []
        for name in theorems:
            users = sorted(d for d in logged if name in self.used(d))
            mentioners = sorted(d for d in dependents if name in self.tokens(d))
            registered = name in external
            if users:
                verdict = "used"
            elif mentioners:
                verdict = "mentioned"
            elif registered:
                verdict = "registered"
            else:
                verdict = "unused"
            rows.append({"theorem": name, "verdict": verdict, "users": users,
                         "mentioners": mentioners, "registered": registered})
        return {"book": book, "dependents": len(dependents), "logged": len(logged),
                "theorems": rows}

    def includers(self, hub: str) -> list[dict]:
        """For each direct includer X of HUB: what X uses of HUB, and what the
        hub's dependents would be without the edge X -> HUB."""
        _, definitions = self.exports(hub)
        theorems, _ = self.exports(hub)
        names = set(definitions) | set(theorems)
        before = self.dependents(hub)
        rows = []
        for includer in sorted(self.included_by.get(hub, ())):
            by = {k: set(v) for k, v in self.included_by.items()}
            by[hub] = by[hub] - {includer}
            # X still reaches HUB through another include: the cut must go further.
            after = self.dependents(hub, by)
            applied = self.used(includer) or set()
            direct = sorted(n for n in names if n in self.tokens(includer) or n in applied)
            rows.append({"includer": includer, "names_used": direct,
                         "includer_dependents": len(self.dependents(includer)) + 1,
                         "hub_dependents_after": len(after),
                         "hub_dependents_saved": len(before) - len(after)})
        rows.sort(key=lambda row: (-row["hub_dependents_saved"], len(row["names_used"])))
        return rows


def chain_edges(usage: "Map", slack: int = 0) -> list[dict]:
    """The edges that set the longest chain: X -> Y where Y is X's only include
    of maximal depth and X lies on a chain within SLACK of the graph's depth.
    Rerouting such an edge (X takes what it uses of Y from a lower book)
    lowers X's depth, and with it every chain through X."""
    position = shape_books.chain_position(usage.graph)
    depth = max(below for below, _ in position.values())
    rows = []
    for book, includes in usage.graph.items():
        below, above = position[book]
        if below + above - 1 < depth - slack or not includes:
            continue
        deepest = max(position[d][0] for d in includes)
        top = [d for d in includes if position[d][0] == deepest]
        if len(top) != 1:
            continue
        target = top[0]
        others = max((position[d][0] for d in includes if d != target), default=0)
        theorems, definitions = usage.exports(target)
        names = set(theorems) | set(definitions)
        applied = usage.used(book) or set()
        used = sorted(n for n in names if n in usage.tokens(book) or n in applied)
        rows.append({"includer": book, "included": target, "includer_below": below,
                     "through": below + above - 1,
                     "levels_if_rerouted": below - 1 - max(others, 0),
                     "names_used": used,
                     "dependents": len(usage.dependents(book)) + 1})
    rows.sort(key=lambda row: (len(row["names_used"]), -row["dependents"]))
    return rows


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("run_dirs", nargs="+", type=Path,
                        help="build/acl2/certify-* directories whose logs to read")
    parser.add_argument("--book", action="append", default=[],
                        help="per-theorem table for this book (repeatable)")
    parser.add_argument("--unused", action="store_true",
                        help="with --book: print only the unused theorems")
    parser.add_argument("--includers", action="append", default=[], metavar="HUB",
                        help="what each direct includer of HUB uses of it, and the "
                             "dependents HUB would lose without that edge")
    parser.add_argument("--summary", action="store_true",
                        help="one row per book with at least --min-dependents dependents")
    parser.add_argument("--min-dependents", type=int, default=200)
    parser.add_argument("--chain-edges", action="store_true",
                        help="the includes that set the longest chain, fewest names used first")
    parser.add_argument("--slack", type=int, default=0,
                        help="with --chain-edges: also chains within this many levels of the longest")
    parser.add_argument("--json", action="store_true")
    arguments = parser.parse_args(argv)
    for directory in arguments.run_dirs:
        if not directory.is_dir():
            parser.error(f"{directory}: not a directory")
    usage = Map([d.resolve() for d in arguments.run_dirs])
    print(f"rule_usage: {len(usage.logs)} book logs over {len(usage.graph)} books in the graph",
          file=sys.stderr)
    output: dict = {}
    if arguments.summary:
        rows = []
        for book in sorted(usage.graph):
            if len(usage.dependents(book)) < arguments.min_dependents:
                continue
            table = usage.classify(book)
            counts = collections.Counter(row["verdict"] for row in table["theorems"])
            rows.append({"book": book, "dependents": table["dependents"],
                         "logged": table["logged"], "theorems": len(table["theorems"]),
                         **{k: counts.get(k, 0) for k in ("used", "mentioned", "registered", "unused")}})
        rows.sort(key=lambda row: (-row["dependents"], row["book"]))
        output["summary"] = rows
        if not arguments.json:
            print("| book | dependents | with a log | exported theorems | used | mentioned | registered | unused |")
            print("|---|---:|---:|---:|---:|---:|---:|---:|")
            for row in rows:
                print(f"| `{row['book']}` | {row['dependents']} | {row['logged']} | {row['theorems']} "
                      f"| {row['used']} | {row['mentioned']} | {row['registered']} | {row['unused']} |")
    for name in arguments.book:
        book = certify_books.normalize_book(name)
        table = usage.classify(book)
        output.setdefault("books", []).append(table)
        if not arguments.json:
            print(f"\n{book}: {table['dependents']} dependents, {table['logged']} with a log")
            for row in table["theorems"]:
                if arguments.unused and row["verdict"] != "unused":
                    continue
                print(f"  {row['verdict']:10s} {row['theorem']}  users={len(row['users'])} "
                      f"mentioners={len(row['mentioners'])}"
                      + (f" e.g. {row['users'][0] if row['users'] else row['mentioners'][0]}"
                         if row["users"] or row["mentioners"] else ""))
    for name in arguments.includers:
        hub = certify_books.normalize_book(name)
        rows = usage.includers(hub)
        output.setdefault("includers", {})[hub] = rows
        if not arguments.json:
            print(f"\n{hub}: {len(usage.dependents(hub))} dependents; direct includers by dependents saved")
            for row in rows:
                print(f"  {row['includer']:48s} saves {row['hub_dependents_saved']:5d} "
                      f"(includer has {row['includer_dependents']}); uses {len(row['names_used'])}: "
                      f"{' '.join(row['names_used'][:8])}{' ...' if len(row['names_used']) > 8 else ''}")
    if arguments.chain_edges:
        rows = chain_edges(usage, arguments.slack)
        output["chain_edges"] = rows
        if not arguments.json:
            print("\nincludes that set the longest chain (X -> Y, Y X's only deepest include):")
            for row in rows:
                print(f"  {row['includer']} -> {row['included']}  (X below {row['includer_below']}, "
                      f"through {row['through']}, up to {row['levels_if_rerouted']} level(s), "
                      f"{row['dependents']} dependents) uses {len(row['names_used'])}: "
                      f"{' '.join(row['names_used'][:6])}{' ...' if len(row['names_used']) > 6 else ''}")
    if arguments.json:
        print(json.dumps(output, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
