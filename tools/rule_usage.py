#!/usr/bin/env python3
"""Which of a book's exported names anything downstream actually uses.

    python3 tools/rule_usage.py RUN_DIR [RUN_DIR ...] --summary [--min-dependents 200]
    python3 tools/rule_usage.py RUN_DIR --book books/config [--unused]
    python3 tools/rule_usage.py RUN_DIR --includers books/records-invariants
    python3 tools/rule_usage.py RUN_DIR --summary --json
    python3 tools/rule_usage.py RUN_DIR --edges 40      # includes worth cutting
    python3 tools/rule_usage.py RUN_DIR --simulate books/x:-books/y [--simulate books/x:+books/z] \
        --fixup --watch books/y --walls RUN_DIR/manifest.json

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

**`--edges N`** ranks every include X -> Y by what dropping it would take off
X's closure times X's dependents, first the ones where X names nothing only the
dropped books define, then the ones where X uses a few names (move those down,
or include their book directly).  **`--simulate`** rewires the graph before
anything is edited (the architect's rule: simulate the cut first) and prints
depth, the watched books' dependents and chain position, and with `--walls`
the weighted longest chain, before and after; it names every book that would
lose a name it uses, and `--fixup` gives each such book a direct include of
the book defining it, to a fixed point, so the after-counts are what the cut
can really save.

**Tau.**  689 of the tree's 1,470 books run the tau system (2026-09-28).  A tau
step's summary names only `(:EXECUTABLE-COUNTERPART TAU-SYSTEM)`, never the
signature rule it used, so for those books the log cannot rule out a use of
an included book: dropping `frame` from `byte-store-invariants` (no name
used) failed eight of its proofs.  Both modes flag such books; certification
decides.

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
import statistics
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import certify_books  # noqa: E402
import ledger  # noqa: E402

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
    # Strings and comments name nothing a proof uses (a docstring's prose
    # would otherwise count as a use, and hide a dead include).
    text = re.sub(r"#\\.", " ", text)  # a character literal, #\" among them
    text = re.sub(r'"(?:[^"\\]|\\.)*"', " ", text)
    text = re.sub(r"#\|.*?\|#", " ", text, flags=re.S)
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

    def tau(self, book: str) -> bool:
        """Whether the book's proofs ran the tau system: tau applies every
        signature rule of the closure and its summaries name only
        `(:EXECUTABLE-COUNTERPART TAU-SYSTEM)`, so a log cannot say which
        included rule a tau step used (byte-store-invariants dropping
        `frame`, 2026-09-28: no name used, eight proofs failed)."""
        used = self.used(book)
        return bool(used) and "tau-system" in used

    def source_text(self, book: str) -> str:
        try:
            return (self.root / f"{book}.lisp").read_text(encoding="utf-8", errors="replace")
        except OSError:
            return ""

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


def chain_position(closure: dict[str, list[str]]) -> dict[str, tuple[int, int]]:
    """book -> (below, above): the longest include chain ending at the book and
    the longest includer chain starting at it, each counting the book (unweighted
    levels; tools/shape_books.py --critical weighs the chain by seconds)."""
    included_by: dict[str, set[str]] = collections.defaultdict(set)
    for book, includes in closure.items():
        for dependency in includes:
            included_by[dependency].add(book)

    def depths(edges) -> dict[str, int]:
        memo: dict[str, int] = {}
        for start in closure:
            stack = [start]
            while stack:
                top = stack[-1]
                if top in memo:
                    stack.pop()
                    continue
                pending = [n for n in edges(top) if n not in memo]
                if pending:
                    stack.extend(pending)
                    continue
                memo[top] = 1 + max((memo[n] for n in edges(top)), default=0)
                stack.pop()
        return memo

    below = depths(lambda b: closure.get(b, ()))
    above = depths(lambda b: included_by.get(b, ()))
    return {book: (below[book], above[book]) for book in closure}


def chain_edges(usage: "Map", slack: int = 0) -> list[dict]:
    """The edges that set the longest chain: X -> Y where Y is X's only include
    of maximal depth and X lies on a chain within SLACK of the graph's depth.
    Rerouting such an edge (X takes what it uses of Y from a lower book)
    lowers X's depth, and with it every chain through X."""
    position = chain_position(usage.graph)
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


def book_name(value: str) -> str:
    """A graph key from `books/x`, `books/x.lisp` or `./books/x.lisp` (simulate
    checks it is in the graph)."""
    return value.strip().removeprefix("./").removesuffix(".lisp")


def parse_rewire(spec: str) -> tuple[str, str, str]:
    """`X:-Y` drops X's include of Y, `X:+Y` adds one."""
    for sign in ("-", "+"):
        book, sep, target = spec.partition(":" + sign)
        if sep:
            book, target = book_name(book), book_name(target)
            if book == target:
                raise SystemExit(f"rule_usage: --simulate {spec!r}: a book cannot include itself")
            return book, sign, target
    raise SystemExit(f"rule_usage: --simulate {spec!r}: want X:-Y or X:+Y")


def closure_of(graph: dict[str, list[str]], book: str) -> set[str]:
    seen: set[str] = set()
    stack = list(graph.get(book, ()))
    while stack:
        top = stack.pop()
        if top not in seen:
            seen.add(top)
            stack.extend(graph.get(top, ()))
    return seen


DEFRECORD = re.compile(r"\(fn-defrecord\s+([^\s()]+)", re.I)


_SOURCE_NAMES: dict[str, set[str]] = {}


def source_names(usage: "Map", book: str) -> set[str]:
    """Every name BOOK's source can introduce: its tokens, plus the names
    fn-defrecord derives from a record name (recognizer, shape, internals)."""
    if book in _SOURCE_NAMES:
        return _SOURCE_NAMES[book]
    names = set(usage.tokens(book))
    for record in DEFRECORD.findall(usage.source_text(book)):
        record = record.lower()
        names.update({record + "p", record + "-shapep", record + "-internals",
                      record + "p-forward-shape"})
    _SOURCE_NAMES[book] = names
    return names


def lost_uses(usage: "Map", before: dict[str, list[str]], after: dict[str, list[str]]) -> dict:
    """For every book whose include closure a rewire shrinks: the names it
    uses (source tokens and its log's runes) that only the lost books'
    sources contain.  An over-approximation of what it would miss (a token
    shared by chance counts); an empty list is the pre-check, certification
    the check."""
    report = {}
    for book in before:
        lost = closure_of(before, book) - closure_of(after, book)
        if not lost:
            continue
        report[book] = {"lost": len(lost), "tau": usage.tau(book),
                        "uses": names_only_in(usage, book, lost, closure_of(after, book))}
    return report


def names_only_in(usage: "Map", book: str, lost: set[str], kept_closure: set[str]) -> dict[str, list[str]]:
    """The fn- names BOOK uses (source tokens, its log's runes) that some book
    of LOST contains and no book of KEPT_CLOSURE (nor BOOK) does."""
    if True:
        kept = kept_closure
        theorems, definitions = usage.exports(book)
        wanted = (usage.tokens(book) | (usage.used(book) or set())) - set(theorems) - set(definitions)
        in_lost: dict[str, list[str]] = collections.defaultdict(list)
        for other in lost:
            for name in wanted & source_names(usage, other):
                in_lost[name].append(other)
        if not in_lost:
            return {}
        elsewhere: set[str] = set()
        for other in kept:
            elsewhere |= source_names(usage, other) & set(in_lost)
        return {n: sorted(v) for n, v in in_lost.items()
                if n not in elsewhere and (n.startswith("fn-") or n.startswith("*fn-"))}


def edge_candidates(usage: "Map", min_dependents: int = 0) -> list[dict]:
    """Every include X -> Y ranked by what dropping it would take off X's
    closure, weighed by X's dependents: `saved` = (dependents(X) + 1) x the
    books X would stop loading (an upper bound on the book-certifications a
    change to those books stops costing), with the names X itself uses that
    only the dropped books define (none: a dead include; few: move them down)."""
    rows = []
    for book, includes in usage.graph.items():
        if not includes:
            continue
        weight = len(usage.dependents(book)) + 1
        if weight < min_dependents:
            continue
        full = closure_of(usage.graph, book)
        for target in includes:
            others = [d for d in includes if d != target]
            kept: set[str] = set(others)
            for other in others:
                kept |= closure_of(usage.graph, other)
            lost = full - kept
            if not lost:
                continue
            uses = names_only_in(usage, book, lost, kept)
            rows.append({"includer": book, "included": target, "lost": len(lost),
                         "tau": usage.tau(book),
                         "includer_dependents": weight - 1, "saved": weight * len(lost),
                         "names_used": sorted(uses),
                         "from": sorted({b for v in uses.values() for b in v})})
    rows.sort(key=lambda row: (len(row["names_used"]) > 0, -row["saved"]))
    return rows


def simulate(usage: "Map", specs: list[str], watch: list[str],
             walls: dict[str, float] | None = None, fixup: bool = False) -> dict:
    """The graph after a set of include rewires, before and after: depth,
    each watched book's dependents and chain position, and with WALLS (book ->
    seconds) the weighted longest chain.  Run before touching a book: the
    architect's rule (simulate the cut on the graph first)."""
    after = {book: list(includes) for book, includes in usage.graph.items()}
    for spec in specs:
        book, sign, target = parse_rewire(spec)
        if book not in after or target not in after:
            raise SystemExit(f"rule_usage: --simulate {spec!r}: not in the graph")
        if sign == "-":
            after[book] = [d for d in after[book] if d != target]
        elif target not in after[book]:
            after[book].append(target)

    def by(graph):
        inverse: dict[str, set[str]] = collections.defaultdict(set)
        for book, includes in graph.items():
            for dependency in includes:
                inverse[dependency].add(book)
        return inverse

    def weighted(graph) -> tuple[float, list[str]]:
        if walls is None:
            return 0.0, []
        order = [b for b, _ in sorted(chain_position(graph).items(), key=lambda kv: kv[1][0])]
        best: dict[str, tuple[float, str | None]] = {}
        for book in order:
            below = max(((best[d][0], d) for d in graph.get(book, ()) if d in best), default=(0.0, None))
            best[book] = (below[0] + walls.get(book, 0.0), below[1])
        top = max(best, key=lambda b: best[b][0])
        chain, cursor = [], top
        while cursor is not None:
            chain.append(cursor)
            cursor = best[cursor][1]
        return best[top][0], chain

    fixups: list[str] = []
    for _ in range(6 if fixup else 0):
        lost = lost_uses(usage, usage.graph, after)
        added = False
        for book, row in sorted(lost.items()):
            for name, holders in sorted(row["uses"].items()):
                definers = [h for h in holders if name in set().union(*usage.exports(h))]
                target = (definers or holders)[0]
                if target not in after[book] and target != book and book not in closure_of(after, target):
                    after[book].append(target)
                    fixups.append(f"{book}:+{target}")
                    added = True
        if not added:
            break
    result = {"fixups": fixups}
    for label, graph in (("before", usage.graph), ("after", after)):
        position = chain_position(graph)
        inverse = by(graph)
        seconds, chain = weighted(graph)
        result[label] = {
            "depth": max(below for below, _ in position.values()),
            "books": {b: {"dependents": len(usage.dependents(b, inverse)),
                          "below": position[b][0], "above": position[b][1],
                          "through": sum(position[b]) - 1} for b in watch},
            "weighted_chain_seconds": round(seconds, 1), "weighted_chain": chain}
    result["lost_uses"] = lost_uses(usage, usage.graph, after)
    return result


def manifest_walls(paths: list[Path]) -> dict[str, float]:
    """book -> seconds from certification manifests' `book_wall_seconds`
    (the last manifest given wins); books no manifest measured count the median."""
    walls: dict[str, float] = {}
    for path in paths:
        data = json.loads(path.read_text(encoding="utf-8"))
        for book, seconds in (data.get("book_wall_seconds") or {}).items():
            walls[book[:-5] if book.endswith(".lisp") else book] = float(seconds)
    return walls


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
    parser.add_argument("--simulate", action="append", default=[], metavar="X:-Y|X:+Y",
                        help="rewire the graph (drop or add X's include of Y; repeatable) and "
                             "print depth, --watch books' dependents/chain position, before and after")
    parser.add_argument("--watch", action="append", default=[], metavar="BOOK",
                        help="with --simulate: books whose dependents and chain position to print")
    parser.add_argument("--fixup", action="store_true",
                        help="with --simulate: give every book that would lose a name it uses a "
                             "direct include of the book defining it (repeated to a fixed point), "
                             "so the after-counts are what the cut can really save")
    parser.add_argument("--walls", action="append", default=[], type=Path, metavar="MANIFEST",
                        help="with --simulate: certification manifests whose book_wall_seconds "
                             "weigh the chain (books unmeasured count the median)")
    parser.add_argument("--edges", type=int, metavar="N", default=0,
                        help="the N includes whose removal would save the most book-certifications, "
                             "dead ones (the includer uses nothing they alone bring) first")
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
    if arguments.edges:
        rows = edge_candidates(usage)
        dead = [r for r in rows if not r["names_used"]]
        live = sorted((r for r in rows if r["names_used"]),
                      key=lambda r: (-r["saved"] / (1 + len(r["names_used"]))))
        output["edges"] = {"dead": dead[:arguments.edges], "few_names": live[:arguments.edges]}
        if not arguments.json:
            print(f"\n{len(dead)} includes bring nothing the includer names (dead, or kept for rules); top by saving:")
            for row in dead[:arguments.edges]:
                print(f"  {row['includer']} -> {row['included']}: drops {row['lost']} books "
                      f"from {row['includer_dependents'] + 1} closures (saves <= {row['saved']})"
                      + ("  [tau: the log cannot rule out a tau use]" if row["tau"] else ""))
            print("\nincludes whose dropped books the includer uses a few names of (saving per name):")
            for row in live[:arguments.edges]:
                print(f"  {row['includer']} -> {row['included']}: drops {row['lost']} from "
                      f"{row['includer_dependents'] + 1} (saves <= {row['saved']}); uses "
                      f"{len(row['names_used'])}: {' '.join(row['names_used'][:6])}"
                      f"{' ...' if len(row['names_used']) > 6 else ''} <- {' '.join(row['from'][:3])}")
    if arguments.simulate:
        walls = None
        if arguments.walls:
            measured = manifest_walls(arguments.walls)
            fill = statistics.median(measured.values()) if measured else 0.0
            walls = {b: measured.get(b, fill) for b in usage.graph}
        watch = [certify_books.normalize_book(b) for b in arguments.watch]
        result = simulate(usage, arguments.simulate, watch, walls, arguments.fixup)
        output["simulate"] = result
        if not arguments.json:
            for label in ("before", "after"):
                row = result[label]
                print(f"{label}: depth {row['depth']}"
                      + (f", weighted chain {row['weighted_chain_seconds']} s over "
                         f"{len(row['weighted_chain'])} books (top {row['weighted_chain'][0]})"
                         if row["weighted_chain"] else ""))
                for book, info in row["books"].items():
                    print(f"  {book}: {info['dependents']} dependents, below {info['below']}, "
                          f"through {info['through']}")
            if result["fixups"]:
                print(f"fixups ({len(result['fixups'])}): {' '.join(result['fixups'])}")
            lost = result["lost_uses"]
            needing = {b: r for b, r in lost.items() if r["uses"]}
            tau = sorted(b for b, r in lost.items() if r["tau"] and not r["uses"])
            if tau:
                print(f"{len(tau)} of them ran tau, whose uses no log names (certification decides): "
                      f"{' '.join(tau[:12])}{' ...' if len(tau) > 12 else ''}")
            print(f"closure shrinks for {len(lost)} books; {len(needing)} use a name only a "
                  f"lost book defines (add a direct include there, or move the name down):")
            for book, row in sorted(needing.items()):
                names = sorted(row["uses"])
                print(f"  {book}: {' '.join(names[:8])}{' ...' if len(names) > 8 else ''}"
                      f"  <- {' '.join(sorted({b for n in names for b in row['uses'][n]})[:4])}")
    if arguments.json:
        print(json.dumps(output, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
