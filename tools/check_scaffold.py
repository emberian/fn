#!/usr/bin/env python3
"""Check fn's design links and ledgers; this does not execute proof/scenario work."""

import functools
import json
import os
import re
import subprocess
import sys
from pathlib import Path, PurePosixPath
from urllib.parse import unquote, urlsplit


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools import ledger  # noqa: E402  (after ROOT is on the path)
ERRORS: list[str] = []
# Citations under these prefixes name reports that left the tree (D71): they
# stay as text and are not resolved.
HISTORICAL_PREFIXES = ("planning/evidence/", "docs/evidence/")
IGNORED = {".git", ".venv", ".cache", "build", "var", "__pycache__"}
# The shared allocator pads to three digits; it does not stop at 999.
REQUIREMENT_ID = r"[A-Z]{3}-\d{3,}"
PROOF_ID = r"PRF-\d{3,}"
SCENARIO_ID = r"SCN-\d{3,}"


def fail(message: str) -> None:
    ERRORS.append(message)


def prose(path: Path) -> str:
    """Ignore fenced examples for link/heading discovery."""
    return re.sub(r"(?ms)^```[^\n]*\n.*?^```\s*$", "", path.read_text())


def anchors(path: Path) -> set[str]:
    result: set[str] = set()
    for heading in re.findall(r"(?m)^#{1,6}\s+(.+?)\s*#*\s*$", prose(path)):
        slug = re.sub(r"[^\w\- ]", "", heading.lower()).replace(" ", "-")
        candidate, suffix = slug, 0
        while candidate in result:
            suffix += 1
            candidate = f"{slug}-{suffix}"
        result.add(candidate)
    return result


@functools.lru_cache(maxsize=None)
def retired_paths() -> frozenset[str]:
    """planning/retired-paths.json: paths removed from the tree on purpose,
    each with where its role went (tools/cite_check.py reads the same file)."""
    source = ROOT / "planning" / "retired-paths.json"
    if not source.is_file():
        return frozenset()
    return frozenset(json.loads(source.read_text()).get("paths", {}))


def link(target: str, base: Path, context: str) -> None:
    if not isinstance(target, str) or not target:
        fail(f"{context}: expected a nonempty path")
        return
    parts = urlsplit(target.strip("<>"))
    if parts.scheme or parts.netloc:
        return  # Offline check: external URLs are deliberately not fetched.
    dest = (base.parent / unquote(parts.path)).resolve() if parts.path else base
    if not dest.is_relative_to(ROOT):
        fail(f"{context}: local link escapes repository: {target}")
        return
    rel = dest.relative_to(ROOT).as_posix()
    if rel.startswith(HISTORICAL_PREFIXES) and not dest.exists():
        return
    if not dest.exists() and rel in retired_paths():
        return  # Disclosed centrally: removed on purpose, and where its role went.
    if not dest.exists():
        fail(f"{context}: missing target: {target}")
    elif parts.fragment and dest.suffix == ".md":
        if unquote(parts.fragment) not in anchors(dest):
            fail(f"{context}: missing heading: {target}")


def registry(path: str, key: str, pattern: str) -> dict[str, dict]:
    data = json.loads((ROOT / path).read_text())
    if data.get("schema_version") != 1:
        fail(f"{path}: unsupported schema_version")
    entries = data.get(key)
    if not isinstance(entries, list):
        raise ValueError(f"{path}: expected list named {key}")
    result = {}
    for entry in entries:
        ident = entry.get("id", "")
        if not re.fullmatch(pattern, ident) or ident in result:
            fail(f"{path}: invalid or duplicate ID {ident!r}")
        result[ident] = entry
    return result


def references(values: list, known: dict | set, context: str) -> None:
    if not isinstance(values, list) or any(not isinstance(v, str) for v in values):
        fail(f"{context}: expected a list of IDs")
        return
    if len(values) != len(set(values)):
        fail(f"{context}: repeated reference")
    for value in values:
        if value not in known:
            fail(f"{context}: unknown reference {value}")


def evidence(entry: dict, advanced: set[str]) -> None:
    paths = entry.get("evidence", [])
    if not isinstance(paths, list):
        fail(f"{entry['id']}: evidence must be a list")
        return
    if entry.get("status") in advanced and not paths:
        fail(f"{entry['id']}: status requires actual evidence references")
    for path in paths:
        if not isinstance(path, str) or urlsplit(path).scheme or not path:
            fail(f"{entry['id']}: evidence must name a repository file")
        else:
            # A prose entry is a finding, never a crash: an OSError here is a
            # name no file system accepts (ENAMETOOLONG on a sentence).
            try:
                link(path, ROOT / "README.md", entry["id"])
                missing = (not path.startswith(HISTORICAL_PREFIXES)
                           and not (ROOT / path).exists())
            except OSError as exc:
                fail(f"{entry['id']}: evidence is not a path ({exc.strerror}): {path[:120]}")
                continue
            if missing:
                fail(f"{entry['id']}: evidence is not a file: {path}")


# The evidence archive (D71): content-addressed bytes on hbox under
# /tank/fn/evidence, indexed by its history-ledger*.tsv files (SHA256 SIZE
# GITBLOB PATH per line).  A citation of a file that left the tree is
# checked against the ledger's paths: read from FN_EVIDENCE_ARCHIVE (the
# archive directory, on the box), else from build/evidence-archive/paths.txt
# (`--fetch-archive BOX` writes it), else not readable (None).
ARCHIVE_ENV = "FN_EVIDENCE_ARCHIVE"
ARCHIVE_DIR = "/tank/fn/evidence"
ARCHIVE_COPY = ROOT / "build" / "evidence-archive" / "paths.txt"


@functools.lru_cache(maxsize=None)
def archive_paths() -> frozenset[str] | None:
    directory = os.environ.get(ARCHIVE_ENV) or (ARCHIVE_DIR if Path(ARCHIVE_DIR).is_dir() else "")
    if directory:
        paths = set()
        for ledger_file in sorted(Path(directory).glob("history-ledger*.tsv")):
            for line in ledger_file.read_text(errors="replace").splitlines():
                fields = line.split()
                if len(fields) >= 4:
                    paths.add(fields[-1])
        return frozenset(paths)
    if ARCHIVE_COPY.is_file():
        return frozenset(ARCHIVE_COPY.read_text().split())
    return None


def fetch_archive(box: str) -> int:
    """Copy the archive ledger's path column from BOX into ARCHIVE_COPY."""
    command = ("cat %s/history-ledger*.tsv | awk 'NF>=4 {print $NF}' | sort -u" % ARCHIVE_DIR)
    result = subprocess.run(["ssh", box, command], capture_output=True, text=True, timeout=300)
    if result.returncode != 0 or not result.stdout.strip():
        print(f"check_scaffold: --fetch-archive {box} failed: {result.stderr.strip()}", file=sys.stderr)
        return 1
    ARCHIVE_COPY.parent.mkdir(parents=True, exist_ok=True)
    ARCHIVE_COPY.write_text(result.stdout)
    print(f"wrote {ARCHIVE_COPY.relative_to(ROOT)}: {len(result.stdout.split())} archived paths from {box}")
    return 0


def scenario_implementation(ident: str, entry: dict) -> None:
    """An implemented scenario names the test that runs it and the run's log.

    `implementation` holds: `test`, a test module in dotted form
    (`tests.test_x`, resolving to tests/test_x.py) or the repository path of
    a harness script; `cases`, the TestCase classes or methods that run the
    steps (required for a module; each must occur in its text); `native`,
    whether the run was against a native image (false: the Python host or a
    fake peer); `log`, the log of a passing run; and `record`, the evidence
    record that reports it.  D71 keeps evidence out of git, so a log or record
    that is not in the tree is cited by its path in the evidence archive
    (hbox:/tank/fn/evidence) and must be one of the archive ledger's paths
    (`archive_paths`); a path neither in the tree nor in the archive is
    refused, never accepted unread.  The record must name the test or the
    log's file, and the log must name the test or a case, or else the record
    must name the log's file (cross-read when both are in the tree).  Whether a
    scenario is `validated` is the qualification's mapping, not this check's.
    """
    impl = entry.get("implementation")
    if not isinstance(impl, dict):
        fail(f"{ident}: status {entry.get('status')} needs an `implementation` "
             "naming the test module and the evidence log")
        return
    test = impl.get("test")
    if not isinstance(test, str) or not test:
        fail(f"{ident}: implementation.test is missing")
        return
    module_rel = test if "/" in test else test.replace(".", "/") + ".py"
    module = ROOT / module_rel
    if not module.is_file():
        fail(f"{ident}: implementation.test {test} does not resolve to a file")
        return
    cases = impl.get("cases", [])
    if not isinstance(cases, list) or any(not isinstance(c, str) or not c for c in cases):
        fail(f"{ident}: implementation.cases must be a list of names")
        return
    if "/" not in test:
        if not cases:
            fail(f"{ident}: implementation.cases must name the classes or tests of {test}")
        text = module.read_text(encoding="utf-8", errors="replace")
        for case in cases:
            if case.split(".")[-1] not in text:
                fail(f"{ident}: case {case} does not occur in {test}")
    if not isinstance(impl.get("native"), bool):
        fail(f"{ident}: implementation.native must say whether a native image ran it")
    log, record = impl.get("log"), impl.get("record")
    historical = []
    for field, value in (("log", log), ("record", record)):
        if not isinstance(value, str) or not value:
            fail(f"{ident}: implementation.{field} must name a file: {value!r}")
            return
        if value.startswith(HISTORICAL_PREFIXES) and not (ROOT / value).exists():
            archived = archive_paths()
            if archived is None:
                fail(f"{ident}: implementation.{field} {value} is not in the tree and no "
                     "evidence-archive ledger is readable to confirm it (set "
                     f"{ARCHIVE_ENV}, or `python3 tools/check_scaffold.py --fetch-archive BOX`)")
                return
            if value not in archived:
                fail(f"{ident}: implementation.{field} {value} is neither in the tree nor "
                     "in the evidence archive")
                return
            historical.append(value)
        elif not (ROOT / value).exists():
            fail(f"{ident}: implementation.{field} must be a committed file: {value!r}")
            return
    if not record.endswith(".md"):
        fail(f"{ident}: implementation.record must be an evidence record (.md)")
    if historical:
        return  # a cited report that left the tree cannot be cross-read
    body = (ROOT / log).read_text(encoding="utf-8", errors="replace")
    prose = (ROOT / record).read_text(encoding="utf-8", errors="replace")
    names = {module.stem, module.name} | {c.split(".")[-1] for c in cases}
    log_named = Path(log).name in prose
    if not (module.name in prose or module.stem in prose or log_named):
        fail(f"{ident}: {record} names neither {test} nor {Path(log).name}")
    if not any(name in body for name in names) and not log_named:
        fail(f"{ident}: neither {log} names {test} nor {record} names the log")


def conflict_markers() -> None:
    """Refuse a tracked file that still carries a merge conflict marker.

    Committed three times in one evening -- twice in planning/BOARD.md and
    once across ~300 lines of planning/decisions.md, each time putting every
    entry after the hunk inside it.  Nothing validated those files, so the
    tree read as clean and two lanes each rediscovered the same wreckage.
    Git's own markers are the check: a line that is exactly seven `<`, `=` or
    `>` followed by a space or end of line.
    """
    pattern = re.compile(r"(?m)^(?:<{7} |>{7} |={7}$)")
    listed = subprocess.run(["git", "ls-files", "-z"], cwd=ROOT, check=False,
                            capture_output=True, text=True).stdout.split("\0")
    for name in listed:
        if not name or set(PurePosixPath(name).parts) & IGNORED:
            continue
        path = ROOT / name
        try:
            text = path.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            continue
        hit = pattern.search(text)
        if hit:
            line = text[:hit.start()].count("\n") + 1
            fail(f"{name}:{line}: a merge conflict marker is committed here")


def markdown_files():
    """Every *.md outside IGNORED, which the walk never enters: ROOT.rglob
    walked all of build/ (certificates, lane worktrees, gate trees) and
    filtered afterwards, minutes on a box, and made the step's traced inputs
    every file under build/ (check-parallel, 2026-09-29)."""
    for base, directories, names in os.walk(ROOT):
        directories[:] = [d for d in directories if d not in IGNORED]
        for name in names:
            if name.endswith(".md") and name not in IGNORED:
                yield Path(base) / name


def assumption_books() -> None:
    """One place lists every named assumption (AGENTS.md): a book
    books/assumptions-*.lisp is either included by books/assumptions.lisp or
    named, by its path, in specs/failures.md's assumption table (a book kept
    out of assumptions.lisp's closure because its signature needs a stobj
    that 766 includers must not load: A-ARENA-STORED)."""
    included = set(re.findall(r'\(include-book "(assumptions-[a-z0-9-]+)"',
                              (ROOT / "books/assumptions.lisp").read_text()))
    rows = "\n".join(line for line in (ROOT / "specs/failures.md").read_text().splitlines()
                     if re.match(r"\| A-[A-Z-]+ \|", line))
    for book in sorted((ROOT / "books").glob("assumptions-*.lisp")):
        if book.stem not in included and f"books/{book.name}" not in rows:
            fail(f"books/{book.name}: an assumption book neither included by "
                 "books/assumptions.lisp nor named in a specs/failures.md A-* row")


def main() -> int:
    conflict_markers()
    markdown = sorted(markdown_files())
    for path in markdown:
        for target in re.findall(r"\[[^\]\n]*\]\(([^)\n]+)\)", prose(path)):
            link(target, path, str(path.relative_to(ROOT)))

    milestones = set(re.findall(r"(?m)^## (M\d+):",
                                (ROOT / "planning/milestones.md").read_text()))
    assumptions = set(re.findall(r"(?m)^\| (A-[A-Z-]+) \|",
                                 (ROOT / "specs/failures.md").read_text()))
    assumption_books()
    requirements = registry("planning/requirements.json", "requirements", REQUIREMENT_ID)
    proofs = registry("planning/proofs.json", "proofs", PROOF_ID)
    scenarios = registry("tests/scenarios/catalog.json", "scenarios", SCENARIO_ID)

    definitions = {}
    for path in (ROOT / "specs").glob("*.md"):
        for ident in re.findall(rf"(?m)^({REQUIREMENT_ID}):", path.read_text()):
            if ident in definitions:
                fail(f"{ident}: more than one authoritative definition")
            definitions[ident] = path
    if set(definitions) != set(requirements):
        fail(f"requirement definitions/registry differ: {sorted(set(definitions) ^ set(requirements))}")

    for entries, statuses, advanced in [
        (requirements, {"specified", "implemented", "validated", "deferred"}, {"implemented", "validated"}),
        (proofs, None, set()),   # a proof's status is computed (green_check), never stored
        (scenarios, {"specified", "implemented", "validated", "deferred"}, {"implemented", "validated"}),
    ]:
        for ident, entry in entries.items():
            if statuses is None:
                if "status" in entry:
                    fail(f"{ident}: a proof target stores no status; it is computed "
                         "from the cert cache (python3 tools/ledger.py --write drops it)")
            elif entry.get("status") not in statuses:
                fail(f"{ident}: invalid status")
            if entry.get("milestone") not in milestones:
                fail(f"{ident}: unknown milestone")
            if not entry.get("title"):
                fail(f"{ident}: missing title")
            evidence(entry, advanced)

    for ident, entry in requirements.items():
        spec = entry.get("specification", "")
        link(spec, ROOT / "README.md", ident)
        if spec and (ROOT / urlsplit(spec).path).resolve() != definitions.get(ident):
            fail(f"{ident}: specification does not point at its authoritative definition")
        references(entry.get("proof_targets", []), proofs, ident)
        if not entry.get("verification"):
            fail(f"{ident}: no verification method")

    for ident, entry in scenarios.items():
        if entry.get("status") in {"implemented", "validated"}:
            scenario_implementation(ident, entry)

    for ident, entry in proofs.items():
        references(entry.get("requirements", []), requirements, ident)
        references(entry.get("depends_on", []), proofs, ident)
        references(entry.get("assumptions", []), assumptions, ident)
        if not entry.get("statement"):
            fail(f"{ident}: missing proposed statement")
        reverse = {r for r, value in requirements.items() if ident in value.get("proof_targets", [])}
        if reverse != set(entry.get("requirements", [])):
            fail(f"{ident}: requirement/proof links are not reciprocal "
                 "(python3 tools/merge_registry.py --reciprocate adds the missing side)")

    visited, visiting = set(), set()

    def visit(ident: str) -> None:
        if ident in visiting:
            fail(f"{ident}: proof dependency cycle")
            return
        if ident in visited or ident not in proofs:
            return
        visiting.add(ident)
        for dependency in proofs[ident].get("depends_on", []):
            visit(dependency)
        visiting.remove(ident)
        visited.add(ident)

    for ident in proofs:
        visit(ident)

    # The generated half of the ledger: `python3 tools/ledger.py --check'.  It
    # reads the books themselves, so it fails on an event name that no book
    # defines, on a theorem whose shape disqualifies it as evidence, and on a
    # ledger that does not build.  Counts are never typed into prose.
    tree = ledger.load_tree()
    for problem in ledger.check_problems(tree):
        fail(f"ledger: {problem}")
    # The two shape lints are WARN here by design: they describe a cost the
    # tree is already carrying, and failing `make check` on them would stop
    # unrelated work.  `python3 tools/ledger.py --check --strict` fails.
    warnings = ledger.lint_warnings(tree)
    for warning in warnings:
        print(f"WARN: ledger: {warning}", file=sys.stderr)

    covered = set()
    for ident, entry in scenarios.items():
        references(entry.get("requirements", []), requirements, ident)
        covered.update(entry.get("requirements", []))
        for key in ("steps", "expected"):
            if not entry.get(key) or any(not isinstance(x, str) or not x for x in entry[key]):
                fail(f"{ident}: missing/invalid {key}")
    if set(requirements) - covered:
        fail(f"requirements without scenario specifications: {sorted(set(requirements) - covered)}")

    if ERRORS:
        for error in ERRORS:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1
    print(f"Scaffold OK: {len(markdown)} Markdown files, {len(requirements)} requirements, "
          f"{len(proofs)} proof targets, {len(scenarios)} scenario specifications.")
    print("Ledger OK: cited events exist, are not SUSPECT, and the ledger builds.")
    print(f"Ledger lints: {len(warnings)} warnings (export hygiene, teeth form, "
          "hand-written record, "
          f"include hygiene, host names); see `python3 tools/ledger.py --check`.")
    print("Structural checks only; no ACL2 certification or scenario execution performed.")
    return 0


if __name__ == "__main__":
    if len(sys.argv) == 3 and sys.argv[1] == "--fetch-archive":
        sys.exit(fetch_archive(sys.argv[2]))
    try:
        sys.exit(main())
    except (OSError, ValueError, TypeError, KeyError, AttributeError) as exc:
        print(f"ERROR: malformed scaffold: {exc}", file=sys.stderr)
        sys.exit(1)
