#!/usr/bin/env python3
"""Check fn's design links and ledgers; this does not execute proof/scenario work."""

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
sys.path.insert(0, str(ROOT / "tools"))
import evidence_store  # noqa: E402
ERRORS: list[str] = []
UNAVAILABLE: list[str] = []
IGNORED = {".git", ".venv", ".cache", "build", "var", "__pycache__"}
# The shared allocator pads to three digits; it does not stop at 999.
REQUIREMENT_ID = r"[A-Z]{3}-\d{3,}"
PROOF_ID = r"PRF-\d{3,}"
SCENARIO_ID = r"SCN-\d{3,}"


def fail(message: str) -> None:
    ERRORS.append(message)


def unavailable(message: str) -> None:
    """Uncertain, not failed: an indexed target whose bytes cannot be read."""
    UNAVAILABLE.append(message)


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
    if evidence_store.indexed(ROOT, rel):
        # Evidence the index names: the link holds only if the bytes it
        # reaches hash to the index line -- a working-tree file at that path
        # is checked against it, never accepted as itself (r61 F2), and with
        # none here the object must fetch and verify (a name is not bytes).
        try:
            if parts.fragment:
                dest = evidence_store.materialize(ROOT, rel)
            else:
                evidence_store.read_bytes(ROOT, rel)
        except evidence_store.EvidenceRefused as error:
            fail(f"{context}: indexed target does not match its index line: {target}: {error}")
            return
        except evidence_store.EvidenceUnavailable as error:
            unavailable(f"{context}: indexed target cannot be read: {target}: {error}")
            return
        if not parts.fragment:
            return
    elif not dest.exists() and evidence_store.is_dir(ROOT, rel):
        return
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
            link(path, ROOT / "README.md", entry["id"])
            if not evidence_store.exists(ROOT, path):
                fail(f"{entry['id']}: evidence is not a file: {path}")


def scenario_implementation(ident: str, entry: dict) -> None:
    """An implemented scenario names the test that runs it and the run's log.

    `implementation` holds: `test`, a test module in dotted form
    (`tests.test_x`, resolving to tests/test_x.py) or the repository path of
    a harness script; `cases`, the TestCase classes or methods that run the
    steps (required for a module; each must occur in its text); `native`,
    whether the run was against a native image (false: the Python host or a
    fake peer); `log`, a committed log of a passing run; and `record`, the
    evidence record that reports that run.  The record must name the test or
    the log's file, and the log must name the test or a case, or else the
    record must name the log's file.  Whether a scenario is `validated` is the
    qualification's mapping, not this check's.
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
    if not evidence_store.exists(ROOT, module_rel):
        fail(f"{ident}: implementation.test {test} does not resolve to a file")
        return
    try:
        module = evidence_store.materialize(ROOT, module_rel)
    except evidence_store.EvidenceRefused as error:
        fail(f"{ident}: implementation.test {test} does not match its index line: {error}")
        return
    except evidence_store.EvidenceUnavailable as error:
        unavailable(f"{ident}: implementation.test {test} cannot be read: {error}")
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
    for field, value in (("log", log), ("record", record)):
        # Committed = tracked, or named by the evidence index (its bytes in
        # the archive; tools/evidence_store.py).
        if not isinstance(value, str) or not evidence_store.exists(ROOT, value):
            fail(f"{ident}: implementation.{field} must be a committed file: {value!r}")
            return
    if not record.endswith(".md"):
        fail(f"{ident}: implementation.record must be an evidence record (.md)")
    # Through the store, so the bytes read are the ones the index names
    # (the working tree no longer carries planning/evidence).
    try:
        body = evidence_store.read_bytes(ROOT, log).decode("utf-8", errors="replace")
        prose = evidence_store.read_bytes(ROOT, record).decode("utf-8", errors="replace")
    except evidence_store.EvidenceRefused as error:
        fail(f"{ident}: implementation log/record does not match its index line: {error}")
        return
    except evidence_store.EvidenceUnavailable as error:
        unavailable(f"{ident}: implementation log/record cannot be read: {error}")
        return
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

    # Every indexed file the registries name is read (verified) below: one
    # fetch for all of them, never one round trip each.
    named = [path for entries in (requirements, proofs, scenarios)
             for entry in entries.values()
             for path in list(entry.get("evidence") or [])
             + [(entry.get("implementation") or {}).get(key)
                for key in ("log", "record", "test")]
             if isinstance(path, str)]
    try:
        evidence_store.prefetch(ROOT, named)
    except evidence_store.EvidenceError:
        pass  # each read below reports its own object (UNAVAILABLE or REFUSED)

    for entries, statuses, advanced in [
        (requirements, {"specified", "implemented", "validated", "deferred"}, {"implemented", "validated"}),
        (proofs, {"planned", "uncertified-at-current-digest", "certified"}, {"certified"}),
        (scenarios, {"specified", "implemented", "validated", "deferred"}, {"implemented", "validated"}),
    ]:
        for ident, entry in entries.items():
            if entry.get("status") not in statuses:
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
        if entry.get("status") == "certified" and not entry.get("events"):
            fail(f"{ident}: certification needs actual ACL2 event references")
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
    # stale planning/ledger.md.  Counts are never typed into prose.
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

    if ERRORS or UNAVAILABLE:
        for error in ERRORS:
            print(f"ERROR: {error}", file=sys.stderr)
        for message in UNAVAILABLE:
            print(f"UNAVAILABLE: {message}", file=sys.stderr)
        return 1 if ERRORS else evidence_store.EXIT_UNAVAILABLE
    print(f"Scaffold OK: {len(markdown)} Markdown files, {len(requirements)} requirements, "
          f"{len(proofs)} proof targets, {len(scenarios)} scenario specifications.")
    print("Ledger OK: cited events exist, are not SUSPECT, and planning/ledger.md is current.")
    print(f"Ledger lints: {len(warnings)} warnings (export hygiene, teeth form, "
          "hand-written record, "
          f"include hygiene, host names); see planning/ledger.json.")
    print("Structural checks only; no ACL2 certification or scenario execution performed.")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except evidence_store.EvidenceError as exc:
        print(f"{evidence_store.outcome(exc)}: committed evidence cannot be accepted: {exc}",
              file=sys.stderr)
        sys.exit(evidence_store.exit_code(exc))
    except (OSError, ValueError, TypeError, KeyError, AttributeError) as exc:
        print(f"ERROR: malformed scaffold: {exc}", file=sys.stderr)
        sys.exit(1)
