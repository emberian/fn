#!/usr/bin/env python3
"""Check fn's design links and ledgers; this does not execute proof/scenario work."""

import json
import re
import sys
from pathlib import Path
from urllib.parse import unquote, urlsplit


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools import ledger  # noqa: E402  (after ROOT is on the path)
sys.path.insert(0, str(ROOT / "tools"))
import v0_matrix  # noqa: E402  (the v0 release gate's own validator)
ERRORS: list[str] = []
IGNORED = {".git", ".venv", ".cache", "build", "var", "__pycache__"}


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
    elif not dest.exists():
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
            if not (ROOT / path).is_file():
                fail(f"{entry['id']}: evidence is not a file: {path}")


def main() -> int:
    markdown = sorted(p for p in ROOT.rglob("*.md")
                      if not (set(p.relative_to(ROOT).parts) & IGNORED))
    for path in markdown:
        for target in re.findall(r"\[[^\]\n]*\]\(([^)\n]+)\)", prose(path)):
            link(target, path, str(path.relative_to(ROOT)))

    milestones = set(re.findall(r"(?m)^## (M\d+):",
                                (ROOT / "planning/milestones.md").read_text()))
    assumptions = set(re.findall(r"(?m)^\| (A-[A-Z-]+) \|",
                                 (ROOT / "specs/failures.md").read_text()))
    requirements = registry("planning/requirements.json", "requirements", r"[A-Z]{3}-\d{3}")
    proofs = registry("planning/proofs.json", "proofs", r"PRF-\d{3}")
    scenarios = registry("tests/scenarios/catalog.json", "scenarios", r"SCN-\d{3}")

    definitions = {}
    for path in (ROOT / "specs").glob("*.md"):
        for ident in re.findall(r"(?m)^([A-Z]{3}-\d{3}):", path.read_text()):
            if ident in definitions:
                fail(f"{ident}: more than one authoritative definition")
            definitions[ident] = path
    if set(definitions) != set(requirements):
        fail(f"requirement definitions/registry differ: {sorted(set(definitions) ^ set(requirements))}")

    for entries, statuses, advanced in [
        (requirements, {"specified", "implemented", "validated", "deferred"}, {"implemented", "validated"}),
        (proofs, {"planned", "in-progress", "certified", "deferred"}, {"certified"}),
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
            fail(f"{ident}: requirement/proof links are not reciprocal")

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

    # The v0 release gate. `planning/v0-matrix.json` carries a per-feature
    # verdict, and its counts, its indexes and its digest are `tools/v0_matrix.py`'s
    # over the rows it ran. A verdict word typed into the file by hand does not
    # survive the digest, so this is where "counts come from tools, not typing"
    # is enforced for the matrix.
    for problem in v0_matrix.check_file(ROOT / v0_matrix.MATRIX_JSON):
        fail(f"v0 matrix: {problem}")

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
    print("Ledger OK: cited events exist, are not SUSPECT, and planning/ledger.md is current.")
    print(f"Ledger lints: {len(warnings)} warnings (export hygiene, teeth form, "
          "hand-written record, "
          f"include hygiene, host names); see planning/ledger.json.")
    matrix = json.loads((ROOT / v0_matrix.MATRIX_JSON).read_text())
    print("v0 matrix OK: {total} rows at {rev}, {a} accepted, {r} refused, "
          "{u} uncertain, {n} not exercised, {b} not built, {d} disagreed; "
          "the rows match their digest.".format(
              total=matrix["summary"]["total"], rev=matrix["revision"],
              a=matrix["summary"]["accepted"], r=matrix["summary"]["refused"],
              u=matrix["summary"]["uncertain"],
              n=matrix["summary"]["not-exercised"], b=matrix["summary"]["not-built"],
              d=matrix["summary"]["disagreed"]))
    print("Structural checks only; no ACL2 certification or scenario execution performed.")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, TypeError, KeyError, AttributeError) as exc:
        print(f"ERROR: malformed scaffold: {exc}", file=sys.stderr)
        sys.exit(1)
