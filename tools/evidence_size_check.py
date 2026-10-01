#!/usr/bin/env python3
"""Keep committed raw evidence small without changing existing logs.

MODE §5 (build/coordinator/queue/MODE-2026-10-01.txt):
"EVIDENCE IS SMALL. Never commit a raw log over ~1,000 lines; commit a
summary + the tail + where the full log lives on the box."

Check tracked raw logs under planning/ (`git ls-files`; without .git, a
walk). Manifests and records (.json), Markdown, compressed logs, images and
Lisp sources are data, not raw logs. Existing oversized logs are grandfathered
in tools/evidence_size_baseline.txt. Generate it once with --write-baseline;
later writes only drop entries, never grandfather new logs. No log is changed.
Positional FILE arguments restrict checking, including stale baseline entries;
baseline generation always considers the full scope.

    python3 tools/evidence_size_check.py [--limit N] [--write-baseline] [FILE ...]

Exit 0 clean, 1 with each finding named. Static, no ACL2.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass, field
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
LIMIT = 1000
RAW_LOG_SUFFIXES = (".log", ".txt", ".out", ".stderr", ".stdout", ".jsonl", ".times")
BASELINE = Path("tools/evidence_size_baseline.txt")
BASELINE_HEADER = (
    "# Grandfathered oversized planning raw logs (MODE §5).\n"
    "# This baseline only shrinks; commit a summary + the tail + the full log location.\n"
)


def relative_name(path: Path, root: Path) -> str | None:
    """Normalize a supplied path without following tracked symlink names."""
    absolute = Path(os.path.abspath(path if path.is_absolute() else root / path))
    try:
        return absolute.relative_to(root.absolute()).as_posix()
    except ValueError:
        return None


def in_scope(name: str) -> bool:
    return name.startswith("planning/") and name.endswith(RAW_LOG_SUFFIXES)


def tracked_files(root: Path = ROOT) -> list[Path]:
    if (root / ".git").exists():
        result = subprocess.run(["git", "-C", str(root), "ls-files", "-z", "--", "planning/"],
                                capture_output=True, check=True)
        names = [os.fsdecode(name) for name in result.stdout.split(b"\0") if name]
    else:
        names = [path.relative_to(root).as_posix()
                 for base, _, files in os.walk(root / "planning")
                 for name in files for path in [Path(base) / name]]
    return [root / name for name in sorted(set(names)) if in_scope(name)]


def line_count(path: Path) -> int:
    # Binary iteration also counts an unterminated final line and invalid UTF-8.
    with path.open("rb") as source:
        return sum(1 for _ in source)


def read_baseline(root: Path = ROOT) -> set[str]:
    path = root / BASELINE
    if not path.exists():
        return set()
    return {name for line in path.read_text().splitlines()
            if (name := line.split("#", 1)[0].strip())}


def write_baseline(root: Path = ROOT, limit: int = LIMIT) -> None:
    """Capture existing oversized logs once; subsequent writes only shrink."""
    oversized = {path.relative_to(root).as_posix() for path in tracked_files(root)
                 if path.exists() and line_count(path) > limit}
    path = root / BASELINE
    if path.exists():
        oversized &= read_baseline(root)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(BASELINE_HEADER + "".join(name + "\n" for name in sorted(oversized)))


@dataclass
class Result:
    checked: int = 0
    refused: int = 0
    baselined: int = 0
    stale: int = 0
    findings: list[str] = field(default_factory=list)

    def summary(self) -> str:
        return (f"evidence_size_check: {self.checked} raw logs, {self.refused} refused, "
                f"{self.baselined} baselined, {self.stale} stale")


def check(files: list[Path] | None = None, root: Path = ROOT, limit: int = LIMIT) -> Result:
    baseline = read_baseline(root)
    selected = None if files is None else {relative_name(path, root) for path in files}
    counts = {}
    result = Result()
    for path in tracked_files(root):
        name = path.relative_to(root).as_posix()
        if selected is not None and name not in selected:
            continue
        if not path.exists():
            continue
        count = counts[name] = line_count(path)
        result.checked += 1
        if count > limit:
            if name in baseline:
                result.baselined += 1
            else:
                result.refused += 1
                result.findings.append(
                    f"REFUSED {name}: {count} lines (limit {limit}): commit a summary + "
                    "the tail + where the full log lives (MODE §5)")
    for name in sorted(baseline):
        if selected is not None and name not in selected:
            continue
        path = root / name
        if not path.exists():
            reason = "gone"
        else:
            count = counts[name] if name in counts else line_count(path)
            if count > limit:
                continue
            reason = f"now {count} lines"
        result.stale += 1
        result.findings.append(f"STALE {name}: in the baseline but {reason}: "
                               "drop it (the baseline only shrinks)")
    return result


def main(argv: list[str] | None = None, root: Path = ROOT) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("files", nargs="*", type=Path)
    parser.add_argument("--limit", type=int, default=LIMIT)
    parser.add_argument("--write-baseline", action="store_true")
    arguments = parser.parse_args(argv)
    if arguments.write_baseline:
        write_baseline(root, arguments.limit)
    result = check(arguments.files or None, root, arguments.limit)
    for finding in result.findings:
        print(finding)
    print(result.summary())
    return 1 if result.refused or result.stale else 0


if __name__ == "__main__":
    sys.exit(main())
