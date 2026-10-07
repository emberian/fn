"""What the three citation checkers share: the tree root, the tracked file
list, and the backquoted-span reader (paths.py, names.py and docs.py each
read the prose of this tree for what it cites)."""
from __future__ import annotations

from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
TOOLS = ROOT / "tools"
SPAN = re.compile(r"`([^`\n]+)`")


def run(*argv: str) -> str:
    return subprocess.run(argv, cwd=ROOT, capture_output=True, text=True,
                          check=True).stdout


def tracked() -> list[str]:
    return [p for p in run("git", "ls-files").split("\n") if p]
