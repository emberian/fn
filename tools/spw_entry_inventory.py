#!/usr/bin/env python3
"""Emit a consumer Spw reading checklist from actual native entry definitions.

This is exact source discovery, not reachability, public-image support, or
completed review. Use callgraph.py for conservative downstream reading lists.
The mounted workbench parses/navigates the resulting consumer-owned cards.
"""
from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from callgraph import collect
from ledger import Reader

ROOT = Path(__file__).resolve().parents[1]
SERVICE_ENTRIES = {
    "fnn-main", "fnn-dispatch", "fnn-owner-run", "fnn-web-start",
    "fnn-ninep-start", "fnn-remote-receive-installed",
}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--output", type=Path,
                        default=Path(".spw/audits/entries/entrypoints.spw"))
    args = parser.parse_args()
    root = args.root.resolve()
    revision = subprocess.check_output(
        ["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip()
    output = args.output if args.output.is_absolute() else root / args.output
    import os
    cards = [
        "# Actual native entry candidates; discovery is not full trace coverage.",
        '^"coordinate"{ source_revision: "' + revision + '"',
        ' tier: "exact source discovery; public-image exposure and downstream reading unestablished" }',
    ]
    count = 0
    for path in sorted((root / "host/native").glob("*.lisp")):
        data = path.read_bytes()
        definitions = collect(Reader(data.decode()).top_level(),
                              path.relative_to(root).as_posix(), records=False)
        for definition in definitions:
            if (not definition.name.startswith("fnn-command-")
                    and definition.name not in SERVICE_ENTRIES):
                continue
            count += 1
            relative = Path(os.path.relpath(path, output.parent)).as_posix()
            cards.extend([
                '^"' + definition.name + '"{',
                ' @source: ~"' + relative + '"',
                " line: " + str(definition.line),
                ' source_sha256: "' + hashlib.sha256(data).hexdigest() + '"',
                ' coverage: "catalogued; see coverage.md for actual reading and fixtures"',
                "}",
            ])
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text("\n".join(cards) + "\n")
    print(f"Inventoried {count} native entry candidates at {revision[:12]}.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
