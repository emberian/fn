#!/usr/bin/env python3
"""A test module's `if __name__ == "__main__":` block is its LAST statement.

    python3 tools/main_last_check.py            # every tests/*.py
    python3 tools/main_last_check.py FILE...

Run as a script (`python3 tests/test_x.py`, and tools/test_budget.py's
runner imports the module the same way unittest does), a module whose main
block sits mid-file runs `unittest.main()` before the classes below it are
defined, and every one of them silently never runs: tests/test_farm.py and
tests/test_native_bounds_blob.py both did (obstructions-4; obstructions-5
item 36).  An unguarded `unittest.main()` anywhere else (in a class body,
at the top level) runs at import and ends the importing runner (obstructions-3
item 29: test_budget read its argv and exited 2).

It refuses, per file, with the line:
  * a top-level `if __name__ == "__main__":` that is not the last statement;
  * more than one such block;
  * a call of `unittest.main(...)` (or a bare `main()` imported from unittest)
    outside that block.
Exit 0 clean, 1 with findings.  Static (ast), no imports, seconds.
"""
from __future__ import annotations

import ast
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def is_main_guard(node: ast.stmt) -> bool:
    if not isinstance(node, ast.If) or not isinstance(node.test, ast.Compare):
        return False
    test = node.test
    sides = [test.left, *test.comparators]
    names = {side.id for side in sides if isinstance(side, ast.Name)}
    texts = {side.value for side in sides if isinstance(side, ast.Constant)}
    return (len(test.ops) == 1 and isinstance(test.ops[0], ast.Eq)
            and names == {"__name__"} and texts == {"__main__"})


def unittest_main_calls(tree: ast.AST) -> list[int]:
    """Lines of `unittest.main(...)` calls (and `main()` from `from unittest import main`)."""
    bare = any(isinstance(node, ast.ImportFrom) and node.module == "unittest"
               and any(alias.name == "main" and alias.asname is None for alias in node.names)
               for node in ast.walk(tree))
    lines = []
    for node in ast.walk(tree):
        if not isinstance(node, ast.Call):
            continue
        func = node.func
        if (isinstance(func, ast.Attribute) and func.attr == "main"
                and isinstance(func.value, ast.Name) and func.value.id == "unittest"):
            lines.append(node.lineno)
        elif bare and isinstance(func, ast.Name) and func.id == "main":
            lines.append(node.lineno)
    return lines


def findings(path: Path, text: str | None = None) -> list[str]:
    source = path.read_text(encoding="utf-8") if text is None else text
    try:
        tree = ast.parse(source, filename=str(path))
    except SyntaxError as error:
        return [f"{path}:{error.lineno}: does not parse: {error.msg}"]
    body = tree.body
    guards = [node for node in body if is_main_guard(node)]
    found = []
    if len(guards) > 1:
        found.append(f"{path}:{guards[1].lineno}: a second `if __name__ == \"__main__\":` "
                     f"block (the first is at line {guards[0].lineno})")
    for guard in guards:
        if guard is not body[-1]:
            later = body[body.index(guard) + 1]
            found.append(f"{path}:{guard.lineno}: `if __name__ == \"__main__\":` is not the "
                         f"last statement (line {later.lineno} follows it): run as a script, "
                         "nothing after it is defined before unittest.main() runs")
    guarded = {node.lineno for guard in guards for node in ast.walk(guard)
               if isinstance(node, ast.Call)}
    for line in unittest_main_calls(tree):
        if line not in guarded:
            found.append(f"{path}:{line}: unittest.main() outside the "
                         "`if __name__ == \"__main__\":` block runs at import")
    return found


def main(argv: list[str] | None = None) -> int:
    words = sys.argv[1:] if argv is None else argv
    files = [Path(word) for word in words] or sorted((ROOT / "tests").glob("*.py"))
    found = [one for path in files for one in findings(path)]
    for one in found:
        print(f"FAIL {one}")
    print(f"main_last_check: {len(files)} file(s), {len(found)} finding(s)")
    return 1 if found else 0


if __name__ == "__main__":
    raise SystemExit(main())
