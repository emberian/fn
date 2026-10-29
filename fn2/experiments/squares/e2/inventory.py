#!/usr/bin/env python3
"""Physical/code lines and named forms; no generated proof counts inferred."""
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / "tools"))
from lisp_rewrite import parse, match, Lst, Atom  # noqa: E402


def code_lines(text):
    return sum(bool(line.strip()) and not line.lstrip().startswith(";")
               for line in text.splitlines())


def entry(path):
    text = path.read_text()
    parsed = parse(text)
    definitions = []
    for found in match("_", parsed.forms, deep=True):
        node = found.node
        if not isinstance(node, Lst) or len(node.items) < 2:
            continue
        head, name = node.items[:2]
        if not isinstance(head, Atom) or not isinstance(name, Atom):
            continue
        if head.low not in {"defun", "defun-nx", "defun-sk", "defmacro", "defthm",
                            "defthmd", "defconst", "defparameter", "defvar", "defsquare"}:
            continue
        span = text[node.start:node.end]
        definitions.append(dict(kind=head.low, name=name.text,
                                line=text[:node.start].count("\n") + 1,
                                lines=span.count("\n") + 1, code_lines=code_lines(span)))
    return dict(file=str(path.relative_to(ROOT)), physical_lines=len(text.splitlines()),
                code_lines=code_lines(text), top_level_forms=len(parsed.forms),
                definitions=definitions)


def main():
    files = sorted(HERE.glob("*.lisp")) + sorted(HERE.glob("*.lsp"))
    rows = [entry(path) for path in files if path.name != "evidence-events.lsp"]
    for group, names in {
        "q1": {"q1-contract.lisp", "q1-bindings.lisp", "q1-campaigns.lsp", "q1-template-tests.lisp"},
        "q4": {"fold-contract.lisp", "read-state-history.lisp", "read-state-summary.lisp",
               "read-state-transport.lisp", "read-state-teeth.lisp", "q4-checker.lisp",
               "q4-template.lisp", "q4-square.lisp", "q4-template-tests.lisp"},
    }.items():
        selected = [row for row in rows if Path(row["file"]).name in names]
        (HERE / (group + "-inventory.json")).write_text(json.dumps(selected, indent=2) + "\n")
    (HERE / "inventory.json").write_text(json.dumps(rows, indent=2) + "\n")
    for row in rows:
        print(f'{Path(row["file"]).name}: {row["physical_lines"]} physical, '
              f'{row["code_lines"]} code, {len(row["definitions"])} named forms')


if __name__ == "__main__":
    main()
