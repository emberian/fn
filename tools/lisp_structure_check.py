#!/usr/bin/env python3
"""Check ACL2 expression structure after reading source with lisp_source.

This is a source preflight, not an ACL2 reader, macroexpander or admission gate.
It checks B*, IF, COND, LET and LET* shapes, including quasiquoted templates;
ordinary quoted data is skipped. A direct quoted PROGN returned by a
DEFMACRO is checked as emitted code. No arity/guard claims are made.
Usage: python3 tools/lisp_structure_check.py FILE...
"""
from __future__ import annotations
import argparse
from pathlib import Path
import lisp_source


def check_tree(tree: object, where: str = "form") -> list[str]:
    errors: list[str] = []

    def visit(node: object, path: str, template_depth: int = 0) -> None:
        if not isinstance(node, list) or not node:
            return
        head = node[0].lower() if isinstance(node[0], str) else None
        if head == "quote":
            return
        if head == "quasiquote" and len(node) == 2:
            visit(node[1], f"{path}/template", template_depth + 1)
            return
        if head in ("unquote", "unquote-splicing") and template_depth and len(node) == 2:
            visit(node[1], f"{path}/generator", template_depth - 1)
            return
        if head in {"defun", "defmacro"}:
            for i, child in enumerate(node[3:], 3):
                # ACL2 event emitters often return a literal quoted PROGN.
                # Only the direct result position has this code context; a
                # quoted list inside a function/constant remains ordinary data.
                if (head == "defmacro" and i == len(node) - 1
                        and isinstance(child, list) and len(child) == 2
                        and child[0] == "quote" and isinstance(child[1], list)
                        and child[1] and child[1][0] == "progn"):
                    visit(child[1], f"{path}/{head}-emitted-progn", template_depth)
                else:
                    visit(child, f"{path}/{head}[{i}]", template_depth)
            return
        if head == "if" and len(node) != 4:
            errors.append(f"{path}: IF needs test, then and else; got {len(node) - 1} arguments")
        if head == "cond":
            for i, clause in enumerate(node[1:], 1):
                if (template_depth and isinstance(clause, list) and clause
                        and clause[0] in ("unquote", "unquote-splicing")):
                    visit(clause, f"{path}/clause-generator[{i}]", template_depth)
                elif not isinstance(clause, list) or len(clause) != 2:
                    errors.append(f"{path}: COND clause {i} needs test and expression")
        if head in {"b*", "let", "let*"}:
            if len(node) != 3:
                errors.append(f"{path}: {head.upper()} needs bindings and one body")
            bindings = node[1] if len(node) > 1 else None
            if (template_depth and isinstance(bindings, list) and bindings
                    and bindings[0] in ("unquote", "unquote-splicing")):
                # The generator determines the binding list only at expansion.
                # Its expression still gets normal structural validation.
                visit(bindings, f"{path}/bindings-generator", template_depth)
            elif not isinstance(bindings, list):
                errors.append(f"{path}: {head.upper()} needs a binding list")
            else:
                for i, binding in enumerate(bindings):
                    if (template_depth and isinstance(binding, list) and binding
                            and binding[0] in ("unquote", "unquote-splicing")):
                        visit(binding, f"{path}/binding-generator[{i}]", template_depth)
                        continue
                    if not isinstance(binding, list) or len(binding) != 2:
                        errors.append(f"{path}: {head.upper()} binding {i} needs pattern and expression")
                    elif head != "b*" and not isinstance(binding[0], str):
                        errors.append(f"{path}: {head.upper()} binding {i} needs a symbol")
                    if isinstance(binding, list) and len(binding) == 2:
                        pattern = binding[0]
                        if head == "b*" and isinstance(pattern, list) and pattern:
                            if pattern[0] in {"when", "unless"}:
                                for child in pattern[1:]:
                                    visit(child, f"{path}/test[{i}]", template_depth)
                        visit(binding[1], f"{path}/binding[{i}]", template_depth)
            for i, child in enumerate(node[2:], 2):
                visit(child, f"{path}/body[{i}]", template_depth)
            return
        for i, child in enumerate(node):
            visit(child, f"{path}[{i}]", template_depth)

    visit(tree, where)
    return errors


def check_source(source: str) -> list[str]:
    def datum(node: object) -> object:
        value = ([datum(child) for child in node.items]
                 if isinstance(node, lisp_source.List) else node.text)
        names = {"'": "quote", "`": "quasiquote", ",": "unquote",
                 ",@": "unquote-splicing", "#'": "function", "#.": "read-eval"}
        for mark in reversed(node.marks):
            value = [names.get(mark, mark), value]
        return value

    errors: list[str] = []
    for i, node in enumerate(lisp_source.read_all(source, strict=True), 1):
        errors.extend(check_tree(datum(node), f"form {i}"))
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("files", nargs="+", type=Path)
    args = parser.parse_args()
    failed = False
    for path in args.files:
        try:
            errors = check_source(path.read_text())
        except (ValueError, IndexError) as exc:
            errors = [f"source parse failed: {exc}"]
        for error in errors:
            print(f"{path}: {error}")
        print(f"{path}: {len(errors)} structural finding(s)")
        failed |= bool(errors)
    return int(failed)


if __name__ == "__main__":
    raise SystemExit(main())
