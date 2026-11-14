#!/usr/bin/env python3
"""Check ACL2 expression structure after reading source with lisp_source.

This is a source preflight, not an ACL2 reader, macroexpander or admission gate.
It checks B*, IF, COND, LET and LET* shapes and the ACL2 MV output limit,
including quasiquoted templates. MV counts use literal positions and known
list lengths from quoted constants or lexical aliases; no Lisp is evaluated.
Unresolved MV splices are findings, not evidence that an expansion is safe.
Other unexpanded macro calls remain outside this check. Readonly inputs and
formal parameter counts are not output counts. Ordinary quoted data is skipped;
a direct quoted DEFMACRO result is checked as emitted code. No general
arity, guard or admission claim is made.
Usage: python3 tools/lisp_structure_check.py FILE...
"""
from __future__ import annotations
import argparse
from pathlib import Path
import lisp_source

# ACL2 8.7_8 acl2.lisp defines *number-of-return-values* as 32; translate.lisp
# enforces the same bound on MV. This is ACL2's bound, not the host CL limit.
ACL2_MV_LIMIT = 32


def symbol_key(name: str) -> str:
    # Preserve case-sensitive reader escapes; treating those as different
    # aliases is conservative, whereas lowercasing them could invent a size.
    return name if "|" in name or "\\" in name else name.lower()


def operator_name(node: object) -> str | None:
    if not isinstance(node, list) or not node or not isinstance(node[0], str):
        return None
    name = symbol_key(node[0])
    return name.removeprefix("acl2::")


def known_list_size(node: object, sizes: dict[str, int]) -> int | None:
    """Recognize list-building syntax only; never expand or execute a call."""
    if isinstance(node, str):
        return 0 if node.lower() == "nil" else sizes.get(symbol_key(node))
    if not isinstance(node, list):
        return None
    if not node:
        return 0
    head = operator_name(node)
    if head == "quote" and len(node) == 2:
        return len(node[1]) if isinstance(node[1], list) else (
            0 if isinstance(node[1], str) and node[1].lower() == "nil" else None)
    if head == "list":
        return len(node) - 1
    if head == "quasiquote" and len(node) == 2 and isinstance(node[1], list):
        count, unknown = mv_output_count(node[1], sizes, 1)
        return None if unknown else count
    if head in {"append", "list*", "cons"}:
        if head == "cons":
            if len(node) != 3:
                return None
            tail = known_list_size(node[2], sizes)
            return None if tail is None else tail + 1
        if head == "list*":
            if len(node) < 2:
                return None
            tail = known_list_size(node[-1], sizes)
            return None if tail is None else tail + len(node) - 2
        lengths = [known_list_size(part, sizes) for part in node[1:]]
        return None if None in lengths else sum(lengths)
    return None


def mv_output_count(arguments: list, sizes: dict[str, int],
                    template_depth: int) -> tuple[int, list[object]]:
    """Return a definite lower bound and unresolved template splices."""
    count = 0
    unknown = []
    for argument in arguments:
        if template_depth and operator_name(argument) == "unquote-splicing":
            length = (known_list_size(argument[1], sizes)
                      if len(argument) == 2 and template_depth == 1 else None)
            if length is None:
                unknown.append(argument)
            else:
                count += length
        else:
            # An unquoted expression still supplies exactly one MV position.
            count += 1
    return count, unknown


def check_tree(tree: object, where: str = "form", *,
               list_sizes: dict[str, int] | None = None) -> list[str]:
    errors: list[str] = []

    def visit(node: object, path: str, template_depth: int = 0,
              sizes: dict[str, int] | None = None) -> None:
        sizes = {} if sizes is None else sizes
        if not isinstance(node, list) or not node:
            return
        head = operator_name(node)
        if head == "quote":
            return
        if head == "quasiquote" and len(node) == 2:
            visit(node[1], f"{path}/template", template_depth + 1, sizes)
            return
        if head in ("unquote", "unquote-splicing") and template_depth and len(node) == 2:
            visit(node[1], f"{path}/generator", template_depth - 1, sizes)
            return
        if head in {"defun", "defmacro"}:
            local_sizes = dict(sizes)
            # Generated formals bind the emitted program, not the generator's
            # lexical variables used by unquotes inside its template.
            if not template_depth and len(node) > 2 and isinstance(node[2], list):
                for formal in node[2]:
                    if isinstance(formal, str):
                        local_sizes.pop(symbol_key(formal), None)
                    elif isinstance(formal, list) and formal and isinstance(formal[0], str):
                        local_sizes.pop(symbol_key(formal[0]), None)
            for i, child in enumerate(node[3:], 3):
                # Only a macro's direct result position has code context; a
                # quoted list inside a function/constant remains ordinary data.
                if (head == "defmacro" and i == len(node) - 1
                        and isinstance(child, list) and len(child) == 2
                        and child[0] == "quote" and isinstance(child[1], list)):
                    visit(child[1], f"{path}/{head}-emitted-code", template_depth,
                          local_sizes)
                else:
                    visit(child, f"{path}/{head}[{i}]", template_depth, local_sizes)
            return
        if head == "mv":
            count, unknown = mv_output_count(node[1:], sizes, template_depth)
            if count > ACL2_MV_LIMIT:
                qualifier = "at least " if unknown else ""
                errors.append(f"{path}: MV returns {qualifier}{count} values; "
                              f"ACL2 limit is {ACL2_MV_LIMIT}")
            if unknown:
                errors.append(f"{path}: MV output count unresolved: "
                              f"{len(unknown)} splice(s) require expansion "
                              f"({count} known output positions)")
        if head in {"mv-let", "lambda"}:
            local_sizes = dict(sizes)
            if not template_depth and len(node) > 1 and isinstance(node[1], list):
                for name in node[1]:
                    if isinstance(name, str):
                        local_sizes.pop(symbol_key(name), None)
            start = 2
            if head == "mv-let" and len(node) > 2:
                visit(node[2], f"{path}/producer", template_depth, sizes)
                start = 3
            for i, child in enumerate(node[start:], start):
                visit(child, f"{path}/body[{i}]", template_depth, local_sizes)
            return
        if head == "if" and len(node) != 4:
            errors.append(f"{path}: IF needs test, then and else; got {len(node) - 1} arguments")
        if head == "cond":
            for i, clause in enumerate(node[1:], 1):
                if (template_depth and isinstance(clause, list) and clause
                        and clause[0] in ("unquote", "unquote-splicing")):
                    visit(clause, f"{path}/clause-generator[{i}]", template_depth, sizes)
                elif not isinstance(clause, list) or len(clause) != 2:
                    errors.append(f"{path}: COND clause {i} needs test and expression")
        if head in {"b*", "let", "let*"}:
            local_sizes = dict(sizes)
            if len(node) != 3:
                errors.append(f"{path}: {head.upper()} needs bindings and one body")
            bindings = node[1] if len(node) > 1 else None
            if (template_depth and isinstance(bindings, list) and bindings
                    and bindings[0] in ("unquote", "unquote-splicing")):
                # The generator determines the binding list only at expansion.
                # Its expression still gets normal structural validation.
                visit(bindings, f"{path}/bindings-generator", template_depth, sizes)
            elif not isinstance(bindings, list):
                errors.append(f"{path}: {head.upper()} needs a binding list")
            else:
                for i, binding in enumerate(bindings):
                    if (template_depth and isinstance(binding, list) and binding
                            and binding[0] in ("unquote", "unquote-splicing")):
                        visit(binding, f"{path}/binding-generator[{i}]", template_depth, local_sizes)
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
                                    visit(child, f"{path}/test[{i}]", template_depth, local_sizes)
                        rhs_sizes = sizes if head == "let" else local_sizes
                        visit(binding[1], f"{path}/binding[{i}]", template_depth, rhs_sizes)
                        if not template_depth and isinstance(pattern, str):
                            length = known_list_size(binding[1], rhs_sizes)
                            local_sizes.pop(symbol_key(pattern), None)
                            if length is not None:
                                local_sizes[symbol_key(pattern)] = length
                        elif (not template_depth and head == "b*" and isinstance(pattern, list) and pattern
                              and pattern[0] == "mv"):
                            # These bind results, not list-valued constants.
                            for name in pattern[1:]:
                                if isinstance(name, str):
                                    local_sizes.pop(symbol_key(name), None)
            for i, child in enumerate(node[2:], 2):
                visit(child, f"{path}/body[{i}]", template_depth, local_sizes)
            return
        for i, child in enumerate(node):
            visit(child, f"{path}[{i}]", template_depth, sizes)

    visit(tree, where, sizes=list_sizes)
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
    sizes: dict[str, int] = {}
    for i, node in enumerate(lisp_source.read_all(source, strict=True), 1):
        form = datum(node)
        errors.extend(check_tree(form, f"form {i}", list_sizes=sizes))
        if (isinstance(form, list) and len(form) >= 3
                and operator_name(form) == "defconst" and isinstance(form[1], str)):
            name = symbol_key(form[1])
            length = known_list_size(form[2], sizes)
            sizes.pop(name, None)
            if length is not None:
                sizes[name] = length
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
