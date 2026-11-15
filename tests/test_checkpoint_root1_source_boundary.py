"""Source controls for root1's IO and completion boundaries; no ACL2 execution."""
import sys
import unittest
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
from lisp_source import forms, read_sexp

ROOT = Path(__file__).resolve().parents[1]


def nodes(tree):
    if isinstance(tree, list):
        yield tree
        for child in tree:
            yield from nodes(child)


def operations(source):
    return {tree[1]: tree for text in forms(source)
            if isinstance((tree := read_sexp(text)), list) and tree
            and tree[0] == "fn2-checkpoint-root1-operation"}


def pure_driver(source):
    return all(not any(isinstance(node[0], str)
                       and (node[0].startswith(("fn2-block-read", "fn2-issue-"))
                            or node[0].endswith(("-issue", "-read")))
                       for node in nodes(op[3:]) if node)
               for op in operations(source).values())


def output_contracts(source):
    declaration = next(tree for text in forms(source)
                       if isinstance((tree := read_sexp(text)), list)
                       and tree[:2] == ["defconst", "*fn2-checkpoint-root1-outputs*"])
    rows = declaration[2]
    if rows and rows[0] == "quote":
        rows = rows[1]
    return {row[0]: set(row[1:]) for row in rows}


def assigned_carriers(op, outputs):
    assigned = set()
    for node in nodes(op[3:]):
        if node and node[0] in ("b*", "let", "let*") and isinstance(node[1], list):
            for binding in node[1]:
                if isinstance(binding, list) and binding:
                    lhs = binding[0]
                    names = lhs[1:] if isinstance(lhs, list) and lhs and lhs[0] == "mv" else [lhs]
                    assigned.update(name for name in names if isinstance(name, str) and name.startswith("fn2-"))
        if node and node[0] == "fn2-checkpoint-root1-call":
            assigned.update(outputs[node[1]])
    return assigned


class Root1SourceBoundary(unittest.TestCase):
    def test_pure_driver_cannot_publish_a_read(self):
        source = (ROOT / "books/checkpoint-metadata-driver.lisp").read_text()
        self.assertTrue(pure_driver(source))
        self.assertFalse(pure_driver(source.replace("(fn2-run-build-work b", "(fn2-block-read-children b", 1)))
        self.assertIn(":descriptors 1", source)
        self.assertIn("fn2-checkpoint-semantic-issue 1", source)
        self.assertIn("fn2-checkpoint-payload-issue 1", source)

    def test_page_wait_has_no_source_work_and_completion_uses_manifest_scan(self):
        source = (ROOT / "books/checkpoint-metadata-driver.lisp").read_text()
        ops = operations(source)
        bind = list(nodes(ops["fn2-checkpoint-root1-bind"][3:]))
        consume = list(nodes(ops["fn2-checkpoint-root1-consume"][3:]))
        self.assertFalse(any(n and n[0] == "fn2-run-build-work" for n in bind + consume))
        self.assertTrue(any(n and n[0] == "fn2-checkpoint-metadata-page-consume" for n in consume))
        setters = [name for name, op in ops.items()
                   if any(n and n[0] == "fn2-csnapshot-set-complete" for n in nodes(op))]
        self.assertEqual(setters, ["fn2-checkpoint-root1-closure"])
        self.assertIn("fn2-checkpoint-metadata-manifest-scan-step", str(ops[setters[0]]))

    def test_exact_harvest_hooks_and_issue_success_abi(self):
        resources = (ROOT / "books/checkpoint-metadata-resources.lisp").read_text()
        driver = (ROOT / "books/checkpoint-metadata-driver.lisp").read_text()
        declarations = resources + "\n" + (ROOT / "books/boot-kind.lisp").read_text() + "\n" + (ROOT / "books/machines-c.lisp").read_text()
        children = {tree[1]: tree for text in forms(declarations)
                    if isinstance((tree := read_sexp(text)), list) and tree
                    and tree[0] in ("fn2-sealer-child", "defcorechild")}
        hooks = []
        for field in ("fn2-core-checkpoint-semantic", "fn2-core-checkpoint-payload", "fn2-core-run-load-ops"):
            declaration = children[field]
            hooks.append(declaration[declaration.index(":harvest") + 1][0])
        self.assertEqual(hooks, ["fn2-checkpoint-semantic-harvest", "fn2-checkpoint-payload-harvest-children", "fn2-run-load-harvest"])
        self.assertNotIn("fn2-checkpoint-root1-harvest", operations(driver))
        normalized = [n for text in forms(driver) for n in nodes(read_sexp(text))
                      if n and n[0] == "fn2-checkpoint-root1-read-mv"
                      and len(n) == 2 and n[1] == ["if", ["eq", "code", ":issued"], ":ok", "code"]]
        self.assertEqual(len(normalized), 2)

    def test_projection_preserves_every_assigned_and_family_return_carrier(self):
        source = (ROOT / "books/checkpoint-metadata-driver.lisp").read_text()
        outputs = output_contracts(source)
        for name, op in operations(source).items():
            self.assertEqual(assigned_carriers(op, outputs), outputs[name], name)
            self.assertLessEqual(1 + len(outputs[name]), 32, name)
        self.assertEqual(1 + len(outputs["fn2-checkpoint-root1-step"]), 31)
        self.assertEqual(3 + len(outputs["fn2-checkpoint-root1-read"]), 19)
        self.assertTrue({"fn2-run-loads", "fn2-checkpoint-summary", "fn2-checkpoint-summary-leases"}.issubset(outputs["fn2-checkpoint-root1-work"]))
        self.assertTrue({"fn2-run-loads", "fn2-run-load-ops"}.issubset(outputs["fn2-checkpoint-root1-read"]))
        # A real output from the manifest scan must survive closure dispatch.
        damaged = {name: set(values) for name, values in outputs.items()}
        damaged["fn2-checkpoint-root1-closure"].remove("fn2-checkpoint-metadata-manifest")
        self.assertNotEqual(assigned_carriers(operations(source)["fn2-checkpoint-root1-closure"], damaged),
                            damaged["fn2-checkpoint-root1-closure"])
        self.assertIn("fn2-checkpoint-root1-project body outputs", source)
        self.assertIn("fn2-checkpoint-root1-child-specs outputs 1", source)
        self.assertIn("fn2-checkpoint-root1-child-specs outputs 3", source)
        self.assertIn(":effects ((:acquire (:operation)))", source)


if __name__ == "__main__":
    unittest.main()
