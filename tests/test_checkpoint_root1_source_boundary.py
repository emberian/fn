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


if __name__ == "__main__":
    unittest.main()
