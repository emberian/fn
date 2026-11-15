"""Source controls for the semantic descriptor-publication boundary.

These do not execute ACL2 or establish physical IO correctness.
"""
import sys
import unittest
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
from lisp_source import forms, read_sexp

BOOK = Path(__file__).resolve().parents[1] / "books" / "checkpoint-semantic-retention.lisp"


def definitions(source):
    return {node[1]: node for text in forms(source)
            if isinstance((node := read_sexp(text)), list) and node and node[0] == "defun"}


def calls(node):
    if not isinstance(node, list) or not node:
        return []
    return ([node[0]] if isinstance(node[0], str) else []) + [call for child in node for call in calls(child)]


def step_is_descriptor_free(source):
    step = definitions(source)["fn2-checkpoint-semantic-step"]
    return not any(name.startswith(("fn2-block-read", "fn2-issue-")) for name in calls(step[3:]))


class SemanticIssueSplit(unittest.TestCase):
    def test_actual_step_defers_the_read_to_one_explicit_issue(self):
        source = BOOK.read_text()
        self.assertTrue(step_is_descriptor_free(source))
        defs = definitions(source)
        step = defs["fn2-checkpoint-semantic-step"]
        issue = defs["fn2-checkpoint-semantic-issue"]
        self.assertEqual(step[2], issue[2])
        self.assertEqual(calls(issue[3:]).count("fn2-block-read-children"), 1)
        self.assertIn("(fn2-checkpoint-semantic-mv :need-read)", source)

    def test_hidden_read_mutation_is_detected(self):
        source = BOOK.read_text().replace("(fn2-checkpoint-semantic-mv :need-read)",
                                         "(fn2-block-read-children hidden)", 1)
        self.assertFalse(step_is_descriptor_free(source))


if __name__ == "__main__":
    unittest.main()
