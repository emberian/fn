#!/usr/bin/env python3
"""Fixed-source beta and call normalization for the ADOPTED rearm family.

The immutable 5b00fa335 functions are the control.  Normalizing an internal
body replaces its phase formal with HELD and folds each phase-threaded call
back to the original callee.  Applying the public wrapper to its own formals
must then recover that exact control body and declaration.
"""
from __future__ import annotations

import hashlib
import subprocess
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import lisp_rewrite as lr
import rewrite_adopted_rearm_phase as rw

BASE = "5b00fa335b9ba67dfaad84a4bbb4c13bad46f3da"


def tree(node):
    if isinstance(node, lr.Pre):
        return ("prefix", node.prefix, tree(node.node))
    if isinstance(node, lr.Str):
        return ("string", node.text)
    if isinstance(node, lr.Atom):
        return node.low
    return tuple(tree(item) for item in node.items)


def restored_body(node):
    if isinstance(node, lr.Pre):
        return ("prefix", node.prefix, restored_body(node.node))
    if isinstance(node, lr.Str):
        return ("string", node.text)
    if isinstance(node, lr.Atom):
        return rw.HELD if node.low == "phase" else node.low
    items = node.items
    if rw.head(node) in {name + "-at-phase" for name in rw.NAMES}:
        assert len(items) > 1 and tree(items[1]) == "phase"
        return (rw.head(node).removesuffix("-at-phase"),
                *(restored_body(item) for item in items[2:]))
    return tuple(restored_body(item) for item in items)


class RearmPhaseSourceTest(unittest.TestCase):
    def test_old_api_is_exact_held_beta_expansion(self):
        for stem, names in rw.FAMILY.items():
            path = f"books/{stem}.lisp"
            original = subprocess.check_output(["git", "show", f"{BASE}:{path}"], cwd=rw.ROOT).decode()
            control = lr.parse(original)
            current = lr.parse(rw.ROOT / path)
            for name, digest in names.items():
                with self.subTest(name=name):
                    old = rw.source_function(control, name)
                    self.assertEqual(hashlib.sha256(original[old.start:old.end].encode()).hexdigest(), digest)
                    wrapper = rw.source_function(current, name)
                    inner = rw.source_function(current, name + "-at-phase")
                    self.assertEqual(tree(wrapper.items[2]), tree(old.items[2]))
                    self.assertEqual(tree(wrapper.items[3]), tree(old.items[3]))
                    self.assertEqual(tree(inner.items[3]), tree(old.items[3]))
                    self.assertEqual(tree(inner.items[2]), ("phase", *tree(old.items[2])))
                    args = tree(old.items[2])
                    self.assertEqual(tree(wrapper.items[4]),
                                     (name + "-at-phase", rw.HELD, *args))
                    self.assertEqual(restored_body(inner.items[4]), tree(old.items[4]))

    def test_only_named_bodies_call_phase_functions(self):
        for stem, names in rw.FAMILY.items():
            parsed = lr.parse(rw.ROOT / "books" / (stem + ".lisp"))
            defuns = [node for top in parsed.forms for node in rw.walk(top)
                      if rw.head(node) == "defun"]
            for function in defuns:
                if not isinstance(function.items[1], lr.Atom):
                    continue
                caller = function.items[1].low
                calls = [node for node in rw.walk(function.items[4])
                         if rw.head(node) in {name + "-at-phase" for name in rw.NAMES}]
                if caller in names or caller.removesuffix("-at-phase") in names:
                    continue
                self.assertEqual(calls, [], caller)


if __name__ == "__main__":
    unittest.main()
