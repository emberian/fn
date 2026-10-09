"""Every native action the operator surface names has a heap growth row.

books/heap-command.lisp *fn-heap-action-growth* tables each native action
(books/native-operator.lisp fn-native-operator-result-native-action) by what
the command does to the store: :serves, :grows, :lists, :reads or
:store-less (coordinator ruling, 2026-10-09: a command's reservation states
what the command does).  An action missing from the table would fall to the
default :grows silently; this test makes a new action a red until it is
classed.
"""
from __future__ import annotations

import re
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CLASSES = {":serves", ":grows", ":lists", ":reads", ":store-less"}


def defun_body(text: str, name: str) -> str:
    start = text.index(f"(defun {name} ")
    depth = 0
    for i in range(start, len(text)):
        if text[i] == "(":
            depth += 1
        elif text[i] == ")":
            depth -= 1
            if depth == 0:
                return text[start:i + 1]
    raise ValueError(name)


def native_actions() -> set[str]:
    text = (ROOT / "books/native-operator.lisp").read_text(encoding="utf-8")
    body = defun_body(text, "fn-native-operator-result-native-action")
    body = body.split('"""', 1)[0] if '"""' in body else body
    # the docstring holds no keyword result; the results are the keywords that
    # end a cond arm: `) :KEYWORD)' or a bare `:KEYWORD)' on its own line
    found = set(re.findall(r"\)\s+(:[a-z][a-z0-9-]*)\)", body))
    found |= set(re.findall(r"^\s*(:[a-z][a-z0-9-]*)\)", body, re.M))
    found |= set(re.findall(r"\(t (:[a-z][a-z0-9-]*)\)", body))
    found.discard(":accepted")
    return found


def growth_table() -> dict[str, str]:
    text = (ROOT / "books/heap-command.lisp").read_text(encoding="utf-8")
    start = text.index("(defconst *fn-heap-action-growth*")
    end = text.index("\n\n", start)
    return dict(re.findall(r"\((:[a-z][a-z0-9-]*) \. (:[a-z-]+)\)", text[start:end]))


def list_actions() -> set[str]:
    text = (ROOT / "books/heap-figure.lisp").read_text(encoding="utf-8")
    m = re.search(r"\(defconst \*fn-heap-list-actions\* '\(([^)]*)\)\)", text)
    return set(m.group(1).split())


class HeapActionGrowthTests(unittest.TestCase):
    def test_the_parser_sees_the_surface(self):
        actions = native_actions()
        for known in (":run", ":init", ":status", ":none", ":owner-required", ":recover",
                      ":admin", ":inspect-group"):
            self.assertIn(known, actions)

    def test_every_native_action_has_a_row(self):
        table = growth_table()
        missing = sorted(native_actions() - set(table))
        self.assertEqual(missing, [], "native actions with no growth row in books/heap-command.lisp")

    def test_every_row_names_a_class_and_an_action(self):
        table = growth_table()
        self.assertEqual(sorted(set(table.values()) - CLASSES), [])
        self.assertEqual(sorted(set(table) - native_actions()), [],
                         "growth rows for actions the surface no longer names")

    def test_the_list_rows_are_the_list_verbs(self):
        table = growth_table()
        self.assertEqual({a for a, c in table.items() if c == ":lists"}, list_actions())

    def test_run_alone_serves_and_init_holds_no_store(self):
        table = growth_table()
        self.assertEqual([a for a, c in table.items() if c == ":serves"], [":run"])
        self.assertEqual(table[":init"], ":store-less")
        self.assertEqual(table[":status"], ":reads")

    def test_a_stopped_status_holds_no_store(self):
        """`status' opens the store only with `--replay'
        (host/native/operator.lisp fnn-operator-status-once: the stopped
        report is the checkpoint header's); fn-heap-command-growth classes
        the stopped one store-less, and its keystone says so."""
        text = (ROOT / "books/heap-command.lisp").read_text(encoding="utf-8")
        body = defun_body(text, "fn-heap-command-growth")
        self.assertIn("(and (equal action :status) (not replayp))", body)
        self.assertIn(":store-less", body)
        self.assertIn("(defthm fn-heap-stopped-status-holds-no-store", text)

    def test_the_offline_readers_that_open_the_store_read(self):
        table = growth_table()
        for action in (":health", ":inspect", ":inspect-group"):
            self.assertEqual(table[action], ":reads", action)
        for action in (":operation", ":export-status"):
            self.assertEqual(table[action], ":store-less", action)
        # Codex (b-heap-growth review): account-hash reads a credential file
        # the profile sizes, so it is not store-less.
        self.assertEqual(table[":account-hash"], ":grows")


if __name__ == "__main__":
    unittest.main()
