#!/usr/bin/env python3
"""Emit the original actual wait implementation and its unchanged full witness.

Send after the current compression fixture in a retained ACL2 world. The
negative assertion checks that restoring the old fresh-sibling kick fails
while all owner progress/settlement code remains the actual fixture.
"""
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
from lisp_source import forms


def mutant_forms():
    old_source = subprocess.check_output(
        ["git", "show", "694b73f6e:books/compress-close.lisp"], cwd=ROOT, text=True)
    candidates = [f for f in forms(old_source)
                  if f.startswith("(defun fn2-compress-record-stack-wait\n")]
    assert len(candidates) == 1, "expected the original actual wait implementation"
    yield candidates[0].replace("fn2-compress-record-stack-wait", "fn2-compress-record-stack-wait-spinning")
    selected = [f for f in forms((ROOT / "tests/compress-record-unit.lisp").read_text())
                if f.startswith("(defun fn2-compress-sibling-")]
    assert len(selected) == 4, "expected both fresh-instance and owner control pairs"
    for form in selected:
        yield form.replace("fn2-compress-sibling-", "fn2-compress-spinning-").replace(
            "fn2-compress-record-stack-wait", "fn2-compress-record-stack-wait-spinning")
    yield "(assert-event (not (fn2-compress-spinning-owner-check)))"


if __name__ == "__main__":
    print("\n".join(mutant_forms()))
