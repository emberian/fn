#!/usr/bin/env python3
"""Emit an ACL2 negative control from the actual TLS NEXT and progress fixture.

After loading tests/tls-record-progress-unit in proof_repl, send the emitted
forms with send-file. Both assertions must pass: conflating readiness and SSL
progress must make each full transition control return false.
"""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
from lisp_source import forms


def mutant_forms():
    controller = forms((ROOT / "books/tls-record.lisp").read_text())
    selected = [f for f in controller if f.startswith("(defun fn2-tls-record-next ")]
    assert len(selected) == 1, "expected the actual NEXT definition"
    original = selected[0]
    argument = "(fn2-tls-record-ssl-progress 0 fn2-tls-record)"
    assert original.count(argument) == 1, "expected one SSL epoch policy argument"
    yield original.replace("fn2-tls-record-next", "fn2-tls-record-next-conflated").replace(
        argument, "(fn2-tls-record-seen-progress 0 fn2-tls-record)")
    fixture = forms((ROOT / "tests/tls-record-progress-unit.lisp").read_text())
    runners = [f for f in fixture if f.startswith("(defun fn2-tls-record-progress-")]
    assert len(runners) == 2, "expected runner and local-stobj wrapper"
    for form in runners:
        yield form.replace("fn2-tls-record-progress-", "fn2-tls-record-conflated-").replace(
            "fn2-tls-record-next", "fn2-tls-record-next-conflated")
    yield "(assert-event (not (fn2-tls-record-conflated-check nil)))"
    yield "(assert-event (not (fn2-tls-record-conflated-check t)))"


if __name__ == "__main__":
    print("\n".join(mutant_forms()))
