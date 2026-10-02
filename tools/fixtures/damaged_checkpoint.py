#!/usr/bin/env python3
"""Test fixture: a published state checkpoint re-written by ACL2 with one
group's article-number watermark set past the maximum article number.

No store verb sets a watermark and replay only increments one, so the store
the open must refuse by name (books/owner-number-bound.lisp fn-onb-open-okp,
:article-numbers-damaged) is built from a real checkpoint: the codec work --
split, decode, replace, re-encode, re-seal, round-trip check -- is ACL2's
(tools/fixtures/damaged-checkpoint.lisp over the tree's certified books);
this driver only moves the file and reads ACL2's verdict.

    python3 tools/fixtures/damaged_checkpoint.py CHECKPOINT [--watermark N]

rewrites CHECKPOINT in place and prints `GROUP OLD -> N'.  Needs FN_ACL2 (or
`acl2' on PATH) and the certified closure of the two books the script
includes.
"""
from __future__ import annotations

import argparse
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools"))
import acl2_slots  # noqa: E402

SCRIPT = ROOT / "tools" / "fixtures" / "damaged-checkpoint.lisp"
# books/nntp-syntax.lisp *fn-nntp-max-article-number* is 2147483647.
DEFAULT_WATERMARK = 2147483648
RESULT = re.compile(r"FX-RESULT \(:OK (.+) (\d+)\)")
REFUSED = re.compile(r"FX-RESULT (\(:REFUSED[^\n]*)")


class FixtureError(Exception):
    pass


def acl2_executable() -> str:
    configured = os.environ.get("FN_ACL2", "acl2")
    found = configured if os.sep in configured else shutil.which(configured)
    if not found or not os.access(found, os.X_OK):
        raise FixtureError("no ACL2 executable (set FN_ACL2)")
    return found


def lisp_string(path: Path) -> str:
    text = str(path)
    if '"' in text or "\\" in text:
        raise FixtureError("path not representable as an ACL2 string: " + text)
    return '"' + text + '"'


def damage(checkpoint: Path, watermark: int = DEFAULT_WATERMARK,
           timeout: float = 900.0) -> tuple[str, int]:
    """Rewrite CHECKPOINT with its first group's watermark at WATERMARK;
    the group and the watermark it replaced."""
    with tempfile.TemporaryDirectory(prefix="fn-damaged-checkpoint-") as scratch:
        out = Path(scratch) / "checkpoint"
        forms = "\n".join([
            '(include-book "books/store-checkpoint-tables")',
            '(include-book "books/history-image-snapshot")',
            '(include-book "books/crypto-attach")',
            "(ld {})".format(lisp_string(SCRIPT)),
            "(mv-let (result state) (fx-damage-file {} {} {} state)".format(
                lisp_string(checkpoint.resolve()), lisp_string(out), int(watermark)),
            "  (prog2$ (cw \"~%FX-RESULT ~x0~%\" result) (mv nil :done state)))",
            "(good-bye)",
            "",
        ])
        done = acl2_slots.run([acl2_executable()], "damaged-checkpoint fixture",
                              cwd=ROOT, input=forms.encode("ascii"),
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                              timeout=timeout)
        text = done.stdout.decode("utf-8", errors="replace")
        found = RESULT.search(text)
        if not found:
            refused = REFUSED.search(text)
            raise FixtureError(refused.group(1) if refused else
                               "ACL2 gave no verdict:\n" + text[-3000:])
        shutil.copyfile(out, checkpoint)
        return found.group(1), int(found.group(2))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("checkpoint", type=Path)
    parser.add_argument("--watermark", type=int, default=DEFAULT_WATERMARK)
    args = parser.parse_args(argv)
    try:
        group, old = damage(args.checkpoint, args.watermark)
    except FixtureError as error:
        print("damaged_checkpoint: {}".format(error), file=sys.stderr)
        return 2
    print("{} {} -> {}".format(group, old, args.watermark))
    return 0


if __name__ == "__main__":
    sys.exit(main())
