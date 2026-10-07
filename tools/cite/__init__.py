"""One citation checker, three rule sets over the tree's prose.

  paths  a repository path no file answers          (was tools/cite_check.py)
  names  a Lisp name no book or host file defines   (was tools/spec_cite_check.py)
  docs   a command, reply or generated region the
         docs state that the code does not back     (was tools/docs_check.py)

    python3 -m cite paths --summary --strict       (run from tools/)

The old command names stay as entry points: tools/cite_check.py,
tools/spec_cite_check.py and tools/docs_check.py each call one rule set's main.
"""
from __future__ import annotations

import importlib
import sys

RULESETS = ("paths", "names", "docs")


def main(argv=None) -> int:
    argv = list(sys.argv[1:] if argv is None else argv)
    if not argv or argv[0] not in RULESETS:
        print("usage: python3 -m cite {%s} [options]" % ",".join(RULESETS), file=sys.stderr)
        return 2
    return importlib.import_module("cite." + argv[0]).main(argv[1:])
