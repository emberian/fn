#!/usr/bin/env python3
"""Find the repository paths this tree cites that no file in it answers.

The rules live in tools/cite/paths.py; this is the command's long-standing entry point."""
import sys

from cite.paths import *  # noqa: F401,F403
from cite.paths import main

if __name__ == "__main__":
    sys.exit(main())
