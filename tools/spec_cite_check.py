#!/usr/bin/env python3
"""Every Lisp name a specification or document cites is one the tree defines.

The rules live in tools/cite/names.py; this is the command's long-standing entry point."""
import sys

from cite.names import *  # noqa: F401,F403
from cite.names import main

if __name__ == "__main__":
    sys.exit(main())
