#!/usr/bin/env python3
"""Every command the docs name exists, with the grammar the docs give.

The rules live in tools/cite/docs.py; this is the command's long-standing entry point."""
import sys

from cite.docs import *  # noqa: F401,F403
from cite.docs import main

if __name__ == "__main__":
    sys.exit(main())
