"""Unit tests for tools/machine_field_rewrite.py."""
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))

from machine_field_rewrite import RewriteTests  # noqa: E402,F401

if __name__ == "__main__":
    unittest.main()
