"""Warm raw-cache seam, in a developer world plus P's actual span export.

The selected warm image supplies the unchanged lookup/touch/window ABI;
ACL2 admits the current span export before the current native closure runs.
This is a seam test, not a rebuilt-image or W2L qualification.
"""
import os
from pathlib import Path
import subprocess
import shutil
import tempfile
import unittest

from tools import ledger

ROOT = Path(__file__).resolve().parents[1]
CORE = os.environ.get("FN_XC2_NATIVE_CORE")
SBCL = os.environ.get("FN_XC2_SBCL") or shutil.which("sbcl")


def span_export_forms():
    source = (ROOT / "books/extent-cache-span.lisp").read_text()
    lines = source.splitlines(keepends=True)
    forms = ledger.Reader(source).top_level()
    names = {"fn-xc-span-end", "fn-xc-span-end-bounds",
             "fn-xc-span-end-positive", "fn-xc-span-at"}
    chosen = []
    for index, (form, line) in enumerate(forms):
        if (isinstance(form, list) and len(form) > 1
                and str(form[1]).lower() in names):
            end = forms[index + 1][1] - 1 if index + 1 < len(forms) else len(lines)
            chosen.append("".join(lines[line - 1:end]))
    assert len(chosen) == len(names)
    return "\n".join(chosen)


@unittest.skipUnless(CORE and SBCL, "needs FN_XC2_NATIVE_CORE and matching SBCL")
class NativeExtentCacheSpanTests(unittest.TestCase):
    def test_warm_raw_extent_is_one_span_export_and_preserves_cold_miss(self):
        with tempfile.TemporaryDirectory(prefix="fn-xc2-raw-span-") as directory:
            forms = span_export_forms() + "\n:q\n"
            result = subprocess.run(
                [SBCL, "--tls-limit", "20480", "--dynamic-space-size", "2048",
                 "--control-stack-size", "64MB", "--core", CORE,
                 "--noinform", "--disable-debugger", "--load",
                 "tests/native_extent_cache_span_session.lisp"], cwd=ROOT,
                env=dict(os.environ, FN_XC2_RAW_EXTENT=str(Path(directory) / "extent")),
                input=forms, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                text=True, timeout=180)
            error_at = result.stdout.find("Unhandled")
            detail = result.stdout[error_at:error_at + 3500] if error_at >= 0 else result.stdout[-6000:]
            self.assertEqual(result.returncode, 0, detail)
            self.assertIn("native_extent_cache_span: PASS", result.stdout, detail)
            self.assertNotIn("ACL2 Error", result.stdout)
