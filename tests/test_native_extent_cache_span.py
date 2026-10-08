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
    # Keep the book's executable definitions and admission lemmas unchanged.
    # The existing image already supplies the two included dependencies.
    source = (ROOT / "books/extent-cache-span.lisp").read_text()
    lines = source.splitlines(keepends=True)
    forms = ledger.Reader(source).top_level()
    chosen = []
    prefix = True
    installation = {"fn-xcw-copy", "fn-xcw-plan-octets", "fn-xcw-store",
                    "fn-xc-install-window-bytes", "fn-xc-init-windows"}
    for index, (form, line) in enumerate(forms):
        if (isinstance(form, list) and form
                and str(form[0]).lower() not in {"include-book", "in-package"}
                and (prefix or (len(form) > 1 and str(form[1]).lower() in installation))):
            end = forms[index + 1][1] - 1 if index + 1 < len(forms) else len(lines)
            chosen.append("".join(lines[line - 1:end]))
        if isinstance(form, list) and len(form) > 1 and str(form[1]).lower() == "fn-xc-span-at":
            prefix = False
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
            error_at = result.stdout.find("ACL2 Error")
            if error_at < 0:
                error_at = result.stdout.find("Unhandled")
            detail = result.stdout[max(0, error_at - 2500):error_at + 3500] if error_at >= 0 else result.stdout[-6000:]
            self.assertEqual(result.returncode, 0, detail)
            self.assertIn("native_extent_cache_span: PASS", result.stdout, detail)
            self.assertNotIn("ACL2 Error", result.stdout)
