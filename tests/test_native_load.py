"""Thin unittest wrapper over tools/load/driver.py (LOAD-PROGRAM section 3).

    tools/hbox_native.sh --box hbox --reuse-image NAME/native-LABEL --images developer --mem 16G \
        --env FN_LOAD_CELLS=W2@10k,W13 tests.test_native_load

FN_LOAD_CELLS names the cells (comma separated); FN_LOAD_ARMS the W13 idle-GC arms (A,B);
FN_LOAD_REPEAT the repetitions; FN_LOAD_CORE an fn-core to run beside the image.  The image is
FN_NATIVE_HOST.  Each cell prints one FN_LOAD_RESULT line; the test fails only when a cell could
not run (status error): a bar that FAILs is a result, filed by `tools.load.result judge --file-items`.
"""
import json
import os
import tempfile
import unittest
from pathlib import Path

from tests.native_harness import executable, native_image

CELLS = os.environ.get("FN_LOAD_CELLS", "")
IMAGE = native_image("FN_NATIVE_HOST")


@unittest.skipUnless(CELLS, "FN_LOAD_CELLS names the cells to run")
@unittest.skipUnless(os.path.isdir("/proc/self"), "needs Linux /proc")
class LoadCellTests(unittest.TestCase):
    def test_cells_run(self):
        from tools.load import driver
        if not executable(IMAGE):
            self.skipTest("needs the image %s" % IMAGE)
        out = Path(os.environ.get("FN_LOAD_OUT") or tempfile.mkdtemp(prefix="fn-load-"))
        argv = ["run", "--cell", CELLS, "--image", str(IMAGE), "--out", str(out), "--label", os.environ.get("FN_LOAD_LABEL", "unittest"),
                "--box", os.environ.get("FN_LOAD_BOX", "hbox"), "--repeat", os.environ.get("FN_LOAD_REPEAT", "1")]
        if os.environ.get("FN_LOAD_ARMS"):
            argv += ["--arms", os.environ["FN_LOAD_ARMS"]]
        if os.environ.get("FN_LOAD_CORE"):
            argv += ["--fn-core", os.environ["FN_LOAD_CORE"]]
        self.assertEqual(driver.main(argv), 0, "a cell could not run; see %s/result.json" % out)
        res = json.loads((out / "result.json").read_text())
        self.assertTrue(res["cells"])


if __name__ == "__main__":
    unittest.main()
