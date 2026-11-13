"""Portable :FN pairs remain candidates while their author worktree exists."""
import copy
from pathlib import Path
import sys
import tempfile
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import certs


class PortableOriginTests(unittest.TestCase):
    def test_qualified_project_pair_from_live_foreign_tree(self):
        with tempfile.TemporaryDirectory() as origin:
            compatibility = {"project_directories": {":FN": "."}, "core_sha256": "record-core"}
            meta = {"origin_root": origin, "origin_kind": "worktree",
                    "key_version": certs.KEY_VERSION, "toolchain": compatibility,
                    "toolchain_identity": certs.stable_identity(compatibility)}
            self.assertTrue(certs.usable_origin(meta, "/different/tree"))
            for field in ("key_version", "toolchain", "toolchain_identity"):
                broken = copy.deepcopy(meta)
                del broken[field]
                self.assertFalse(certs.usable_origin(broken, "/different/tree"), field)
            for directories in ({}, {":FN": origin}, {":OTHER": "."}):
                broken = copy.deepcopy(meta)
                broken["toolchain"]["project_directories"] = directories
                broken["toolchain_identity"] = certs.stable_identity(broken["toolchain"])
                self.assertFalse(certs.usable_origin(broken, "/different/tree"))
            broken = copy.deepcopy(meta)
            broken["toolchain_identity"] = "wrong"
            self.assertFalse(certs.usable_origin(broken, "/different/tree"))
            self.assertTrue(certs.usable_origin(broken, origin))
            self.assertFalse(certs.usable_origin({**meta, "origin_root": None}, "/different/tree"))


if __name__ == "__main__":
    unittest.main()
