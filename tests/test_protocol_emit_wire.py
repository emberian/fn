"""`protocol_emit.py --wire --check` is red when specs/wire-grammar.json is
not the bytes ACL2 renders now, and green only when it is.

ACL2 is not run here: `wire_octets' (the evaluation of books/wire-export.lisp
fn-wgx-file-hex) is replaced by a stub, so this pins the comparison itself --
the guard a stale committed file (lane/mini-contract 0fccd3de2: the books
changed, the file did not) must trip.
"""
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import protocol_emit  # noqa: E402


class WireCheck(unittest.TestCase):
    def run_check(self, committed, rendered, write=False, key="k1", stamp=None, d=None):
        with tempfile.TemporaryDirectory() as tmp:
            d = Path(d or tmp)
            path = d / "specs" / "wire-grammar.json"
            if committed is not None:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(committed)
            stamp_path = d / "build" / "cache" / "wire-emit.json"
            if stamp is not None:
                stamp_path.parent.mkdir(parents=True, exist_ok=True)
                stamp_path.write_text(stamp)
            evaluate = mock.Mock(return_value=rendered)
            with mock.patch.object(protocol_emit, "WIRE_FILE", path), \
                 mock.patch.object(protocol_emit, "WIRE_STAMP", stamp_path), \
                 mock.patch.object(protocol_emit, "ROOT", d), \
                 mock.patch.object(protocol_emit, "_wire_key", return_value=key), \
                 mock.patch.object(protocol_emit, "wire_octets", evaluate):
                code = protocol_emit.wire(write)
            self.evaluated = evaluate.called
            return code, (path.read_bytes() if path.exists() else None)

    def stamp_for(self, key, octets):
        import hashlib, json
        return json.dumps({"key": key, "sha256": hashlib.sha256(octets).hexdigest()})

    def test_unchanged_closure_skips_the_evaluation(self):
        code, _ = self.run_check(b'{"v":1}', b'{"v":2}', key="k1",
                                 stamp=self.stamp_for("k1", b'{"v":1}'))
        self.assertEqual((code, self.evaluated), (0, False))

    def test_changed_closure_evaluates(self):
        code, _ = self.run_check(b'{"v":1}', b'{"v":2}', key="k2",
                                 stamp=self.stamp_for("k1", b'{"v":1}'))
        self.assertEqual((code, self.evaluated), (1, True))

    def test_edited_file_evaluates(self):
        code, _ = self.run_check(b'{"v":9}', b'{"v":1}', key="k1",
                                 stamp=self.stamp_for("k1", b'{"v":1}'))
        self.assertEqual((code, self.evaluated), (1, True))

    def test_stale_file_is_red(self):
        code, _ = self.run_check(b'{"version":1,"families":[]}', b'{"version":1,"families":[1]}')
        self.assertEqual(code, 1)

    def test_missing_file_is_red(self):
        code, _ = self.run_check(None, b'{"version":1}')
        self.assertEqual(code, 1)

    def test_current_file_is_green(self):
        code, _ = self.run_check(b'{"version":1}', b'{"version":1}')
        self.assertEqual(code, 0)

    def test_write_writes_the_rendering(self):
        code, after = self.run_check(b'{"old":1}', b'{"new":1}', write=True)
        self.assertEqual((code, after), (0, b'{"new":1}'))

    def test_unreadable_rendering_is_refused(self):
        with self.assertRaises(ValueError):
            self.run_check(b"x", b"not json")


if __name__ == "__main__":
    unittest.main()
