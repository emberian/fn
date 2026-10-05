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
    def run_check(self, committed, rendered, write=False):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / "specs" / "wire-grammar.json"
            if committed is not None:
                path.parent.mkdir(parents=True)
                path.write_bytes(committed)
            with mock.patch.object(protocol_emit, "WIRE_FILE", path), \
                 mock.patch.object(protocol_emit, "ROOT", Path(d)), \
                 mock.patch.object(protocol_emit, "wire_octets", return_value=rendered):
                code = protocol_emit.wire(write)
            return code, (path.read_bytes() if path.exists() else None)

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
