"""Source controls only; these do not establish the new ACL2 frame theorems."""
from pathlib import Path
import subprocess
import sys
import unittest
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
from lisp_rewrite import match, parse, write

BASE = '31635689e152fa20aa3e9eb18ae456ebe2397b64'

def connect_frames(source, names):
    edits = []
    for node in match(None, parse(source), deep=False, head='in-theory'):
        form = source[node.start:node.end]
        for name in names:
            if form == f'(in-theory (disable {name}))':
                edits.append((node.start, node.start, f'(fn2-b3-word-frame {name})\n'))
    if len(edits) != len(names):
        raise ValueError('Each actual wrapper must have one boundary')
    return write(source, edits)

class WordFrames(unittest.TestCase):
    def test_original_runtime_guards_and_statements_unchanged(self):
        groups = {
            'block-integrity': ['fn2-block-hash-span', 'fn2-block-hash-into', 'fn2-block-read-commitment-children'],
            'cns-source-hash': ['fn2-cns-source-hash-begin', 'fn2-cns-source-hash-update', 'fn2-cns-source-hash-finish'],
        }
        for book, names in groups.items():
            path = f'books/{book}.lisp'
            original = subprocess.check_output(['git', 'show', f'{BASE}:{path}'], cwd=ROOT, text=True)
            expected = connect_frames(original, names)
            if book == 'block-integrity':
                expected = expected.replace('(include-book "blake3-row-frames")', '(include-book "blake3-word-frames")', 1)
            self.assertEqual((ROOT / path).read_text(), expected)
    def test_actual_abi_generator_controls(self):
        result = subprocess.run(['sbcl', '--noinform', '--script', 'tests/blake3-word-frame-controls.lsp'], cwd=ROOT,
                                capture_output=True, text=True, timeout=20)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('SOURCE CONTROLS PASS', result.stdout)
    def test_missing_connection_is_rejected(self):
        with self.assertRaises(ValueError):
            connect_frames('(in-theory (disable unrelated))', ['required'])

if __name__ == '__main__':
    unittest.main()
