import unittest
from pathlib import Path
import pool_credit_frames as frames
import lisp_rewrite

class Frames(unittest.TestCase):
    def test_actual_declarations_and_idempotence(self):
        source = Path('books/pool-credit.lisp').read_text()
        generated = frames.generate(source, Path('books/pool.lisp').read_text())
        self.assertEqual(len(lisp_rewrite.parse(generated).forms), 6)
        self.assertEqual(len(lisp_rewrite.parse(frames.generate_resizers(source, Path('books/pool.lisp').read_text())).forms), 9)
        self.assertEqual(frames.rewrite(source, Path('books/pool.lisp').read_text()), source)

    def test_undeclared_setter_refused(self):
        with self.assertRaises(AssertionError):
            frames.generate(Path('books/pool-credit.lisp').read_text(), '')

if __name__ == '__main__':
    unittest.main()
