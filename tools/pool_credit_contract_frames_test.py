from pathlib import Path
import unittest
import pool_credit_contract_frames as frames
import lisp_rewrite

class ContractFrames(unittest.TestCase):
    def test_production_class_and_idempotence(self):
        source = Path('books/pool-credit-contracts.lisp').read_text()
        api = Path('books/pool-credit.lisp').read_text()
        declaration = Path('books/pool.lisp').read_text()
        self.assertEqual(len(lisp_rewrite.parse(frames.generate(api, declaration)).forms), 9)
        self.assertEqual(frames.rewrite(source, api, declaration), source)

    def test_undeclared_resizer_refused(self):
        with self.assertRaises(AssertionError):
            frames.generate(Path('books/pool-credit.lisp').read_text(), '')

if __name__ == '__main__':
    unittest.main()
