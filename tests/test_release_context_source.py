import sys
from pathlib import Path
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import release_context_rewrite as rw
class Context(unittest.TestCase):
    def test_actual_readers_only(self):
        before = '(and (fn2-machine-rc-base id fn2-core) (fn2-machine-rc-commit other fn2-core) (fn2-machine-pool-slot id fn2-core))'
        self.assertEqual(rw.rewrite(before), '(and actual-rc-base (fn2-machine-rc-commit other fn2-core) actual-pool-slot)')
    def test_all_cached_bindings_derive_real_child(self):
        text = rw.bindings()
        for field in rw.READERS:
            self.assertIn(f'(actual-{field} (fn2-machine-{field} id fn2-core))', text)
if __name__ == '__main__':
    unittest.main()
