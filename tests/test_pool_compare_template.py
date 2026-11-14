"""The generated consumer must use the current proof template verbatim."""
from pathlib import Path
import re
import unittest

BASE = Path(__file__).parents[1]


class PoolCompareTemplate(unittest.TestCase):
    def test_current_generated_proof_matches_template(self):
        generated = (BASE/'meta/Fn2/ACL2/PoolCompare.lean').read_text()
        template = (BASE/'meta/emit/pool_compare.lean.in').read_text()
        step = re.search(r'def step : State → Sum Val State\n  \| .*? => (.*)\n', generated).group(1)
        body = re.search(r'def bodyValue .*? := (.*)\n', generated).group(1)
        expected = template.replace('@STEP@', step).replace('@BODY@', body)
        start = 'namespace Fn2.ACL2.PoolCompare'
        end = 'end Fn2.ACL2.PoolCompare'
        self.assertEqual(generated.split(start, 1)[1].split(end, 1)[0],
                         expected.split(start, 1)[1].split(end, 1)[0])
        self.assertNotIn('Mathlib', generated)
        self.assertNotIn('split_ifs', generated)
        self.assertNotIn('import Fn2.ACL2.Fuel', generated)


if __name__ == '__main__':
    unittest.main()
