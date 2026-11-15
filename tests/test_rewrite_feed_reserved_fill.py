from pathlib import Path
import sys
import unittest
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'tools'))
import rewrite_feed_reserved_fill as r

class FeedRename(unittest.TestCase):
    def test_original_source_replay_and_idempotence(self):
        current = (ROOT/'books/upload-feed.lisp').read_text()
        original = r.BACK.sub('fill', current)
        self.assertEqual(r.transform(original), current)
        self.assertEqual(r.transform(current), current)
        self.assertEqual(original.count('fn2-gram-fill'), current.count('fn2-gram-fill'))

if __name__ == '__main__':
    unittest.main()
