"""The real checkpoint worker uses only its captured arena capability.

Check the complete host call graph and a mutation of the actual checkpoint
walk, so adding an indirect live-state lookup cannot restore the off-owner
publication path. This is lock discipline evidence, not a custody proof.
"""
import shutil
import tempfile
import unittest
from pathlib import Path

from tools import lock_discipline_check as ldc

ROOT = Path(__file__).resolve().parents[1]
CONTRACTS = ROOT / "tools" / "lock_discipline_contracts.json"


def publication_findings(root):
    _, model, checker = ldc.analyze_tree(root, ldc.load_contracts(CONTRACTS), reach={})
    roots = {name for name, info in model.infos.items()
             if info.thread_of and info.thread_of[0] == "fnn-owner-maybe-publish-quantum"}
    if not roots:
        raise AssertionError("the publication worker must be reachable")
    return [finding for finding in checker.run({"R1"}) if finding.function in roots]


class PublicationCaptureTests(unittest.TestCase):
    def test_worker_and_indirect_helpers_do_not_resolve_live_state(self):
        self.assertEqual(publication_findings(ROOT), [])

    def test_indirect_live_arena_lookup_is_detected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            shutil.copytree(ROOT / "host", root / "host")
            source = root / "host" / "native" / "io.lisp"
            text = source.read_text()
            before = '(let ((walk (list records nil nil)))'
            after = '(let ((walk (list records nil nil)) (arena (fnn-live-arena)))'
            self.assertEqual(text.count(before), 1)
            source.write_text(text.replace(before, after))
            self.assertTrue(any('fnn-checkpoint-walk:fnn-live-arena' in finding.key
                                for finding in publication_findings(root)))
