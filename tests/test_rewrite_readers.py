"""Archive-only corpora and arguments survive a clone without local evidence."""
import contextlib
import io
import json
import os
import subprocess
from pathlib import Path
from unittest import mock
from tests.test_evidence_store import Sandbox, store
from tests import mldsa65_interop as interop


class InteropCorpus(Sandbox):
    def test_tracked_and_indexed_corpus_and_counts(self):
        subprocess.run(['git', 'init', '-q', str(self.root)], check=True)
        self.write('tests/a.eml', b'FN-Authorship: tracked\n')
        subprocess.run(['git', '-C', str(self.root), 'add', 'tests'], check=True)
        archived = 'planning/evidence/b.eml'
        key = 'planning/evidence/key.raw'
        self.write(archived, b'FN-Authorship: archived\n')
        self.write(key, b'key')
        store.put(self.root, [archived, key])
        (self.root / archived).unlink()
        (self.root / key).unlink()
        keys, carriers, counts = interop.corpus(self.root)
        self.assertEqual(keys, [key])
        self.assertEqual(carriers, [archived, 'tests/a.eml'])
        self.assertEqual(counts, {'tracked': 1, 'indexed': 1, 'both': 0})
        self.assertEqual(interop.corpus_bytes(key, self.root), b'key')
        self.write(archived, b'altered')
        with self.assertRaises(store.EvidenceMismatch):
            interop.corpus(self.root)

    def test_unreadable_indexed_corpus_is_named_nonzero(self):
        rel = 'planning/evidence/missing.eml'
        store.add_to_index(self.root, {rel: ('a' * 64, 10)})
        subprocess.run(['git', 'init', '-q', str(self.root)], check=True)
        err = io.StringIO()
        with mock.patch.object(interop, 'ROOT', str(self.root)), contextlib.redirect_stderr(err):
            self.assertNotEqual(interop.main(['unused-library']), 0)
        self.assertIn('EvidenceUnavailable', err.getvalue())
        self.assertIn(rel, err.getvalue())


class CostInputs(Sandbox):
    def test_indexed_rankings_and_manifest_in_all_four_branches(self):
        import tau_cost
        import rule_cost
        rank = 'planning/evidence/ranking.json'
        manifest = 'planning/evidence/manifest.json'
        payload = {'books': [], 'runes': []}
        self.write(rank, json.dumps(payload).encode())
        self.write(manifest, b'{"book_results":{}}')
        store.put(self.root, [rank, manifest])
        (self.root / rank).unlink()
        (self.root / manifest).unlink()
        with mock.patch.object(tau_cost, 'ROOT', self.root), mock.patch.object(rule_cost, 'ROOT', self.root), mock.patch.object(tau_cost, 'apply', return_value=[]) as apply, mock.patch.object(tau_cost, 'repair', return_value=[]) as repair, mock.patch.object(tau_cost, 'rank', return_value={}):
            self.assertEqual(tau_cost.main(['apply', str(self.root / rank)]), 0)
            apply.assert_called_once_with(payload, 1.0, 0.2)
            self.assertEqual(tau_cost.main(['repair', str(self.root / rank), 'unused.log']), 0)
            repair.assert_called_once_with({}, payload)
            self.assertEqual(rule_cost.main(['withdraw', str(self.root / rank), '--dry-run', '--enable-in', 'failed', '--manifest', str(self.root / manifest)]), 0)
            self.write('local.json', json.dumps(payload).encode())
            self.assertEqual(rule_cost.main(['withdraw', str(self.root / 'local.json'), '--dry-run']), 0)
            self.write(rank, b'bad shadow')
            self.assertNotEqual(tau_cost.main(['apply', str(self.root / rank)]), 0)


class PowerLossRecords(Sandbox):
    def test_indexed_path_spellings_and_shadow_are_verified(self):
        from tools.resilience.adapters import power_loss
        rel = 'planning/evidence/cuts.jsonl'
        self.write(rel, b'{"cut":1}\n')
        store.put(self.root, [rel])
        (self.root / rel).unlink()
        cwd = Path.cwd()
        with mock.patch.object(power_loss, 'ROOT', self.root), mock.patch.object(power_loss, 'EVIDENCE', self.root / rel):
            try:
                os.chdir(self.root)
                for path in (rel, './' + rel, 'planning/../' + rel, self.root / rel):
                    self.assertEqual(power_loss.records(path), [{'cut': 1}])
                self.write(rel, b'{"cut":999}\n')
                for path in (rel, './' + rel, 'planning/../' + rel, self.root / rel):
                    with self.assertRaises(store.EvidenceMismatch):
                        power_loss.records(path)
                self.write('ordinary.jsonl', b'{"cut":2}\n')
                self.assertEqual(power_loss.records('ordinary.jsonl'), [{'cut': 2}])
            finally:
                os.chdir(cwd)
