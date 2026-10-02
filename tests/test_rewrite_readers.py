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
