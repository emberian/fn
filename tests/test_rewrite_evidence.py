"""Rewrite regressions, using local archives only."""
import argparse
import json
import subprocess
from unittest import mock
from tests.test_evidence_store import Sandbox, store
from tests.test_evidence_manifests import archive, RUN

REL = f'planning/evidence/manifests/{RUN}.json'


class ImmutableEvidence(Sandbox):
    def filed(self):
        archive.write_manifest(RUN, '{"status":"passed"}', '/local/run', self.root)
        store.put(self.root, [REL])
        (self.root / REL).unlink()

    def test_indexed_manifest_collision_without_local_copy(self):
        self.filed()
        self.assertEqual(archive.write_manifest(RUN, '{"status":"failed"}', root=self.root), 'conflict')
        self.assertFalse((self.root / REL).exists())

    def test_indexed_manifest_same_without_local_copy(self):
        self.filed()
        self.assertEqual(archive.write_manifest(RUN, '{"status":"passed"}', root=self.root), 'present')

    def test_put_refuses_different_bytes(self):
        self.filed()
        before = store.read_index(self.root).copy()
        self.write(REL, b'changed')
        with self.assertRaisesRegex(store.EvidenceConflict, REL):
            store.put(self.root, [REL])
        self.assertEqual(store.read_index(self.root), before)

    def test_index_refuses_different_bytes(self):
        self.filed()
        with self.assertRaisesRegex(store.EvidenceConflict, REL):
            store.add_to_index(self.root, {REL: ('b' * 64, 7)})

    def test_explicit_replacement_and_idempotence(self):
        self.filed()
        self.write(REL, b'changed')
        store.put(self.root, [REL], replace=True)
        self.assertEqual(store.put(self.root, [REL]), store.read_index(self.root))
        self.assertEqual(store.read_bytes(self.root, REL), b'changed')

    def test_provenance_upgrade_filed_but_changed_claim_refused(self):
        self.filed()
        subprocess.run(['git', 'init', '-q', str(self.root)], check=True)
        self.assertEqual(archive.write_manifest(RUN, '{"status":"passed"}', 'hbox:/run', self.root), 'written')
        self.assertEqual(archive.commit_paths(self.root, [REL]), 0)
        (self.root / REL).unlink()
        self.assertEqual(json.loads(store.read_text(self.root, REL))['archived_from'], 'hbox:/run')
        self.write(REL, b'{"status":"failed", "archived_from":"hbox:/run"}')
        self.assertNotEqual(archive.commit_paths(self.root, [REL]), 0)
        self.write(REL, b"malformed changed bytes")
        self.assertEqual(archive.commit_paths(self.root, [REL]), store.EXIT_REFUSED)
