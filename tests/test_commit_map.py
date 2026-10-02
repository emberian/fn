"""Historical revision lookup is explicit, unique and object-checked."""
import subprocess
import tempfile
import unittest
from pathlib import Path
from tools import commit_map


class Resolve(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        subprocess.run(['git', 'init', '-q', str(self.root)], check=True)
        self.sha = subprocess.check_output(['git', '-C', str(self.root), 'hash-object',
                                            '-w', '--stdin'], input=b'fixture').decode().strip()
        (self.root / 'planning').mkdir()
        (self.root / 'planning/commit-map-20261002.txt').write_text(
            'old new\n' + 'a' * 40 + ' ' + self.sha + '\n' +
            'a' * 39 + 'b ' + self.sha + '\n' + 'b' * 40 + ' ' + self.sha + '\n')

    def test_self(self):
        self.assertEqual(commit_map.resolve(self.sha, self.root), self.sha)

    def test_mapped_prefix(self):
        self.assertEqual(commit_map.resolve('bbbbbb', self.root), self.sha)

    def test_ambiguous_refused(self):
        with self.assertRaisesRegex(commit_map.AmbiguousRevision, 'aaaaaa'):
            commit_map.resolve('aaaaaa', self.root)

    def test_old_abbreviation_colliding_with_a_current_object_is_refused(self):
        # An abbreviated OLD sha that also names a different object of the
        # rewritten repository must never resolve silently to either one.
        other = subprocess.check_output(['git', '-C', str(self.root), 'hash-object', '-w',
                                         '--stdin'], input=b'other').decode().strip()
        prefix = self.sha[:10]
        with open(self.root / 'planning/commit-map-20261002.txt', 'a') as f:
            f.write(prefix + '0' * 30 + ' ' + other + '\n')
        with self.assertRaisesRegex(commit_map.AmbiguousRevision, prefix):
            commit_map.resolve(prefix, self.root)
        # the full current sha is not a map key prefix: it still resolves to itself
        self.assertEqual(commit_map.resolve(self.sha, self.root), self.sha)

    def test_map_wins_for_an_old_abbreviation(self):
        self.assertEqual(commit_map.resolve('b' * 12, self.root), self.sha)

    def test_unmapped_refused(self):
        with self.assertRaisesRegex(commit_map.UnmappedRevision, 'cccccc'):
            commit_map.resolve('cccccc', self.root)


class RuntimeLookups(unittest.TestCase):
    def test_dependency_bytes_keep_the_original_hashes(self):
        import hashlib
        from tools.bpsec_source_observation import DEPENDENCIES
        from tools.bpsec_registered_source_observation import REVISION, OWNED_HASHES
        for rev, path, expected in DEPENDENCIES + [(REVISION, p, h) for p, h in OWNED_HASHES.items()]:
            with self.subTest(revision=rev, path=path):
                data = subprocess.check_output(['git', '-C', str(commit_map.ROOT), 'show',
                                                commit_map.resolve(rev) + ':' + path])
                self.assertEqual(hashlib.sha256(data).hexdigest(), expected)

    def test_pin_image_translates_only_lookup_and_keeps_source_identity(self):
        import hashlib
        import json
        from unittest import mock
        from tools import current_view
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            sidecar = root / current_view.SIDECAR
            sidecar.parent.mkdir(parents=True)
            sidecar.write_text(json.dumps({'images': {'old-image': {
                'source': 'original-identity', 'closure_manifest': 'historical-name'}},
                'capabilities': [{'host': {'file': 'host/example.lisp'}}]}))
            def git_run(command, **kwargs):
                self.assertEqual(command[-1], 'new-object:host/example.lisp')
                return subprocess.CompletedProcess(command, 0, stdout=b'exact source')
            with mock.patch.object(current_view.commit_map, 'resolve', return_value='new-object') as resolve, mock.patch('subprocess.run', side_effect=git_run):
                self.assertEqual(current_view.pin_image('old-image', root), 0)
                resolve.assert_called_once_with('original-identity', root)
            image = json.loads(sidecar.read_text())['images']['old-image']
            self.assertEqual(image['source'], 'original-identity')
            self.assertEqual(image['closure_manifest'], 'historical-name')
            self.assertEqual(image['host_sha256'], {'host/example.lisp': hashlib.sha256(b'exact source').hexdigest()})
