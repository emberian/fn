"""Fail closed before a composed BP fixture mutates either Store."""
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from tests.native_image_provenance import _digest, assert_same_native_source, source_execution_identity


class SourceExecutionProvenanceTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name).resolve()
        self.launcher = self.root / 'native'
        self.launcher.write_text('selected execution wrapper')
        self.inputs = {}
        for name in ('core', 'sbcl', 'raw', 'logical', 'loader'):
            path = self.root / name
            path.write_text(name)
            self.inputs[name] = str(path)
        self.manifest = self.root / 'execution.json'
        self.data = dict(schema='fn-native-source-runner-v1',
                         source_revision='b' * 40, world_revision='a' * 40,
                         execution_core=self.inputs['core'], sbcl=self.inputs['sbcl'],
                         raw_overlays=[self.inputs['raw']],
                         logical_files=[self.inputs['logical']],
                         source_loader=self.inputs['loader'],
                         execution_sha256={p: _digest(p) for p in self.inputs.values()})
        self.bind()

    def bind(self):
        self.manifest.write_text(json.dumps(self.data))
        self.binding = {str(self.launcher): dict(
            manifest=str(self.manifest), manifest_sha256=_digest(self.manifest),
            launcher_sha256=_digest(self.launcher))}

    def invoke(self, binding=None, images=None):
        with patch.dict(os.environ, FN_NATIVE_SOURCE_EXECUTIONS=json.dumps(
                self.binding if binding is None else binding)):
            return assert_same_native_source(self, *(images or [self.launcher, self.launcher]))

    def test_exact_loaded_execution_preserves_distinct_bootstrap_revision(self):
        self.assertEqual(self.invoke(), 'b' * 40)

    def test_single_workload_identity_preserves_exact_loaded_inputs(self):
        with patch.dict(os.environ, FN_NATIVE_SOURCE_EXECUTIONS=json.dumps(self.binding)):
            coordinate = source_execution_identity(self.launcher)
        self.assertEqual(coordinate['manifest']['world_revision'], 'a' * 40)
        self.assertEqual(coordinate['source_revision'], 'b' * 40)
        self.assertEqual(coordinate['manifest']['execution_sha256'], self.data['execution_sha256'])
        self.assertEqual(coordinate['binding']['manifest_sha256'], _digest(self.manifest))

    def test_single_workload_cannot_use_unbound_launcher(self):
        with patch.dict(os.environ, FN_NATIVE_SOURCE_EXECUTIONS='{}'):
            with self.assertRaises(KeyError):
                source_execution_identity(self.launcher)

    def test_changed_loaded_raw_source_refused(self):
        Path(self.inputs['raw']).write_text('changed semantic consumer')
        with self.assertRaisesRegex(AssertionError, 'loaded execution input changed'):
            self.invoke()

    def test_changed_manifest_refused_before_source_label_is_used(self):
        self.data['source_revision'] = 'c' * 40
        self.manifest.write_text(json.dumps(self.data))
        with self.assertRaisesRegex(AssertionError, 'manifest changed'):
            self.invoke()

    def test_unhashed_logical_input_refused(self):
        del self.data['execution_sha256'][self.inputs['logical']]
        self.bind()
        with self.assertRaisesRegex(AssertionError, 'loaded input not bound'):
            self.invoke()

    def test_changed_launcher_refused(self):
        self.launcher.write_text('another cached process')
        with self.assertRaisesRegex(AssertionError, 'source launcher changed'):
            self.invoke()

    def test_same_source_label_different_loaded_executions_refused(self):
        other = self.root / 'other'
        other.write_text('other execution wrapper')
        manifest2 = self.root / 'other.json'
        manifest2.write_text(json.dumps(dict(self.data, world_revision='c' * 40)))
        binding = dict(self.binding)
        binding[str(other)] = dict(manifest=str(manifest2),
                                  manifest_sha256=_digest(manifest2),
                                  launcher_sha256=_digest(other))
        with self.assertRaisesRegex(AssertionError, 'different executions'):
            self.invoke(binding, [self.launcher, other])

    def test_missing_explicit_producer_binding_refused(self):
        with self.assertRaisesRegex(AssertionError, 'source execution unavailable'):
            self.invoke({})

    def test_published_pair_route_remains_default(self):
        with patch.dict(os.environ), patch(
                'tests.native_image_provenance._published_source', return_value='d' * 40):
            os.environ.pop('FN_NATIVE_SOURCE_EXECUTIONS', None)
            self.assertEqual(assert_same_native_source(self, 'producer', 'receiver'), 'd' * 40)
