"""Read-only core closure selection controls; no ACL2 or Lean builds."""
import contextlib
import importlib.util
import io
from pathlib import Path
import tempfile
import unittest
from unittest import mock

SPEC = importlib.util.spec_from_file_location(
    'core_certificate', Path(__file__).parents[1] / 'meta/emit/emit_core_certificate.py')
c = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(c)


def obj(value):
    if isinstance(value, int):
        return f'(:INTEGER {value})'
    if isinstance(value, list):
        result = obj('NIL')
        for item in reversed(value):
            result = f'(:CONS {obj(item)} {result})'
        return result
    package = 'KEYWORD' if value.startswith(':') else 'ACL2'
    name = value.lstrip(':')
    return '(:SYMBOL (' + ' '.join(str(ord(x)) for x in package) + ') (' + ' '.join(str(ord(x)) for x in name) + '))'


BASE = c.ROOTS + ['FN2-CNS-ROWS', 'FN2-MACHINES-ROWS',
                  'FN2-MACHINE-SLOT', 'FN2-CONTROL-RECORD-STOP', 'FN2-CNS-SET-ROWS']


def packet(changed=None, attachment='NIL', refused=False):
    rows = []
    for name in BASE + ['UNUSED']:
        body = (changed.get(name, ['QUOTE', 0]) if isinstance(changed, dict) else
                changed if name == BASE[0] and changed is not None else ['QUOTE', 0])
        attached = attachment if name == BASE[0] else 'NIL'
        rows.append(f'(:FUNCTION {obj(name)} :FORMALS {obj([])} '
                    f':LOGICAL-BODY {obj(body)} :GUARD {obj("T")} :ATTACHMENT {obj(attached)})')
    return ('(:PACKET :REFUSED ' + ('(:MISSING)' if refused else '()') +
            ' :FUNCTIONS (' + ' '.join(rows) + ') :OPERATIONS ' + obj([[BASE[0], ':CALLEE', 'NIL']]) +
            ' :KIND ' + obj(['FN2-CNS', ':COLUMNS', [['ROWS']]]) + ')')


class CoreCertificateInspection(unittest.TestCase):
    def fixture(self, directory, **kwargs):
        source = Path(directory) / 'packet.sexp'
        source.write_text(packet(**kwargs))
        return source

    def test_inspection_and_cli_write_nothing(self):
        with tempfile.TemporaryDirectory() as directory:
            source = self.fixture(directory)
            before = {p: p.read_bytes() for p in Path(directory).rglob('*') if p.is_file()}
            with mock.patch.object(Path, 'write_text', side_effect=AssertionError('artifact write')), \
                    mock.patch.object(c, 'write_identity', side_effect=AssertionError('identity write')):
                _, selected, _, names, _ = c.inspect_core_certificate(source)
                output = io.StringIO()
                with contextlib.redirect_stdout(output):
                    c.cli(['--inspect', str(source)])
            self.assertEqual([f.name for f, _ in selected], BASE)
            self.assertEqual(names, set(BASE))
            self.assertIn('7 functions', output.getvalue())
            self.assertNotIn('UNUSED', output.getvalue())
            self.assertEqual(before, {p: p.read_bytes() for p in Path(directory).rglob('*') if p.is_file()})

    def test_existing_refusals(self):
        for kwargs, reason in [
                ({'attachment': 'ATTACHED'}, 'attached core callee'),
                ({'changed': [BASE[0]]}, 'recursive core callee'),
                ({'changed': {BASE[0]:[BASE[1]],BASE[1]:[BASE[0]]}}, 'mutually recursive core callees'),
                ({'changed': ['MISSING']}, 'missing core callee'),
                ({'refused': True}, 'unresolved export roots')]:
            with self.subTest(reason=reason), tempfile.TemporaryDirectory() as directory:
                source = self.fixture(directory, **kwargs)
                with self.assertRaisesRegex(ValueError, reason):
                    c.inspect_core_certificate(source)

    def test_default_emission_uses_inspected_selection(self):
        class StopBeforeArtifactWrite(Exception):
            pass
        with tempfile.TemporaryDirectory() as directory:
            source = self.fixture(directory)
            inspected = c.inspect_core_certificate(source)
            with mock.patch.object(c, 'inspect_core_certificate', return_value=inspected) as inspect, \
                    mock.patch.object(Path, 'write_text', side_effect=StopBeforeArtifactWrite) as write:
                with self.assertRaises(StopBeforeArtifactWrite):
                    c.cli([str(source)])
            inspect.assert_called_once_with(str(source))
            world = write.call_args.args[0]
            for name in BASE:
                self.assertIn(f'«{name}».dispatched', world)
            self.assertNotIn('UNUSED', world)


if __name__ == '__main__':
    unittest.main()
