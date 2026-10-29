"""Surface gate regressions; no native image or subprocess is needed."""
from contextlib import redirect_stdout
import copy
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

from fn2.tests import surface
from fn2.tests.surface import run_surface


class SurfaceRunnerTests(unittest.TestCase):
    def run_gate(self, tests, *, served=False, inventory=()):
        for index, test in enumerate(tests):
            test.id = lambda name=test.id(), index=index: f'{name}_{index}'
        entry = copy.deepcopy(surface.FAMILIES['nntp'])
        entry['cadence']['laptop']['forms'] = ['E']
        manifest = dict(surface.MANIFEST, serves={'fn1': ['nntp'], 'fn2': ['nntp'] if served else []})
        with tempfile.TemporaryDirectory() as directory, \
                mock.patch.object(run_surface, 'FAMILIES', {'nntp': entry}), \
                mock.patch.object(run_surface, 'MANIFEST', manifest), \
                mock.patch.object(run_surface, 'form_suite', return_value=unittest.TestSuite(tests)), \
                mock.patch.object(run_surface.run_natives, 'inventory', return_value=inventory), \
                mock.patch.dict(surface.RUN, clear=True), redirect_stdout(io.StringIO()) as stdout:
            code = run_surface.main(['--all', '--target', 'fn2', '--out', directory])
            report = json.loads((Path(directory) / 'surface.json').read_text())
            markdown = (Path(directory) / 'nntp.md').read_text()
            self.assertFalse((Path(directory) / 'surface.pid').exists())
        return code, report, stdout.getvalue(), markdown

    @staticmethod
    def case(call):
        return type('Fixture', (unittest.TestCase,), {'test_fixture': call})('test_fixture')

    def test_all_skip_is_not_run(self):
        case = self.case(lambda case: case.skipTest('layer D/E not yet serving'))
        code, report, stdout, markdown = self.run_gate([case])
        self.assertEqual(code, 3)
        self.assertEqual(report['families']['nntp']['status'], 'NOT RUN')
        self.assertEqual(report['totals']['not_run'], 1)
        self.assertIn('NOT RUN: 1 selected tests', stdout)
        self.assertIn('layer D/E not yet serving', stdout)
        self.assertIn('| E | NOT RUN |', markdown)

    def test_fail_beats_not_run(self):
        skip = self.case(lambda case: case.skipTest('missing driver'))
        fail = self.case(lambda case: case.fail('planted failure'))
        code, report, _, _ = self.run_gate([skip, fail])
        self.assertEqual(code, 1)
        self.assertEqual(report['totals']['fail'], 1)

    def test_served_family_ran_nothing_is_failure(self):
        skip = self.case(lambda case: case.skipTest('missing driver'))
        code, report, stdout, _ = self.run_gate([skip], served=True)
        self.assertEqual(code, 1)
        self.assertTrue(report['families']['nntp']['served_empty'])
        self.assertIn('served family ran nothing', stdout)
        code, _, _, _ = self.run_gate([], served=True)
        self.assertEqual(code, 1)

    def test_retired_and_intended_skips_only_exit_zero_but_not_green(self):
        def retired(case):
            case.evidence = {'native': {'module': 'fixture', 'tests': [run_surface.run_natives.row(
                'tests.test_native_fixture.Legacy.test_old', 'skip', reason='retired (inventory): obsolete')]}}
            case.skipTest('retired (inventory): obsolete')

        def intended(case):
            reason = 'FN_RUN_IMAGE_HEAP=1 runs the 128 MB bar\'s measurement'
            case.evidence = {'native': {'module': 'image_heap', 'tests': [run_surface.run_natives.row(
                'tests.test_native_image_heap.Measurement.test_opt_in', 'skip', reason=reason)]}}
            case.skipTest(reason)

        records = [{'module': 'fixture', 'judgment': {'in_image_tests': ['Legacy.test_old']}}]
        code, report, _, markdown = self.run_gate([self.case(retired), self.case(intended)], inventory=records)
        self.assertEqual(code, 0)
        self.assertEqual(report['totals']['not_run'], 0)
        self.assertEqual(report['totals']['skip'], 2)
        self.assertEqual(report['totals']['ok'], 0)
        self.assertIn('| E | NOT RUN |', markdown)
        code, _, _, _ = self.run_gate([self.case(retired)], served=True, inventory=records)
        self.assertEqual(code, 1)

    def test_retirement_prefix_alone_is_not_permission(self):
        code, _, _, _ = self.run_gate([self.case(lambda case: case.skipTest('retired (inventory): invented'))])
        self.assertEqual(code, 3)

    def test_setup_skip_is_not_run(self):
        class Fixture(unittest.TestCase):
            @classmethod
            def setUpClass(cls):
                raise unittest.SkipTest('fixture unavailable')

            def test_unreached(self):
                raise AssertionError('must not execute')

            def test_also_unreached(self):
                raise AssertionError('must not execute')

        code, report, stdout, _ = self.run_gate([
            Fixture('test_unreached'), Fixture('test_also_unreached')])
        self.assertEqual(code, 3)
        self.assertIn('fixture unavailable', stdout)
        self.assertEqual(report['totals']['tests'], 2)
        self.assertEqual(report['totals']['not_run'], 2)
        self.assertEqual(report['totals']['executed'], 0)
        self.assertEqual(len(report['families']['nntp']['forms']['E']['fixtures']), 1)

    def test_intended_setup_skip_is_permitted_without_stop_test(self):
        class Fixture(unittest.TestCase):
            __module__ = 'tests.test_native_image_heap'

            @classmethod
            def setUpClass(cls):
                raise unittest.SkipTest("FN_RUN_IMAGE_HEAP=1 runs the 128 MB bar's measurement")

            def test_unreached(self):
                raise AssertionError('must not execute')

        code, report, _, _ = self.run_gate([Fixture('test_unreached')])
        self.assertEqual(code, 0)
        self.assertEqual(report['totals']['not_run'], 0)
        self.assertEqual(report['totals']['skip'], 1)

    def test_subtest_failure_beats_skip(self):
        def call(case):
            with case.subTest(part='skip'):
                case.skipTest('missing subpart')
            with case.subTest(part='fail'):
                case.fail('planted subtest failure')
        code, report, _, _ = self.run_gate([self.case(call)])
        self.assertEqual(code, 1)
        self.assertEqual(report['totals']['fail'], 1)

    def test_subtest_skip_and_pass_counts_one_not_run_test(self):
        def call(case):
            with case.subTest(part='skip'):
                case.skipTest('missing subpart')
            with case.subTest(part='pass'):
                case.assertEqual(1, 1)
            with case.subTest(part='another skip'):
                case.skipTest('another missing subpart')
        code, report, _, _ = self.run_gate([self.case(call)])
        self.assertEqual(code, 3)
        self.assertEqual(report['totals']['tests'], 1)
        self.assertEqual(report['totals']['not_run'], 1)
        self.assertEqual(report['totals']['ok'], 0)
        self.assertEqual(report['totals']['not_run_reasons'], {
            'missing subpart': 1, 'another missing subpart': 1})

    def test_setup_error_blocks_two_selected_tests(self):
        class Fixture(unittest.TestCase):
            @classmethod
            def setUpClass(cls):
                raise ValueError('planted fixture error')

            def test_first(self):
                raise AssertionError('must not execute')

            def test_second(self):
                raise AssertionError('must not execute')

        code, report, _, _ = self.run_gate([Fixture('test_first'), Fixture('test_second')])
        self.assertEqual(code, 1)
        self.assertEqual(report['totals']['tests'], 2)
        self.assertEqual(report['totals']['fail'], 2)
        self.assertEqual(report['totals']['executed'], 0)

    def test_unset_hook_is_not_run(self):
        def call(case):
            surface.hook('nntp', 'FIXTURE', case)
        with mock.patch.dict('os.environ', {}, clear=True):
            code, _, stdout, _ = self.run_gate([self.case(call)])
        self.assertEqual(code, 3)
        self.assertIn('set FN2_SURFACE_FIXTURE_NNTP=module:callable', stdout)

    def test_pass_counts_bare_assert_without_testcase_calls(self):
        def call(case):
            assert 2 + 2 == 4
        code, report, _, markdown = self.run_gate([self.case(call)], served=True)
        self.assertEqual(code, 0)
        self.assertEqual(report['totals']['ok'], 1)
        self.assertEqual(report['totals']['testcase_calls'], 0)
        self.assertIn('TestCase-call count', markdown)

    def test_owed_forms_are_listed_but_not_generated(self):
        for family, entry in surface.FAMILIES.items():
            if family in ('nntp', 'consumer'):
                continue
            self.assertEqual(entry['forms']['S']['status'], 'owed')
            self.assertEqual(entry['forms']['S']['model'], entry['model'])
            self.assertEqual(surface.form_suite(family, 'S').countTestCases(), 0)
        with mock.patch.dict('os.environ', {'FN2_SURFACE_TARGET': 'fn2'}):
            report = run_surface.run_family('web', 'laptop')
        self.assertEqual(report['forms']['S']['status'], 'OWED')
        self.assertFalse(report['forms']['S']['selected'])
        self.assertEqual(report['owed_forms'], [{'form': 'S', 'model': surface.FAMILIES['web']['model']}])

    def test_consumer_s_loads_implemented_module_and_skips_unserved(self):
        with mock.patch.dict('os.environ', {'FN2_SURFACE_TARGET': 'fn2'}):
            result = run_surface.Result()
            surface.form_suite('consumer', 'S').run(result)
        self.assertEqual(len(result.skipped), 1)
        self.assertIn('test_live_state_machine', result.skipped[0][0].id())
        self.assertIn(surface.SKIP, result.skipped[0][1])
        self.assertEqual(surface.FAMILIES['consumer']['forms']['S']['status'], 'implemented')

    def test_package_discovery_preserves_ids_without_owed_forms(self):
        suite = unittest.defaultTestLoader.loadTestsFromName('fn2.tests.surface.nntp')
        ids = [test.id() for test in run_surface.run_natives.flatten(suite)]
        self.assertIn('fn2.tests.surface.nntp.test_model_nntp.TestSurface.test_live_state_machine', ids)
        self.assertIn('fn2.tests.surface.nntp.test_examples_nntp.TestSurface.test_native_article_quiet', ids)
        suite = unittest.defaultTestLoader.loadTestsFromName('fn2.tests.surface.web')
        self.assertFalse(any('.test_model_' in test.id() for test in run_surface.run_natives.flatten(suite)))

    def test_fn1_nntp_s_runs_live_machine_with_fake_target(self):
        from fn2.tests.surface.nntp import test_model_nntp
        from fn2.tests.model.nntp_model import NntpModel
        from fn2.tests.model.differential import fake_reply

        class FakeClient:
            commands = 0

            def __init__(self):
                self.conn = NntpModel({'surface.test': {}}, [], {}, {'posting': True}).connect(
                    tls=False, implicit_tls=False)
                self.greeting, _ = fake_reply(self.conn, b'', self.conn.greeting())
                self.rows = []

            def command(self, command):
                type(self).commands += 1
                line = command + b'\r\n'
                status, body = fake_reply(self.conn, line, self.conn.send(line))
                self.rows = (body or b'').splitlines(keepends=True)
                return status

            def line(self):
                return self.rows.pop(0)

            def close(self, quit=False):
                pass

        class FakeTarget:
            connections = 0

            def __init__(self, case):
                pass

            def connect(self):
                type(self).connections += 1
                return FakeClient()

        with mock.patch.dict('os.environ', {'FN2_SURFACE_TARGET': 'fn1'}), \
                mock.patch.dict(surface.RUN, {'examples': 2}), \
                mock.patch.object(test_model_nntp, 'Target', FakeTarget):
            result = run_surface.Result()
            surface.form_suite('nntp', 'S').run(result)
        self.assertTrue(result.wasSuccessful(), result.errors + result.failures)
        self.assertEqual(result.skipped, [])
        self.assertEqual(len(result.records), 1)
        self.assertEqual(result.records[0]['outcome'], 'ok')
        self.assertGreater(FakeTarget.connections, 0)
        self.assertGreater(FakeClient.commands, 0)


if __name__ == '__main__':
    unittest.main()
