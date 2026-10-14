"""Native control fixtures; subprocess/SSH outcomes are simulated locally."""
import contextlib
import io
import json
import os
from pathlib import Path
import subprocess
import unittest
from unittest import mock

from tools import box_table, dev_control, test_budget, train
from tests.test_train import TrainBase, sh


class DevControlTests(TrainBase):
    A = 'tests.test_native_a'
    B = 'tests.test_native_b'
    FAILED = 'tests.test_native_failed'
    SKIP = 'tests.test_native_skip'
    EMPTY = 'tests.test_native_empty'
    MISSING = 'tests.test_native_missing'
    RULE_ONLY = 'tests.test_native_rules'

    def setUp(self):
        super().setUp()
        self.expected = [self.A, self.B, self.FAILED, self.SKIP, self.EMPTY, self.MISSING, self.RULE_ONLY]
        for module in self.expected[:-1]:
            (self.work / (module.replace('.', '/') + '.py')).write_text('# fixture\n')
        (self.work / 'tests/test_other.py').write_text('# excluded\n')
        self.rules = (('fixture', ('host/native/',), (self.RULE_ONLY, self.A)),)
        (self.work / 'tools/train.py').write_text(
            f'SERVED_NATIVES = ({self.RULE_ONLY!r},)\n'
            f'IMAGE_RULES = (("fixture", ("host/native/",), SERVED_NATIVES + ({self.A!r},)),)\n')
        rows = [dict(kind='native', subject=self.A + '.T.test_retire', item='KR-X', owner='B', evidence='fixture'),
                dict(kind='native', subject=self.B + '.T.test_known', item='KR-X', owner='B', evidence='fixture'),
                dict(kind='native', subject=self.SKIP + '.T.test_skip', item='KR-X', owner='B', evidence='fixture')]
        (self.work / train.KNOWN_REDS).write_text(json.dumps({'rows': rows}) + '\n')
        self.sha = self.commit(self.work, 'native control fixture')
        self.label = 'devctl-' + self.sha[:12]
        self.record_path = self.work / 'build/hbox-native' / (self.label + '.run')
        self.record_path.parent.mkdir(parents=True)
        self.text = self.results()
        self.load = 'hbox      load  12.50 on  32 cores (0.39/core)  free mem 80 GiB\n'
        self.calls = []
        self.real_run = subprocess.run

    def record(self, **changes):
        fields = dict(box='hbox', dir='/box/native-run', source=self.sha, tree=self.sha)
        fields.update(changes)
        self.record_path.write_text(''.join(f'{key}={value}\n' for key, value in fields.items()))

    def results(self):
        records = [
            (self.A, 1, [[self.A + '.T.test_retire', 'ok'], [self.A + '.T.test_new', 'FAIL'],
                          [self.A + '.T.test_partial_skip', 'skip']],
             dict(executed=2, skips=[[self.A + '.T.test_partial_skip', 'partial fixture absent']])),
            (self.B, 1, [[self.B + '.T.test_known', 'ERROR']], dict(executed=1)),
            (self.SKIP, 4, [[self.SKIP + '.T.test_skip', 'skip']],
             dict(executed=0, skips=[[self.SKIP + '.T.test_skip', 'FN_FIXTURE missing']])),
            (self.EMPTY, 0, [], dict(executed=0)),
            (self.RULE_ONLY, 0, [[self.RULE_ONLY + '.T.test_ok', 'ok']], dict(executed=1)),
        ]
        lines = [f'RC {self.FAILED} 16']
        for module, rc, cases, fields in records:
            lines += [f'RC {module} {rc}', dev_control.RESULT_PREFIX + json.dumps(dict(module=module, cases=cases, **fields))]
        return '\n'.join(lines) + '\n'

    def fake_run(self, argv, **kwargs):
        self.calls.append(list(argv))
        if argv[:4] == ['timeout', '60', 'sh', 'tools/boxes.sh']:
            return subprocess.CompletedProcess(argv, 0, self.load, '')
        if argv[:4] == ['timeout', '600', 'sh', 'tools/hbox_native.sh']:
            # The real runner publishes the record before detached launch/readback.
            self.record()
            return subprocess.CompletedProcess(argv, 0, 'detached\n', '')
        if argv[:4] == ['timeout', '60', 'ssh', '-n']:
            self.assertEqual(argv[4], 'hbox')
            self.assertIn(train.image_read_script('/box/native-run'), argv[5])
            return subprocess.CompletedProcess(argv, 0, self.text, '')
        if argv[:1] != ['git']:
            raise AssertionError(f'unexpected subprocess: {argv}')
        return self.real_run(argv, **kwargs)

    def invoke(self, *args):
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err), \
                mock.patch.object(dev_control.subprocess, 'run', side_effect=self.fake_run):
            rc = dev_control.main(list(args), root=self.work)
        return rc, out.getvalue(), err.getvalue()

    def report(self):
        return json.loads((self.work / 'build/dev-control' / (self.label + '.json')).read_text())

    def test_modules_union_from_fixture_tree_minus_none(self):
        with mock.patch.object(train, 'IMAGE_RULES', self.rules):
            rc, out, err = self.invoke('modules')
        self.assertEqual(rc, 0, err)
        self.assertEqual(out.splitlines(), sorted(self.expected))
        self.assertEqual(dev_control.modules(self.work, self.sha), sorted(self.expected))
        self.assertNotIn('tests.test_other', out)

    def test_launch_explicit_sha_detaches_with_all_modules_and_label(self):
        rc, out, err = self.invoke('launch', '--sha', self.sha[:9])
        self.assertEqual(rc, 0, err)
        self.assertEqual(out.strip(), self.label)
        launch = next(argv for argv in self.calls if 'tools/hbox_native.sh' in argv)
        self.assertEqual(launch, ['timeout', '600', 'sh', 'tools/hbox_native.sh', '--box', 'hbox',
                                  '--label', self.label, '--allow-skips', '--detach',
                                  '--env', 'FN_INN_SRC=/tank/fn/inn/2.7.4', self.sha,
                                  *sorted(self.expected)])
        self.assertTrue(self.record_path.exists())

    def test_launch_uses_selected_box_fact(self):
        with mock.patch.object(box_table, 'native_test_env', return_value={
                'FN_INN_SRC': '/fixture/inn'}) as facts:
            rc, _, err = self.invoke('launch', '--sha', self.sha)
        self.assertEqual(rc, 0, err)
        facts.assert_called_once_with('hbox')
        launch = next(argv for argv in self.calls if 'tools/hbox_native.sh' in argv)
        self.assertEqual(launch[launch.index('--env') + 1], 'FN_INN_SRC=/fixture/inn')

    def test_fixed_box_without_inn_does_not_get_hbox_path(self):
        self.assertEqual(box_table.native_test_env('persvati'), {})

    def test_registered_subtest_parent_matches_both_readers(self):
        module = 'tests.test_native_foreign_format_open'
        class ForeignFormatOpenTest(unittest.TestCase):
            def test_a_store_of_another_format_is_refused_by_name(self):
                for args in (('operator', 'health'), ('operator', 'status')):
                    with self.subTest(args=args):
                        self.fail('foreign format refusal')
        ForeignFormatOpenTest.__module__ = module
        ForeignFormatOpenTest.__qualname__ = 'ForeignFormatOpenTest'
        suite = unittest.defaultTestLoader.loadTestsFromTestCase(ForeignFormatOpenTest)
        out = io.StringIO()
        with mock.patch.object(unittest.defaultTestLoader, 'loadTestsFromName', return_value=suite), \
                mock.patch.object(test_budget, 'store_verdict'), \
                contextlib.redirect_stdout(out), contextlib.redirect_stderr(io.StringIO()):
            rc = test_budget.run_one(module)
        self.assertEqual(rc, 1)
        text = f'RC {module} {rc}\n' + out.getvalue()
        results = train.parse_image_results(text)
        subject = module + '.ForeignFormatOpenTest.test_a_store_of_another_format_is_refused_by_name'
        self.assertEqual(results[module]['cases'], {subject: 'FAIL'})
        rows = json.loads((test_budget.ROOT / train.KNOWN_REDS).read_text())['rows']
        self.assertTrue(any(row['subject'] == subject for row in rows))
        verdict, detail = train.image_verdict({module: ['fixture']},
            dict(source=self.sha, modules=results), self.sha, rows)
        self.assertEqual((verdict, detail['known_reds']), (0, [subject]))
        classified = dev_control.classify([module], results, dev_control.result_details(text),
                                          rows, 'hbox', '/fixture')
        self.assertEqual(classified, dict(new=[], retire=[], not_run=[]))

    def test_launch_refuses_load_at_or_above_24(self):
        for load in (24, 24.01, 50):
            with self.subTest(load=load):
                self.load = f'hbox      load {load} on 32 cores\n'
                self.calls.clear()
                rc, _, err = self.invoke('launch', '--sha', self.sha)
                self.assertEqual(rc, 1)
                self.assertIn('not under 24', err)
                self.assertFalse(any('tools/hbox_native.sh' in argv for argv in self.calls))
                self.assertFalse(self.record_path.exists())

    def test_launch_refuses_missing_load_and_invalid_sha(self):
        self.load = 'hbox      unreachable\n'
        rc, _, err = self.invoke('launch', '--sha', self.sha)
        self.assertEqual(rc, 1)
        self.assertIn('no load reading', err)
        rc, _, _ = self.invoke('launch', '--sha', 'f' * 40)
        self.assertEqual(rc, 1)
        self.assertFalse(any('tools/hbox_native.sh' in argv for argv in self.calls))

    def test_launch_refuses_existing_record_before_any_box_call(self):
        self.record()
        rc, _, err = self.invoke('launch', '--sha', self.sha)
        self.assertEqual(rc, 1)
        self.assertIn('already recorded', err)
        self.assertFalse(any(argv[0] == 'timeout' for argv in self.calls))
        self.record_path.rename(self.record_path.with_name('devctl-another-label.run'))
        rc, _, err = self.invoke('launch', '--sha', self.sha)
        self.assertEqual(rc, 1)
        self.assertIn('already recorded', err)
        self.assertFalse(any(argv[0] == 'timeout' for argv in self.calls))

    def test_default_sha_fetch_uses_private_ref_without_tracking_updates(self):
        old = sh(self.work, 'git', '-C', str(self.work), 'rev-parse', 'origin/dev').stdout.strip()
        self.advance_dev({'src.txt': 'new dev\n'})
        current = self.origin_rev('dev')
        with mock.patch.object(dev_control, 'modules', return_value=[self.A]):
            rc, out, err = self.invoke('launch')
        self.assertEqual(rc, 0, err)
        self.assertEqual(out.strip(), 'devctl-' + current[:12])
        self.assertEqual(sh(self.work, 'git', '-C', str(self.work), 'rev-parse', 'origin/dev').stdout.strip(), old)
        fetch = next(argv for argv in self.calls if 'fetch' in argv)
        self.assertIn('--refmap=', fetch)
        self.assertIn('--no-write-fetch-head', fetch)
        self.assertTrue(fetch[-1].startswith('+refs/heads/dev:refs/dev-control/'))
        self.assertEqual(sh(self.work, 'git', '-C', str(self.work), 'for-each-ref', 'refs/dev-control/').stdout, '')

    def test_diff_classifies_new_retire_not_run_and_keeps_skip_reasons(self):
        self.record()
        rc, out, err = self.invoke('diff', self.label)
        self.assertEqual(rc, 1, err)
        report = self.report()
        self.assertEqual(report['sha'], self.sha)
        self.assertEqual({entry['subject'] for entry in report['new']},
                         {self.A + '.T.test_new', self.FAILED})
        self.assertEqual([entry['subject'] for entry in report['retire']], [self.A + '.T.test_retire'])
        not_run = {entry['subject']: entry for entry in report['not_run']}
        self.assertEqual(set(not_run), {self.MISSING, self.EMPTY, self.SKIP, self.FAILED,
                                       self.A + '.T.test_partial_skip'})
        self.assertIn('FN_FIXTURE missing', not_run[self.SKIP]['reason'])
        self.assertEqual(not_run[self.A + '.T.test_partial_skip']['reason'], 'partial fixture absent')
        self.assertEqual(not_run[self.EMPTY]['reason'], 'no test executed')
        self.assertEqual(not_run[self.MISSING]['reason'], 'missing module result')
        self.assertIn(f'RED {self.FAILED} hbox:/box/native-run/logs/test-{self.FAILED}.log', out)
        self.assertIn('RETIRE candidates: 1', out)
        self.assertIn('NOT RUN: 5', out)
        self.assertNotIn('RED ' + self.B + '.T.test_known', out)

    def test_diff_uses_baseline_and_module_list_at_run_sha(self):
        self.record()
        # Current working bytes try to hide the red; they are not the run baseline.
        path = self.work / train.KNOWN_REDS
        data = json.loads(path.read_text())
        data['rows'].append(dict(data['rows'][0], subject=self.A + '.T.test_new'))
        path.write_text(json.dumps(data))
        (self.work / 'tests/test_native_after_run.py').write_text('# later\n')
        self.commit(self.work, 'later baseline and test')
        rc, _, err = self.invoke('diff', self.label)
        self.assertEqual(rc, 1, err)
        report = self.report()
        self.assertEqual(report['sha'], self.sha)
        self.assertIn(self.A + '.T.test_new', [entry['subject'] for entry in report['new']])
        self.assertNotIn('tests.test_native_after_run', [entry['subject'] for entry in report['not_run']])

    def test_diff_exit_zero_only_when_new_is_empty_even_with_not_run(self):
        self.record()
        self.text = self.text.replace(f'RC {self.FAILED} 16', f'RC {self.FAILED} 0')
        self.text = self.text.replace('"FAIL"', '"ok"')
        self.text = self.text.replace(f'RC {self.A} 1', f'RC {self.A} 0')
        rc, _, err = self.invoke('diff', self.label)
        self.assertEqual(rc, 0, err)
        self.assertEqual(self.report()['new'], [])
        self.assertTrue(self.report()['not_run'])

    def test_diff_node_dead_module_error_is_new(self):
        self.record()
        self.text = f'RC {self.FAILED} 1\n' + dev_control.RESULT_PREFIX + json.dumps(
            dict(module=self.FAILED, cases=[], executed=0, load_error='node dead at start'))
        self.assertEqual(self.invoke('diff', self.label)[0], 1)
        report = self.report()
        self.assertEqual([entry['subject'] for entry in report['new']], [self.FAILED])
        self.assertEqual(next(entry for entry in report['not_run'] if entry['subject'] == self.FAILED)['reason'],
                         'node dead at start')

    def test_diff_rejects_identity_mismatch_and_bad_labels_without_ssh(self):
        (self.work / 'src.txt').write_text('image input changed\n')
        other = self.commit(self.work, 'different image tree')
        self.record(tree=other)
        rc, _, err = self.invoke('diff', self.label)
        self.assertEqual(rc, 1)
        self.assertIn('changes image input', err)
        self.assertFalse(any('ssh' in argv for argv in self.calls))
        self.assertFalse((self.work / 'build/dev-control').exists())
        self.assertEqual(self.invoke('diff', '../escape')[0], 1)

    def test_diff_accepts_train_style_neutral_image_reuse(self):
        (self.work / 'planning/note.txt').write_text('neutral\n')
        new = self.commit(self.work, 'planning only')
        self.record(tree=new)
        rc, _, err = self.invoke('diff', self.label)
        self.assertEqual(rc, 1, err)  # Reads correctly and still finds actual NEW reds.
        self.assertEqual(self.report()['sha'], new)
        self.assertEqual(self.report()['images_from'], self.sha)

    def test_diff_reader_failure_does_not_write_report(self):
        self.record()
        real_fake = self.fake_run
        def failure(argv, **kwargs):
            if 'ssh' in argv:
                return subprocess.CompletedProcess(argv, 255, '', 'fixture read refused')
            return real_fake(argv, **kwargs)
        with mock.patch.object(self, 'fake_run', side_effect=failure):
            rc, _, err = self.invoke('diff', self.label)
        self.assertEqual(rc, 1)
        self.assertIn('reading hbox:', err)
        self.assertFalse((self.work / 'build/dev-control').exists())

    def test_status_none_and_newest_report_with_age_sha_and_count(self):
        self.assertEqual(dev_control.status_line(self.work), 'dev control: none recorded')
        self.record()
        self.assertEqual(self.invoke('diff', self.label)[0], 1)
        report_dir = self.work / 'build/dev-control'
        old = report_dir / 'older.json'
        old.write_text(json.dumps(dict(sha='older', recorded_at=0, new=[])))
        os.utime(old, (1, 1))
        with mock.patch.object(dev_control.time, 'time', return_value=self.report()['recorded_at'] + 7200):
            line = dev_control.status_line(self.work)
        self.assertEqual(line, f'dev control: {self.sha} age 2.0 hours NEW 2')
        status = self.train('status')
        self.assertEqual(status.returncode, 0, status.stderr)
        lines = [line for line in status.stdout.splitlines() if line.startswith('dev control:')]
        self.assertEqual(len(lines), 1)
        self.assertIn(self.sha, lines[0])
        self.assertIn('NEW 2', lines[0])
