"""Known-red writer fixtures; no production registers or remote commands."""
import contextlib
import io
import json
from pathlib import Path
from unittest import mock

from tools import known_reds, train
from tests.test_train import TrainBase, sh


class KnownRedsTests(TrainBase):
    SUBJECT = 'tests.test_native_fixture.NativeTests.test_red'

    def setUp(self):
        super().setUp()
        self.rows_path = self.work / train.KNOWN_REDS
        self.amendments_path = self.work / train.KNOWN_RED_AMENDMENTS
        self.item_path = self.work / 'planning/repair/items/KR-X.json'
        self.item_path.parent.mkdir(parents=True)
        self.item_path.write_text('{"id": "KR-X", "state": "open"}\n')
        self.original = dict(kind='check', subject='check-fast:lock_discipline_check',
                             item='KR-X', owner='builder-B', evidence='original état')
        self.rows_path.write_text(self.render({'note': 'keep this état', 'rows': [self.original]}))
        self.amendments_path.write_text(self.render({'note': 'keep this too', 'amendments': []}))
        self.commit(self.work, 'fixture baseline')
        sh(self.work, 'git', '-C', str(self.work), 'update-ref', 'refs/remotes/origin/dev', self.head())
        self.sha = self.head()

    @staticmethod
    def render(data):
        return json.dumps(data, indent=1, ensure_ascii=False) + '\n'

    def invoke(self, *args):
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            rc = known_reds.main(list(args), root=self.work)
        return rc, out.getvalue(), err.getvalue()

    def add_args(self, **changes):
        fields = dict(kind='native', subject=self.SUBJECT, item='KR-X', owner='builder-B',
                      dev_sha=self.sha[:9], evidence='fixture évidence', ruling='seat ruling')
        fields.update(changes)
        return ['add', *['--' + key.replace('_', '-') + '=' + value for key, value in fields.items()]]

    def add(self, **changes):
        return self.invoke(*self.add_args(**changes))

    def snapshot(self):
        return self.rows_path.read_bytes(), self.amendments_path.read_bytes()

    def refuse_add(self, **changes):
        before = self.snapshot()
        rc, _, err = self.add(**changes)
        self.assertEqual(rc, 1, err)
        self.assertTrue(err)
        self.assertEqual(self.snapshot(), before)
        return err

    def test_add_native_preserves_bytes_and_writes_once_each(self):
        before_rows, before_amendments = self.snapshot()
        original_write = Path.write_bytes
        with mock.patch.object(Path, 'write_bytes', autospec=True,
                               side_effect=original_write) as writer:
            rc, _, err = self.add()
        self.assertEqual(rc, 0, err)
        self.assertEqual([call.args[0] for call in writer.call_args_list],
                         [self.rows_path, self.amendments_path])
        rows_text, amendment_text = [blob.decode() for blob in self.snapshot()]
        rows = train.parse_known_reds(rows_text)
        records = train.parse_amendments(amendment_text)
        self.assertEqual(len(rows), 2)
        self.assertEqual(len(records), 1)
        self.assertEqual(rows[0], self.original)
        for field in ('kind', 'subject', 'item', 'owner'):
            self.assertEqual(rows[-1][field], records[-1][field])
        self.assertEqual(records[-1]['dev_sha'], self.sha[:9])
        self.assertEqual(records[-1]['ruling'], 'seat ruling')
        self.assertEqual(rows_text, self.render(json.loads(rows_text)))
        self.assertEqual(amendment_text, self.render(json.loads(amendment_text)))
        # Every byte preceding the insertion, including the old last row, stays.
        insertion = before_rows.rfind(b'\n ]')
        self.assertEqual(self.rows_path.read_bytes()[:insertion], before_rows[:insertion])
        self.assertIn(before_amendments.split(b'[]')[0], self.amendments_path.read_bytes())
        self.assertEqual(self.invoke('check')[0], 0)

    def test_add_check_and_committed_train_baseline_gate(self):
        rc, _, err = self.add(kind='check', subject='check:fixture')
        self.assertEqual(rc, 0, err)
        self.commit(self.work, 'fixture admission')
        with contextlib.redirect_stdout(io.StringIO()):
            rc, result = train._baseline_gate(train.Train(self.work))
        self.assertEqual(rc, 0, result)
        self.assertEqual(result['admitted'], [['check', 'check:fixture']])
        self.assertFalse(result['mismatched_amendments'])

    def test_add_to_empty_rows_uses_current_format(self):
        self.rows_path.write_text(self.render({'note': 'empty', 'rows': []}))
        rc, _, err = self.add()
        self.assertEqual(rc, 0, err)
        text = self.rows_path.read_text()
        self.assertEqual(text, self.render(json.loads(text)))

    def test_refuses_missing_item(self):
        self.assertIn('repair item', self.refuse_add(item='MISSING'))

    def test_refuses_every_closed_item_state(self):
        for state in sorted(train.CLOSED_ITEM_STATES):
            with self.subTest(state=state):
                self.item_path.write_text(json.dumps({'state': state}))
                self.assertIn('closed', self.refuse_add())

    def test_refuses_malformed_item(self):
        self.item_path.write_text('not JSON')
        self.refuse_add()

    def test_refuses_item_path_escape(self):
        self.refuse_add(item='../KR-X')

    def test_refuses_duplicate_key(self):
        self.assertEqual(self.add()[0], 0)
        self.assertIn('already exists', self.refuse_add())

    def test_refuses_invalid_native_subjects(self):
        for subject in ('tests.test_native_fixture', 'tests.test_native_fixture.NativeTests',
                        'tests.test_fixture.NativeTests.test_red', 'other.test_native_fixture.T.test_x',
                        'tests.test_native_fixture.T.test_x.extra'):
            with self.subTest(subject=subject):
                self.assertIn('native subject', self.refuse_add(subject=subject))

    def test_add_accepts_a_module_that_failed_to_import(self):
        # unittest records an import failure as one case named after the module.
        (self.work / 'tests').mkdir(exist_ok=True)
        (self.work / 'tests/test_fn_fixture_owner.py').write_text('import missing_name\n')
        subject = 'unittest.loader._FailedTest.test_fn_fixture_owner'
        rc, out, err = self.add(subject=subject)
        self.assertEqual(rc, 0, err)
        rows = train.parse_known_reds(self.rows_path.read_text())
        self.assertEqual(rows[-1]['subject'], subject)
        self.assertEqual(known_reds.native_module(self.work, subject), 'tests.test_fn_fixture_owner')

    def test_refuses_a_failed_import_subject_without_its_module(self):
        for subject in ('unittest.loader._FailedTest.test_fn_absent_module',
                        'unittest.loader._FailedTest.not_a_test_module',
                        'unittest.loader._FailedTest.test_x.extra',
                        'unittest.loader._FailedTest.'):
            with self.subTest(subject=subject):
                self.assertIn('native subject', self.refuse_add(subject=subject))

    def test_add_accepts_an_errored_fixture(self):
        (self.work / 'tests').mkdir(exist_ok=True)
        (self.work / 'tests/test_native_fixture_set.py').write_text('')
        for subject in ('setUpClass (tests.test_native_fixture_set.ReleaseTests)',
                        'tearDownClass (tests.test_native_fixture_set.ReleaseTests)',
                        'setUpModule (tests.test_native_fixture_set)'):
            with self.subTest(subject=subject):
                self.assertEqual(known_reds.native_module(self.work, subject),
                                 'tests.test_native_fixture_set')
        rc, _, err = self.add(subject='setUpClass (tests.test_native_fixture_set.ReleaseTests)')
        self.assertEqual(rc, 0, err)

    def test_refuses_an_errored_fixture_without_its_module_or_shape(self):
        for subject in ('setUpClass (tests.test_native_absent.ReleaseTests)',
                        'setUpClass tests.test_native_fixture_set.ReleaseTests',
                        'setUpClass (tests.test_native_fixture_set)',
                        'setUpModule (tests.test_native_fixture_set.ReleaseTests)'):
            with self.subTest(subject=subject):
                self.assertIn('native subject', self.refuse_add(subject=subject))

    def test_refuses_noncommit_shas(self):
        blob = sh(self.work, 'git', '-C', str(self.work), 'rev-parse', 'HEAD:src.txt').stdout.strip()
        sh(self.work, 'git', '-C', str(self.work), 'tag', '-a', 'fixture-tag', '-m', 'fixture tag')
        tag = sh(self.work, 'git', '-C', str(self.work), 'rev-parse', 'refs/tags/fixture-tag').stdout.strip()
        for sha in ('f' * 40, blob, tag, 'HEAD', '--help', 'not-a-sha'):
            with self.subTest(sha=sha):
                self.assertIn('commit', self.refuse_add(dev_sha=sha))

    def test_refuses_empty_required_fields_before_writing(self):
        for field in ('owner', 'evidence', 'ruling'):
            with self.subTest(field=field):
                self.refuse_add(**{field: ''})

    def test_transfer_changes_only_owner_and_appends_one_record(self):
        self.assertEqual(self.add()[0], 0)
        before_rows, before_amendments = self.snapshot()
        records = train.parse_amendments(before_amendments.decode())
        rc, _, err = self.invoke('transfer', '--subject', self.SUBJECT, '--owner', 'builder-é',
                                 '--ruling', 'ownership ruling')
        self.assertEqual(rc, 0, err)
        # The original baseline owner's bytes also occur; replace just the final row.
        at = before_rows.rfind(b'"owner": "builder-B"')
        expected_rows = before_rows[:at] + before_rows[at:].replace(
            b'"owner": "builder-B"', '"owner": "builder-é"'.encode(), 1)
        self.assertEqual(self.rows_path.read_bytes(), expected_rows)
        after = train.parse_amendments(self.amendments_path.read_text())
        self.assertEqual(after[:-1], records)
        self.assertEqual(after[-1], dict(records[-1], owner='builder-é', ruling='ownership ruling',
                                        transfer_from='builder-B'))
        insertion = before_amendments.rfind(b'\n ]')
        self.assertEqual(self.amendments_path.read_bytes()[:insertion], before_amendments[:insertion])
        self.assertEqual(self.invoke('check')[0], 0)
        self.commit(self.work, 'fixture transfer')
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(train._baseline_gate(train.Train(self.work))[0], 0)

    def target_item(self, state='open', owner='builder-B'):
        path = self.item_path.with_name('KR-TARGET.json')
        path.write_text(json.dumps({'state': state, 'owner': owner}) + '\n')
        return path

    def retired_admission(self):
        self.assertEqual(self.add()[0], 0)
        self.commit(self.work, 'fixture admission')
        self.item_path.write_text('{"state": "landed"}\n')
        self.assertEqual(self.invoke('retire', '--item', 'KR-X')[0], 0)
        self.commit(self.work, 'fixture retirement')
        sh(self.work, 'git', '-C', str(self.work), 'update-ref', 'refs/remotes/origin/dev', self.head())

    def readmit(self, **changes):
        fields = dict(item='KR-TARGET', owner='builder-M', dev_sha=self.head()[:9],
                      evidence='recurrence log', ruling='recurrence ruling')
        fields.update(changes)
        args = self.add_args(**fields)
        args[0] = 'readmit'
        return self.invoke(*args)

    def test_admit_retire_readmit_live_and_retire_again(self):
        self.retired_admission()
        self.target_item(owner='builder-M')
        before = self.snapshot()
        previous = train.parse_amendments(before[1].decode())
        measured = self.head()[:9]
        rc, out, err = self.readmit()
        self.assertEqual(rc, 0, err)
        self.assertEqual(out, f'readmit: native {self.SUBJECT}\n')
        rows = train.parse_known_reds(self.rows_path.read_text())
        records = train.parse_amendments(self.amendments_path.read_text())
        self.assertEqual(rows, [dict(kind='native', subject=self.SUBJECT, item='KR-TARGET',
                                    owner='builder-M', evidence='recurrence log')])
        self.assertEqual(records, [*previous, dict(kind='native', subject=self.SUBJECT,
                         item='KR-TARGET', owner='builder-M', dev_sha=measured,
                         evidence='recurrence log', ruling='recurrence ruling', readmit_from='KR-X')])
        self.assertNotEqual(records[-1]['dev_sha'], records[0]['dev_sha'])
        self.assertEqual(self.invoke('check')[0], 0)
        self.commit(self.work, 'fixture re-admission')
        self.assertEqual(train.known_reds_at(train.Train(self.work), 'HEAD'), rows)
        with contextlib.redirect_stdout(io.StringIO()):
            rc, result = train._baseline_gate(train.Train(self.work))
        self.assertEqual(rc, 0, result)
        self.assertEqual(result['admitted'], [['native', self.SUBJECT]])
        sh(self.work, 'git', '-C', str(self.work), 'update-ref', 'refs/remotes/origin/dev', self.head())
        self.target_item(state='landed', owner='builder-M')
        before = self.amendments_path.read_bytes()
        self.assertEqual(self.invoke('retire', '--item', 'KR-TARGET')[0], 0)
        self.assertEqual(self.amendments_path.read_bytes(), before)
        self.assertEqual(self.invoke('check')[0], 0)
        self.commit(self.work, 'fixture second retirement')
        with contextlib.redirect_stdout(io.StringIO()):
            rc, result = train._baseline_gate(train.Train(self.work))
        self.assertEqual(rc, 0, result)
        self.assertEqual(result['rows'], 0)
        self.assertEqual(result['gone'], [['native', self.SUBJECT]])

    def test_readmit_refuses_live_row_or_no_chain_without_writes(self):
        self.target_item(owner='builder-M')
        before = self.snapshot()
        self.assertIn('earlier amendment', self.readmit()[2])
        self.assertEqual(self.snapshot(), before)
        self.assertEqual(self.add()[0], 0)
        before = self.snapshot()
        rc, _, err = self.readmit()
        self.assertEqual(rc, 1, err)
        self.assertIn('already exists', err)
        self.assertEqual(self.snapshot(), before)

    def test_readmit_refusals_leave_register_bytes_unchanged(self):
        self.retired_admission()
        for state, owner, item, message in [
                *[(state, 'builder-M', 'KR-TARGET', 'closed')
                  for state in sorted(train.CLOSED_ITEM_STATES)],
                ('unknown', 'builder-M', 'KR-TARGET', 'not open'),
                ('open', 'builder-B', 'KR-TARGET', 'owner'),
                ('open', 'builder-M', 'MISSING', 'repair item'),
                ('open', 'builder-M', 'KR-X', 'retiring item')]:
            with self.subTest(state=state, owner=owner, item=item):
                self.target_item(state=state, owner=owner)
                before = self.snapshot()
                rc, out, err = self.readmit(item=item)
                self.assertEqual(rc, 1, err)
                self.assertEqual(out, '')
                self.assertIn(message, err)
                self.assertEqual(self.snapshot(), before)
        self.assertIn('use readmit', self.refuse_add(item='KR-TARGET'))
        self.item_path.write_text('{"state": "open"}')
        before = self.snapshot()
        self.assertEqual(self.readmit()[0], 1)
        self.assertEqual(self.snapshot(), before)

    def test_readmit_refile_and_check_whole_chain(self):
        self.retired_admission()
        target = self.target_item(owner='builder-M')
        self.assertEqual(self.readmit()[0], 0)
        target.write_text('{"state": "open", "owner": "builder-B"}')
        self.assertEqual(self.invoke('check')[0], 1)
        self.target_item(owner='builder-M')
        self.assertEqual(self.invoke('transfer', '--subject', self.SUBJECT,
                         '--owner', 'builder-B', '--ruling', 'owner changed')[0], 1)
        next_item = self.item_path.with_name('KR-NEXT.json')
        next_item.write_text('{"state": "open", "owner": "builder-M"}')
        self.assertEqual(self.refile(item='KR-NEXT')[0], 0)
        records = train.parse_amendments(self.amendments_path.read_text())
        self.assertNotIn('readmit_from', records[-1])
        self.assertEqual(self.invoke('check')[0], 0)
        next_item.write_text('{"state": "closed", "owner": "builder-M"}')
        self.assertEqual(self.invoke('retire', '--item', 'KR-NEXT')[0], 0)
        self.assertEqual(self.invoke('check')[0], 0)
        self.target_item(owner='builder-M')
        self.assertEqual(self.readmit()[0], 0)
        self.assertEqual(self.invoke('check')[0], 0)
        # The earliest readmit's retirement link must still be checked, even
        # after another recurrence supersedes it as the latest record.
        self.item_path.write_text('{"state": "open"}')
        before = self.snapshot()
        rc, _, err = self.invoke('check')
        self.assertEqual(rc, 1)
        self.assertIn('source repair item', err)
        self.assertEqual(self.snapshot(), before)

    def refile(self, subject=None, item='KR-TARGET'):
        return self.invoke('refile', '--subject', subject or self.SUBJECT,
                           '--item', item, '--ruling', 're-file ruling')

    def test_refile_changes_only_item_bytes_and_appends_once_each(self):
        self.assertEqual(self.add()[0], 0)
        self.target_item()
        # Preserve noncanonical whitespace, CRLF and UTF-8 in both files.
        for path in (self.rows_path, self.amendments_path):
            text = path.read_text().replace('"note": ', '"note" :  ')
            path.write_bytes(text.replace('\n', '\r\n').encode())
        before_rows, before_amendments = self.snapshot()
        records = train.parse_amendments(before_amendments.decode())
        original_write = Path.write_bytes
        with mock.patch.object(Path, 'write_bytes', autospec=True,
                               side_effect=original_write) as writer:
            rc, out, err = self.refile()
        self.assertEqual(rc, 0, err)
        self.assertEqual(out, f'refile: native {self.SUBJECT} KR-X -> KR-TARGET\n')
        self.assertEqual([call.args[0] for call in writer.call_args_list],
                         [self.rows_path, self.amendments_path])
        at = before_rows.rfind(b'"item": "KR-X"')
        self.assertEqual(self.rows_path.read_bytes(), before_rows[:at] +
                         before_rows[at:].replace(b'"item": "KR-X"', b'"item": "KR-TARGET"', 1))
        after = train.parse_amendments(self.amendments_path.read_bytes().decode())
        self.assertEqual(after, [*records, dict(records[-1], item='KR-TARGET',
                                              item_from='KR-X', ruling='re-file ruling')])
        _, _, entries = known_reds.array_entries(before_amendments.decode(), 'amendments')
        offset = len(before_amendments.decode()[:entries[-1][2]].encode())
        self.assertEqual(self.amendments_path.read_bytes()[:offset], before_amendments[:offset])
        self.assertTrue(self.amendments_path.read_bytes().endswith(before_amendments[offset:]))
        self.assertEqual(self.invoke('check')[0], 0)

    def test_refile_refusals_leave_both_files_byte_identical(self):
        self.assertEqual(self.add()[0], 0)
        cases = [(state, 'builder-B', self.SUBJECT, 'KR-TARGET', 'closed')
                 for state in sorted(train.CLOSED_ITEM_STATES)]
        cases += [('open', 'builder-M', self.SUBJECT, 'KR-TARGET', 'owner'),
                  ('open', 'builder-B', self.SUBJECT, 'KR-X', 'differ'),
                  ('open', 'builder-B', 'missing', 'KR-TARGET', 'exactly one row'),
                  ('open', 'builder-B', self.SUBJECT, 'MISSING', 'repair item')]
        for state, owner, subject, item, message in cases:
            with self.subTest(state=state, owner=owner, subject=subject, item=item):
                self.target_item(state, owner)
                before = self.snapshot()
                rc, out, err = self.refile(subject, item)
                self.assertEqual(rc, 1, err)
                self.assertEqual(out, '')
                self.assertIn(message, err)
                self.assertEqual(self.snapshot(), before)

    def test_refile_refuses_ambiguous_subject_without_writes(self):
        self.assertEqual(self.add()[0], 0)
        self.assertEqual(self.add(kind='check')[0], 0)
        self.target_item()
        before = self.snapshot()
        rc, _, err = self.refile()
        self.assertEqual(rc, 1)
        self.assertIn('exactly one row', err)
        self.assertEqual(self.snapshot(), before)

    def test_check_refuses_refile_target_owner_mismatch(self):
        self.assertEqual(self.add()[0], 0)
        self.target_item()
        self.assertEqual(self.refile()[0], 0)
        self.target_item(owner='builder-M')
        before = self.snapshot()
        rc, _, err = self.invoke('check')
        self.assertEqual(rc, 1)
        self.assertIn('owner', err)
        self.assertEqual(self.snapshot(), before)

    def test_transfer_after_refile_cannot_disagree_with_target_owner(self):
        self.assertEqual(self.add()[0], 0)
        self.target_item()
        self.assertEqual(self.refile()[0], 0)
        before = self.snapshot()
        rc, _, err = self.invoke('transfer', '--subject', self.SUBJECT,
                                 '--owner', 'builder-M', '--ruling', 'transfer ruling')
        self.assertEqual(rc, 1)
        self.assertIn('owner', err)
        self.assertEqual(self.snapshot(), before)

    def test_umbrella_admission_transfer_refile_close_retire_chain(self):
        umbrella_rows = self.rows_path.read_bytes()
        self.assertEqual(self.add()[0], 0)
        rc, _, err = self.invoke('transfer', '--subject', self.SUBJECT,
                                 '--owner', 'builder-M', '--ruling', 'transfer ruling')
        self.assertEqual(rc, 0, err)
        target = self.target_item(owner='builder-M')
        rc, _, err = self.refile()
        self.assertEqual(rc, 0, err)
        records = train.parse_amendments(self.amendments_path.read_text())
        self.assertEqual(len(records), 3)
        self.assertEqual(records[-1], dict(records[-2], item='KR-TARGET', item_from='KR-X',
                                          ruling='re-file ruling'))
        self.commit(self.work, 'fixture re-filed dev')
        sh(self.work, 'git', '-C', str(self.work), 'update-ref', 'refs/remotes/origin/dev', self.head())
        target.write_text('{"state": "closed", "owner": "builder-M"}\n')
        amendments_before = self.amendments_path.read_bytes()
        rc, out, err = self.invoke('retire', '--item', 'KR-TARGET')
        self.assertEqual(rc, 0, err)
        self.assertEqual(out, f'retire: native {self.SUBJECT}\n')
        self.assertEqual(self.snapshot(), (umbrella_rows, amendments_before))
        self.assertEqual(self.invoke('check')[0], 0)
        self.commit(self.work, 'fixture re-file retirement')
        with contextlib.redirect_stdout(io.StringIO()):
            rc, result = train._baseline_gate(train.Train(self.work))
        self.assertEqual(rc, 0, result)
        self.assertEqual(result['gone'], [['native', self.SUBJECT]])
        self.assertEqual(result['rows'], 1)
        self.assertEqual(train.parse_known_reds(self.rows_path.read_text()), [self.original])

    def test_transfer_original_baseline_row_refuses_exact_reason(self):
        before = self.snapshot()
        rc, _, err = self.invoke('transfer', '--subject', self.original['subject'], '--owner', 'new', '--ruling', 'rule')
        self.assertEqual(rc, 1)
        self.assertIn(known_reds.ORIGINAL_ROW, err)
        self.assertEqual(self.snapshot(), before)

    def test_transfer_missing_subject_or_same_owner_refuses_without_writes(self):
        self.assertEqual(self.add()[0], 0)
        for subject, owner in [('missing', 'new'), (self.SUBJECT, 'builder-B')]:
            before = self.snapshot()
            rc, _, _ = self.invoke('transfer', '--subject', subject, '--owner', owner, '--ruling', 'rule')
            self.assertEqual(rc, 1)
            self.assertEqual(self.snapshot(), before)

    def test_retire_two_rows_preserves_survivors_amendments_and_baseline_gate(self):
        other_item = self.item_path.with_name('KR-OTHER.json')
        other_item.write_text('{"state": "open"}\n')
        survivors = [dict(self.original, subject=f'check:keep-{i}', item='KR-OTHER',
                          evidence=f'keep évidence {i}') for i in range(2)]
        data = {'note': 'keep this état', 'rows': [self.original, *survivors]}
        self.rows_path.write_text(self.render(data))
        self.commit(self.work, 'fixture other baseline rows')
        sh(self.work, 'git', '-C', str(self.work), 'update-ref', 'refs/remotes/origin/dev', self.head())
        self.assertEqual(self.add()[0], 0)
        admitted = train.parse_known_reds(self.rows_path.read_text())[-1]
        self.commit(self.work, 'fixture amended baseline')
        sh(self.work, 'git', '-C', str(self.work), 'update-ref', 'refs/remotes/origin/dev', self.head())
        self.item_path.write_text('{"state": "landed"}\n')
        # Every pair of positions: leading, middle, trailing and separated runs.
        for positions in ((0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)):
            with self.subTest(positions=positions):
                kept = iter(survivors)
                removed = iter((self.original, admitted))
                data['rows'] = [next(removed) if i in positions else next(kept)
                                for i in range(4)]
                self.rows_path.write_text(self.render(data))
                before = self.snapshot()
                original_write = Path.write_bytes
                with mock.patch.object(Path, 'write_bytes', autospec=True,
                                       side_effect=original_write) as writer:
                    rc, out, err = self.invoke('retire', '--item', 'KR-X')
                self.assertEqual(rc, 0, err)
                self.assertEqual(out, f'retire: check {self.original["subject"]}\n'
                                 f'retire: native {self.SUBJECT}\n')
                self.assertEqual([call.args[0] for call in writer.call_args_list], [self.rows_path])
                expected = self.render(dict(data, rows=survivors)).encode()
                self.assertEqual(self.snapshot(), (expected, before[1]))
                rows, records = known_reds.validate(self.work, expected.decode(), before[1].decode())
                self.assertEqual(rows, survivors)
                self.assertEqual(len(records), 1)
                self.assertEqual(records[0]['item'], 'KR-X')
        self.commit(self.work, 'fixture retirement')
        with contextlib.redirect_stdout(io.StringIO()):
            gate_rc, result = train._baseline_gate(train.Train(self.work))
        self.assertEqual(gate_rc, 0, result)
        self.assertEqual(result['gone'], sorted([
            ['check', self.original['subject']], ['native', self.SUBJECT]]))
        self.assertFalse(result['dangling_amendments'])
        self.assertFalse(result['amendments_rewritten'])

    def test_retire_only_row_renders_empty_array_for_every_closed_state(self):
        for state in sorted(train.CLOSED_ITEM_STATES):
            with self.subTest(state=state):
                data = {'note': 'keep this état', 'rows': [self.original]}
                self.rows_path.write_text(self.render(data))
                self.item_path.write_text(json.dumps({'state': state}))
                before = self.snapshot()
                rc, out, err = self.invoke('retire', '--item', 'KR-X')
                self.assertEqual(rc, 0, err)
                self.assertEqual(out, f'retire: check {self.original["subject"]}\n')
                self.assertEqual(self.snapshot(), (self.render(dict(data, rows=[])).encode(), before[1]))
                self.assertEqual(self.invoke('check')[0], 0)

    def test_retire_preserves_noncanonical_outer_bytes(self):
        text = self.rows_path.read_text().replace('"note": ', '"note" :  ')
        text = text.replace('\n', '\r\n')
        self.rows_path.write_bytes(text.encode())
        self.item_path.write_text('{"state": "landed"}')
        before = self.snapshot()
        start, end, _ = known_reds.array_entries(text, 'rows')
        expected = (text[:start + 1] + text[end - 1:]).encode()
        rc, _, err = self.invoke('retire', '--item', 'KR-X')
        self.assertEqual(rc, 0, err)
        self.assertEqual(self.snapshot(), (expected, before[1]))

    def test_retire_refuses_open_item_without_writes(self):
        before = self.snapshot()
        rc, out, err = self.invoke('retire', '--item', 'KR-X')
        self.assertEqual(rc, 1)
        self.assertEqual(out, '')
        self.assertIn('known_reds: close the item first', err)
        self.assertEqual(self.snapshot(), before)

    def test_retire_refuses_invalid_items_without_writes(self):
        for item in ('MISSING', '../KR-X'):
            with self.subTest(item=item):
                before = self.snapshot()
                rc, out, err = self.invoke('retire', '--item', item)
                self.assertEqual(rc, 1)
                self.assertEqual(out, '')
                self.assertIn('known_reds:', err)
                self.assertIn('repair item', err)
                self.assertEqual(self.snapshot(), before)

    def test_retire_refuses_item_without_rows_without_writes(self):
        self.rows_path.write_text(self.render({'note': 'keep this état', 'rows': []}))
        self.item_path.write_text('{"state": "landed"}')
        before = self.snapshot()
        rc, out, err = self.invoke('retire', '--item', 'KR-X')
        self.assertEqual(rc, 1)
        self.assertEqual(out, '')
        self.assertIn('known_reds: no rows for repair item', err)
        self.assertEqual(self.snapshot(), before)

    def test_retire_validates_result_before_writing(self):
        self.assertEqual(self.add()[0], 0)
        self.commit(self.work, 'fixture amended baseline')
        sh(self.work, 'git', '-C', str(self.work), 'update-ref', 'refs/remotes/origin/dev', self.head())
        self.item_path.write_text('{"state": "landed"}')
        self.amendments_path.write_text(self.amendments_path.read_text().replace('seat ruling', 'edited'))
        before = self.snapshot()
        rc, out, err = self.invoke('retire', '--item', 'KR-X')
        self.assertEqual(rc, 1)
        self.assertEqual(out, '')
        self.assertIn('known_reds: amendments are append-only', err)
        self.assertEqual(self.snapshot(), before)

    def test_check_positive_and_train_parsers_are_reused(self):
        with mock.patch.object(train, 'parse_known_reds', wraps=train.parse_known_reds) as rows, \
                mock.patch.object(train, 'parse_amendments', wraps=train.parse_amendments) as amendments:
            self.assertEqual(self.invoke('check')[0], 0)
        self.assertTrue(rows.called)
        self.assertTrue(amendments.called)

    def test_check_rejects_malformed_files_without_writes(self):
        for path in (self.rows_path, self.amendments_path):
            before = path.read_bytes()
            path.write_text('not JSON\n')
            broken = self.snapshot()
            self.assertEqual(self.invoke('check')[0], 1)
            self.assertEqual(self.snapshot(), broken)
            path.write_bytes(before)

    def test_check_rejects_missing_or_closed_items_and_mismatch(self):
        self.assertEqual(self.add()[0], 0)
        before_item = self.item_path.read_bytes()
        self.item_path.unlink()
        self.assertEqual(self.invoke('check')[0], 1)
        self.item_path.write_text('{"state": "closed"}')
        self.assertEqual(self.invoke('check')[0], 1)
        self.item_path.write_bytes(before_item)
        text = self.amendments_path.read_text().replace('"builder-B"', '"other"')
        self.amendments_path.write_text(text)
        self.assertEqual(self.invoke('check')[0], 1)

    def test_check_rejects_unadmitted_rows_dangling_and_rewritten_amendments(self):
        self.assertEqual(self.add()[0], 0)
        admission = self.snapshot()
        self.amendments_path.write_text(self.render({'amendments': []}))
        self.assertEqual(self.invoke('check')[0], 1)
        self.amendments_path.write_bytes(admission[1])
        self.rows_path.write_text(self.render({'rows': [self.original]}))
        self.assertEqual(self.invoke('check')[0], 1)
        self.rows_path.write_bytes(admission[0])
        self.commit(self.work, 'fixture amended dev')
        sh(self.work, 'git', '-C', str(self.work), 'update-ref', 'refs/remotes/origin/dev', self.head())
        self.amendments_path.write_text(self.amendments_path.read_text().replace('seat ruling', 'edited'))
        self.assertEqual(self.invoke('check')[0], 1)
