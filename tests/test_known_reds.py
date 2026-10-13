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
