"""Scripted raw observer teeth; no native/INN execution."""
import base64
import unittest
import tempfile
import json
from pathlib import Path
from tools.resilience.adapters.inn_control import observe, subject, Recorder

EXPECTED = '<control@fn.invalid>'
def article(identity=EXPECTED):
    return ('Message-ID: '+identity+'\r\nControl: checkgroups\r\n\r\nfn.test y\r\n').encode()
def exchange(**changed):
    return dict(article=article(), result='239 '+EXPECTED, block_complete=True, transfer_complete=True, **changed)

class ControlCorpusTests(unittest.TestCase):
    def test_selected_lab_callback_retains_each_trial_without_overwriting(self):
        with tempfile.TemporaryDirectory() as temporary:
            recorder = Recorder(Path(temporary) / 'corpus')
            recorder('inn-checkgroups-control', EXPECTED, exchange(), article())
            recorder('inn-throttle-resumed', EXPECTED, None, None)
            rows=sorted(recorder.directory.glob('*/disposition.json'))
            self.assertEqual([json.loads(p.read_text())['status'] for p in rows], ['observed', 'unavailable'])
            self.assertEqual(len(list(recorder.directory.glob('*/journal.jsonl'))), 2)
            with self.assertRaises(ValueError):
                recorder('invented-receipt', EXPECTED, exchange(), article())

    def test_exact_raw_subject_is_retained_without_whole_control_claim(self):
        journal, result = observe('control', EXPECTED, exchange(), article())
        self.assertEqual(result['status'], 'observed')
        raw = journal.of_kind('environment')[0]
        self.assertEqual(base64.b64decode(raw['arrived_octets']), article())
        self.assertEqual(base64.b64decode(raw['served_octets']), article())
    def test_matching_reply_cannot_authorize_shared_wrong_article_subject(self):
        data = exchange(); data['article'] = article('<wrong@fn.invalid>')
        _, result = observe('control', EXPECTED, data, data['article'])
        self.assertEqual(result['status'], 'violation')
    def test_missing_or_truncated_block_never_counts_complete_from_239(self):
        for field in ('block_complete', 'transfer_complete'):
            for value in (None, False):
                data=exchange(); data[field]=value
                _, result=observe('control', EXPECTED, data, article())
                self.assertEqual(result['status'], 'unavailable')
    def test_completed_prebody_refusal_requires_no_article_transfer(self):
        data=dict(complete=True, offer='438 '+EXPECTED, result='', article=None,
                  block_complete=False, transfer_complete=False)
        _, result=observe('control', EXPECTED, data, None)
        self.assertEqual(result['status'], 'refused')
        data['complete']=False
        _, result=observe('control', EXPECTED, data, None)
        self.assertEqual(result['status'], 'unavailable')

    def test_refused_and_unknown_outcomes_are_distinct_from_observed(self):
        for reply, status in [('439 '+EXPECTED, 'refused'), ('', 'unavailable'), ('400 timeout', 'unavailable')]:
            data=exchange(); data['result']=reply
            _, result=observe('control', EXPECTED, data, article())
            self.assertEqual(result['status'], status)
        data=exchange(); data['result']='239 <wrong@fn.invalid>'
        _, result=observe('control', EXPECTED, data, article())
        self.assertEqual(result['cause'], 'inn-control-reply-subject-mismatch')

    def test_missing_raw_or_duplicate_subject_refuses_observation(self):
        _, result=observe('control', EXPECTED, exchange(), None)
        self.assertEqual(result['status'], 'unavailable')
        duplicate=article().replace(b'Control:', ('Message-ID: '+EXPECTED+'\r\nControl:').encode())
        self.assertIsNone(subject(duplicate))
        _, result=observe('control', EXPECTED, exchange(), duplicate)
        self.assertEqual(result['status'], 'violation')
