"""Scripted raw observer teeth; no native/INN execution."""
import base64
import unittest
from tools.resilience.adapters.inn_control import observe, subject

EXPECTED = '<control@fn.invalid>'
def article(identity=EXPECTED):
    return ('Message-ID: '+identity+'\r\nControl: checkgroups\r\n\r\nfn.test y\r\n').encode()
def exchange(**changed):
    return dict(article=article(), result='239 '+EXPECTED, block_complete=True, transfer_complete=True, **changed)

class ControlCorpusTests(unittest.TestCase):
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
