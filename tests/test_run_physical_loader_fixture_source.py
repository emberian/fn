"""Declaration-bound source controls for the unexecuted physical lookup fixture."""
from pathlib import Path
import copy
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
from lisp_source import forms, read_sexp
ROOT = Path(__file__).resolve().parents[1]
TEXT = (ROOT / 'tests/run-physical-loader-unit.lisp').read_text()
FORMS = [read_sexp(s) for s in forms(TEXT)]


def walk(node):
    if isinstance(node, list):
        yield node
        for child in node:
            yield from walk(child)


def calls(node):
    return [n[0] for n in walk(node) if n and isinstance(n[0], str)]


def definitions():
    return {n[1]: n for n in FORMS if n and n[0] in ('defun', 'fn2-rpl-wrapper')}


def returned_adopted_hash_is_produced(node):
    text = str(node)
    return all('fn2-digest-word' in calls(n) for n in walk(node)
               if n and n[0] in [f'hash-{i}' for i in range(8)]) and all(
        f'hash-{i}' in text for i in range(8))


class RunPhysicalLoaderFixtureSource(unittest.TestCase):
    def setUp(self):
        self.defs = definitions()

    def test_actual_queue_adapter_completion_and_verifier_chain(self):
        done = self.defs['fn2-rpl-complete-read']
        for name in ['fn2-host-outbox-peek', 'fn2-host-action', 'fn2-rpl-input-copy',
                     'fn2-outbox-ack', 'fn2-post-result', 'fn2-harvest-one']:
            self.assertIn(name, calls(done))
        copybytes = self.defs['fn2-rpl-input-copy']
        self.assertIn('fn2-pool-read', calls(copybytes))
        self.assertIn('fn2-pool-adapter-write', calls(copybytes))
        load = self.defs['fn2-rpl-load-step']
        self.assertIn('fn2-run-load-step', calls(load))
        drive = self.defs['fn2-rpl-load-drive']
        self.assertIn('*fn2-run-load-phase-header*', str(drive))
        self.assertIn('fn2-rpl-loadedp', calls(drive))
        self.assertNotIn('fn2-run-cursors-set-phase', calls(drive))
        self.assertNotIn('fn2-run-loads-set-phase', calls(drive))

    def test_catalog_hashes_follow_real_producer_not_fixture_expected_words(self):
        for name, actual in [('fn2-rpl-open', 'fn2-run-open'), ('fn2-rpl-add', 'fn2-run-add'),
                             ('fn2-rpl-seal-step', 'fn2-run-seal-step'), ('fn2-rpl-check', 'fn2-format-drive')]:
            self.assertIn(actual, calls(self.defs[name]))
        record = self.defs['fn2-rpl-record-page']
        self.assertTrue(returned_adopted_hash_is_produced(record))
        damaged = copy.deepcopy(record)
        for n in walk(damaged):
            if n and n[0] == 'fn2-digest-word':
                n[0] = 'unchecked-expected-word'
                break
        self.assertFalse(returned_adopted_hash_is_produced(damaged))

    def test_rebuilt_entries_and_ranks_come_from_actual_held_sources(self):
        capture = self.defs['fn2-rpl-capture']
        for field in ['kind', 'row', 'rank']:
            self.assertIn('fn2-checkpoint-source-' + field, calls(capture))
        self.assertIn('fn2-checkpoint-source-step', calls(self.defs['fn2-rpl-select-step']))
        held = self.defs['fn2-rpl-held-entry']
        self.assertIn('fn2-csnapshot-overlay-entry', calls(held))
        self.assertIn('fn2-csnapshot-run-page', calls(held))
        self.assertIn('fn2-run-nth', calls(self.defs['fn2-rpl-copy-held-row']))
        self.assertNotIn('fn2-rpl-entry', calls(self.defs['fn2-rpl-rebuild']))
        body = self.defs['fn2-rpl-body']
        self.assertIn('fn2-csnapshot-begin', calls(body))
        self.assertIn('fn2-csnapshot-release', calls(body))
        self.assertIn([['1', '1', '1'], ['2', '1', '0'], ['3', '0', '0']],
                      [n for n in walk(body)])

    def test_before_after_whole_values_and_physical_read_counts_are_asserted(self):
        body = self.defs['fn2-rpl-body']
        text = str(body)
        for expected in ["['equal', 'value1', ['quote', ['1', '1', '303', '1', '65']]]", "['equal', 'value2', ['quote', ['1', '2', '111', '2', '65']]]",
                         "['equal', 'value1', 'again1']", "['equal', 'value2', 'again2']",
                         "['=', 'physical1', '16']", "['=', 'physical2', '32']"]:
            self.assertIn(expected, text)
        self.assertIn('fn2-xl-step', calls(self.defs['fn2-rpl-lookup-step']))
        self.assertIn('fn2-checkpoint-summary-apply-step', calls(self.defs['fn2-rpl-apply-step']))
        self.assertIn('fn2-rpl-cache-emptyp', calls(body))
        self.assertIn('fn2-rpl-never-exposed-p', calls(body))
        self.assertIn('(assert-event (fn2-rpl-test nil))', TEXT)
        self.assertIn('(assert-event (fn2-rpl-test t))', TEXT)

    def test_actual_wrapper_outputs_respect_mv32_and_all_readonly_inputs_remain(self):
        for n in FORMS:
            if n and n[0] == 'fn2-rpl-wrapper':
                _, name, args, inputs, outputs, scalars, call = n
                self.assertLessEqual(len(outputs) + len(scalars), 32, name)
                self.assertTrue(set(outputs).issubset(set(inputs)), name)
                self.assertTrue(set(inputs).issubset(set(calls(call)) | set(str(call).replace('[', ' ').replace(']', ' ').replace("'", '').replace(',', '').split())), name)
        reserve = self.defs['fn2-rpl-load-read']
        self.assertEqual(reserve[5], ['code', 'op', 'gen'])
        self.assertIn('fn2-run-load-issue', calls(reserve[6]))


if __name__ == '__main__':
    unittest.main()
