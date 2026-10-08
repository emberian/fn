"""Startup load is outside O; served history sync has no disk read edge."""
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import ledger
import lock_discipline_check as ldc


def definitions(path):
    return {str(f[1]): f for f, _ in ledger.Reader(path.read_text()).top_level()
            if ldc.head(f) == 'defun'}


def mentions(form, name):
    if isinstance(form, list):
        return ldc.head(form) == name or any(mentions(x, name) for x in form)
    return False


class HistoryStartup(unittest.TestCase):
    def test_history_find_expansion_exposes_reads_and_predicate(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'books').mkdir()
            source = root / 'books/reader.lisp'
            prefix = '''
(defun fn-hist-count (hist) 1)
(defun fn-hist-at (k hist) nil)
(defun reference (m rows) (fn-pgs-fill-frame rows))
'''
            source.write_text(prefix + '''
(def-loop-history-find served (m) reference (equal event m))
''')
            reach = ldc.acl2_realizer_reach(root, {'fn-pgs-fill-frame'})
            self.assertIn('served', reach.known)
            self.assertIn('served-from', reach.known)
            self.assertNotIn('fn-pgs-fill-frame', reach.get('served', {}))
            self.assertIn('fn-pgs-fill-frame', reach['reference'])
            # Ablation: a disk read in the generated predicate must be visible.
            source.write_text(prefix + '''
(def-loop-history-find served (m) reference (fn-pgs-fill-frame event))
''')
            reach = ldc.acl2_realizer_reach(root, {'fn-pgs-fill-frame'})
            self.assertIn('fn-pgs-fill-frame', reach['served'])
            # The actual column reader is also part of the executable closure.
            source.write_text((prefix + '''
(def-loop-history-find served (m) reference (equal event m))
''').replace('(defun fn-hist-at (k hist) nil)',
             '(defun fn-hist-at (k hist) (fn-pgs-fill-frame hist))'))
            reach = ldc.acl2_realizer_reach(root, {'fn-pgs-fill-frame'})
            self.assertIn('fn-pgs-fill-frame', reach['served'])

    def test_history_fold_expansion_exposes_column_and_step(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'books').mkdir()
            path = root / 'books/fold.lisp'
            prefix = """
(defun fn-hist-count (hist) 1)
(defun fn-hist-at (k hist) nil)
(defun reference (rows acc) (fn-pgs-fill-frame rows))
"""
            path.write_text(prefix + '(def-loop-history-fold served reference (cons event acc))')
            reach = ldc.acl2_realizer_reach(root, {'fn-pgs-fill-frame'})
            self.assertIn('served-from', reach.known)
            self.assertNotIn('fn-pgs-fill-frame', reach.get('served', {}))
            path.write_text(prefix + '(def-loop-history-fold served reference (fn-pgs-fill-frame event))')
            self.assertIn('fn-pgs-fill-frame', ldc.acl2_realizer_reach(
                root, {'fn-pgs-fill-frame'})['served'])

    def test_owner_completion_callback_class_and_ablation(self):
        from tests.test_lock_discipline_check import run
        source = """
(defun standalone (store) (fnn-extent-pread store nil 0))
(defun missing (store) (fnn-fault "missing owner completion"))
(defun resident (store) nil)
(defvar *standalone* #'standalone)
(defvar *owner* #'missing)
(defun finish-owner (store) (funcall *owner* store))
(defun quantum (service store)
 (let ((*owner* #'resident))
  (sb-thread:with-mutex ((fnn-owner-service-lock service)) (finish-owner store))))
"""
        self.assertEqual(run(source, ['R2']), [])
        mutant = source.replace('(funcall *owner* store)', '(funcall *standalone* store)')
        self.assertTrue(any(f.key == 'O:fnn-extent-pread' for f in run(mutant, ['R2'])))
        actual = definitions(ROOT / 'host/native/io.lisp')['fnn-owner-finish-store']
        self.assertIn('*fnn-owner-finish-callback*', str(actual))
        self.assertNotIn('*fnn-finish-callback*', str(actual))

    def test_round_three_served_entries_have_no_page_fill_arm(self):
        reach = ldc.acl2_realizer_reach(ROOT, {'fn-pgs-fill-frame'})
        subjects = ('fn-owner-io-served', 'fn-owner-prepare-buffer',
                    'fn-owner-prepare-identity-served', 'fn-owner-prepare-consumer-served',
                    'fn-owner-prepare-topic-served', 'fn-owner-prepare-retention-served',
                    'fn-owner-finish-synced', 'fn-owner-finish-submission-synced',
                    'fn-owner-key-statement-redecide-find', 'fn-bprj-install',
                    'fn-owner-sco-capture-served', 'fn-owner-oex-capture-served',
                    'fn-owner-orc-capture-served', 'fn-owner-orcp-capture',
                    'fn-native-live-status-host-answer', 'fn-owner-reconfigure-complete')
        for subject in subjects:
            with self.subTest(subject=subject):
                self.assertIn(subject, reach.known)
                self.assertNotIn('fn-pgs-fill-frame', reach.get(subject, {}))
        self.assertIn('fn-pgs-fill-frame', reach['fn-owner-sco-capture'])
        self.assertIn('fn-pgs-fill-frame', reach['fn-bpaj-replay'])
        self.assertIn('fn-pgs-fill-frame', reach['fn-oclc-publish'])

    def test_install_loads_before_mutex_and_maintenance(self):
        source = (ROOT / 'host/native/owner.lisp').read_text()
        start = source.index('(defun fnn-owner-install (')
        end = source.index('\n(defun ', start + 1)
        install = source[start:end]
        sync = install.index('(fnn-owner-history-sync-first)')
        self.assertLess(sync, install.index('(sb-thread:make-mutex'))
        self.assertNotIn('(fnn-owner-history-root-maintain', install)
        run = source[source.index('(defun fnn-owner-run ('):]
        self.assertLess(run.index('(fnn-mux-budget-install'),
                        run.index('(fnn-owner-history-root-maintain'))
        first = definitions(ROOT / 'host/native/history-root.lisp')['fnn-owner-history-sync-first']
        self.assertFalse(mentions(first, 'fnn-owner-gated'))
        self.assertIn('fn-owner-history-startup', str(first))

    def test_only_install_calls_startup(self):
        callers = []
        for path in (ROOT / 'host/native').glob('*.lisp'):
            for name, form in definitions(path).items():
                if mentions(form[3:], 'fnn-owner-history-sync-first'):
                    callers.append(name)
        self.assertEqual(callers, ['fnn-owner-install'])

    def test_served_sync_has_no_disk_realizer(self):
        reach = ldc.acl2_realizer_reach(ROOT, {'fn-pgs-fill-frame'})
        self.assertNotIn('fn-pgs-fill-frame', reach.get('fn-host-hist-sync', {}))
        # Positive control: startup really does retain the disk-load edge.
        self.assertIn('fn-pgs-fill-frame', reach['fn-owner-history-startup'])

    def test_carried_readers_and_dispatcher_have_no_disk_realizer(self):
        reach = ldc.acl2_realizer_reach(ROOT, {'fn-pgs-fill-frame'})
        for subject in ('fn-owner-record-debt', 'fn-owner-record-octets',
                        'fn-owner-carried-usage', 'fn-owner-step'):
            with self.subTest(subject=subject):
                self.assertNotIn('fn-pgs-fill-frame', reach.get(subject, {}))
        # Ablation controls: the old fallback and generic dispatcher do read disk.
        self.assertIn('fn-pgs-fill-frame', reach['fn-hist-debt-carried'])
        self.assertIn('fn-pgs-fill-frame', reach['fn-ocfg-step'])

    def test_actual_step_callers_use_supported_events(self):
        allowed = {':open', ':advance', ':reconfigure', ':take', ':control-submit',
                   ':legacy-control-submit', ':bp-transit-submit',
                   ':operator-submit', ':feed-conn'}
        calls = []
        def walk(form):
            if not isinstance(form, list):
                return
            if ldc.head(form) == 'fn-owner-step':
                self.assertIsInstance(form[1], list)
                self.assertEqual(ldc.head(form[1]), 'list')
                self.assertIn(str(form[1][1]), allowed)
                calls.append(form)
            for child in form:
                walk(child)
        for form in definitions(ROOT / 'host/owner-host.lisp').values():
            walk(ldc.executable_part(form[3:]))
        self.assertEqual(len(calls), 8)

    def test_no_owner_region_can_call_reset_open_or_startup(self):
        forbidden = {'fn-store-sn-reset', 'fn-store-sn-open-classified',
                     'fn-owner-history-startup', 'fn-owner-install-profile'}
        reach = ldc.acl2_realizer_reach(ROOT, forbidden)
        _, model, _ = ldc.analyze_tree(
            ROOT, ldc.load_contracts(ROOT / 'tools/lock_discipline_contracts.json'),
            reach=reach)
        seeds = {name for name, info in model.infos.items()
                 if any(e.kind == 'core' and reach.get(e.name) for e in info.events)}
        callers = set(seeds)
        for seed in seeds:
            callers.update(ldc._ancestors(model, seed))
        bad = []
        for name, info in model.infos.items():
            for event in info.events:
                if 'O' in event.ctx.locks and (
                    (event.kind == 'core' and reach.get(event.name)) or
                    (event.kind == 'call' and event.name in callers)):
                    bad.append((name, event.line, event.name))
        self.assertEqual(bad, [])
        # The audit must have found the real startup/open call sites.
        self.assertIn('fnn-owner-history-sync-first', seeds)
        self.assertIn('fnn-bridge-reset', seeds)

    def test_cache_writers_are_covered_by_initialization_or_preservation(self):
        keys = {'fn-owner-record-debt', 'fn-owner-record-octets', 'fn-owner-carried-usage'}
        def writes_cache(form):
            if not isinstance(form, list):
                return False
            if ldc.head(form) == 'f-put-global' and len(form) > 2:
                key = form[1]
                if isinstance(key, list) and ldc.head(key) == 'quote' and str(key[1]) in keys:
                    return True
            return any(writes_cache(x) for x in form)
        writers = set()
        for directory in ('books', 'host'):
            for path in (ROOT / directory).glob('*.lisp'):
                for name, form in definitions(path).items():
                    if writes_cache(form):
                        writers.add(name)
        self.assertEqual(writers, {
            'fn-owner-install-profile', 'fn-owner-history-cache-put',
            'fn-owner-record-debt', 'fn-owner-record-octets',
            'fn-owner-carried-usage', 'fn-owner-orcp-swap'})
        mutant, _ = ledger.Reader(
            "(defun corrupt (state) (f-put-global 'fn-owner-record-debt nil state))"
        ).top_level()[0]
        self.assertTrue(writes_cache(mutant))

    def test_reload_writers_are_startup_only(self):
        writers = []
        def puts(form):
            if not isinstance(form, list):
                return False
            if ldc.head(form) == 'f-put-global' and len(form) > 2:
                if form[1] == [ledger.Sym('quote'), ledger.Sym('fn-store-sn-hist-reload')]:
                    return True
            return any(puts(x) for x in form)
        for directory in ('books', 'host'):
            for path in (ROOT / directory).glob('*.lisp'):
                for name, form in definitions(path).items():
                    if puts(form):
                        writers.append(name)
        self.assertEqual(sorted(writers), sorted([
            'fn-host-hist-startup', 'fn-store-sn-reset', 'fn-store-sn-open-classified']))
        # Mutation control: a mid-run writer is detected by the same walk.
        mutant, _ = ledger.Reader("(defun mid-run (state) (f-put-global 'fn-store-sn-hist-reload t state))").top_level()[0]
        self.assertTrue(puts(mutant))


if __name__ == '__main__':
    unittest.main()
