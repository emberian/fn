"""Source-only controls for sealer cleanup phase consumers and observer hold."""

from pathlib import Path
import subprocess
import unittest

import lisp_rewrite as lr
import seal_cleanup_consumer_rewrite as rw

ROOT = Path(__file__).resolve().parents[1]
BASE = '44d549172'


def one(pattern, source, *, deep=False):
    found = lr.match(pattern, lr.parse(source).forms, deep=deep)
    if len(found) != 1:
        raise AssertionError(f'expected one {pattern}')
    return found[0].node


def check_consumers(sources):
    status = one('(defun fn2-sealer-load-status ?*body)',
                 sources['books/sealer-physical-loader.lisp'])
    cleanup = lr.match('((when (or (equal phase *fn2-seal-phase-overlay-return*) '
                       '(equal phase *fn2-seal-phase-hash-return*))) :run)', [status])
    held_copy = lr.match('(equal (fn2-csnapshot-phase 0 fn2-csnapshot) '
                         '*fn2-csnapshot-phase-held*)', [status])
    closed = lr.match('((when (fn2-csnapshot-source-closed-p fn2-csnapshot)) :pause)',
                      [status])
    if (len(cleanup) != 1 or len(held_copy) != 1 or len(closed) != 1
            or not held_copy[0].start < closed[0].start < cleanup[0].start):
        raise ValueError('cleanup bypasses held/adopting/adopted source closure')
    if lr.match('(fn2-sealer-load-reserve ?*args)', [cleanup[0].node]) or lr.match(
            '(fn2-run-page-read ?*args)', [cleanup[0].node]):
        raise ValueError('cleanup status allocates or reads')
    cost = one('(defcost fn2-sealer-step ?*body)',
               sources['books/machines-c-sealer-kind.lisp'])
    items = cost.items
    answers = [items[i + 1] for i in range(len(items) - 1)
               if getattr(items[i], 'low', None) == ':answers']
    if len(answers) != 1 or not all(lr.match(tag, [answers[0]])
                                        for tag in (':held', ':credit')):
        raise ValueError('actual sealer cost omits held/credit')
    events = sources['books/machines-c-sealer-events.lisp']
    arm = lr.match('(:sealing ?*body)',
                   [one('(defmachine-arms fn2-sealer ?*body)', events)])
    if len(arm) != 1:
        raise ValueError('sealing arm missing')
    arm = arm[0].node
    held = lr.match('((:held) (:charge :steps *fn2-work-transition* :runnable t))', [arm])
    credit = lr.match('((:credit) (:do () (fn2-sealer-refuse code)) '
                      '(:set (stopped 1)) (:next :stopped) '
                      '(:charge :steps *fn2-work-transition*))', [arm])
    terminal = lr.match('((:done :retired :idle) ?*body)', [arm])
    if len(held) != 1 or len(credit) != 1 or len(terminal) != 1:
        raise ValueError('held retry, credit retention stop, or terminal branch missing')
    if not held[0].start < credit[0].start < terminal[0].start:
        raise ValueError('held/credit branch order changed')
    if lr.match('(:next :source-drain)', [held[0].node, credit[0].node]) or lr.match(
            '(fn2-sealer-source-end ?*args)', [held[0].node, credit[0].node]):
        raise ValueError('observer drained before terminal release')
    if not lr.match('(:next :source-drain)', [terminal[0].node]):
        raise ValueError('terminal owner drain lost')
    acquired = one('(defun fn2-c-source-read-acquire-raw ?*body)',
                   (ROOT / 'books/c-source-observer.lisp').read_text())
    if not lr.match('(if (fn2-c-source-observer-ownerp kind id generation '
                    'fn2-c-source-observers) :ok :stale)', [acquired]):
        raise ValueError('observer re-acquire no longer idempotent')
    source_closed = one('(defun fn2-csnapshot-source-closed-p ?*body)',
                        (ROOT / 'books/c-snapshot-state.lisp').read_text())
    for phase in ('held', 'adopting', 'adopted'):
        if not lr.match(f'*fn2-csnapshot-phase-{phase}*', [source_closed]):
            raise ValueError('source closure phase omitted: ' + phase)
    actual_step = one('(defun fn2-sealer-step ?*body)', events, deep=True)
    if not lr.match('(fn2-csnapshot-source-closed-p fn2-csnapshot)', [actual_step]):
        raise ValueError('sealer core bypasses source closure')
    snapshot = (ROOT / 'books/c-snapshot.lisp').read_text()
    quiescent = one('(defun fn2-csnapshot-sealer-quiescent-p ?*body)',
                    snapshot, deep=True)
    poll = one('(fn2-csnapshot-op fn2-csnapshot-poll ?*body)', snapshot,
               deep=True)
    source_quiescent = one('(defun fn2-sealer-source-quiescent-p ?*body)',
                           sources['books/sealer-physical-loader.lisp'])
    for fn in (quiescent, source_quiescent):
        gate = lr.match('(list *fn2-seal-phase-idle* *fn2-seal-phase-release*)', [fn])
        if len(gate) != 1 or lr.match('*fn2-seal-phase-overlay-return*', [fn]) or lr.match(
                '*fn2-seal-phase-hash-return*', [fn]):
            raise ValueError('snapshot can ACK unfinished sealer cleanup')
    if not lr.match('(fn2-c-source-observers-live id fn2-c-source-observers)', [quiescent]):
        raise ValueError('snapshot lost real observer check')
    if not lr.match('(not sealer-quiescent)', [poll]):
        raise ValueError('snapshot poll no longer waits for sealer cleanup')


class Source(unittest.TestCase):
    def sources(self):
        return {file: (ROOT / file).read_text() for file in rw.BEFORE}

    def test_fixed_original_and_exact_current_transform(self):
        for file, spec in rw.BEFORE.items():
            original = subprocess.check_output(['git', 'show', f'{BASE}:{file}'],
                                               cwd=ROOT, text=True)
            node = rw.form(file, original)
            self.assertEqual(original[node.start:node.end], spec['before'], file)
            expected, count = rw.transform(file, original)
            self.assertEqual(count, 1, file)
            self.assertEqual(expected, (ROOT / file).read_text(), file)
            self.assertEqual(rw.transform(file, expected), (expected, 0))

    def test_actual_status_cost_arm_and_observer(self):
        check_consumers(self.sources())

    def test_missing_held_or_status_gate_refused(self):
        sources = self.sources()
        status = sources['books/sealer-physical-loader.lisp']
        status = status.replace('*fn2-seal-phase-hash-return*',
                                '*fn2-seal-phase-install*', 1)
        with self.assertRaises(ValueError):
            check_consumers({**sources, 'books/sealer-physical-loader.lisp': status})
        arm = sources['books/machines-c-sealer-events.lisp']
        arm = arm.replace('((:held) (:charge :steps *fn2-work-transition* :runnable t))',
                          '((:held) (:next :source-drain))', 1)
        with self.assertRaises(ValueError):
            check_consumers({**sources, 'books/machines-c-sealer-events.lisp': arm})


if __name__ == '__main__':
    unittest.main()
