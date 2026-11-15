"""Source-only controls for actual event reader adoption; no ACL2 execution."""
from pathlib import Path
import sys
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
import event_record_digest_current_rewrite as r

class EventRecordDigestCurrent(unittest.TestCase):
 def test_replay_and_idempotence(self):
  for name,fun in [('event-read-state',r.state),('event-read-source',r.source_begin),('event-read-verify',r.verify),('event-read-verified-unit',r.verified)]:
   before=(ROOT/'tools/fixtures/event-record-digest-current'/f'{name}.lisp').read_text()
   actual=(ROOT/('tests' if name.endswith('unit') else 'books')/f'{name}.lisp').read_text()
   self.assertEqual(fun(before),actual,name)
   self.assertEqual(fun(actual),actual,name)
   r.lr.parse(actual)
 def test_minimal_state_and_seed_yield(self):
  state=(ROOT/'books/event-read-state.lisp').read_text()
  self.assertNotIn('(fetch-',state)
  self.assertEqual(state.count('(record-fetch-'),3)
  verify=(ROOT/'books/event-read-verify.lisp').read_text()
  core=r.one(verify,'(defun fn2-event-read-format-core ?*body)')
  text=verify[core.start:core.end]
  seed=r.one(text,'((when semantic) ?*body)'); seed=text[seed.start:seed.end]
  self.assertNotIn('fn2-rec-fetch',seed)
  self.assertIn('(mv (if valid :more :seal)',seed)
  self.assertIn('(record-fetch-next 0) (record-fetch-acc 0)',seed)
  self.assertLess(text.index('*fn2-event-read-phase-record-digest*'),text.index('(fn2-format-run'))
  self.assertLess(text.index('*fn2-event-read-phase-record-digest*'),text.index('(fn2-rec-context'))
 def test_ref_and_completion(self):
  v=(ROOT/'books/event-read-verify.lisp').read_text()
  n=r.one(v,'(defun fn2-event-read-record-digest-current-p ?*body)');p=v[n.start:n.end]
  for field in ['ref-slot','ref-gen','ref-off','ref-len']:
   self.assertIn('fn2-fields-'+field,p)
  self.assertIn('fn2-digest-equal',p)
  self.assertIn('(+ off 32)',p)
  n=r.one(v,'(defun fn2-event-read-record-digest-step ?*body)');s=v[n.start:n.end]
  self.assertIn('(and (eq code :ok) (equal next 32) (equal acc 0))',s)
  self.assertNotIn('fn2-event-members',s)
  self.assertEqual(s.count('fn2-rec-fetch-step'),1)
 def test_public_zero_before_seals_and_live_source_gates(self):
  v=(ROOT/'books/event-read-verify.lisp').read_text();n=r.one(v,'(defun fn2-event-read-format-step ?*body)');s=v[n.start:n.end]
  self.assertLess(s.index('fn2-event-read-ownerp'),s.index('fn2-event-read-source-held-p'))
  self.assertLess(s.index('fn2-event-read-source-held-p'),s.index('(equal budget 0)'))
  self.assertLess(s.index('(equal budget 0)'),s.index('(fn2-event-source-seal'))
  self.assertLess(s.index('(natp budget)'),s.index('(equal budget 0)'))
 def test_actual_consumer_routes(self):
  for name in ['event-producer','checkpoint-restore-events']:
   s=(ROOT/'books'/f'{name}.lisp').read_text()
   self.assertIn('(fn2-event-read-format-phase-p ',s)
   self.assertIn('fn2-event-read-format-',s)
  cold=(ROOT/'books/checkpoint-restore-events.lisp').read_text()
  n=r.one(cold,'(defun fn2-checkpoint-restore-events-journal-bind ?*body)');bind=cold[n.start:n.end]
  self.assertIn('*fn2-checkpoint-restore-events-phase-journal-bind*',bind)
  self.assertIn('fn2-checkpoint-restore-events-set-phase 0 *fn2-checkpoint-restore-events-phase-journal*',bind)
  n=r.one(cold,'(defun fn2-checkpoint-restore-events-journal-step ?*body)');step=cold[n.start:n.end]
  self.assertLess(step.index('fn2-event-read-format-phase-p'),step.index('fn2-event-read-member-core'))
  self.assertLess(step.index('((unless good)'),step.index('*fn2-checkpoint-restore-events-phase-journal-bind*'))
 def test_actual_writer_fixture(self):
  s=(ROOT/'tests/event-read-verified-unit.lisp').read_text()
  for call in ['fn2-commit-admit-keyed','fn2-retirement-live-drive','fn2-epv-open token','fn2-epv-format 1','fn2-epv-format 0','fn2-pool-release','(assert-event (fn2-epv-test :loan))']:
   self.assertIn(call,s)
  self.assertIn('(= after (+ next 1))',s)
  self.assertIn('(if (= after 32) *fn2-event-read-phase-read-records* *fn2-event-read-phase-record-digest*)',s)
  self.assertNotIn('set-phase 0 *fn2-event-read-phase-record-digest*',s)
 def test_legacy_fetch_unchanged(self):
  import subprocess
  original=subprocess.check_output(['git','show','1c70451f:books/pool-digest.lisp'],cwd=ROOT,text=True)
  current=(ROOT/'books/pool-digest.lisp').read_text()
  for s in [original,current]:r.lr.parse(s)
  a=r.one(original,'(defun fn2-rec-fetch ?*body)');b=r.one(current,'(defun fn2-rec-fetch ?*body)')
  self.assertEqual(original[a.start:a.end],current[b.start:b.end])

if __name__=='__main__':unittest.main()
