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
 def test_cold_uses_real_source_and_full_outputs(self):
  s=(ROOT/'tests/event-read-digest-cold-unit.lisp').read_text()
  for call in ['fn2-ccp-prefix-and-publication','fn2-ccp-restart','fn2-ecd-hold-fetch','fn2-boot-checkpoint-events-begin id generation','fn2-boot-checkpoint-events-journal-bind fn2-core','fn2-boot-checkpoint-events-journal-step 1','fn2-ecd-bytes 32']:
   self.assertIn(call,s)
  self.assertNotIn('fn2-event-read-put',s)
  self.assertNotIn('fn2-checkpoint-restore-events-put',s)
  for child in ['fn2-checkpoint-restore-reader','fn2-checkpoint-restore-events-work','fn2-journal-members','fn2-mk','fn2-fc-context','fn2-b3','fn2-fields','fn2-digests']:
   self.assertIn('fn2-test-table-snapshot-'+child,s)
 def test_changed_literal_call_arities(self):
  def walk(node):
   if isinstance(node,r.lr.Lst):
    yield node
    for child in node.items:yield from walk(child)
   elif isinstance(node,r.lr.Pre):yield from walk(node.node)
  def atom(node):return node.low if isinstance(node,r.lr.Atom) else None
  files=['books/event-read-verify.lisp','books/pool-digest.lisp','tests/event-read-verified-unit.lisp','tests/event-read-digest-cold-unit.lisp']
  parsed=[r.lr.parse((ROOT/file).read_text()) for file in files]
  arities={}
  for doc in parsed:
   for node in doc.forms:
    if not isinstance(node,r.lr.Lst) or len(node.items)<3:continue
    head=atom(node.items[0]);name=atom(node.items[1]);args=node.items[2]
    if head=='defun' and isinstance(args,r.lr.Lst):arities[name]=len(args.items)
    if head=='fn2-epv-wrapper':arities[name]=1+(len(args.items) if isinstance(args,r.lr.Lst) else 0)
  checked=0
  for doc in parsed:
   for form in doc.forms:
    if not isinstance(form,r.lr.Lst) or not form.items:continue
    head=atom(form.items[0])
    bodies=form.items[3:] if head=='defun' else form.items[-1:] if head=='fn2-epv-wrapper' else []
    for body in bodies:
     if isinstance(body,r.lr.Lst) and body.items and atom(body.items[0])=='declare':continue
     for node in walk(body):
      if node.items and atom(node.items[0]) in arities:
       name=atom(node.items[0]);self.assertEqual(len(node.items)-1,arities[name],name);checked+=1
  self.assertGreater(checked,40)
 def test_legacy_fetch_unchanged(self):
  import subprocess
  original=subprocess.check_output(['git','show','1c70451f:books/pool-digest.lisp'],cwd=ROOT,text=True)
  current=(ROOT/'books/pool-digest.lisp').read_text()
  for s in [original,current]:r.lr.parse(s)
  a=r.one(original,'(defun fn2-rec-fetch ?*body)');b=r.one(current,'(defun fn2-rec-fetch ?*body)')
  self.assertEqual(original[a.start:a.end],current[b.start:b.end])

if __name__=='__main__':unittest.main()
