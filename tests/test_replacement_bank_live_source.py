"""Named source/projection controls only; actual ACL2 bank fixtures are separate."""
from pathlib import Path
import json,sys,unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
import lisp_rewrite as lr
from replacement_bank_live_rewrite import project
DATA=json.loads((ROOT/'tools/fixtures/replacement-bank-live-source.json').read_text())

def form(text, name):
    matches=lr.match('(defun '+name+' ?*body)',lr.parse(text).forms,deep=True)
    if len(matches)!=1:raise ValueError(name)
    n=matches[0].node
    return text[n.start:n.end]

class ReplacementBanks(unittest.TestCase):
    def test_exact_named_replay_and_idempotence(self):
        for book,before in DATA['before'].items():
            current=(ROOT/'books'/(book+'.lisp')).read_text()
            self.assertEqual(project(book,before),current)
            self.assertEqual(project(book,current),current)
            lr.parse(current)

    def test_actual_installer_reserves_entire_target_bank(self):
        body=form((ROOT/'books/checkpoint-live-install.lisp').read_text(),
                  'fn2-checkpoint-live-replace-install-step')
        self.assertIn('(= (fn2-checkpoint-summary-free-count 1 fn2-checkpoint-summary) (fn2-run-installed-bank-capacity fn2-run-installed))',body)
        self.assertIn('(<= (fn2-checkpoint-summary-count 1 fn2-checkpoint-summary) (fn2-run-installed-bank-capacity fn2-run-installed))',body)
        self.assertIn('(fn2-run-installed-bank-row-p bank i fn2-run-installed)',body)
        self.assertIn('(= (fn2-run-installed-physical i fn2-run-installed) 0)',body)
        self.assertIn('(target start)',body)
        self.assertIn('(fn2-run-installed-bank-row-p bank r fn2-run-installed)',body)
        self.assertIn('(target (+ 1 r))',body)
        self.assertNotIn('(fn2-checkpoint-summary-set-target 1 (+ 1 r)',body)

    def test_terminal_promotion_retains_exact_bank(self):
        text=(ROOT/'books/checkpoint-live-finish.lisp').read_text()
        promote=form(text,'fn2-checkpoint-live-replace-finish')
        reopen=form(text,'fn2-checkpoint-live-replace-reopen')
        self.assertIn('(bank (fn2-checkpoint-summary-bank 1 fn2-checkpoint-summary))',promote)
        self.assertIn('(= (fn2-checkpoint-summary-bank 0 fn2-checkpoint-summary) (fn2-checkpoint-summary-bank 1 fn2-checkpoint-summary))',reopen)
        # Actual old-catalog drain and canonical authority consume still gate
        # reopen. Bank metadata is not a substitute ready/complete flag.
        self.assertIn('*fn2-checkpoint-summary-authority-phase-idle*',reopen)
        self.assertIn('*fn2-directory-rebase-phase-committed*',reopen)

    def test_guards_formals_and_nonbank_events_preserved(self):
        for book,before in DATA['before'].items():
            after=project(book,before)
            old=lr.match('(defun ?name ?*body)',lr.parse(before).forms,deep=True)
            new=lr.match('(defun ?name ?*body)',lr.parse(after).forms,deep=True)
            self.assertEqual(len(old),len(new))
            for a,b in zip(old,new):
                for i in (1,2,3):
                    x=a.node.items[i];y=b.node.items[i]
                    self.assertEqual(before[x.start:x.end],after[y.start:y.end])

    def test_mutations_lose_actual_safety_clauses(self):
        text=project('checkpoint-live-install',DATA['before']['checkpoint-live-install'])
        # The old shared-free-space algorithm is the concrete negative: it
        # counts R resident holes and active-bank holes as replacement space.
        before=DATA['before']['checkpoint-live-install']
        self.assertNotIn('(fn2-run-installed-bank-row-p bank i fn2-run-installed)',before)
        self.assertNotIn('(target start)',before)
        for clause in ('(fn2-run-installed-bank-row-p bank i fn2-run-installed)',
                       '(fn2-run-installed-bank-row-p bank r fn2-run-installed)',
                       '(target (+ 1 r))'):
            self.assertEqual(text.count(clause),1)
            self.assertNotIn(clause,text.replace(clause,'t',1))

if __name__=='__main__':unittest.main()
