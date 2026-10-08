"""Separate execution/guard obligations from invariant preservation proofs."""
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'tools'))
import lisp_rewrite as rw

def split(text):
 a=text.index('(defthm fn-ocp-gc-linkedp-initially')
 b=text.index('; Guard obligations describe only representation shape.')
 theory=text[text.index('(local (in-theory\n (disable (tau-system)'):text.index('(local\n (defthm fn-ocp-gc-linkedp-output-update')]
 # The guard of SEAL needs the extent's natural-number type independently
 # of all semantic invariants. Keep this small local type proof at its use.
 for h in rw.match('_',rw.parse(text).forms,head='defthm',name='fn-ocp-gc-seal-extent-natp'):
  extent='(local '+text[h.start:h.end]+')\n'
  break
 else:raise ValueError('extent type lemma missing')
 steps=text[:a]+theory+extent+text[b:]
 first=text[text.index('(local (in-theory\n (disable fn-lgk-pipe-countedp'):text.index('(defun fn-ocp-gc-shapedp')]
 proofs='; Invariant proofs over the one guarded dispatcher.\n(in-package "ACL2")\n(include-book "owner-commit-durability-steps")\n'+first+text[a:b]
 return steps,proofs
if __name__=='__main__':
 p=ROOT/'books/owner-commit-durability.lisp'
 steps,proofs=split(p.read_text())
 assert steps.count('(defun fn-ocp-gc-host-step ')==1
 assert '(defun fn-ocp-gc-host-step ' not in proofs
 assert proofs.count('(defthm fn-ocp-gc-linkedp-preserved')==1
 (ROOT/'books/owner-commit-durability-steps.lisp').write_text(steps)
 p.write_text(proofs)
