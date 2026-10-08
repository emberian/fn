"""Delete retired declarations and the obsolete inline START classifier."""
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'tools'))
import lisp_rewrite as rw

def remove(text,names):
 edits=[]
 for h in rw.match('_',rw.parse(text).forms,head='definterface',deep=False):
  if h.node.items[1].low in names:edits.append((h.start,h.end,''))
 return rw.write(text,edits)
assert remove('(definterface gone :class :common-lisp-compliant)\n(definterface kept)',{'gone'})=='\n(definterface kept)'
assert remove('; gone\n(definterface kept)',{'gone'})=='; gone\n(definterface kept)'
if __name__=='__main__':
 p=ROOT/'host/interfaces.lisp';p.write_text(remove(p.read_text(),{'fn-ros-install-syncer','fn-ros-issue','fn-ros-physical','fn-ros-outcome','fn-otm-commit-event','fn-otm-committer-wake','fn-ocs-commit-step','fn-ocs-start-event','fn-ocp-gc-entry-begin','fn-otm-held-committer-wake'}))
 p=ROOT/'host/native/owner.lisp';s=p.read_text();a=s.index('(defun fnn-owner-commit-start-event ');b=s.index('(defun fnn-owner-commit-release-member ',a);p.write_text(s[:a]+s[b:])
