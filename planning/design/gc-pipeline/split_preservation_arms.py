"""Give effect and drain preservation separate proof units; one dispatcher remains."""
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'tools'))
import lisp_rewrite as rw

def exported(text):
    edits=[]
    for form in rw.parse(text).forms:
        if form.items and form.items[0].low=='local' and len(form.items)==2:
            node=form.items[1]
            if node.items and node.items[0].low=='defthm':
                edits.append((form.start,form.end,text[node.start:node.end]))
    for a,b,value in reversed(edits):text=text[:a]+value+text[b:]
    return text

if __name__=='__main__':
    assert exported('(local (defthm a t))\n(local (in-theory (disable f)))')=='(defthm a t)\n(local (in-theory (disable f)))'
    p=ROOT/'books/owner-commit-durability.lisp';s=p.read_text()
    a=s.index('(local\n (defthm fn-ocp-gc-linkedp-output-update')
    b=s.index('(local\n (defthm fn-ocvm-gc-start-fields')
    c=s.index('(local\n (defthm fn-ocp-gc-gate-record-fields')
    header=s[:s.index('(defthm fn-ocp-gc-linkedp-initially')]
    theory=s[s.index('; Preservation arm lemmas'):a]
    effects=header+theory+exported(s[a:b])
    drain=header+'(local (include-book "owner-commit-durability-effects"))\n'+theory+exported(s[b:c])
    initial=s[s.index('(defthm fn-ocp-gc-linkedp-initially'):s.index('; Preservation arm lemmas')]
    core=header+'(local (include-book "owner-commit-durability-effects"))\n(local (include-book "owner-commit-durability-drain"))\n'+initial+theory+s[c:]
    for name,text in [('owner-commit-durability-effects',effects),('owner-commit-durability-drain',drain),('owner-commit-durability',core)]:
        assert '(defun ' not in text
        (ROOT/'books'/f'{name}.lisp').write_text(text)
