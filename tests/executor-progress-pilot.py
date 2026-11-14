#!/usr/bin/env python3
"""Emit an execution-only cached-baseline control driver from current source.

Run from repository root; stdout is an ACL2/raw-Lisp driver. Load it in an
unchanged qualified A tree with books/host-boundary certificates installed.
This is not a proof world: logical proofs use executor-progress separately.
The replacement body is structurally extracted, never a handwritten twin.
"""
from pathlib import Path
import sys
sys.path.insert(0,'tools')
import lisp_rewrite as l
unit=l.parse(Path('tests/executor-progress-unit.lisp'))
stop=l.parse(Path('books/executor.lisp'))
control=Path('tests/executor-progress-control.lsp').read_text()
helpers=[]; assertions=[]
for f in unit.forms:
 if isinstance(f,l.Lst) and isinstance(f.items[0],l.Atom):
  if f.items[0].low=='defun': helpers.append(unit.text[f.start:f.end])
  elif f.items[0].low=='assert-event': assertions.append('(assert '+unit.text[f.items[1].start:f.items[1].end]+')')
m=l.match('(defun fn2-concrete-loop-stop-p ?args ?*body)',stop.forms,deep=False)
assert len(m)==1
f=m[0].node
args=stop.text[f.items[2].start:f.items[2].end]
body='\n'.join(stop.text[x.start:x.end] for x in f.items[3:] if not (isinstance(x,l.Lst) and x.items[0].low=='declare'))
rawcontrol=control[control.index('(let ((original'):control.index('(sb-ext:exit')]
text='(in-package "ACL2")\n(include-book "books/host-boundary")\n'+ '\n'.join(helpers)+'\n(set-guard-checking nil)\n:q\n'
text+='(let ((saved-stop (symbol-function \'fn2-concrete-loop-stop-p)))\n (unwind-protect\n (progn\n'
text+='(assert (equal (fn2-progress-clock-test 1 t 8) (list t (make-list 8 :initial-element \'(t :more 1 0 0 (0 2) (0 2) t)))))\n'
text+='(setf (symbol-function \'fn2-concrete-loop-stop-p) (lambda '+args+'\n'+body+'))\n'
text+='\n'.join(assertions)+'\n'+rawcontrol+'\n'
text+='(format t "PROGRESS A RAW exact-source-stop whole-antecedent/fuel controls PASS~%"))\n(setf (symbol-function \'fn2-concrete-loop-stop-p) saved-stop)))\n(sb-ext:exit :code 0)\n'
prelude, raw = text.split(':q\n', 1)
raw = raw.replace('(sb-ext:exit :code 0)', '')
text = (prelude + ':q\n(handler-case\n (progn\n' + raw
        + '\n (sb-ext:exit :code 0))\n'
        + ' (cl:error (condition) (format t \"PROGRESS CONTROL ERROR ~A~%\" condition)'
        + ' (sb-ext:exit :code 1)))\n')
sys.stdout.write(text)
