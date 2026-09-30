#!/usr/bin/env python3
"""Actual selected buffer source events; proof observer, not allocator pricing."""
from pathlib import Path
import argparse, hashlib
from ledger import Sym, read_forms
from payload_profile_trace import sexp
from decoded_window_initial_trace import InitialInstrument
ROOT=Path(__file__).resolve().parents[1]
SOURCES=('books/octets-stobj.lisp','books/decoded-window-initial-buffer-exec.lisp')
SELECTED=('fn-octets$c-clear','fn-octets$c-reserve','fn-octets$c-append-octet',
 'fn-oct-back-loop','fn-oct-write-list','fn-octets$c-append-back',
 'fn-piwc-payload-ready','fn-piwc-initialize','fn-piwc-ewz-begin','fn-piwc-begin')
BORROWED=frozenset(('fn-octets$c-buf-length','fn-octets$c-fill','fn-octets$c-bufi',
 'fn-zin-reset','fn-zin-set','fn-pwz-nth','fn-pwz-dictionary','fn-ews-begin',
 'fn-ewz-state','fn-pzd-budget','fn-pzw-stored-admissiblep','mbt','atom','car','cdr'))
class BufferInstrument(InitialInstrument):
 def expr(self,x):
  if isinstance(x,list) and x and str(x[0]) in BORROWED|{'resize-fn-octets$c-buf','update-fn-octets$c-bufi','update-fn-octets$c-fill'}:
   op=str(x[0])
   def done(values,traces):
    site=self.fresh()
    kind={'resize-fn-octets$c-buf':':array-resize','update-fn-octets$c-bufi':':array-write','update-fn-octets$c-fill':':fill-write'}.get(op,':borrow')
    event=f"(list (list {kind} '{op} (list {' '.join(values)}) '{site}))"
    return f'(cons ({op} {" ".join(values)}) {self.combine(traces+[event])})'
   return self.bind(x[1:],done)
  return super().expr(x)
def generate():
 defs={};headers=['; GENERATED actual executive source trace; observer conses are not target allocations.']
 for rel in SOURCES:
  p=ROOT/rel;headers.append('; '+rel+' SHA256 '+hashlib.sha256(p.read_bytes()).hexdigest())
  for f in read_forms(p.read_text()):
   if isinstance(f,list) and f and str(f[0]) in ('defun','defun-nx'):defs[str(f[1])]=f
 names={n:'fn-pib-'+n.removeprefix('fn-') for n in SELECTED};gen=BufferInstrument(names)
 out=headers+['(in-package "ACL2")','(include-book "decoded-window-initial-buffer-refinement")']
 introduced=[]
 for orig in SELECTED:
  f=defs[orig];name=names[orig];params=sexp(f[2]);args=' '.join(map(sexp,f[2]));decl=''
  if orig=='fn-oct-back-loop':decl=' (declare (xargs :measure (nfix (- (nfix end) (nfix dst))) :ruler-extenders :all))'
  if orig=='fn-oct-write-list':decl=' (declare (xargs :measure (len xs) :ruler-extenders :all))'
  out.append(f'(defun-nx {name} {params}\n{decl}\n {gen.expr(f[-1])})');introduced.append(name)
  disabled=' '.join(sorted(set(SELECTED+tuple(introduced)+tuple(BORROWED)+('binary-append',)+(('nfix',) if orig=='fn-piwc-begin' else ()))- {name,orig,"mbt"}))
  hint=f':induct ({orig} {args})' if orig in ('fn-oct-back-loop','fn-oct-write-list') else ":do-not '(preprocess)"
  out.append(f'(defthm {name}-value-and-effects-projection\n (equal (car ({name} {args})) ({orig} {args}))\n :hints (("Goal" {hint} :in-theory (e/d ({name} {orig}) ({disabled})))))')
  out.append(f'(in-theory (disable {name}))')
 return '\n\n'.join(out)+'\n'
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--write',action='store_true');p.add_argument('--check',action='store_true');a=p.parse_args();s=generate();out=ROOT/'books/decoded-window-initial-buffer-trace.lisp'
 if a.write:out.write_text(s)
 elif a.check:
  if not out.exists() or out.read_text()!=s:raise SystemExit('actual buffer source observer stale')
  print('actual buffer source observer matches selected source')
 else:print(s,end='')
