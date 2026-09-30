#!/usr/bin/env python3
"""Proof-only executive composition from actual abstract-stobj export selectors.

No host executes this model. The generated concrete calls are the real
executives selected by the existing WIN/TAB exports; correspondence and
capacity bounds must be proved before any source/funding claim.
"""
from pathlib import Path
import argparse, hashlib
from ledger import Sym, read_forms
from payload_profile_trace import sexp
ROOT=Path(__file__).resolve().parents[1]
SOURCE='books/deflate-inflate.lisp'

def export_map(forms):
 maps={};expected={'fn-zin-win','fn-zin-tab','fn-zin-out'};seen=set()
 for f in forms:
  if isinstance(f,list) and f and str(f[0])=='defabsstobj' and str(f[1]) in expected:
   name=str(f[1])
   if name in seen:raise ValueError('duplicate buffer declaration')
   seen.add(name)
   if f[f.index(Sym(':foundation'))+1]!=Sym('fn-octets$c'):raise ValueError('changed buffer foundation')
   for entry in f[f.index(Sym(':exports'))+1]:
    if Sym(':exec') not in entry:raise ValueError('missing explicit executive selector')
    maps[str(entry[0])]=entry[entry.index(Sym(':exec'))+1]
 if seen!=expected:raise ValueError('missing buffer declaration')
 return maps

def generate():
 p=ROOT/SOURCE;forms=read_forms(p.read_text());defs={str(f[1]):f for f in forms if isinstance(f,list) and f and str(f[0])=='defun'}
 maps=export_map(forms)
 selected=defs['fn-zin-payload-ready'];variables={'fn-zin-win':Sym('cwin'),'fn-zin-tab':Sym('ctab'),'fn-zin-out':Sym('cout')}
 maps['fn-zin-payload-ready']=Sym('fn-piwc-payload-ready')
 more=read_forms((ROOT/'books/payload-window.lisp').read_text())
 init=next(f for f in more if isinstance(f,list) and f and str(f[0])=='defun' and str(f[1])=='fn-pzw-initialize')
 extra=[]
 for rel,orig,target in [('books/extent-window-compressed.lisp','fn-ewz-begin','fn-piwc-ewz-begin'),('books/decoded-window-begin.lisp','fn-pwz-begin','fn-piwc-begin')]:
  fs=read_forms((ROOT/rel).read_text())
  source=next(f for f in fs if isinstance(f,list) and f and str(f[0])=='defun' and str(f[1])==orig)
  extra.append((rel,source,target));maps[orig]=Sym(target)
 maps['fn-pzw-initialize']=Sym('fn-piwc-initialize')
 def walk(x):
  if isinstance(x,list):return [walk(y) for y in x]
  if isinstance(x,Sym):return variables.get(str(x),maps.get(str(x),x))
  return x
 result=['; GENERATED proof-only composition by tools/decoded_window_buffer_exec.py.',
  '; '+SOURCE+' SHA256 '+hashlib.sha256(p.read_bytes()).hexdigest(),
  '; books/octets-stobj.lisp SHA256 '+hashlib.sha256((ROOT/'books/octets-stobj.lisp').read_bytes()).hexdigest(),
  '; books/payload-window.lisp SHA256 '+hashlib.sha256((ROOT/'books/payload-window.lisp').read_bytes()).hexdigest(),
  '(in-package "ACL2")','(include-book "decoded-window-initial-buffer-capacity")',
  '(defun-nx fn-piwc-payload-ready (dict cwin ctab)\n '+sexp(walk(selected[-1]))+')',
  '(defun-nx fn-piwc-initialize (dict fn-zin-st cwin ctab cout)\n '+sexp(walk(init[-1]))+')']
 for rel,source,target in extra:
  result.append('; '+rel+' SHA256 '+hashlib.sha256((ROOT/rel).read_bytes()).hexdigest())
  result.append('(defun-nx '+target+' '+sexp(walk(source[2]))+'\n '+sexp(walk(source[-1]))+')')
 return '\n\n'.join(result)+'\n'
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--write',action='store_true');p.add_argument('--check',action='store_true');a=p.parse_args();s=generate();out=ROOT/'books/decoded-window-initial-buffer-exec.lisp'
 if a.write:out.write_text(s)
 elif a.check:
  if not out.exists() or out.read_text()!=s:raise SystemExit('concrete buffer composition stale')
  print('concrete composition matches actual source and executive selectors')
 else:print(s,end='')
