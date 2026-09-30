#!/usr/bin/env python3
"""Generate branch-sensitive logical instrumentation from trusted parser source.
The observer's own allocations are excluded. This is not compiler adequacy.
"""
from pathlib import Path
import argparse
import hashlib
from ledger import Sym, read_forms
ROOT = Path(__file__).resolve().parents[1]

def sexp(x):
    if isinstance(x, list): return '('+' '.join(map(sexp,x))+')'
    if isinstance(x, Sym): return str(x)
    if isinstance(x, str): return '"'+x.replace('\\','\\\\').replace('"','\\"')+'"'
    return str(x)

class Instrument:
    def __init__(self, names):
        self.names, self.serial = names, 0
    def fresh(self):
        self.serial += 1
        return f'lpt-tmp-{self.serial}'
    def bind(self, exprs, continuation):
        def go(i, values, traces):
            if i == len(exprs): return continuation(values, traces)
            var = self.fresh()
            return f'(let (({var} {self.expr(exprs[i])})) {go(i+1, values+[f"(car {var})"], traces+[f"(cdr {var})"])})'
        return go(0, [], [])
    def combine(self, traces):
        if not traces: return 'nil'
        if len(traces)==1: return traces[0]
        return '(append '+' '.join(traces)+')'
    def expr(self,x):
        if not isinstance(x,list) or not x: return f'(cons {sexp(x)} nil)'
        op = str(x[0]).lower()
        args = x[1:]
        if op == 'quote': return f'(cons {sexp(x)} nil)'
        if op == 'if':
            v=self.fresh(); branch=self.fresh()
            return f'(let* (({v} {self.expr(args[0])}) ({branch} (if (car {v}) {self.expr(args[1])} {self.expr(args[2])}))) (cons (car {branch}) (append (cdr {v}) (cdr {branch}))))'
        if op == 'cond':
            out=Sym('nil')
            for clause in reversed(args):
                if len(clause)!=2: raise ValueError('nonbinary cond')
                out=[Sym('if'),clause[0],clause[1],out]
            return self.expr(out)
        if op in ('and','or'):
            if not args: return self.expr(Sym('t' if op=='and' else 'nil'))
            if len(args)==1: return self.expr(args[0])
            var=self.fresh()
            branch=self.fresh()
            remainder=self.expr([Sym(op),*args[1:]])
            selected=f'(if (car {var}) {remainder} (cons nil nil))' if op=='and' else f'(if (car {var}) (cons (car {var}) nil) {remainder})'
            return f'(let* (({var} {self.expr(args[0])}) ({branch} {selected})) (cons (car {branch}) (append (cdr {var}) (cdr {branch}))))'
        if op in ('let','let*'):
            bindings,body=args
            if op=='let':
                def done(values,traces):
                    b=self.fresh()
                    return f'(let ({" ".join(f"({sexp(pair[0])} {value})" for pair,value in zip(bindings,values))}) (let (({b} {self.expr(body)})) (cons (car {b}) {self.combine(traces+[f"(cdr {b})"])})))'
                return self.bind([p[1] for p in bindings],done)
            if not bindings: return self.expr(body)
            first,*rest=bindings
            v=self.fresh(); b=self.fresh()
            tail=self.expr([Sym('let*'),rest,body])
            return f'(let* (({v} {self.expr(first[1])}) ({sexp(first[0])} (car {v})) ({b} {tail})) (cons (car {b}) (append (cdr {v}) (cdr {b}))))'
        def done(values,traces):
            if op in self.names:
                b=self.fresh()
                return f'(let (({b} ({self.names[op]} {" ".join(values)}))) (cons (car {b}) {self.combine(traces+[f"(cdr {b})"])}))'
            allowed={'+','-','1-','cons','list','zp','natp','integerp','nfix','<','<=','equal','eq','not','car','cdr','consp','fn-ag-car','fn-ag-cdr','fn-article-header-bytep','fn-article-vcharp','fn-article-wspp','fn-article-ftextp'}
            if op not in allowed: raise ValueError(f'unclassified source operation: {op}')
            site=self.fresh()
            call=f'({op} {" ".join(values)})'
            events=[]
            if op in ('cons','list'):
                count='1' if op=='cons' else str(len(values))
                events=[f'(list (list :constructor \'{op} {count} \'{site}))']
            elif op in ('+','-','1-'):
                events=[f'(list (list :signed \'{op} (list {" ".join(values)}) \'{site}))']
            else:
                events=[f'(list (list :borrow \'{op} \'{site}))']
            return f'(cons {call} {self.combine(traces+events)})'
        return self.bind(args,done)

def generate():
    source=ROOT/'books/legacy-parser-cursor.lisp'
    forms=read_forms(source.read_text())
    selected=[f for f in forms if isinstance(f,list) and f and str(f[0]).lower()=='defun' and str(f[1]).lower() not in ('fn-lpc-ready-p','fn-lpc-tick','fn-lpc-span-ready-p','fn-lpc-span-get')]
    article=read_forms((ROOT/'books/article.lisp').read_text())
    ascii_form=next(f for f in article if isinstance(f,list) and len(f)>1 and str(f[1]).lower()=='fn-article-ascii-downcase-byte')
    selected.insert(0,ascii_form)
    names={str(f[1]).lower():'fn-lpt-'+str(f[1]).lower().removeprefix('fn-lpc-').removeprefix('fn-article-') for f in selected}
    gen=Instrument(names)
    out=['; GENERATED by tools/legacy_parser_trace.py. Logical source events only.',f'; Cursor source SHA256 {hashlib.sha256(source.read_bytes()).hexdigest()}', f'; Article source SHA256 {hashlib.sha256((ROOT / "books/article.lisp").read_bytes()).hexdigest()}', '(in-package "ACL2")','(include-book "legacy-parser-cursor")']
    for f in selected:
        original=str(f[1]).lower(); name=names[original]; params=sexp(f[2]); body=f[-1]
        recursive=original in ('fn-lpc-at','fn-lpc-put')
        measure=' :measure (nfix i) :ruler-extenders :all' if recursive else ''
        observer=gen.expr(body)
        args=' '.join(map(sexp,f[2]))
        out.append(f'(defund {name} {params}\n (declare (xargs :verify-guards nil{measure}))\n (let ((lpt-answer {observer}))\n  (cons (car lpt-answer) (cons (list :enter \'{original})\n    (append (cdr lpt-answer) (list (list :leave \'{original})))))))')
        induction=f' :induct ({name} {args})' if recursive else ''
        disabled=' '.join(n for n in names if n != original)+' fn-article-ftextp fn-article-wspp fn-article-vcharp fn-article-header-bytep fn-ag-car fn-ag-cdr binary-append'
        out.append(f'(defthm {name}-value-projection\n (equal (car ({name} {args})) ({original} {args}))\n :hints (("Goal"{induction} :do-not \'(preprocess) :in-theory (e/d ({name} {original}) ({disabled})))))')
    return '\n\n'.join(out)+'\n'

if __name__=='__main__':
    p=argparse.ArgumentParser(); p.add_argument('--write',action='store_true'); a=p.parse_args()
    output=generate()
    if a.write: (ROOT/'books/legacy-parser-trace.lisp').write_text(output)
    else: print(output,end='')
