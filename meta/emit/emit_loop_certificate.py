#!/usr/bin/env python3
"""Canonical, tail-recursive loop certificate proposer; both kernels judge it."""
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).parent))
from emit_certificate import *

ROOT = 'FN2-POOL-COMPARE-LOOP'

def tail(t, defined):
    if isinstance(t,List) and t:
        if t[0] == 'IF':
            return f'(if ({shallow(t[1],defined)}).truthy then {tail(t[2],defined)} else {tail(t[3],defined)})'
        if t[0] == 'RETURN-LAST': return tail(t[3],defined)
        if is_lambda(t[0]):
            bs=' '.join(f'({ident(str(v))} : Val)' for v in t[0][1])
            vs=' '.join(shallow(x,defined) for x in t[1:])
            return f'((fun {bs} => {tail(t[0][2],defined)}) {vs})'
        if t[0] == ROOT:
            return '(.inr ('+', '.join(shallow(x,defined) for x in t[1:])+'))'
    if ROOT in calls_of(t,set()): raise ValueError('recursive call outside a tail position')
    return '(.inl '+shallow(t,defined)+')'

def replace_rec(t):
    if not isinstance(t,List) or not t: return t
    if t[0] == 'QUOTE': return t
    if t[0] == ROOT:
        return List([Atom('FN2-TV-POOL-COMPARE-FUEL'), List([Atom('BINARY-+'),List([Atom('QUOTE'),Atom('-1')]),Atom('FUEL')]), *[replace_rec(x) for x in t[1:]]])
    return List([replace_rec(x) for x in t])

def main(src):
    p=fields(read_canonical(open(src,newline='').read())[1:])
    allfs=[fn_of(r) for r in p[':FUNCTIONS']]; allf={f.name:(f,d) for f,d in allfs}
    want=set()
    def visit(n):
        if n in NATIVE or n in SPECIAL or n in want: return
        want.add(n);f,d=allf[n]
        if decode(d[':ATTACHMENT']) != Atom('NIL'): raise ValueError('attached loop callee '+n)
        cs=calls_of(f.body,set())
        if n in cs and n != ROOT: raise ValueError('another recursive callee '+n)
        for c in cs: visit(c)
    visit(ROOT)
    fs=[(f,d) for f,d in allfs if f.name in want]; f,d=allf[ROOT]
    if f.formals != ['A','B','I','N','FN2-POOL']: raise ValueError('changed loop signature')
    raw=shallow(f.body,want)
    template=Path(__file__).with_name('pool_compare.lean.in').read_text()
    template=template.replace('@STEP@',tail(f.body,want)).replace('@BODY@',raw)
    L=[template, 'namespace Fn2.ACL2.PoolCompare', 'open Fn2.ACL2 Fn2.Instances.LayerAWorld',
       'set_option maxRecDepth 100000', 'set_option maxHeartbeats 4000000',
       'def fns : Fns', *[f'  | {lean_str(x.name)}, [{", ".join(ident(a) for a in x.formals)}] => some ({ident(x.name)} {" ".join(ident(a) for a in x.formals)})' for x,_ in fs], '  | _, _ => none']
    for x,row in fs:
        bs=' '.join(f'({ident(a)} : Val)' for a in x.formals)
        args=' '.join(ident(a) for a in x.formals)
        env='['+', '.join(f'({lean_str(a)}, {ident(a)})' for a in x.formals)+']'
        L += [f'def {ident(x.name)}.canonicalBody : Translation.Object := {lean_object(row[":LOGICAL-BODY"])}',
              f'def {ident(x.name)}.body : Term := {term(x.body)}',
              f'theorem {ident(x.name)}.decoded : Translation.readTerm 512 {ident(x.name)}.canonicalBody = some {ident(x.name)}.body := by rfl',
              f'theorem {ident(x.name)}.canonical_body {bs} :',
              f'    Translation.evalExport 512 {ident(x.name)}.canonicalBody fns {env} = .ok ({ident(x.name)} {args}) := by',
              f'  simp only [Translation.evalExport, {ident(x.name)}.decoded]']
        if x.name == ROOT: L += ['  rw [← body_equation '+args+']']
        L += [f'  change Translation.eval fns {env} {term(x.body)} 512 = _',*expression_proof(x.body,want,{a:ident(a) for a in x.formals})]
    L += ['#print axioms certificate','#print axioms «FN2-POOL-COMPARE-LOOP».canonical_body','end Fn2.ACL2.PoolCompare','']
    Path('meta/Fn2/ACL2/PoolCompare.lean').write_text('\n'.join(L))
    C=['(in-package "ACL2")','(include-book "../../books/assembly-callbacks-a")',
       '(include-book "../../books/translation-validation")',
       evaluator_certificate(fs,allf).replace('FN2-EXPORT-EVAL','FN2-LOOP-EXPORT-EVAL')]
    for x,row in fs: C += [s.replace('FN2-EXPORT-EVAL','FN2-LOOP-EXPORT-EVAL') for s in body_certificate(x,row,allf)]
    C += [f'''(defun fn2-tv-pool-compare-fuel (fuel a b i n fn2-pool)
 (declare (xargs :stobjs fn2-pool :measure (nfix fuel) :verify-guards nil))
 (if (zp fuel) nil {show(replace_rec(f.body))}))''',
 '''(defthm fn2-tv-pool-compare-fuel-adequate
 (implies (< (nfix (- (nfix n) (nfix i))) (nfix fuel))
          (equal (fn2-tv-pool-compare-fuel fuel a b i n fn2-pool)
                 (fn2-pool-compare-loop a b i n fn2-pool)))
 :rule-classes nil
 :hints (("Goal" :induct (fn2-tv-pool-compare-fuel fuel a b i n fn2-pool)
                 :in-theory (enable fn2-tv-pool-compare-fuel fn2-pool-compare-loop))))''',
 '''(defthm fn2-tv-pool-compare-fuel-teeth
 (and (equal (fn2-tv-pool-compare-fuel 2 a a 0 1 fn2-pool) '(:equal 1))
      (equal (fn2-pool-compare-loop a a 0 1 fn2-pool) '(:equal 1))
      (not (equal (fn2-tv-pool-compare-fuel 1 a a 0 1 fn2-pool)
                  (fn2-pool-compare-loop a a 0 1 fn2-pool))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn2-tv-pool-compare-fuel fn2-pool-compare-loop))))''']
    Path('meta/emit/loop-body.lisp').write_text('\n\n'.join(C)+'\n')
    write_identity(src, 'meta/Fn2/Instances/loop-identity.json', p, fs, allf, want,
        'Pool comparison body closure; generic countdown existence and canonical body equality; primitive contracts in PrimitiveContracts')
    print('LOOP CERTIFICATE PROPOSAL',len(fs),'functions')

if __name__ == '__main__': main(sys.argv[1])
