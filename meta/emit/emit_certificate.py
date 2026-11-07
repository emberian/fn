#!/usr/bin/env python3
"""Propose certificates from the canonical package; ACL2 and Lean check them.
No Python result is a certificate. Run the generated book and Lean module.
"""
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).parent))
from emit_lean import Atom, Str, List, read_all, show, as_list, val, term, lean_str, ident
from emit_embed import Fn, emit_fn, emit_kinds, calls_of, NATIVE, SPECIAL, plist

sys.setrecursionlimit(30000)


def fields(xs):
    xs = list(xs)
    if len(xs) % 2 or len(set(map(str, xs[::2]))) != len(xs)//2:
        raise ValueError('odd or duplicate package fields')
    return dict(zip(map(str, xs[::2]), xs[1::2]))


def codes(x):
    ns = [int(n) for n in as_list(x)]
    if any(n < 0 or n > 255 for n in ns):
        raise ValueError('not an ACL2 character code')
    return ''.join(map(chr, ns))


def decode(x):
    tag, *xs = as_list(x)
    if tag == ':CONS' and len(xs) == 2:
        a, d = decode(xs[0]), decode(xs[1])
        if d == Atom('NIL'): return List([a])
        if isinstance(d, List): return List([a, *d])
        return List([a, Atom('.'), d])
    if tag == ':SYMBOL' and len(xs) == 2:
        pkg, name = codes(xs[0]), codes(xs[1])
        if pkg == 'KEYWORD': return Atom(':' + name)
        if pkg not in ('ACL2', 'COMMON-LISP'): raise ValueError('unsupported package ' + pkg)
        # Canonical identity is retained in the checked package. The existing Val
        # presentation uses the ACL2-imported spelling on this admitted world.
        if any(c.isspace() or c in '()|\\"' for c in name):
            raise ValueError('symbol outside the legacy Val presentation: ' + name)
        return Atom(name)
    if tag == ':INTEGER' and len(xs) == 1: return Atom(str(int(xs[0])))
    if tag == ':STRING' and len(xs) == 1: return Str(codes(xs[0]))
    if tag == ':CHARACTER' and len(xs) == 1:
        n = int(xs[0])
        if not 0 <= n < 256: raise ValueError('character outside ACL2')
        return Atom('#\\' + {10:'Newline', 13:'Return', 32:'Space', 9:'Tab'}.get(n, chr(n)))
    raise ValueError('object outside integer Val basis: ' + str(tag))


def fn_of(row):
    d = fields(row)
    name = decode(d[':FUNCTION'])
    j = decode(d[':JUSTIFICATION'])
    # The bridge's first closure is nonrecursive except guard dependencies; do
    # not guess recursive adequacy from the examples. Existing emitter handles
    # measures supplied explicitly by the printer below.
    f = List([name, Atom(':FORMALS'), decode(d[':FORMALS']),
              Atom(':BODY'), decode(d[':LOGICAL-BODY']),
              Atom(':GUARD'), decode(d[':GUARD']),
              Atom(':MEASURE'), Atom('NIL'), Atom(':RECURSIVE'), Atom('NIL')])
    return Fn(f), d


def body_certificate(fn, d, allf):
    name = fn.name
    callees = sorted(calls_of(fn.body, set()) - {'IF', 'RETURN-LAST'})
    sigs = ['(if a b c)', '(return-last a b c)']
    for c in callees:
        if c in allf: args = allf[c][0].formals
        else:
            arities = {'CONS':2, 'EQUAL':2, 'CAR':1, 'CDR':1, 'NTH':2, 'MV-NTH':2,
                       'UPDATE-NTH':3, '<':2, 'INTEGERP':1, 'BINARY-+':2, 'LEN':1,
                       'CONSP':1}
            if c not in arities: raise ValueError('no evaluator signature: ' + c)
            args = ['A'+str(i) for i in range(arities[c])]
        sigs.append('(' + c + ' ' + ' '.join(args) + ')')
    ev = name + '-EXPORT-EVAL'
    env = '(list ' + ' '.join("(cons '" + a + ' ' + a + ')' for a in fn.formals) + ')'
    return [f"(fn2-tv-check-function '{show(List(sum(([Atom(k),v] for k,v in d.items()), [])))} '{name})",
            f"(defevaluator {ev} {ev}-LIST ({' '.join(sigs)}))",
            f"(defthm {name}-EXPORT-BODY\n  (equal ({ev} '{show(fn.body)} {env})\n         ({name} {' '.join(fn.formals)}))\n  :rule-classes nil\n  :hints ((\"Goal\" :in-theory (enable {name}))))"]


def main(src, outdir):
    top = as_list(read_all(Path(src).read_text(newline='') if False else open(src, newline='').read())[0])
    if top[0] != ':FN2-CERTIFICATE': raise ValueError('wrong package tag')
    p = fields(top[1:])
    if str(p[':VERSION']) != '1': raise ValueError('unsupported version')
    if as_list(p[':REFUSED']): raise ValueError('unresolved roots')
    out = Path(outdir); out.mkdir(parents=True, exist_ok=True)
    functions = [fn_of(as_list(r)) for r in as_list(p[':FUNCTIONS'])]
    allf = {f.name:(f,d) for f,d in functions}
    # Only the nonrecursive BODY closure is claimed. Guards, measures and other
    # exported roots remain in the package, explicitly outside this certificate.
    roots = ['FN2-ECHO-RUN-FREE', 'FN2-ECHO-RUN-FREE-CHILDREN']
    want = set()
    def visit(n):
        if n in NATIVE or n in SPECIAL or n in want: return
        want.add(n)
        f,d = allf[n]
        if n in calls_of(f.body, set()): raise ValueError('recursive body needs loop certificate: ' + n)
        for c in calls_of(f.body, set()): visit(c)
    for r in roots: visit(r)
    # Include row readers for the independently read arm interpreter.
    kd = decode(p[':KIND'])
    k = plist(kd[1:])
    for col in as_list(k[':COLUMNS']):
        n = str(col[0]); prefix = 'FN2-MACHINES' if n in ['READY-PREV','READY-NEXT','WAIT-REASON'] else 'FN2-ECHO'
        visit(prefix + '-' + n)
    visit('FN2-MACHINE-SLOT')
    fs = [(f,d) for f,d in functions if f.name in want]
    L = ['-- Generated from the canonical ACL2 export. Checked by the Lean kernel.',
         'import Fn2.ACL2.Translation', 'set_option maxRecDepth 100000',
         'set_option maxHeartbeats 0', 'set_option linter.unusedVariables false',
         'namespace Fn2.Instances.BridgeWorld', 'open Fn2.ACL2']
    defined = set()
    for f,d in fs:
        emit_fn(f, defined, L); defined.add(f.name)
    L += ['def fns : Fns', *[f'  | {lean_str(f.name)}, [{", ".join(ident(a) for a in f.formals)}] => some ({ident(f.name)} {" ".join(ident(a) for a in f.formals)})' for f,d in fs],
          '  | _, _ => none', 'end Fn2.Instances.BridgeWorld', '']
    (out/'BridgeWorld.lean').write_text('\n'.join(L))
    constants = decode(p[':CONSTANTS'])
    # Reuse the old presentation only after lossless decoding of the canonical
    # objects. The original decl remains data and Arms.read reads it itself.
    manifest = fields(as_list(p[':MANIFEST']))
    layout = decode(manifest[':CORE-LAYOUT'])[1]
    tuple_ = List([r[1] for r in layout])
    emb = {':KINDS': List([kd]), ':OPERATIONS':List([]), ':CONSTANTS':constants, ':CORE-TUPLE':tuple_}
    emit_kinds(emb, [], out/'BridgeKinds.lean', 'Fn2.Instances.BridgeKinds', 'Fn2.Instances.BridgeWorld', {})
    C = ['(in-package "ACL2")', '(include-book "../../books/assembly-callbacks-a")',
         '(include-book "../../books/translation-validation")',
         f"(fn2-tv-check-manifest '{show(p[':MANIFEST'])})"]
    for f,d in fs:
        C += body_certificate(f,d,allf)
    (out/'bridge-body.lisp').write_text('\n\n'.join(C)+'\n')
    print('CERTIFICATE PROPOSAL', len(fs), 'body equations;', len(functions)-len(fs), 'exported functions unvalidated')
    for f,d in fs:
        print(f.name, show(f.body)[:120])

if __name__ == '__main__': main(*sys.argv[1:])
