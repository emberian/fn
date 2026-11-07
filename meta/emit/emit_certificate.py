#!/usr/bin/env python3
"""Propose certificates from the canonical package; ACL2 and Lean check them.
No Python result is a certificate. Run the generated book and Lean module.
"""
from pathlib import Path
import sys
import re
import hashlib
import json
import os
import subprocess
sys.path.insert(0, str(Path(__file__).parent))
from emit_lean import Atom, Str, List, read_all, show, as_list, val, term, lean_str, ident
from emit_embed import Fn, emit_fn, emit_kinds, calls_of, NATIVE, SPECIAL, plist, shallow, is_lambda

sys.setrecursionlimit(30000)


def read_canonical(text):
    """The transport contains only tags, integers and explicit lists.
    Scan iteratively: long cons spines must not consume Python's call stack.
    """
    stack = [List([])]
    for m in re.finditer(r"\(|\)|[^\s()]+", text):
        t = m.group()
        if t == '(':
            node = List([]); stack[-1].append(node); stack.append(node)
        elif t == ')':
            if len(stack) == 1: raise ValueError('unexpected close')
            stack.pop()
        else:
            if not re.fullmatch(r'NIL|:[A-Z0-9-]+|-?[0-9]+', t):
                raise ValueError('noncanonical transport atom: ' + t[:80])
            stack[-1].append(Atom(t))
    if len(stack) != 1 or len(stack[0]) != 1: raise ValueError('unbalanced package')
    return stack[0][0]


def canonical_text(x):
    chunks = []
    todo = [x]
    while todo:
        a = todo.pop()
        if isinstance(a, List):
            chunks.append('(')
            todo.append(')')
            for i in range(len(a)-1, -1, -1):
                todo.append(a[i])
                if i: todo.append(' ')
        else: chunks.append(str(a))
    return ''.join(chunks)


def fields(xs):
    xs = list(xs)
    if len(xs) % 2 or len(set(map(str, xs[::2]))) != len(xs)//2:
        raise ValueError('odd or duplicate package fields')
    return dict(zip(map(str, xs[::2]), xs[1::2]))


def object_list(x):
    """Project an exact canonical list without decoding its elements."""
    result = []
    while x[0] == ':CONS':
        if len(x) != 3: raise ValueError('malformed canonical cons')
        result.append(x[1]); x = x[2]
    if decode(x) != Atom('NIL'): raise ValueError('improper canonical list')
    return result


def object_fields(xs):
    if len(xs) % 2: raise ValueError('odd canonical property list')
    return fields(sum(([decode(k), v] for k,v in zip(xs[::2], xs[1::2])), []))


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


def lean_object(x):
    tag, *xs = as_list(x)
    if tag == ':CONS': return f'(.cons {lean_object(xs[0])} {lean_object(xs[1])})'
    if tag == ':SYMBOL': return f'(.symbol [{", ".join(map(str,as_list(xs[0])))}] [{", ".join(map(str,as_list(xs[1])))}])'
    if tag == ':INTEGER': return f'(.integer ({xs[0]}))'
    if tag == ':RATIONAL': return f'(.rational ({xs[0]}) {xs[1]})'
    if tag == ':COMPLEX': return f'(.complex {lean_object(xs[0])} {lean_object(xs[1])})'
    if tag == ':CHARACTER': return f'(.character {xs[0]})'
    if tag == ':STRING': return f'(.string [{", ".join(map(str,as_list(xs[0])))}])'
    raise ValueError('unknown canonical object ' + str(tag))


def expression_value(t, defined, env):
    if isinstance(t, List):
        if not t: return 'Val.nil'
        if t[0] == 'QUOTE': return val(t[1])
        if is_lambda(t[0]):
            names = [str(v) for v in as_list(t[0][1])]
            vals = [expression_value(a, defined, env) for a in t[1:]]
            return expression_value(t[0][2], defined, dict(zip(names, vals)))
        f = str(t[0]); args = [expression_value(a, defined, env) for a in t[1:]]
        if f == 'IF': return f'(if ({args[0]}).truthy then {args[1]} else {args[2]})'
        if f == 'RETURN-LAST': return args[2]
        return '(' + (NATIVE.get(f) or ident(f)) + ' ' + ' '.join(args) + ')'
    return env.get(str(t), val(t)) if str(t) not in env else env[str(t)]


def expression_proof(t, defined, env, indent='  '):
    """A structural proof proposal: calls use the concrete dispatch equation;
    the kernel's generic evaluation lemmas supply the composition."""
    def sub(x, e=env): return expression_proof(x, defined, e, indent+'  ')
    def args_proof(args, pad=None):
        pad = pad or indent+'  '
        if not args: return [pad+'rfl']
        return ([pad+'refine Translation.eval_args_cons ?_ ?_',pad+'·']
                + expression_proof(args[0],defined,env,pad+'  ')
                + [pad+'·'] + args_proof(args[1:],pad+'  '))
    if not isinstance(t,List) or not t or t[0] == 'QUOTE': return [indent+'rfl']
    if is_lambda(t[0]):
        names=[str(v) for v in as_list(t[0][1])]
        vals=[expression_value(a,defined,env) for a in t[1:]]
        return [indent+'refine Translation.eval_lam (vs := ['+', '.join(vals)+']) ?_ ?_',
                indent+'·']+args_proof(t[1:])+[indent+'·']+sub(t[0][2],dict(zip(names,vals)))
    if t[0] == 'IF':
        vs=[expression_value(a,defined,env) for a in t[1:]]
        lines=[indent+f'refine Translation.eval_if (vc := {vs[0]}) (va := {vs[1]}) (vb := {vs[2]}) ?_ ?_ ?_']
        for a in t[1:]: lines += [indent+'·']+sub(a)
        return lines
    if t[0] == 'RETURN-LAST':
        return [indent+'change Translation.eval _ _ '+term(t[3])+' _ = _']+expression_proof(t[3],defined,env,indent)
    vals=[expression_value(a,defined,env) for a in t[1:]]
    return [indent+'refine Translation.eval_app (vs := ['+', '.join(vals)+']) (by decide) (by decide) ?_ (by rfl)', indent+'·']+args_proof(t[1:])


def fn_of(row):
    d = fields(row)
    name = decode(d[':FUNCTION'])
    # Justification is retained exactly; only nonrecursive bodies are claimed.
    # The bridge's first closure is nonrecursive except guard dependencies; do
    # not guess recursive adequacy from the examples. Existing emitter handles
    # measures supplied explicitly by the printer below.
    f = List([name, Atom(':FORMALS'), decode(d[':FORMALS']),
              Atom(':BODY'), decode(d[':LOGICAL-BODY']),
              Atom(':GUARD'), decode(d[':GUARD']),
              Atom(':MEASURE'), Atom('NIL'), Atom(':RECURSIVE'), Atom('NIL')])
    return Fn(f), d


def evaluator_certificate(fs, allf):
    callees = sorted(set().union(*(calls_of(f.body, set()) for f,d in fs)) - {'IF', 'RETURN-LAST'})
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
    return f"(defevaluator FN2-EXPORT-EVAL FN2-EXPORT-EVAL-LIST ({' '.join(sigs)}))"


def body_certificate(fn, d, allf):
    name = fn.name
    ev = 'FN2-EXPORT-EVAL'
    env = '(list ' + ' '.join("(cons '" + a + ' ' + a + ')' for a in fn.formals) + ')'
    forms = [f"(fn2-tv-check-function '{canonical_text(List(sum(([Atom(k),v] for k,v in d.items()), [])))} '{name})"]
    body = "'" + show(fn.body)
    if name == 'FN2-ECHO-RUN-FREE':
        forms.append(f'(defconst *FN2-ECHO-RUN-FREE-EXPORTED-BODY* {body})')
        body = '*FN2-ECHO-RUN-FREE-EXPORTED-BODY*'
    return forms + [f"(defthm {name}-EXPORT-BODY\n  (equal ({ev} {body} {env})\n         ({name} {' '.join(fn.formals)}))\n  :rule-classes nil\n  :hints ((\"Goal\" :in-theory (enable {name}))))"]


def emit_echo_validation(kd, tuple_, out):
    """The instance schema is layout-parametric. Every child gets a variable;
    names and narrowing facts come from the canonical original declaration.
    """
    k = plist(kd[1:]); names = [str(x) for x in tuple_]
    n = len(names); own = names.index('FN2-ECHO'); directory = names.index('FN2-MACHINES')
    xs = ['c'+str(i) for i in range(n)]
    rows=[]; cols=[]; cases=[]
    for col in k[':COLUMNS']:
        c = str(col[0]); cols.append(c)
        d = c in ['READY-PREV','READY-NEXT','WAIT-REASON']
        f = ('FN2-MACHINES-' if d else 'FN2-ECHO-') + c
        rows.append(f'("ROW-{c}", {ident(f)} ' + (f'id c{directory}' if d else f'slot c{own}') + ')')
        cases.append(f'  | "{c}" => {ident(f)} ' + ('id dir' if d else 'slot own'))
    values = dict(CORE_SIZE=str(n), CORE_BINDERS=' '.join('('+x+' : Val)' for x in xs),
        CORE_VALUES='['+', '.join(xs)+']',
        IMAGE_ARGUMENTS=' '.join('(kids ⟨'+str(i)+', by decide⟩)' for i in range(n)),
        READ_DEFINITION='def echoRead (id slot own dir : Val) : String → Val\n'+'\n'.join(cases)+'\n  | _ => Val.nil\n',
        ROW_VALUES='['+', '.join(rows)+']', COLUMN_NAMES='['+', '.join(lean_str(c) for c in cols)+']',
        COLUMN_CASES=' | '.join(['rfl']*len(cols)),
        DIRECTORY_VALUE=f'c{directory}', OWN_VALUE=f'c{own}', DIRECTORY_INDEX=str(directory), OWN_INDEX=str(own))
    template = Path(__file__).with_name('echo_validation.lean.in').read_text()
    for key,value in values.items(): template=template.replace('@'+key+'@',value)
    if re.search(r'@[A-Z_]+@',template): raise ValueError('unexpanded certificate template')
    target = out.parent/'Arms'/'Validation.lean' if out.name == 'Instances' else out/'Validation.lean'
    target.parent.mkdir(parents=True,exist_ok=True)
    target.write_text(template)


def main(src, outdir, bookpath=None):
    top = as_list(read_canonical(open(src, newline='').read()))
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
        if str(f.body) in (':MISSING', 'NIL'):
            raise ValueError('no admitted logical body certificate: ' + n)
        if decode(d[':ATTACHMENT']) != Atom('NIL'):
            raise ValueError('attachment contract certificate required: ' + n)
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
    T = ['-- Generated body equations; the kernel checks every equation.',
         'import Fn2.Instances.BridgeWorld', 'set_option maxRecDepth 100000',
         'set_option maxHeartbeats 4000000', 'set_option linter.unusedVariables false',
         'namespace Fn2.Instances.BridgeWorld', 'open Fn2.ACL2']
    for f,d in fs:
        binders = ' '.join(f'({ident(a)} : Val)' for a in f.formals)
        args = ' '.join(ident(a) for a in f.formals)
        env = '[' + ', '.join(f'({lean_str(a)}, {ident(a)})' for a in f.formals) + ']'
        T += [f'def {ident(f.name)}.canonicalAttachment : Translation.Object := {lean_object(d[":ATTACHMENT"])}',
              f'theorem {ident(f.name)}.attachment_free : {ident(f.name)}.canonicalAttachment.value? = some Val.nil := by rfl',
              f'def {ident(f.name)}.canonicalBody : Translation.Object := {lean_object(d[":LOGICAL-BODY"])}',
              f'def {ident(f.name)}.body : Term := {term(f.body)}',
              f'theorem {ident(f.name)}.decoded : Translation.readTerm 512 {ident(f.name)}.canonicalBody = some {ident(f.name)}.body := by rfl',
              f'theorem {ident(f.name)}.export_body {binders} :',
              f'    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ {env} {ident(f.name)}.body 512 = .ok ({ident(f.name)} {args}) := by',
              f'  change Translation.eval fns {env} {term(f.body)} 512 = _',
              *expression_proof(f.body, defined, {a:ident(a) for a in f.formals}),
              f'theorem {ident(f.name)}.canonical_body {binders} :',
              f'    Translation.evalExport 512 {ident(f.name)}.canonicalBody fns {env} = .ok ({ident(f.name)} {args}) := by',
              f'  simp only [Translation.evalExport, {ident(f.name)}.decoded]',
              f'  exact {ident(f.name)}.export_body {args}', '']
    T += ['end Fn2.Instances.BridgeWorld', '']
    (out/'BridgeTranslation.lean').write_text('\n'.join(T))
    constants = decode(p[':CONSTANTS'])
    # Reuse the old presentation only after lossless decoding of the canonical
    # objects. The original decl remains data and Arms.read reads it itself.
    manifest = fields(as_list(p[':MANIFEST']))
    layout = decode(manifest[':CORE-LAYOUT'])[1]
    tuple_ = List([r[1] for r in layout])
    emb = {':KINDS': List([kd]), ':OPERATIONS':List([]), ':CONSTANTS':constants, ':CORE-TUPLE':tuple_}
    emit_kinds(emb, [], out/'BridgeKinds.lean', 'Fn2.Instances.BridgeKinds', 'Fn2.Instances.BridgeWorld', {})
    canonical_kind = object_fields(object_list(p[':KIND'])[1:])
    first_arm = object_list(canonical_kind[':ARMS'])[0]
    arm_fields = object_fields(object_list(first_arm)[1:])
    declaration = arm_fields[':DECL']
    # These equations bind the independently read arm and complete layout to
    # canonical objects. The same declaration is checked against the live world.
    path = out/'BridgeKinds.lean'
    extra = '\n'.join([
        f'def canonicalLayout : Translation.Object := {lean_object(manifest[":CORE-LAYOUT"])}',
        'theorem canonical_layout : Translation.readCoreLayout canonicalLayout = some coreTuple := by rfl',
        f'def canonicalFreeDeclaration : Translation.Object := {lean_object(declaration)}',
        'theorem canonical_free_declaration : canonicalFreeDeclaration.value? = some kinds.head!.arms.head!.decl := by rfl', ''])
    path.write_text(path.read_text().replace('end Fn2.Instances.BridgeKinds', extra+'end Fn2.Instances.BridgeKinds'))
    emit_echo_validation(kd, tuple_, out)
    C = ['(in-package "ACL2")', '(include-book "../../books/assembly-callbacks-a")',
         '(include-book "../../books/translation-validation")',
         f"(fn2-tv-check-manifest '{canonical_text(p[':MANIFEST'])})",
         f'''(make-event
 (if (equal '{show(decode(declaration))}
            (cdr (assoc-eq :free (fn2-machine-declared 'fn2-echo :arms (w state)))))
     '(value-triple :export-matches-live-declaration)
   (er soft 'fn2-tv-check-declaration "Export differs from the live FREE declaration.")))''']
    C.append(evaluator_certificate(fs, allf))
    for f,d in fs:
        C += body_certificate(f,d,allf)
    Path(bookpath or out/'bridge-body.lisp').write_text('\n\n'.join(C)+'\n')
    root = Path(__file__).resolve().parents[2]
    tracked = sorted(root.glob('books/*.lisp')) + sorted((root/'meta').rglob('*.lean'))
    tracked += sorted((root/'meta/emit').glob('*.py')) + sorted((root/'meta/emit').glob('*.in'))
    tracked += [root/'meta/emit/print-world.lisp', root/'meta/emit/print-certificate.lsp',
                root/'meta/emit/bridge-body.lisp', root/'meta/emit/emit.sh']
    digest = lambda b: hashlib.sha256(b).hexdigest()
    try:
        revision = subprocess.check_output(['git','-C',str(root),'rev-parse','HEAD'], text=True, stderr=subprocess.DEVNULL).strip()
    except subprocess.CalledProcessError:
        revision = os.environ.get('FN2_EMIT_SRC', 'unrecorded')
    identity = dict(format=1, source=revision,
        source_files={str(p.relative_to(root)):digest(p.read_bytes()) for p in tracked},
        package_sha256=digest(Path(src).read_bytes()),
        lean_toolchain=(root/'meta/lean-toolchain').read_text().strip(),
        mathlib_manifest_sha256=digest((root/'meta/lake-manifest.json').read_bytes()),
        acl2_toolchain=json.loads(os.environ.get('FN2_ACL2_IDENTITY', '"UNRECORDED"')),
        exporting_runtime=[str(x) for x in decode(p[':TOOLCHAIN'])] if ':TOOLCHAIN' in p else 'UNRECORDED',
        validated_body_candidates=sorted(want),
        unvalidated_functions=sorted(set(allf)-want),
        absent_guard_properties=sorted(f.name for f,d in fs if str(f.guard) == ':MISSING'),
        guard_policy='Preserved exactly; equations are unconditional, no absent guard is interpreted as true',
        primitive_basis=sorted(set().union(*(calls_of(f.body,set()) for f,d in fs)) & set(NATIVE)),
        primitive_domain_obligations={
            'representation': 'Integer Val, ACL2/COMMON-LISP imported names and KEYWORD names; no rational or complex lowering',
            'trusted_correspondence': 'CONS EQUAL INTEGERP < NTH MV-NTH UPDATE-NTH retain the existing ACL2/Val primitive correspondence',
            'scope': 'No recursive body, ASH, division, string conversion or attached executable is certified by this instance'},
        status='PROPOSED: certify bridge-body.lisp and build BridgeTranslation/Arms.Validation')
    (out/'bridge-identity.json').write_text(json.dumps(identity,indent=2)+'\n')
    print('CERTIFICATE PROPOSAL', len(fs), 'body equations;', len(functions)-len(fs), 'exported functions unvalidated')
    for f,d in fs:
        print(f.name, show(f.body)[:120])

if __name__ == '__main__': main(*sys.argv[1:])
