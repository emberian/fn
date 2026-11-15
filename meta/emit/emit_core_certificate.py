#!/usr/bin/env python3
"""Propose CNS core certificates from the live canonical package."""
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).parent))
from emit_certificate import *

ROOTS=['FN2-CNS-RUN-DRAINING','FN2-CNS-ON-READ-RESULT']

def conversion_proof(t, defined, env, names):
    """Congruence, never global rewriting by a possibly variable lambda body."""
    if not isinstance(t,List) or not t or t[0]=='QUOTE':return 'rfl'
    if t[0]=='RETURN-LAST':return conversion_proof(t[3],defined,env,names)
    args=t[1:]
    def application(vals):
        if is_lambda(t[0]):return '('+names[id(t)]+' '+' '.join(vals)+')'
        f=str(t[0])
        if f=='IF':return '(if ('+vals[0]+').truthy then '+vals[1]+' else '+vals[2]+')'
        return '('+(NATIVE.get(f) or ident(f))+' '+' '.join(vals)+')'
    current=[shallow(a,defined)for a in args]; proofs=[]
    if is_lambda(t[0]):proofs.append('('+names[id(t)]+'.unfolded '+' '.join(current)+')')
    for i,a in enumerate(args):
        cp=conversion_proof(a,defined,env,names)
        if cp=='rfl':continue
        vs=current[:];vs[i]='__arg'
        proofs.append('(congrArg (fun (__arg : Val) => '+application(vs)+') '+cp+')')
        current[i]=expression_value(a,defined,env,names)
    if not proofs:return 'rfl'
    result=proofs[0]
    for proof in proofs[1:]:result='('+result+'.trans '+proof+')'
    return result

def lambda_certificates(body, defined, prefix, fuel=512):
    """Check each lambda body once over fresh formals, retaining lexical sharing.

    Applying its checked equation avoids substituting a large branch/state into
    every variable occurrence in the next lambda's structural proof.
    """
    names={};lines=[]
    def walk(t, fuel):
        if not isinstance(t,List) or not t or t[0]=='QUOTE':return
        for a in t[1:]:walk(a,fuel-1)
        if not is_lambda(t[0]):return
        walk(t[0][2],fuel-1)
        fs=[str(x) for x in t[0][1]]
        n=ident(prefix+'-lambda-'+str(len(names)))
        env={a:ident(a) for a in fs};bs=' '.join('('+ident(a)+' : Val)'for a in fs)
        av=' '.join(ident(a)for a in fs)
        e='['+', '.join('('+lean_str(a)+', '+ident(a)+')'for a in fs)+']'
        lines.extend([f'def {n} {bs} : Val := {expression_value(t[0][2],defined,env,names)}',
          f'theorem {n}.unfolded {bs} : {shallow(t[0][2],defined)} = {n} {av} := by',
          '  unfold '+n,
          '  exact '+conversion_proof(t[0][2],defined,env,names),
          f'theorem {n}.eval {bs} :',
          f'    Translation.eval fns {e} {term(t[0][2])} {fuel-1} = .ok ({n} {av}) := by',
          '  unfold '+n,
          *expression_proof(t[0][2],defined,env,dispatch=defined,lambdas=names),
          'attribute [local irreducible] '+n])
        names[id(t)]=n
    walk(body,fuel)
    return names,lines

def inspect_core_certificate(src, roots=None, *, snapshot=None):
    """Read and select the existing core body closure without writing artifacts.

    Only the separately proved MEMBER-EQ-EXEC self recursion is admitted.
    Other direct or mutual recursion needs its own adequacy certificate.
    Returns packet, selected function rows, all function rows by name, selected
    names, and decoded kind, in the same order used by emission.
    """
    if snapshot is None:
        snapshot = Path(src).read_text()
    p=fields(read_canonical(snapshot)[1:])
    if as_list(p[':REFUSED']):raise ValueError('unresolved export roots')
    allfs=[fn_of(r) for r in p[':FUNCTIONS']]; allf={f.name:(f,d) for f,d in allfs}
    if len(allf) != len(allfs):raise ValueError('duplicate decoded canonical function subject')
    want=set();active=[]
    def visit(n):
        if n in NATIVE or n in SPECIAL:return
        if n in active:raise ValueError('mutually recursive core callees '+ ' -> '.join(active+[n]))
        if n in want:return
        if n not in allf:raise ValueError('missing core callee '+n)
        want.add(n);f,d=allf[n]
        if decode(d[':ATTACHMENT'])!=Atom('NIL'):raise ValueError('attached core callee '+n)
        cs=calls_of(f.body,set())
        if n in cs and n!='MEMBER-EQ-EXEC':raise ValueError('recursive core callee '+n)
        active.append(n)
        for c in sorted(cs):
            if c==n and n=='MEMBER-EQ-EXEC':continue
            visit(c)
        active.pop()
    for r in (ROOTS if roots is None else roots):visit(r)
    kd=decode(p[':KIND'])
    if roots is not None:
        if not roots:raise ValueError('empty selected core roots')
        fs=[(f,d)for f,d in allfs if f.name in want]
        return p,fs,allf,want,kd
    for op in decode(p[':OPERATIONS']):
        child=plist(op[1:])[':CALLEE']
        visit(str(op[0] if str(child)=='NIL' else child))
    kd=decode(p[':KIND']); k=plist(kd[1:])
    for col in k[':COLUMNS']:
        c=str(col[0]);pre='FN2-MACHINES' if c in ['READY-PREV','READY-NEXT','WAIT-REASON'] else 'FN2-CNS'
        visit(pre+'-'+c);visit(pre+'-SET-'+c)
    for r in ['FN2-CNS-ROWS','FN2-MACHINES-ROWS','FN2-MACHINE-SLOT','FN2-CONTROL-RECORD-STOP']:visit(r)
    fs=[(f,d)for f,d in allfs if f.name in want]
    return p,fs,allf,want,kd

MEMBER_DEFINITIONS = {
    'NOT': 'notDefinition', 'ATOM': 'atomDefinition', 'ENDP': 'endpDefinition',
    'EQ': 'eqDefinition', 'MEMBER-EQ-EXEC': 'memberDefinition',
}


def closed_member_book(src, roots, output, *, snapshot=None):
    """Propose current-world identity/closure checks, not semantic adequacy.

    Qualify ALL packet records, including guard and measure dependencies omitted
    from the Lean body program. The selected roots must be the packet's exact
    census: print with INCLUDE-CONTEXT NIL and no extra operation roots.
    """
    if snapshot is None:
        snapshot = Path(src).read_text()
    packet = read_canonical(snapshot)
    if not packet or packet[0] != ':FN2-CERTIFICATE':
        raise ValueError('scoped qualification requires FN2-CERTIFICATE packet')
    p = fields(packet[1:])
    if str(p.get(':VERSION')) != '1':
        raise ValueError('unsupported scoped packet version')
    for key in (':ROOTS', ':MANIFEST', ':NATIVES'):
        if key not in p:
            raise ValueError('scoped packet missing ' + key)
    packet_roots = [str(decode(x)) for x in p[':ROOTS']]
    if (not roots or len(set(roots)) != len(roots) or
            len(set(packet_roots)) != len(packet_roots) or
            set(packet_roots) != set(roots)):
        raise ValueError('explicit roots differ from scoped packet root census')
    # Same selector and rejection policy as the emitted Lean consumer.
    _, _, allf, _, _ = inspect_core_certificate(src, roots, snapshot=snapshot)
    if not set(roots) <= set(allf):
        raise ValueError('scoped root lacks exported function record')
    base = Path(__file__).resolve().parents[2]
    def include(name):
        rel = os.path.relpath(base / 'books' / name, Path(output).resolve().parent)
        return '(include-book "' + rel.replace('\\', '/').replace('"', '\\"') + '")'
    names = '(' + ' '.join(allf) + ')'
    natives = '(' + ' '.join(show(decode(x)) for x in p[':NATIVES']) + ')'
    lines = ['; PROPOSAL: certify at the current closure key before using as evidence.',
             '; Checks exported identity and closure only; no domain/MBE/attachment theorem.',
             '(in-package "ACL2")', include('assembly-callbacks-e-cns'),
             include('translation-validation'),
             "(fn2-tv-check-manifest '" + canonical_text(p[':MANIFEST']) + ')']
    for row in p[':FUNCTIONS']:
        d = fields(row)
        lines.append("(fn2-tv-check-function '" + canonical_text(row) +
                     " '" + show(decode(d[':FUNCTION'])) + ')')
    lines.append("""(make-event
 (let ((names '%s) (roots '%s) (natives '%s))
  (if (and (consp roots) (no-duplicatesp-eq roots)
           (no-duplicatesp-eq names) (subsetp-eq roots names)
           (no-duplicatesp-eq natives)
           (subsetp-eq natives *fn2-tv-native-boundary*)
           (subsetp-eq *fn2-tv-native-boundary* natives)
           (fn2-tv-closed-functions names (append names natives) (w state)))
      '(value-triple :scoped-export-identity-and-closure)
    (er soft 'scoped-core-export "Missing root/callee or changed native boundary."))))""" %
                 (names, '(' + ' '.join(roots) + ')', natives))
    return '\n\n'.join(lines) + '\n'


def closed_member_source(src, roots, *, snapshot=None):
    """Propose an exact-record recursive consumer; domain premises stay explicit.

    This is a Lean proposal, not packet qualification or a discharge of caller
    guards, primitive correspondence, selected attachments, or MBE equivalence.
    """
    _, _, allf, names, _ = inspect_core_certificate(src, roots, snapshot=snapshot)
    missing = set(MEMBER_DEFINITIONS) - names
    if missing:
        raise ValueError('member closure missing: ' + ', '.join(sorted(missing)))
    # Closed guard derivations use the same program as body derivations. Keep
    # guard/measure-only records instead of dropping them at body selection.
    fs = list(allf.values())
    for f, d in fs:
        dependencies = calls_of(f.body, set()) | calls_of(decode(d[':GUARD']), set())
        absent = dependencies - set(allf) - set(NATIVE) - set(SPECIAL)
        if absent:
            raise ValueError('missing canonical body/guard callees for ' + f.name + ': ' + ', '.join(sorted(absent)))
        if decode(d[':ATTACHMENT']) != Atom('NIL'):
            raise ValueError('attached canonical body/guard callee ' + f.name)
    lines = ['module', 'public import Fn2.ACL2.MemberBodyCorrect',
             '@[expose] public section', 'namespace Fn2.Instances.CoreCanonical',
             'open Fn2.ACL2 Fn2.ACL2.Translation',
             'def program : CanonicalProgram']
    for f, d in fs:
        fuel = 32 if f.name in MEMBER_DEFINITIONS else 512
        formals = '[' + ', '.join(lean_str(a) for a in f.formals) + ']'
        lines.append('  | ' + lean_str(f.name) + ' => some ⟨' + formals + ', ' +
                     lean_object(d[':LOGICAL-BODY']) + ', ' + str(fuel) + '⟩')
    lines += ['  | _ => none', 'def guards : CanonicalGuards']
    for f, d in fs:
        formals = '[' + ', '.join(lean_str(a) for a in f.formals) + ']'
        lines.append('  | ' + lean_str(f.name) + ' => some ⟨' + formals + ', ' +
                     lean_object(d[':GUARD']) + ', 512⟩')
    lines += ['  | _ => none',
              'theorem member_records : ∀ name definition,',
              '    MemberExecEvaluation.program name = some definition →',
              '    program name = some definition := by',
              '  apply MemberExecEvaluation.program_extension_of_lookups',
              *['  · rfl' for _ in MEMBER_DEFINITIONS],
              'theorem member_closed (domain primitiveDomain : CallDomain)',
              '    (calls : ∀ name values, MemberExecEvaluation.domain name values → domain name values)',
              '    (primitives : ∀ name values, MemberExecEvaluation.primitiveDomain name values → primitiveDomain name values)',
              '    (key : String) (xs : List Val) :',
              '    CanonicalExportEval program domain primitiveDomain "MEMBER-EQ-EXEC"',
              '      [.sym key, Val.ofList xs]',
              '      (LayerAWorld.«MEMBER-EQ-EXEC» (.sym key) (Val.ofList xs)) :=',
              '  MemberExecEvaluation.closed_in_program member_records calls primitives key xs',
              'theorem member_body_correct (domain primitiveDomain : CallDomain)',
              '    (calls : ∀ name values, MemberExecEvaluation.domain name values → domain name values)',
              '    (primitives : ∀ name values, MemberExecEvaluation.primitiveDomain name values → primitiveDomain name values)',
              '    (memberInputs : ∀ values, domain "MEMBER-EQ-EXEC" values → MemberExecEvaluation.domain "MEMBER-EQ-EXEC" values) :',
              '    CanonicalBodyCorrect program domain primitiveDomain LayerAWorld.fns "MEMBER-EQ-EXEC" MemberBodyCorrect.result :=',
              '  MemberBodyCorrect.body_correct_in_program member_records calls primitives memberInputs',
              '#print axioms member_records', '#print axioms member_closed', '#print axioms member_body_correct',
              'end Fn2.Instances.CoreCanonical', 'end', '']
    return '\n'.join(lines)


def main(src):
    p,fs,allf,want,kd=inspect_core_certificate(src)
    out=Path('meta/Fn2/Instances')
    L=['-- Canonical certificates use the actual emitted world and its checked dispatch equations.',
       'import Fn2.ACL2.Fuel','import Fn2.ACL2.Translation',
       *['import Fn2.Instances.LayerAEqns'+str(i) for i in range(1,5)],
       'set_option maxRecDepth 100000',
       'namespace Fn2.Instances.CoreWorld','open Fn2.ACL2 Fn2.Instances.LayerAWorld',
       'def fns : Fns := Fn2.Instances.LayerAWorld.fns',
       'end Fn2.Instances.CoreWorld','']
    L=L[:-2]
    L += ['private theorem native_prefixes : ∀ n ∈ nativeCallNames, n.startsWith "FN2-" = false := by decide +kernel',
      'theorem fn2_not_native (n : String) (h : n.startsWith "FN2-" = true) : nativeCallNames.contains n = false := by',
      '  apply Bool.eq_false_iff.mpr','  intro hm','  have hn : n ∈ nativeCallNames := by simpa using hm',
      '  have hf := native_prefixes n hn','  rw [h] at hf','  contradiction']
    for f,_ in fs:
        bs=' '.join(f'({ident(a)} : Val)'for a in f.formals)
        av=', '.join(ident(a)for a in f.formals);args=' '.join(ident(a)for a in f.formals)
        L += [f'theorem {ident(f.name)}.dispatched {{err : String}} {bs} :',
          f'    (match nativeCall {lean_str(f.name)} [{av}] with | some x => Except.ok x | none => match fns {lean_str(f.name)} [{av}] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.{ident(f.name)} {args}) := by',
          f'  simp only [nativeCall_none {lean_str(f.name)} [{av}] '+
            (f'(fn2_not_native {lean_str(f.name)} (by decide +kernel))' if f.name.startswith('FN2-') else '(by decide +kernel)')+
            f', fns, Fn2.Instances.LayerAWorld.{ident(f.name)}.fns_eq]']
    L += ['end Fn2.Instances.CoreWorld','']
    (out/'CoreWorld.lean').write_text(as_module('\n'.join(L), import_all=CORE_STRING_BODIES, bodies='scan'))
    f,d=allf['MEMBER-EQ-EXEC']
    T=['-- Generated canonical body certificates; every equation is kernel checked.',
       'import Fn2.Instances.CoreWorld','set_option maxRecDepth 100000','set_option maxHeartbeats 8000000',
       'set_option linter.unusedVariables false',
       'namespace Fn2.Instances.CoreWorld','open Fn2.ACL2 Fn2.Instances.LayerAWorld',
       f'def memberBody (X LST : Val) : Val := {shallow(f.body,want).replace("«X»","X").replace("«LST»","LST")}',
       '''theorem member_body_equation (x lst : Val) : memberBody x lst = «MEMBER-EQ-EXEC» x lst := by
  symm
  unfold memberBody
  rw [«MEMBER-EQ-EXEC», «MEMBER-EQ-EXEC».go]
  split
  · rfl
  · rename_i hc
    split
    · rfl
    · unfold «MEMBER-EQ-EXEC»
      have hd := Fn2.ACL2.Fuel.acl2Count_cdr_lt hc
      have hs := Fn2.ACL2.Fuel.member_eq_exec_fuel
        ((Val.int (Val.acl2Count lst.cdr)).nfix + 1)
        ((Val.int (Val.acl2Count lst)).nfix - ((Val.int (Val.acl2Count lst.cdr)).nfix + 1))
        x lst.cdr (by omega)
      simpa only [Nat.add_sub_of_le (by omega : (Val.int (Val.acl2Count lst.cdr)).nfix + 1 ≤ (Val.int (Val.acl2Count lst)).nfix)] using hs
''']
    T += ['attribute [local irreducible] '+ ' '.join('Fn2.Instances.LayerAWorld.'+ident(f.name) for f,d in fs)]
    for f,d in fs:
        bs=' '.join(f'({ident(a)} : Val)'for a in f.formals);args=' '.join(ident(a)for a in f.formals)
        env='['+', '.join(f'({lean_str(a)}, {ident(a)})'for a in f.formals)+']'
        lambdas,helpers=lambda_certificates(f.body,want,f.name)
        T += helpers
        T += [f'def {ident(f.name)}.canonicalAttachment : Translation.Object := {lean_object(d[":ATTACHMENT"])}',
              f'theorem {ident(f.name)}.attachment_free : {ident(f.name)}.canonicalAttachment.value? = some Val.nil := by rfl',
              f'def {ident(f.name)}.canonicalBody : Translation.Object := {lean_object(d[":LOGICAL-BODY"])}',
              f'def {ident(f.name)}.body : Term := {term(f.body)}',
              f'theorem {ident(f.name)}.decoded : Translation.readTerm 512 {ident(f.name)}.canonicalBody = some {ident(f.name)}.body := by rfl',
              f'theorem {ident(f.name)}.canonical_body {bs} :',
              f'    Translation.evalExport 512 {ident(f.name)}.canonicalBody fns {env} = .ok ({ident(f.name)} {args}) := by',
              f'  have hv : {ident(f.name)} {args} = {expression_value(f.body,want,{a:ident(a)for a in f.formals},lambdas)} := by']
        if f.name=='MEMBER-EQ-EXEC':T += ['    exact (member_body_equation '+args+').symm']
        else:T += ['    unfold Fn2.Instances.LayerAWorld.'+ident(f.name),
          '    exact '+conversion_proof(f.body,want,{a:ident(a)for a in f.formals},lambdas)]
        T += [f'  have evaluated : Translation.eval fns {env} {term(f.body)} 512 = .ok ({expression_value(f.body,want,{a:ident(a)for a in f.formals},lambdas)}) := by',
          *expression_proof(f.body,want,{a:ident(a)for a in f.formals},indent='    ',dispatch=want,lambdas=lambdas),
          f'  exact (Translation.evalExport_of_decoded_by_definition {ident(f.name)}.decoded evaluated).trans (congrArg Except.ok hv.symm)',
          f'#print axioms {ident(f.name)}.canonical_body']
    T += ['#print axioms «FN2-CNS-RUN-DRAINING».canonical_body','#print axioms «FN2-CNS-ON-READ-RESULT».canonical_body','end Fn2.Instances.CoreWorld','']
    (out/'CoreTranslation.lean').write_text(as_module('\n'.join(T), import_all=CORE_STRING_BODIES, bodies='scan'))
    manifest=fields(p[':MANIFEST']);layout=decode(manifest[':CORE-LAYOUT'])[1];tuple_=List([r[1] for r in layout])
    emb={':KINDS':List([kd]),':OPERATIONS':decode(p[':OPERATIONS']),':CONSTANTS':decode(p[':CONSTANTS']),':CORE-TUPLE':tuple_}
    emit_kinds(emb,[],out/'CoreKinds.lean','Fn2.Instances.CoreKinds','Fn2.Instances.CoreWorld',{})
    ck=object_fields(object_list(p[':KIND'])[1:]);ca=object_list(ck[':ARMS']);co=object_list(ck[':OBSERVES'])
    chosen=[('draining',':DRAINING',':arms',next(x for x in ca if str(decode(object_list(x)[0]))==':DRAINING')),
            ('readResult',':READ-RESULT',':observe-arms',next(x for x in co if str(decode(object_list(x)[0]))==':READ-RESULT'))]
    K=[f'def canonicalLayout : Translation.Object := {lean_object(manifest[":CORE-LAYOUT"])}',
       'theorem canonical_layout : Translation.readCoreLayout canonicalLayout = some coreTuple := by rfl',
       'def cns : Kind := kinds.head!']
    C=['(in-package "ACL2")','(include-book "../../books/assembly-callbacks-e-cns")','(include-book "../../books/translation-validation")',
       f"(fn2-tv-check-manifest '{canonical_text(p[':MANIFEST'])})"]
    for name,tag,key,entry in chosen:
        d=object_fields(object_list(entry)[1:]);i=(ca if key==':arms'else co).index(entry);part='arms'if key==':arms'else'observes'
        K += [f'def {name} : Arm := cns.{part}[{i}]!',f'def canonical_{name} : Translation.Object := {lean_object(d[":DECL"])}',
              f'theorem canonical_{name}_decoded : canonical_{name}.value? = some {name}.decl := by rfl']
        C += [f'''(make-event (if (equal '{show(decode(d[':DECL']))} (cdr (assoc-eq {tag} (fn2-machine-declared 'fn2-cns {key} (w state)))))
 '(value-triple :export-matches-live-declaration) (er soft 'core-export "Declaration differs.")))''']
    path=out/'CoreKinds.lean';path.write_text(path.read_text().replace('end Fn2.Instances.CoreKinds','\n'.join(K)+'\nend Fn2.Instances.CoreKinds'))
    for row in as_list(decode(p[':OPERATION-DECLARATIONS'])):
        C += [f'''(make-event (if (equal '{show(List(row[1:]))} (fn2-arms-op-row '{row[0]} (w state)))
 '(value-triple :export-matches-live-operation) (er soft 'core-export "Operation differs.")))''']
    C += [evaluator_certificate(fs,allf).replace('FN2-EXPORT-EVAL','FN2-CORE-EXPORT-EVAL')]
    for f,d in fs:C += [s.replace('FN2-EXPORT-EVAL','FN2-CORE-EXPORT-EVAL')for s in body_certificate(f,d,allf)]
    Path('meta/emit/core-body.lisp').write_text('\n\n'.join(C)+'\n')
    controls=Path(__file__).with_name('core_controls.lisp.in').read_text()
    row_body=allf['FN2-CNS-ROWS'][0].body
    if str(row_body[0])!='NTH' or str(row_body[1][0])!='QUOTE':raise ValueError('CNS rows is not a literal field')
    cv=dict(BODY_DEFINITIONS=' '.join('(:definition '+f.name+')' for f,_ in sorted(fs,key=lambda x:x[0].name)),
      BODY_EXECUTABLES=' '.join('(:executable-counterpart '+f.name+')' for f,_ in sorted(fs,key=lambda x:x[0].name)),
      OWN_INDEX=str(tuple_.index(Atom('FN2-CNS'))),DIRECTORY_INDEX=str(tuple_.index(Atom('FN2-MACHINES'))),
      CORE_SIZE=str(len(tuple_)),ROWS_INDEX=str(row_body[1][1]))
    for key,value in cv.items():controls=controls.replace('@'+key+'@',value)
    Path('tests/core-certificate-unit.lisp').write_text(controls)
    from emit_core_validation import emit_validation
    emit_validation(kd,tuple_,p[':FUNCTIONS'])
    write_identity(src,out/'core-identity.json',p,fs,allf,want,'CNS DRAINING and READ-RESULT body closure; MEMBER-EQ-EXEC measure adequacy; whole-core certificates separately checked')
    print('CORE CERTIFICATE PROPOSAL',len(fs),'functions; layout',len(tuple_))

def cli(argv=None):
    import argparse
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--inspect', action='store_true', help='inspect the selected closure without writing artifacts')
    parser.add_argument('--closed-member-output', type=Path, help='propose packet-bound closed MEMBER consumer; requires explicit roots and Lean checking')
    parser.add_argument('--closed-member-book', type=Path, help='also propose scoped ACL2 packet qualification book; requires --closed-member-output')
    parser.add_argument('--root', action='append', help='inspect only this explicit function body closure (repeatable)')
    parser.add_argument('source', help='canonical export packet')
    args=parser.parse_args(argv)
    if args.closed_member_book and not args.closed_member_output:
        parser.error('--closed-member-book requires --closed-member-output')
    if args.closed_member_output:
        if args.inspect or not args.root:
            parser.error('--closed-member-output requires explicit --root and cannot combine with --inspect')
        # One immutable raw snapshot binds both artifacts even if the pathname
        # is replaced during generation. All selectors consume this same snapshot.
        snapshot = Path(args.source).read_text()
        proposal = closed_member_source(args.source, args.root, snapshot=snapshot)
        book = closed_member_book(args.source, args.root, args.closed_member_book, snapshot=snapshot) if args.closed_member_book else None
        args.closed_member_output.write_text(proposal)
        if book is not None:
            args.closed_member_book.write_text(book)
        print('CLOSED MEMBER PROPOSAL (domain premises remain; kernel and current-world gates required)')
        return
    if args.root and not args.inspect:
        parser.error('--root currently requires --inspect; full core emission keeps its declared arm subjects')
    if args.inspect:
        _,fs,_,_,_=inspect_core_certificate(args.source, args.root) if args.root else inspect_core_certificate(args.source)
        print('CORE CERTIFICATE INSPECTION',len(fs),'functions (selection only; no kernel gates run)')
        for f,_ in fs:print(f.name)
    else:
        main(args.source)

if __name__=='__main__':cli()
