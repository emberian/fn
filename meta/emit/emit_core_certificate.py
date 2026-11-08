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

def main(src):
    p=fields(read_canonical(open(src,newline='').read())[1:])
    if as_list(p[':REFUSED']):raise ValueError('unresolved export roots')
    allfs=[fn_of(r) for r in p[':FUNCTIONS']]; allf={f.name:(f,d) for f,d in allfs}
    want=set()
    def visit(n):
        if n in NATIVE or n in SPECIAL or n in want:return
        want.add(n);f,d=allf[n]
        if decode(d[':ATTACHMENT'])!=Atom('NIL'):raise ValueError('attached core callee '+n)
        cs=calls_of(f.body,set())
        if n in cs and n!='MEMBER-EQ-EXEC':raise ValueError('recursive core callee '+n)
        for c in cs:visit(c)
    for r in ROOTS:visit(r)
    for op in decode(p[':OPERATIONS']):
        child=plist(op[1:])[':CALLEE']
        visit(str(op[0] if str(child)=='NIL' else child))
    kd=decode(p[':KIND']); k=plist(kd[1:])
    for col in k[':COLUMNS']:
        c=str(col[0]);pre='FN2-MACHINES' if c in ['READY-PREV','READY-NEXT','WAIT-REASON'] else 'FN2-CNS'
        visit(pre+'-'+c);visit(pre+'-SET-'+c)
    for r in ['FN2-CNS-ROWS','FN2-MACHINES-ROWS','FN2-MACHINE-SLOT','FN2-CONTROL-RECORD-STOP']:visit(r)
    fs=[(f,d)for f,d in allfs if f.name in want]
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

if __name__=='__main__':main(sys.argv[1])
