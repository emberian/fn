#!/usr/bin/env python3
"""Registry-wide certificate proposals. A generated file is never evidence.

The canonical stream has one header and one exact function record per line.
This bounds printer/reader memory without splitting a proof book or its closure.
All declared roots receive a contract; unsupported proof shapes remain named.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys
sys.path.insert(0, str(Path(__file__).parent))
from emit_certificate import *
from emit_embed import alist_value

BASE = Path(__file__).resolve().parents[2]

def digest(path):
    with open(path, 'rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()

def header(stream):
    h = read_canonical(stream.readline())
    if str(h[0]) != ':FN2-SERVED-CERTIFICATE':
        raise ValueError('expected canonical served package')
    p = fields(h[1:])
    if str(p[':VERSION']) != '2':
        raise ValueError('unsupported served package version')
    return p

def function_records(stream, count):
    names = set()
    for line in stream:
        row = read_canonical(line)
        d = fields(row)
        n = str(decode(d[':FUNCTION']))
        if n in names: raise ValueError('duplicate exported function ' + n)
        names.add(n)
        yield n, row, d
    if len(names) != count:
        raise ValueError(f'function count {len(names)} differs from header {count}')

def live_check(expected, actual):
    return ("(make-event (if (equal '"+show(expected)+' '+actual+")\n"
      " '(value-triple :served-metadata-matches-live-world)\n"
      " (er soft 'served-metadata \"Exported metadata differs from the live declaration.\")))\n")

def metadata_checks(p):
    """Bind the independently read declarations and all interpreter metadata.
    The inventory and manifest alone must not authenticate a second, unchecked
    copy of a declaration, operation signature or constant in the same packet.
    """
    checks=[live_check(List([decode(n) for n in as_list(p[':NATIVES'])]),'*fn2-tv-native-boundary*')]
    for kd in decode(p[':KINDS']):
        kn=str(kd[0]);k=plist(kd[1:]);child=str(k[':FORM'])==':CHILDREN'
        for field in [':STATES',':COLUMNS',':TABLE',':BUDGET']:
            checks.append(live_check(k[field],f"(fn2-machine-property '{kn} {field} (w state))"))
        for field in [':STOPS',':LINKS']:
            checks.append(live_check(k[field],f"(fn2-machine-declared '{kn} {field} (w state))"))
        checks.append(live_check(k[':TUPLE'],f"(fn2-arms-kind-tuple '{kn} (w state))" if child else "'(fn2-core)"))
        for phase,n in k[':PHASES']:
            checks.append(live_check(List([Atom('QUOTE'),n]),
              f"(getpropc (fn2-arms-phase-constant '{kn} '{phase}) 'const :missing (w state))"))
        for field,livefield,infix in [(':ARMS',':arms','-RUN-'),(':OBSERVES',':observe-arms','-ON-'),(':SUBARMS',':subarms','-SUB-')]:
            entries=as_list(k[field])
            original=List([List([e[0],*as_list(plist(e[1:])[':DECL'])]) for e in entries])
            checks.append(live_check(original,f"(fn2-machine-declared '{kn} {livefield} (w state))"))
            for e in entries:
                d=plist(e[1:]);fn=str(d[':FUNCTION'])
                name=f"(fn2-arms-fn-name '{kn} \"{infix}\" '{e[0]})"
                if child:name='(fn2-arms-child-name '+name+')'
                checks.append(live_check(d[':FUNCTION'],name))
                checks.append(live_check(d[':SIG'],f"(cdr (assoc-eq '{fn} (table-alist 'fn2-arms-child-sigs (w state))))"))
        first=as_list(k[':ARMS'])[0][0]
        checks.append(live_check(k[':FORM'],f'''(if (function-symbolp
          (fn2-arms-child-name (fn2-arms-fn-name '{kn} "-RUN-" '{first})) (w state)) :children :core)'''))
    for op in decode(p[':OPERATIONS']):
        name=str(op[0])
        actual=f"(let* ((world (w state)) (row (fn2-arms-op-row '{name} world)) (callee (fn2-decl-get :child row))) (list '{name} :callee callee"
        for field,prop in [(':FORMALS','formals'),(':STOBJS-IN','stobjs-in'),(':STOBJS-OUT','stobjs-out')]:
            actual+=f" {field} (and callee (getpropc callee '{prop} nil world))"
        for field in [':ANSWERS',':FAULTS',':DESCRIPTORS',':EFFECTS',':OWN-WRITES']:
            actual+=f' {field} (fn2-decl-get {field} row)'
        for field,prop in [(':CORE-FORMALS','formals'),(':CORE-STOBJS-IN','stobjs-in'),(':CORE-STOBJS-OUT','stobjs-out')]:
            actual+=f" {field} (and (not callee) (getpropc '{name} '{prop} nil world))"
        actual+=' :bound (list '+' '.join(f'(fn2-arms-bound (fn2-decl-get {f} row) nil world 8)' for f in [':bytes',':steps',':descriptors'])+')))'
        checks.append(live_check(op,actual))
    for row in decode(p[':OPERATION-DECLARATIONS']):
        checks.append(live_check(List(row[1:]),f"(fn2-arms-op-row '{row[0]} (w state))"))
    for row in decode(p[':CONSTANTS']):
        checks.append(live_check(List([Atom('QUOTE'),alist_value(row)]),f"(getpropc '{row[0]} 'const :missing (w state))"))
    checks.append(live_check(p[':WAITS'],"(fn2-tv-object (table-alist 'fn2-waits (w state)))"))
    for kn,area,tag,step,expanded in commit_words(p):
        actualtag='NIL' if str(area)==':SUBARMS' else str(tag)
        checks.append(f'''(make-event
 (mv-let (err expansion)
   (fn2-arms-commit-expand '{show(step)}
     (list :kind '{kn} :tag '{actualtag} :columns (fn2-machine-property '{kn} :columns (w state)) :world (w state)))
   (if (and (not err) (equal expansion '{show(expanded)}))
       '(value-triple :commit-expansion-matches-live-generator)
     (er soft 'served-commit "The live :commit expansion differs."))))
''')
    return ''.join(checks)

def commit_words(p):
    return as_list(decode(p[':COMMIT-WORDS'])) if ':COMMIT-WORDS' in p else []

def lean_metadata(p, out):
    manifest=fields(p[':MANIFEST'])
    lines=['import Fn2.Instances.ServedKinds','import Fn2.ACL2.Translation',
      'set_option maxRecDepth 100000','namespace Fn2.Instances.ServedMetadata',
      'open Fn2.ACL2 Fn2.Instances.ServedKinds',
      'def canonicalLayout : Translation.Object := '+lean_object(manifest[':CORE-LAYOUT']),
      'theorem complete_layout : Translation.readCoreLayout canonicalLayout = some coreTuple := by rfl']
    for ki,kd in enumerate(object_list(p[':KINDS'])):
        k=object_fields(object_list(kd)[1:])
        for field,part in [(':ARMS','arms'),(':SUBARMS','subarms'),(':OBSERVES','observes')]:
            for ai,arm in enumerate(object_list(k[field])):
                a=object_fields(object_list(arm)[1:]);n=f'kind{ki}_{part}{ai}'
                lines += ['def '+n+' : Translation.Object := '+lean_object(a[':DECL']),
                  f'theorem {n}_original : {n}.value? = some kinds[{ki}]!.{part}[{ai}]!.decl := by rfl']
        # Every child of a child-form tuple is retained, independently of narrowing.
        lines += [f'def tuple{ki} : Translation.Object := '+lean_object(k[':TUPLE']),
          f'theorem tuple{ki}_complete : tuple{ki}.value? = some (Val.ofList (kinds[{ki}]!.tuple.map Val.sym)) := by rfl']
    lines += ['#print axioms complete_layout','end Fn2.Instances.ServedMetadata','']
    out.write_text('\n'.join(lines))

def lean_commit_words(p,out):
    kinds=decode(p[':KINDS']);indices={str(k[0]):i for i,k in enumerate(kinds)}
    lines=['import Fn2.Instances.ServedMetadata','namespace Fn2.Instances.ServedCommit',
      'open Fn2.ACL2 Fn2.Arms Fn2.Instances.ServedKinds',
      'deriving instance DecidableEq for Except','set_option maxRecDepth 100000',
      'set_option maxHeartbeats 800000']
    for i,(kn,area,tag,step,expanded) in enumerate(commit_words(p)):
        ki=indices[str(kn)]
        actualtag='NIL' if str(area)==':SUBARMS' else str(tag)
        lines += [f'def word{i} : Val := '+val(step),f'def expansion{i} : Val := '+val(expanded),
          f'theorem word{i}_translation : Commit.expand',
          f'    {{tag := {lean_str(actualtag)}, phases := kinds[{ki}]!.states,',
          f'     tickets := kinds[{ki}]!.columns.filterMap (fun (n,t) => match t with | .uw 60 => some n | _ => none)}}',
          f'    word{i} = .ok expansion{i}.toList := by decide +kernel',f'#print axioms word{i}_translation']
    lines += ['end Fn2.Instances.ServedCommit',''];out.write_text('\n'.join(lines))

def call_proof(name, args, extra=''):
    av = '[' + ', '.join(args) + ']'
    return (f'simp only [{extra}callFn, world, nativeCall_none {lean_str(name)} {av} '
            f'(by decide +kernel), Fn2.Instances.LayerAWorld.{ident(name)}.fns_eq]')

def idle_certificate(kd, ki, ai, layout, consts, namespace):
    k = plist(kd[1:]); kn = str(kd[0]); a = plist(k[':ARMS'][ai][1:])
    if show(a[':DECL']) != '((:IDLE))': raise ValueError('not the idle proof shape')
    tag = str(k[':ARMS'][ai][0]).lstrip(':')
    core = kn+'-RUN-'+tag
    names = list(map(str, layout)); n = len(names)
    own, directory = names.index(kn), names.index('FN2-MACHINES')
    xs = ['c'+str(i) for i in range(n)]
    rows=[]; cases=[]; proofs=[]; cols=[]
    for col in k[':COLUMNS']:
        c = str(col[0]); cols.append(c)
        dr = c in ['READY-PREV','READY-NEXT','WAIT-REASON']
        fn = ('FN2-MACHINES' if dr else kn)+'-'+c
        args = ['id',xs[directory]] if dr else ['slot',xs[own]]
        rows.append('('+lean_str('ROW-'+c)+', '+ident(fn)+' '+' '.join(args)+')')
        cases.append('  | '+lean_str(c)+' => '+ident(fn)+(' id dir' if dr else ' slot own'))
        proofs += ['  · rw [callFn_core_plain _ _ _ _ (by decide +kernel)]',
          '    change callFn world '+lean_str(fn)+' ['+', '.join(args)+'] = .ok ('+ident(fn)+' '+' '.join(args)+')',
          '    '+call_proof(fn,args)]
    kind_number = str(consts['*'+kn+'-KIND*'])
    child = str(k[':FORM']) == ':CHILDREN'
    values = dict(NAMESPACE=namespace,KIND=kn,CORE_FUNCTION=core,
      KIND_INDEX=str(ki),ARM_INDEX=str(ai),KIND_NUMBER=kind_number,
      CHILD_UNFOLD=(ident(core+'-CHILDREN')+',') if child else '',
      CORE_SIZE=str(n),CORE_BINDERS=' '.join('('+x+' : Val)' for x in xs),
      CORE_VALUES='['+', '.join(xs)+']',
      IMAGE_ARGUMENTS=' '.join('(kids ⟨'+str(i)+', by decide⟩)' for i in range(n)),
      READ_DEFINITION='def echoRead (id slot own dir : Val) : String → Val\n'+'\n'.join(cases)+'\n  | _ => Val.nil\n',
      ROW_VALUES='['+', '.join(rows)+']',COLUMN_NAMES='['+', '.join(lean_str(c) for c in cols)+']',
      COLUMN_CASES=' | '.join(['rfl']*len(cols)),ROW_CALL_PROOFS='\n'.join(proofs),
      DIRECTORY_VALUE=xs[directory],OWN_VALUE=xs[own],DIRECTORY_INDEX=str(directory),OWN_INDEX=str(own),
      SNAPSHOT_CALL=call_proof(kn+'-SNAPSHOT-READ-CODE',['i','c'],'echoKind, '),
      SLOT_CALL=call_proof('FN2-MACHINE-SLOT',['i','c']),
      REFUSED_PROOF='simp only [refusedEntry, coreStop, const, world, consts, coreTuple, callFn, '+
        'nativeCall_none "FN2-CONTROL-RECORD-STOP" _ (by decide +kernel), '+
        'Fn2.Instances.LayerAWorld.«FN2-CONTROL-RECORD-STOP».fns_eq]; rfl')
    t=Path(__file__).with_name('idle_validation.lean.in').read_text()
    for key,v in values.items(): t=t.replace('@'+key+'@',v)
    if re.search(r'@[A-Z_]+@',t): raise ValueError('unexpanded proof parameter')
    return t

def whole_contract(kd, ki, area, ai, layout, name, namespace):
    """Universal, successful interpretation, including every core child.
    Subarms in child form use their complete tuple and the checked projection
    of the narrowed result; they do not have invented core entry wrappers.
    """
    k=plist(kd[1:]); part={':ARMS':'arms',':OBSERVE-ARMS':'observes',':SUBARMS':'subarms'}[area]
    observe=area==':OBSERVE-ARMS'
    vals=['id','event','outcome','reason','count','aux0','aux1'] if observe else ['id','budget']
    binders=' '.join('('+v+' : Val)' for v in vals)
    args='['+', '.join(vals)+', image kids]'
    lines=['import Fn2.Arms.Core','import Fn2.Instances.ServedMetadata',
      'namespace Fn2.Arms.Served.'+namespace,'open Fn2.ACL2 Fn2.Arms Fn2.Arms.Core Fn2.Instances.ServedKinds',
      'def kind : Kind := kinds['+str(ki)+']!', 'def arm : Arm := kind.'+part+'['+str(ai)+']!',
      'def image (kids : Fin '+str(len(layout))+' → Val) : Val := Val.ofList (List.ofFn kids)']
    if area==':SUBARMS' and str(k[':FORM'])==':CHILDREN':
        # A child subarm's value formals precede its narrowed child inputs.
        sig=as_list(plist(k[':SUBARMS'][ai][1:]).get(':SIG',List([])))
        if not sig: raise ValueError('child subarm has no narrowed signature')
        takes,returns,results=as_list(sig[0]),as_list(sig[1]),int(str(sig[2]))
        tuple_=list(map(str,k[':TUPLE'])); n=len(tuple_)
        vals=['id','slot','kindTag','ordinal','budget']; binders=' '.join('('+v+' : Val)' for v in vals)
        get=lambda x:'kids ⟨'+str(tuple_.index(str(x)))+', by decide⟩'
        callargs='['+', '.join(vals+[get(t) for t in takes])+']'
        answer='[emitted]' if results+len(returns)==1 else 'emitted.toList'
        rets=list(map(str,returns))
        restored=['('+answer+')['+str(results+rets.index(t))+']!' if t in rets else get(t) for t in tuple_]
        packed='Val.ofList (('+answer+').take '+str(results)+' ++ ['+', '.join(restored)+'])'
        lines += [f'def contract {binders} (kids : Fin {n} → Val) : Prop :=',
          '  ∃ fuel result emitted, runArm world kind arm false (['+', '.join(vals)+'] ++ List.ofFn kids) fuel = .ok result ∧',
          f'    world.fns {lean_str(name)} {callargs} = some emitted ∧ result = {packed}']
    else:
        lines += [f'def contract {binders} (kids : Fin {len(layout)} → Val) : Prop :=',
          f'  ∃ fuel result, runCore world coreTuple kind arm {str(observe).lower()} {args} fuel = .ok result ∧',
          f'    world.fns {lean_str(name)} {args} = some result']
    return '\n'.join(lines+['end Fn2.Arms.Served.'+namespace,''])

def proof_obligations(decl):
    found=set()
    def walk(x):
        if not isinstance(x,List) or not x:return
        if str(x[0])=='QUOTE':return
        if isinstance(x[0],Atom) and str(x[0]).startswith(':'):found.add(str(x[0]))
        for y in x:walk(y)
    walk(decl)
    groups=[({':SET',':NEXT'},'pending-write/phase-update certificate'),
      ({':DO',':ISSUE'},'operation-result and child-writeback certificate'),
      ({':REPEAT'},'symbolic iteration/fuel-adequacy instance'),
      ({':IF',':COND',':CASE'},'branch-join certificate'),
      ({':STOP',':HALT'},'stop/reclamation certificate'),
      ({':GOTO'},'subarm-composition certificate'),
      ({':COMMIT'},'durable-word whole-arm composition certificate')]
    reasons=[name for tags,name in groups if found & tags]
    return 'not generated: '+', '.join(reasons or ['terminal certificate for '+', '.join(sorted(found))])

def generate(src):
    src=Path(src); out=BASE/'meta/Fn2/Instances/ServedCertificates';out.mkdir(parents=True,exist_ok=True)
    export=BASE/'meta/emit/served-export.lisp'
    with src.open(newline='') as stream, export.open('w') as acl2:
        p=header(stream); manifest=fields(p[':MANIFEST'])
        layout=List([r[1] for r in decode(manifest[':CORE-LAYOUT'])[1]])
        kinds=decode(p[':KINDS']); inventory=decode(p[':ARM-INVENTORY'])
        emb={':KINDS':kinds,':OPERATIONS':decode(p[':OPERATIONS']),':CONSTANTS':decode(p[':CONSTANTS']),':CORE-TUPLE':layout}
        waits=[(r[0],List(r[1:])) for r in decode(p[':WAITS'])]
        emit_kinds(emb,waits,out.parent/'ServedKinds.lean','Fn2.Instances.ServedKinds','Fn2.Instances.LayerAWorld',{})
        lean_metadata(p,out.parent/'ServedMetadata.lean')
        lean_commit_words(p,out.parent/'ServedCommit.lean')
        consts={str(r[0]):alist_value(r) for r in emb[':CONSTANTS']}
        acl2.write('(in-package "ACL2")\n(include-book "../../books/reference")\n(include-book "../../books/translation-validation")\n')
        acl2.write("(fn2-tv-check-manifest '"+canonical_text(p[':MANIFEST'])+")\n")
        acl2.write("(fn2-tv-check-arm-inventory '"+show(inventory)+")\n")
        acl2.write(metadata_checks(p))
        acl2.write("(fn2-tv-check-functions '(\n")
        functions=[]; names=set()
        for name,row,d in function_records(stream,int(str(p[':FUNCTION-COUNT']))):
            names.add(name)
            acl2.write('('+name+' . '+canonical_text(row)+')\n')
            functions.append({'name':name,'canonical_export':'proposed',
              'record_sha256':hashlib.sha256(canonical_text(row).encode()).hexdigest()})
        acl2.write('))\n')
        acl2.write("(fn2-tv-check-served-closure '("+' '.join(sorted(names))+") '("+' '.join(str(decode(n)) for n in as_list(p[':REFUSED']))+"))\n")
    bykind={str(k[0]):(i,k) for i,k in enumerate(kinds)}; roots=[]
    for ri,row in enumerate(inventory):
        kn,area,tag,form,fn,core,decl,sig=row
        ki,kd=bykind[str(kn)]; key={':ARMS':':ARMS',':OBSERVE-ARMS':':OBSERVES',':SUBARMS':':SUBARMS'}[str(area)]
        entries=plist(kd[1:])[key]; ai=next(i for i,a in enumerate(entries) if a[0]==tag)
        name=str(fn if str(core)=='NIL' else core); ns='Root'+str(ri); contract=out/(ns+'.lean')
        contract.write_text(whole_contract(kd,ki,str(area),ai,layout,name,ns))
        rec={'name':name,'kind':str(kn),'area':str(area),'tag':str(tag),'form':str(form),
          'contract':str(contract.relative_to(BASE)),'status':'unvalidated','reason':proof_obligations(decl)}
        if name not in names: rec['reason']='function absent from canonical served closure'
        elif str(area)==':ARMS' and show(decl)=='((:IDLE))':
            try:
                proof=out/(ns+'Proof.lean')
                source=idle_certificate(kd,ki,ai,layout,consts,ns+'Proof')
                link=f'''theorem validated (id budget : Val) (kids : Fin {len(layout)} → Val) :
    Fn2.Arms.Served.{ns}.contract id budget kids := by
  obtain ⟨fuel, result, hr, he⟩ := echo_free_certificate id budget kids
  refine ⟨fuel, result, hr, ?_⟩
  change Fn2.Instances.LayerAWorld.fns {lean_str(name)} [id,budget,image kids] = some result
  rw [Fn2.Instances.LayerAWorld.{ident(name)}.fns_eq, he]
#print axioms validated
'''
                source='import Fn2.Instances.ServedCertificates.'+ns+'\n'+source
                source=source.replace('end Fn2.Arms.Served.'+ns+'Proof',link+'end Fn2.Arms.Served.'+ns+'Proof')
                proof.write_text(source)
                rec.update(proof=str(proof.relative_to(BASE)),reason='generated proof has not passed Lean')
            except (ValueError,KeyError) as e: rec['reason']='idle certificate: '+str(e)
        roots.append(rec)
    if len(set(r['name'] for r in roots))!=len(roots): raise ValueError('duplicate arm root')
    report={'schema':1,'package':str(src.relative_to(BASE)) if src.is_relative_to(BASE) else str(src),
      'package_sha256':digest(src),'functions':functions,'roots':roots,
      'unresolved':[str(decode(n)) for n in as_list(p[':REFUSED'])],
      'commit_words':len(commit_words(p)),
      'native_boundary':[str(decode(n)) for n in as_list(p[':NATIVES'])],
      'gates':{},'inputs':{str(f.relative_to(BASE)):digest(f) for f in sorted(set(
        [export,BASE/'meta/Fn2.lean',BASE/'meta/lean-toolchain',BASE/'meta/lake-manifest.json',
         *BASE.glob('books/**/*.lisp'),*BASE.glob('meta/Fn2/**/*.lean'),
         *BASE.glob('meta/emit/*.py'),*BASE.glob('meta/emit/*.lisp'),*BASE.glob('meta/emit/*.lsp'),
         *BASE.glob('meta/emit/*.lean.in')]))}}
    dst=BASE/'build/served-certificate-coverage.json';dst.parent.mkdir(exist_ok=True)
    dst.write_text(json.dumps(report,indent=2)+'\n')
    print(f'SERVED CERTIFICATE PROPOSAL: canonical exports 0/{len(functions)}; whole roots 0/{len(roots)}; '+
      f'{sum("proof" in r for r in roots)} generated proof attempts; {len(report["unresolved"])} unresolved functions')
    return report

if __name__=='__main__':
    generate(sys.argv[1])
