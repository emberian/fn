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

def packed_text(x):
    """Losslessly pack symbol byte lists in the generated source book only.
    ACL2 expands each record and compares the original canonical structure.
    """
    chunks=[];todo=[x]
    while todo:
        a=todo.pop()
        if isinstance(a,List):
            if len(a)==3 and a[0]==':SYMBOL':
                quote=lambda v:'"'+codes(v).replace('\\','\\\\').replace('"','\\"')+'"'
                chunks.append('(:PACKED-SYMBOL '+quote(a[1])+' '+quote(a[2])+')')
                continue
            chunks.append('(');todo.append(')')
            for i in range(len(a)-1,-1,-1):
                todo.append(a[i])
                if i:todo.append(' ')
        else:chunks.append(str(a))
    return ''.join(chunks)

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
    checks.append(live_check(List([List(row[:4]) for row in commit_words(p)]),
      '(fn2-tv-commit-word-inventory (fn2-tv-arm-inventory (w state)))'))
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

def world_index(fn2_dir, extra_calls=None):
    lw = fn2_dir / 'Instances/LayerAWorld.lean'
    if not lw.is_file():
        return None
    mods = [m for m in re.findall(r'^public import Fn2\.Instances\.LayerAWorld\.(\w+)$', lw.read_text(), re.M)
            if not (m.endswith('Keys') or m.endswith('Eqns') or m.startswith('Index') or m == 'Natives')]
    mod_of = {}; D = {}
    for m in mods:
        txt = (fn2_dir / 'Instances/LayerAWorld' / (m + '.lean')).read_text()
        for p in re.split(r'^(?=(?:def|theorem) )', txt, flags=re.M)[1:]:
            hm = re.match(r'^(?:def|theorem) «([^»]+)»(?:\.(?:go|guard|constraint(?:_\d+)?))?(?:\s|:)', p)
            if not hm: continue
            fn = hm.group(1); mod_of[fn] = m
            D.setdefault(fn, set()).update(re.findall(r'«([^»]+)»', p))
    if extra_calls:
        for fn, cs in extra_calls.items():
            if fn in mod_of: D.setdefault(fn, set()).update(cs)
    for fn in D: D[fn] = {g for g in D[fn] if g in mod_of and g != fn}
    eqn_of = {}
    for k in range(1, 5):
        ep = fn2_dir / f'Instances/LayerAEqns{k}.lean'
        if ep.is_file():
            for fn in re.findall(r'^theorem «([^»]+)»\.fns_eq\b', ep.read_text(), re.M):
                eqn_of[fn] = f'Fn2.Instances.LayerAEqns{k}'
    return {'mods': mods, 'mod_of': mod_of, 'D': D, 'eqn_of': eqn_of}

def fill_world_bodies(text, widx):
    if not widx: return text
    m = re.search(r'^-- BEGIN world bodies \(emit_embed\.py\): scan\n(?:import all .*\n)*-- END world bodies$', text, re.M)
    if not m: return text
    rest = text[:m.start()] + text[m.end():]
    mod_of, D = widx['mod_of'], widx['D']
    seen, stack = set(), [n for n in set(re.findall(r'«([^»]+)»', rest)) if n in mod_of]
    while stack:
        f = stack.pop()
        if f not in seen:
            seen.add(f); stack.extend(D[f])
    used = {mod_of[f] for f in seen}
    lines = ['-- BEGIN world bodies (emit_embed.py): scan']
    lines += [f'import all Fn2.Instances.LayerAWorld.{x}' for x in widx['mods'] if x in used]
    lines.append('-- END world bodies')
    return text[:m.start()] + '\n'.join(lines) + text[m.end():]

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
    out.write_text(as_module('\n'.join(lines), expose=True, import_all=CORE_STRING_BODIES))

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
    lines += ['end Fn2.Instances.ServedCommit','']
    out.write_text(as_module('\n'.join(lines), expose=True, import_all=CORE_STRING_BODIES))

def call_proof(name, args, extra=''):
    av = '[' + ', '.join(args) + ']'
    return (f'simp only [{extra}callFn, world, nativeCall_none {lean_str(name)} {av} '
            f'(by decide +kernel), Fn2.Instances.LayerAWorld.{ident(name)}.fns_eq]')

def terminal_parameters(kd, ki, ai, layout, consts, namespace, area=':ARMS'):
    k = plist(kd[1:]); kn = str(kd[0])
    tag = str(k[area][ai][0]).lstrip(':')
    core = kn+('-RUN-' if area==':ARMS' else '-ON-')+tag
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
      ARM_FIELD='arms' if area==':ARMS' else 'observes',
      NONE_VALUE=val(consts['*FN2-NONE*']),
      OBSERVATION_REASON=val(consts['*FN2-STOP-REASON-MACHINE-OBSERVATION*']),
      CHILD_UNFOLD=(ident(core+'-CHILDREN')+',') if child else '',
      CORE_SIZE=str(n),CORE_BINDERS=' '.join('('+x+' : Val)' for x in xs),
      CORE_VALUES='['+', '.join(xs)+']',
      IMAGE_ARGUMENTS=' '.join('(kids ⟨'+str(i)+', by decide⟩)' for i in range(n)),
      READ_DEFINITION='def echoRead (id slot own dir : Val) : String → Val\n'+'\n'.join(cases)+'\n  | _ => Val.nil\n',
      ROW_VALUES='['+', '.join(rows)+']',COLUMN_NAMES='['+', '.join(lean_str(c) for c in cols)+']',
      COLUMN_CASES=' | '.join(['rfl']*len(cols)),ROW_CALL_PROOFS='\n'.join(proofs),
      DIRECTORY_VALUE=xs[directory],OWN_VALUE=xs[own],DIRECTORY_INDEX=str(directory),OWN_INDEX=str(own),
      SNAPSHOT_CALL='change callFn world '+lean_str(kn+'-SNAPSHOT-READ-CODE')+' [i,c] = .ok ('+ident(kn+'-SNAPSHOT-READ-CODE')+' i c)\n    '+call_proof(kn+'-SNAPSHOT-READ-CODE',['i','c']),
      SLOT_CALL=call_proof('FN2-MACHINE-SLOT',['i','c']),
      REFUSED_PROOF='simp only [refusedEntry, coreStop, const, world, consts, coreTuple, callFn, '+
        'nativeCall_none "FN2-CONTROL-RECORD-STOP" _ (by decide +kernel), '+
        'Fn2.Instances.LayerAWorld.«FN2-CONTROL-RECORD-STOP».fns_eq]; rfl')
    return values

def render_template(t, values):
    for key,v in values.items(): t=t.replace('@'+key+'@',v)
    if re.search(r'@[A-Z_]+@',t): raise ValueError('unexpanded proof parameter')
    return t

def idle_certificate(kd, ki, ai, layout, consts, namespace):
    values=terminal_parameters(kd,ki,ai,layout,consts,namespace)
    return render_template(Path(__file__).with_name('idle_validation.lean.in').read_text(),values)

def wake_certificate(kd, ki, ai, layout, consts, namespace):
    values=terminal_parameters(kd,ki,ai,layout,consts,namespace,':OBSERVES')
    prefix=Path(__file__).with_name('idle_validation.lean.in').read_text().split('theorem echo_idle_run')[0]
    body=Path(__file__).with_name('wake_validation.lean.in').read_text()
    return render_template(prefix+body,values)

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
    return as_module('\n'.join(lines+['end Fn2.Arms.Served.'+namespace,'']), expose=True)

def certificate_source(kd,ki,ai,layout,consts,ns,name,area,widx=None):
    observe=str(area)==':OBSERVE-ARMS'
    maker=wake_certificate if observe else idle_certificate
    args='id event outcome reason count aux0 aux1' if observe else 'id budget'
    actuals=args.replace(' ', ',')
    certificate='handler_certificate' if observe else 'echo_free_certificate'
    source=maker(kd,ki,ai,layout,consts,ns+'Proof')
    link=f'''theorem validated ({args} : Val) (kids : Fin {len(layout)} → Val) :
    Fn2.Arms.Served.{ns}.contract {args} kids := by
  obtain ⟨fuel, result, hr, he⟩ := {certificate} {args} kids
  refine ⟨fuel, result, hr, ?_⟩
  change Fn2.Instances.LayerAWorld.fns {lean_str(name)} [{actuals},image kids] = some result
  rw [Fn2.Instances.LayerAWorld.{ident(name)}.fns_eq, he]
#print axioms validated
'''
    kn=str(kd[0]);k=plist(kd[1:]);names=list(map(str,layout))
    own=names.index(kn);directory=names.index('FN2-MACHINES')
    own_columns=sum(str(c[0]) not in ['READY-PREV','READY-NEXT','WAIT-REASON'] for c in k[':COLUMNS'])
    number=val(consts['*'+kn+'-KIND*'])
    zero_args=' '.join(['(.int 0)']*len(args.split()))
    zero_actuals=','.join(['.int 0']*len(args.split()))
    link+=f'''def acceptedKids : Fin {len(layout)} → Val := fun i =>
  if i.val = {directory} then Val.ofList [Val.ofList [{number}],Val.ofList [.int 0],Val.nil,Val.nil,Val.nil,.int 1]
  else if i.val = {own} then Val.ofList (List.replicate {own_columns} Val.nil ++ [.int 1])
  else .int i.val

theorem accepted_entry_positive :
    {ident(kn+'-SNAPSHOT-READ-CODE')} (.int 0) (image acceptedKids) = .sym ":OK" ∧
    Fn2.Arms.Served.{ns}.contract {zero_args} acceptedKids := by
  exact ⟨by decide +kernel, validated {zero_args} acceptedKids⟩

theorem omitted_child_rejected (fuel : Nat) (result : Val) :
    runCore world coreTuple echoKind echoFree {str(observe).lower()}
      [{zero_actuals},Val.ofList (List.ofFn acceptedKids).tail] fuel ≠ .ok result := by
  apply Wrapper.omitted_child_rejected
  decide +kernel
#print axioms accepted_entry_positive
#print axioms omitted_child_rejected
'''
    source='import Fn2.Arms.Wrapper\nimport Fn2.Instances.ServedCertificates.'+ns+'\n'+source
    source=source.replace('end Fn2.Arms.Served.'+ns+'Proof',link+'end Fn2.Arms.Served.'+ns+'Proof')
    return fill_world_bodies(as_module(source, expose=True, import_all=CORE_STRING_BODIES, bodies='scan'), widx)

def statement_words(decl):
    """Inspect statements, not expression data, phase names or case labels."""
    found=set()
    def steps(xs):
        for s in as_list(xs):
            if not isinstance(s,List) or not s:continue
            h=str(s[0]);found.add(h)
            if h==':IF':
                for branch in s[2:4]:steps(branch)
            elif h in [':COND',':CASE']:
                for branch in s[1 if h==':COND' else 2:]:steps(List(branch[1:]))
            elif h==':DO':
                opts=plist(s[3:])
                for branch in as_list(opts.get(':CASE',List([]))):steps(List(branch[1:]))
            elif h==':ISSUE':
                opts=plist(s[2:])
                for key in [':OK',':REFUSED']:steps(opts.get(key,List([])))
            elif h==':REPEAT':steps(s[2])
            elif h==':COMMIT':
                opts=plist(s[2:])
                for key in [':DEPENDENCIES',':UNCHANGED',':ACCEPTED',':REFUSED',':UNCERTAIN']:
                    steps(opts.get(key,List([])))
    xs=list(decl)
    while xs and str(xs[0]) in [':FROM',':ON-REFUSAL']:
        if str(xs[0])==':ON-REFUSAL':
            r=as_list(xs[1]);steps(List([List(r)] if r and isinstance(r[0],Atom) else r))
        xs=xs[2:]
    steps(List(xs))
    return found

def proof_obligations(decl):
    found=statement_words(decl)
    groups=[({':SET',':NEXT'},'pending-write/phase-update certificate'),
      ({':DO',':ISSUE'},'operation-result and child-writeback certificate'),
      ({':REPEAT'},'symbolic iteration/fuel-adequacy instance'),
      ({':IF',':COND',':CASE'},'branch-join certificate'),
      ({':STOP',':HALT'},'stop/reclamation certificate'),
      ({':GOTO'},'subarm-composition certificate'),
      ({':COMMIT'},'durable-word whole-arm composition certificate')]
    reasons=[name for tags,name in groups if found & tags]
    return 'not generated: '+', '.join(reasons or ['terminal certificate for '+', '.join(sorted(found))])

def acl2_sources():
    sys.path.insert(0,str(BASE/'tools'))
    import certs
    names=certs.required_closure(BASE,['books/reference','books/translation-validation'])
    return [BASE/(n+'.lisp') for n in names]

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
        acl2.write("(fn2-tv-check-packed-functions '(\n")
        functions=[]; names=set(); extra_calls={}
        for name,row,d in function_records(stream,int(str(p[':FUNCTION-COUNT']))):
            names.add(name)
            extra_calls[name] = calls_of(decode(d[':LOGICAL-BODY']), set())
            acl2.write('('+name+' . '+packed_text(row)+')\n')
            functions.append({'name':name,'canonical_export':'proposed',
              'record_sha256':hashlib.sha256(canonical_text(row).encode()).hexdigest()})
        acl2.write('))\n')
        acl2.write("(fn2-tv-check-served-closure '("+' '.join(sorted(names))+") '("+' '.join(str(decode(n)) for n in as_list(p[':REFUSED']))+"))\n")
    widx=world_index(BASE/'meta/Fn2',extra_calls)
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
        elif (str(area)==':ARMS' and show(decl)=='((:IDLE))') or (str(area)==':OBSERVE-ARMS' and show(decl)=='((:WAKE))'):
            try:
                proof=out/(ns+'Proof.lean')
                source=certificate_source(kd,ki,ai,layout,consts,ns,name,area,widx)
                proof.write_text(source)
                rec.update(proof=str(proof.relative_to(BASE)),reason='generated proof has not passed Lean')
            except (ValueError,KeyError) as e: rec['reason']='terminal certificate: '+str(e)
        roots.append(rec)
    if len(set(r['name'] for r in roots))!=len(roots): raise ValueError('duplicate arm root')
    report={'schema':1,'package':str(src.relative_to(BASE)) if src.is_relative_to(BASE) else str(src),
      'package_sha256':digest(src),'functions':functions,'roots':roots,
      'unresolved':[str(decode(n)) for n in as_list(p[':REFUSED'])],
      'commit_words':len(commit_words(p)),
      'native_boundary':[str(decode(n)) for n in as_list(p[':NATIVES'])],
      'gates':{},'inputs':{str(f.relative_to(BASE)):digest(f) for f in sorted(set(
        [export,BASE/'meta/Fn2.lean',BASE/'meta/lean-toolchain',BASE/'meta/lake-manifest.json',
         *acl2_sources(),*BASE.glob('meta/Fn2/**/*.lean'),
         *BASE.glob('meta/emit/*.py'),*BASE.glob('meta/emit/*.lisp'),*BASE.glob('meta/emit/*.lsp'),
         *BASE.glob('meta/emit/*.lean.in')]))}}
    dst=BASE/'build/served-certificate-coverage.json';dst.parent.mkdir(exist_ok=True)
    dst.write_text(json.dumps(report,indent=2)+'\n')
    print(f'SERVED CERTIFICATE PROPOSAL: canonical exports 0/{len(functions)}; whole roots 0/{len(roots)}; '+
      f'{sum("proof" in r for r in roots)} generated proof attempts; {len(report["unresolved"])} unresolved functions')
    return report

if __name__=='__main__':
    generate(sys.argv[1])
