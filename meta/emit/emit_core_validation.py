#!/usr/bin/env python3
"""Instantiate CNS proof shapes from canonical columns and the complete layout."""
from pathlib import Path
import sys,re
sys.path.insert(0,str(Path(__file__).parent))
from emit_certificate import *
def emit_validation(kd,tuple_,functions):
    k=plist(kd[1:]);names=[str(x)for x in tuple_];n=len(names)
    own=names.index('FN2-CNS');directory=names.index('FN2-MACHINES')
    xs=['c'+str(i)for i in range(n)];rows=[];cols=[];cases=[];proofs=[]
    for col in k[':COLUMNS']:
        c=str(col[0]);cols.append(c);d=c in ['READY-PREV','READY-NEXT','WAIT-REASON']
        f=('FN2-MACHINES-'if d else'FN2-CNS-')+c
        rows.append(f'("ROW-{c}", {ident(f)} '+(f'id c{directory}'if d else f'slot c{own}')+')')
        av=(f'id, c{directory}' if d else f'slot, c{own}');args=(f'id c{directory}' if d else f'slot c{own}')
        proofs += [f'  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple {lean_str(f)} [{av}] (by decide +kernel)).trans', f'      (Fn2.Instances.CoreWorld.{ident(f)}.dispatched (err := {lean_str('no function '+f+'/2')}) {args})']
        cases.append(f'  | "{c}" => {ident(f)} '+('id dir'if d else'slot own'))
    call_names=['FN2-CNS-ROWS','FN2-MACHINES-ROWS','FN2-CONTROL-RECORD-STOP'] + ['FN2-CNS-SET-'+n for n in ['REVENT','ROUTCOME','RCOUNT','RREADY']]
    call_names += ['FN2-CNS-SET-'+c for c in cols if c not in ['READY-PREV','READY-NEXT','WAIT-REASON']]
    call_names += ['FN2-MACHINES-SET-WAIT-REASON','FN2-CORE-RELEASE-CHILDREN','FN2-MACHINES-RECLAIM','FN2-MACHINES-FREE-HEAD-OF','FN2-MACHINES-GEN-LIMIT']
    call_names = list(dict.fromkeys(call_names))
    call_lines=[]
    allf={f.name:f for f,d in [fn_of(r) for r in functions]}
    for n in call_names:
        f=allf[n];bs=' '.join('('+ident(a)+' : Val)'for a in f.formals)
        av=', '.join(ident(a)for a in f.formals);args=' '.join(ident(a)for a in f.formals)
        cn=('("FN2-CNS" ++ "-SET-" ++ '+lean_str(n.removeprefix('FN2-CNS-SET-'))+')') if n.startswith('FN2-CNS-SET-') else ('("FN2-MACHINES-SET-" ++ "WAIT-REASON")' if n=='FN2-MACHINES-SET-WAIT-REASON' else lean_str(n))
        call_lines += [f'theorem {ident(n)}.core_call {bs} :',
          f'    callFn (coreWorld world coreTuple) {cn} [{av}] = .ok (Fn2.Instances.LayerAWorld.{ident(n)} {args}) := by',
          f'  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple {lean_str(n)} [{av}] (by decide +kernel)).trans', f'    (Fn2.Instances.CoreWorld.{ident(n)}.dispatched (err := {lean_str('no function '+n+'/'+str(len(f.formals)))}) {args})','']
    values=dict(ROW_CALL_CASES='\n'.join(proofs),HANDLER_CALLS="\n".join(call_lines),CORE_SIZE=str(len(names)),CORE_BINDERS=' '.join('('+x+' : Val)'for x in xs),
      HANDLER_SUCCESS_KIDS='['+', '.join('(handlerOwn slot event outcome count '+x+')'if j==own else x for j,x in enumerate(xs))+']',
      HANDLER_FAILURE_KIDS='['+', '.join('(«FN2-CONTROL-RECORD-STOP» (.int 13) '+x+')'if names[j]=='FN2-CONTROL'else x for j,x in enumerate(xs))+']',
      CORE_VALUES='['+', '.join(xs)+']',CORE_ARGUMENTS=' '.join(xs),
      IMAGE_VALUES='['+', '.join('(kids ⟨'+str(i)+', by decide⟩)'for i in range(len(names)))+']',
      IMAGE_ARGUMENTS=' '.join('(kids ⟨'+str(i)+', by decide⟩)'for i in range(len(names))),
      READ_DEFINITION='def cnsRead (id slot own dir : Val) : String → Val\n'+'\n'.join(cases)+'\n  | _ => Val.nil\n',
      ROW_VALUES='['+', '.join(rows)+']',
      IMAGE_ROWS=re.sub(r'\bc(\d+)\b',lambda m:'(kids ⟨'+m[1]+', by decide⟩)', '['+', '.join(rows)+']'),COLUMN_NAMES='['+', '.join(lean_str(c)for c in cols)+']',
      COLUMN_CASES=' | '.join(['rfl']*len(cols)),DIRECTORY_VALUE=f'c{directory}',OWN_VALUE=f'c{own}',
      DIRECTORY_INDEX=str(directory),OWN_INDEX=str(own))
    t=Path(__file__).with_name('core_validation.lean.in').read_text()+Path(__file__).with_name('core_draining.lean.in').read_text()
    for key,value in values.items():t=t.replace('@'+key+'@',value)
    if re.search(r'@[A-Z_]+@',t):raise ValueError('unexpanded template')
    Path('meta/Fn2/Arms/CoreValidation.lean').write_text(t)
if __name__=='__main__':
    p=fields(read_canonical(open(sys.argv[1]).read())[1:])
    layout=decode(fields(p[':MANIFEST'])[':CORE-LAYOUT'])[1]
    emit_validation(decode(p[':KIND']),List([r[1]for r in layout]),p[':FUNCTIONS'])
