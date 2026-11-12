#!/usr/bin/env python3
"""Run kernel gates and report exact, current per-root coverage.

ACL2 evidence is a record-toolchain cache entry at the current closure key.
Lean evidence is a successful compiler invocation plus the named theorem's
axiom census. Neither emitter output nor a pre-existing .olean is counted.
"""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import argparse
import json
import os
import re
import subprocess
import sys
import hashlib
import shutil
sys.path.insert(0,str(Path(__file__).parent))
from emit_served_certificate import BASE, digest

ALLOWED={'propext','Classical.choice','Quot.sound'}

def current(report, root=BASE):
    if digest(root/report['package']) != report['package_sha256']:
        raise ValueError('canonical package changed; regenerate coverage')
    for name,sha in report['inputs'].items():
        if not (root/name).is_file() or digest(root/name)!=sha:
            raise ValueError('certificate input changed: '+name)
    for key in ['roots','functions']:
        names=[r['name'] for r in report[key]]
        if len(names)!=len(set(names)): raise ValueError('duplicate '+key+' denominator')

def census(output, theorem):
    if 'sorryAx' in output: return False
    found=re.search(r"'"+re.escape(theorem)+r"' (does not depend on any axioms|depends on axioms: \[([^]]*)\])",output)
    return bool(found and (not found[2] or set(x.strip() for x in found[2].split(','))<=ALLOWED))

def compile_one(source, lib, seconds, logname):
    out=lib/Path(source).relative_to('meta').with_suffix('.olean')
    out.parent.mkdir(parents=True,exist_ok=True)
    log=BASE/'build/served-certificate-gates'/logname;log.parent.mkdir(parents=True,exist_ok=True)
    try:
        result=subprocess.run(['lean',str(Path(source).relative_to('meta')),'-o',str(out)],
          cwd=BASE/'meta',text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=seconds)
        log.write_text(result.stdout)
        return result.returncode,result.stdout,str(log.relative_to(BASE))
    except subprocess.TimeoutExpired as e:
        output=e.stdout or b''
        if isinstance(output,bytes):output=output.decode(errors='replace')
        log.write_text(output+'\nTIMEOUT\n')
        return 124,output,str(log.relative_to(BASE))

def compile_closure(roots, lib, seconds, jobs):
    """Recheck every local import, then reuse only this checker's bound cache.
    An olean copied from a warm lane is not evidence for changed dependencies.
    """
    deps={}
    def visit(module):
        if module in deps:return
        path=BASE/'meta'/Path(*module.split('.')).with_suffix('.lean')
        if not path.is_file():raise ValueError('missing local Lean import '+module)
        ds=[]
        for line in re.findall(r'^(?:public\s+)?import\s+(?:all\s+)?(.+)$',path.read_text(),re.M):
            ds += [x for x in line.split() if x=='Fn2' or x.startswith('Fn2.')]
        deps[module]=ds
        for d in ds:visit(d)
    for r in roots:visit(r)
    cache_path=BASE/'build/served-lean-cache.json'
    cache=json.loads(cache_path.read_text()) if cache_path.exists() else {}
    compiler=Path(shutil.which('lean')).resolve()
    tool=digest(compiler)+digest(BASE/'meta/lean-toolchain')+digest(BASE/'meta/lake-manifest.json')
    done={};pending=set(deps)
    try:
        while pending:
            ready=sorted(n for n in pending if all(d in done for d in deps[n]))
            if not ready:raise ValueError('cycle in local Lean imports')
            def build(n):
                source='meta/'+n.replace('.','/')+'.lean'
                key=hashlib.sha256((tool+digest(BASE/source)+''.join(done[d] for d in deps[n])).encode()).hexdigest()
                artifact=lib/Path(*n.split('.')).with_suffix('.olean')
                old=cache.get(n,{})
                if old.get('key')==key and artifact.is_file() and old.get('olean')==digest(artifact):
                    return n,key,old,None
                rc,out,log=compile_one(source,lib,seconds,'dependency-'+n+'.log')
                if rc:return n,key,None,log
                return n,key,{'key':key,'olean':digest(artifact)},None
            with ThreadPoolExecutor(max_workers=jobs) as pool:
                results=list(pool.map(build,ready))
            errors=[]
            for n,key,record,error in results:
                if error:cache.pop(n,None);errors.append(error)
                else:cache[n]=record;done[n]=key;pending.remove(n)
            if errors:raise RuntimeError('Lean dependency refused: '+', '.join(errors))
    finally:
        cache_path.write_text(json.dumps(cache,indent=2)+'\n')

def lean_gates(report, lib, seconds, jobs):
    # The caller starts this process under swarm-build/lake env. Install each
    # changed dependency into this lane's own library, never another lane's.
    own={'.'.join(Path(r[k]).relative_to('meta').with_suffix('').parts)
         for r in report['roots'] for k in ('contract','proof') if k in r}
    extra=set()
    for r in report['roots']:
        for k in ('contract','proof'):
            if k not in r or not (BASE/r[k]).is_file():continue
            for line in re.findall(r'^(?:public\s+)?import\s+(?:all\s+)?(.+)$',(BASE/r[k]).read_text(),re.M):
                extra.update(x for x in line.split() if (x=='Fn2' or x.startswith('Fn2.')) and x not in own)
    compile_closure(sorted({'Fn2.Arms.Wrapper','Fn2.Instances.ServedCommit',
      *['Fn2.Instances.LayerAEqns'+str(i) for i in range(1,5)],*extra}),lib,seconds,jobs)
    if report.get('commit_words',0):
        rc,out,log=compile_one('meta/Fn2/Instances/ServedCommit.lean',lib,seconds,'commit-words.log')
        if rc or not all(census(out,'Fn2.Instances.ServedCommit.word'+str(i)+'_translation')
                         for i in range(report['commit_words'])):
            raise RuntimeError('commit word kernel/census gate refused: '+log)
        report['gates']['commit_words_lean']=report['commit_words']
    def one(pair):
        i,row=pair
        row.pop('lean_gate',None)
        rc,out,log=compile_one(row['contract'],lib,seconds,f'{i}-contract.log')
        row['contract_gate']={'exit':rc,'log':log}
        if rc:
            row.update(status='unvalidated',reason='Lean rejected contract: '+log)
        elif 'proof' in row:
            rc,out,log=compile_one(row['proof'],lib,seconds,f'{i}-proof.log')
            theorem='Fn2.Arms.Served.Root'+str(i)+'Proof.validated'
            if rc==0 and all(census(out,'Fn2.Arms.Served.Root'+str(i)+'Proof.'+n)
                            for n in ['validated','accepted_entry_positive','omitted_child_rejected']):
                row.update(status='validated',reason='',lean_gate={'log':log,'theorem':theorem,
                  'log_sha256':digest(BASE/log)})
            else:
                row.update(status='unvalidated',reason=('Lean proof timed out: ' if rc==124 else 'Lean rejected proof/census: ')+log)
        return row
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        report['roots']=list(pool.map(one,enumerate(report['roots'])))
    report['gates']['lean']={'compiler':subprocess.check_output(['lean','--version'],text=True).strip()}

def acl2_gate(report, launcher):
    sys.path.insert(0,str(BASE/'tools'))
    import acl2_toolchain,certs
    found=acl2_toolchain.fingerprint(launcher)
    if not found.qualified: raise ValueError('unqualified record ACL2 toolchain')
    entries=certs.book_entries(BASE,certs.cache_directory(),'meta/emit/served-export',
      metadata_filter=lambda m:m.get('toolchain_identity')==found.identity)
    entry=certs.choose_entry(entries,str(BASE.resolve()))
    if entry is None: raise ValueError('no record-toolchain certificate at current served-export closure key')
    directory,meta=entry
    report['gates']['acl2']={'cache_entry':str(directory),'toolchain':found.identity,
      'certificate_sha256':meta['cert_sha256']}
    for f in report['functions']: f['canonical_export']='validated'

def reconcile(report):
    for r in report['roots']:
        if 'lean_gate' in r:
            if 'acl2' in report['gates']:
                r.update(status='validated',reason='')
            else:
                r.update(status='unvalidated',reason='Lean proof checked; live ACL2 metadata gate missing')

def summary(report):
    fs=report['functions'];rs=report['roots']
    fv=sum(f['canonical_export']=='validated' for f in fs)
    rv=sum(r['status']=='validated' for r in rs)
    lines=[f'Canonical live exports: {fv}/{len(fs)} validated.',
           f'Whole-arm interpretation: {rv}/{len(rs)} validated.',
           'These counts do not assert exported-body evaluation or primitive-domain adequacy for the entire closure.',
           '', 'Unvalidated whole roots:']
    lines += [r['name']+': '+r['reason'] for r in rs if r['status']!='validated']
    if fv!=len(fs):
        lines += ['', 'Unvalidated canonical exports:']
        lines += [f['name']+': current record-toolchain served-export gate missing' for f in fs if f['canonical_export']!='validated']
    lines += ['', 'Unresolved exported names:']+[n+': no logical body or attachment in the live world' for n in report['unresolved']]
    lines += ['', 'Native boundary (primitive-domain proofs are a separate gate):',
      ', '.join(report.get('native_boundary',[]))]
    return '\n'.join(lines)+'\n'

def main():
    a=argparse.ArgumentParser();a.add_argument('--report',type=Path,default=BASE/'build/served-certificate-coverage.json')
    a.add_argument('--lean',action='store_true');a.add_argument('--acl2',type=Path)
    a.add_argument('--lib',type=Path,default=BASE/'build/lean-lib');a.add_argument('--timeout',type=int,default=120)
    a.add_argument('-j',type=int,default=2);args=a.parse_args()
    report=json.loads(args.report.read_text());current(report)
    if args.acl2:acl2_gate(report,args.acl2)
    if args.lean:lean_gates(report,args.lib.resolve(),args.timeout,args.j)
    current(report)
    reconcile(report)
    args.report.write_text(json.dumps(report,indent=2)+'\n')
    text=summary(report);args.report.with_suffix('.txt').write_text(text)
    print('\n'.join(text.splitlines()[:3]))

if __name__=='__main__':main()
