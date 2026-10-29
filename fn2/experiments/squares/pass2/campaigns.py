#!/usr/bin/env python3
import argparse,hashlib,json,os,shutil,subprocess,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
EXP=ROOT/'fn2/experiments/squares'
P=EXP/'pass2'
SEEDS=(1,20261028,314159265)
def jobs(phase):
 if phase=='fixture':return [('ORIGINAL','fixture','c2','data','initial',1)]
 if phase in ('controls','main'):
  ms=['ORIGINAL'] if phase=='controls' else [f'M{i}' for i in range(1,7)]
  return [(m,c,'c1','default','initial',s) for m in ms for c in ('baseline','random','iterative','dedup') for s in (SEEDS if c in ('baseline','random') else (1,))]
 if phase=='local':return [(m,'iterative','c1','default',p,1) for m in ['ORIGINAL']+[f'M{i}' for i in range(1,7)] for p in ('listener','send')]
 if phase=='data':return [(m,c,'c2','data',p,s) for m in ['ORIGINAL','M2','M4'] for p in ('initial','data') for c in ('random','iterative','dedup') for s in (SEEDS if c=='random' else (1,))]
 raise ValueError(phase)
def main():
 a=argparse.ArgumentParser();a.add_argument('phase',choices=('fixture','controls','main','local','data','retry','replay'));a.add_argument('--jobs-file');a.add_argument('--one',action='store_true');args=a.parse_args()
 frozen=json.loads((EXP/'freeze.json').read_text())
 for n,h in frozen['mutants'].items():assert hashlib.sha256((EXP/'mutants'/n).read_bytes()).hexdigest()==h
 todo=json.loads(Path(args.jobs_file).read_text()) if args.jobs_file else jobs(args.phase);running=[];out=[]
 while todo or running:
  while todo and len(running)<(1 if args.one else 2):
   if shutil.disk_usage(ROOT).free<60*1024**3:raise SystemExit('BLOCKED: disk below60GiB; nothing deleted')
   job=todo.pop(0);m,c,p,d,pre,s=job[:6];stem=P/'results'/f'{m}-{c}-{p}-{d}-{pre}-{s}'
   env=dict(os.environ,FN_ACL2_SLOT_DIR='/tmp/fn2-a4-acl2-slots',FN_ACL2_SLOTS='6',E1_MUTANT=m,E1_SEED=str(s),E2_CONFIG=c,E2_PROFILE=p,E2_DECLARATION=d,E2_PREFIX=pre)
   if len(job)>6:env['E2_REPLAY']=str(EXP/job[6])
   log=open(str(stem)+'.log','wb')
   with open(P/'driver.lsp','rb') as driver:
    child=subprocess.Popen(['timeout','-k','5','600','tools/acl2'],cwd=ROOT,env=env,stdin=driver,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
   Path(str(stem)+'.pid').write_text(str(child.pid)+'\n')
   running.append((child,log,str(stem),time.monotonic()));print('E2 START',stem.name,'pid',child.pid,flush=True)
  for item in list(running):
   child,log,stem,start=item
   if child.poll() is not None:
    log.close();record=dict(stem=stem,exit=child.returncode,process_seconds=time.monotonic()-start);out.append(record)
    print('E2 PROCESS',json.dumps(record),flush=True);running.remove(item)
  if running:time.sleep(.5)
 (P/'results'/f'{args.phase}-processes.json').write_text(json.dumps(out,indent=2)+'\n')
 if any(r['exit'] for r in out):raise SystemExit(1)
if __name__=='__main__':main()
