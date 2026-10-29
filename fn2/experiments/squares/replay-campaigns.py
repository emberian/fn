#!/usr/bin/env python3
"""Replay measured witnesses and their original-prefix controls, two at a time."""
import os
from pathlib import Path
import shutil
import subprocess
import time
ROOT = Path(__file__).resolve().parents[3]
EXP = ROOT / 'fn2/experiments/squares'
jobs = [('M1', 'M1', 'random', 1)]
for m in ('M2','M3','M4','M5','M6'):
    jobs += [(m,m,'random',1), ('ORIGINAL',m,'random',1)]
jobs += [('ORIGINAL','ORIGINAL','baseline',1)]
for m in ('M2','M6'):
    jobs += [(m,m,'baseline',20261028), ('ORIGINAL',m,'baseline',20261028)]
running=[]
while jobs or running:
    while jobs and len(running)<2:
        if shutil.disk_usage(ROOT).free < 60*1024**3: raise SystemExit('BLOCKED: disk below 60 GiB')
        runtime, source, config, seed = jobs.pop(0)
        tag=f'-{source}-{config}'
        stem=EXP/'results'/f'{runtime}-replay-{seed}{tag}'
        env=dict(os.environ,FN_ACL2_SLOT_DIR='/tmp/fn2-a4-acl2-slots',FN_ACL2_SLOTS='6',E1_MUTANT=runtime,E1_CONFIG='replay',E1_SEED=str(seed),E1_OUTPUT_TAG=tag,E1_REPLAY=str(EXP/'results'/f'{source}-{config}-{seed}-schedule.sexp'))
        log=open(str(stem)+'.log','wb')
        with open(EXP/'driver.lsp','rb') as driver:
            p=subprocess.Popen(['timeout','-k','5','600','tools/acl2'],cwd=ROOT,env=env,stdin=driver,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
        Path(str(stem)+'.pid').write_text(str(p.pid)+'\n')
        running.append((p,log,stem))
        print('E1 REPLAY START',stem.name,p.pid,flush=True)
    for item in list(running):
        p,log,stem=item
        if p.poll() is not None:
            log.close(); print('E1 REPLAY PROCESS',stem.name,p.returncode,flush=True)
            running.remove(item)
    if running: time.sleep(.5)
