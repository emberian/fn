#!/usr/bin/env python3
"""MEM-003: m3.py workload + per-POST latency + hook log.  usage: mem3.py LAUNCHER RUNDIR ARM [POSTS]"""
import os,sys,time,subprocess,re,json,shutil
from pathlib import Path
base=Path("/tank/fn/scratch/n-mem"); sys.path.insert(0,str(base/"tools")); sys.path.insert(0,str(base))
import rep_measure as r, msgid_measure as m
IMG=sys.argv[1]; work=Path(sys.argv[2]).resolve(); arm=sys.argv[3]; posts=int(sys.argv[4]) if len(sys.argv)>4 else 1000
shutil.rmtree(work,ignore_errors=True); work.mkdir(parents=True)
port=m.free_port(); cfg=work/"fn.toml"
cfg.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n[control]\npath = "%s"\n'%(work/"store",port,work/"c.sock"))
e=dict(os.environ); e["ACL2_CUSTOMIZATION"]="NONE"; e["SBCL_USER_ARGS"]="--dynamic-space-size 1068MB --tls-limit 16384"
e["MEM3_ARM"]=arm; e["MEM3_LOG"]=str(work/"events.log")
flags="--profile development --max-transactions 16384 --max-history-octets 8388608 --max-record-octets 196608 --max-groups-per-article 16 --max-open-suffix 128".split()
i=subprocess.run([IMG,"--fn","operator",str(cfg),"init"]+flags+["fn.letters","fn.test"],env=e,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=600)
assert i.returncode==0, i.stdout[-400:]
p=subprocess.Popen([IMG,"--fn","operator",str(cfg),"run"],env=e,stdout=subprocess.PIPE,stderr=open(work/"owner.err","ab"))
r.wait_for_announcement(p,b"LISTENING ",timeout=900,stderr_path=work/"owner.err"); time.sleep(3)
def snap():
    st=Path("/proc/%d/status"%p.pid).read_text()
    g=lambda k:int(re.search(k+r":\s+(\d+)",st).group(1))
    return dict(rss=g("VmRSS"),hwm=g("VmHWM"),anon=g("RssAnon"),file=g("RssFile"))
out={"img":IMG,"arm":arm,"posts":posts}; out["open"]=snap()
cs=[]
for k in (8,24):
    for _ in range(k): cs.append(m.Conn(port))
    time.sleep(2)
for c in cs: c.close()
time.sleep(2); out["empty-after-close"]=snap()
c=m.Conn(port); lat=[]; t0=time.time()
for k in range(posts):
    t=time.perf_counter(); r.post(c,k,2048); lat.append(time.perf_counter()-t)
c.close(); out["post_wall_s"]=round(time.time()-t0,1); time.sleep(2); out["filled"]=snap()
cs=[]
for k in (8,24):
    for _ in range(k): cs.append(m.Conn(port))
    time.sleep(2)
for c in cs: c.close()
time.sleep(2); out["filled-after-close"]=snap()
time.sleep(8); out["idle-10s"]=snap()
time.sleep(10); out["idle-20s"]=snap()
lat.sort(); q=lambda f: round(lat[min(len(lat)-1,int(f*len(lat)))]*1000,2)
out["post_ms"]={"p50":q(.5),"p95":q(.95),"p99":q(.99),"max":round(lat[-1]*1000,1)}
p.terminate(); p.wait(120)
ev=(work/"events.log").read_text().splitlines() if (work/"events.log").exists() else []
gcs=[l.split() for l in ev if l.startswith("GC ")]; fires=[l.split() for l in ev if l.startswith("FIRE")]
out["hooks"]=[l for l in ev if l.startswith("HOOKS")][:1]
out["gc_count"]=len(gcs); out["gc_ms"]=round(int(gcs[-1][2])/1000,1) if gcs else 0
out["fires"]=len(fires); out["fire_ms"]=[round(int(x[3])/1000,1) for x in fires]
out["pubs"]=sum(1 for l in ev if l.startswith("PUB-START"))
(work/"mem3.json").write_text(json.dumps(out,indent=1)); print(json.dumps(out))
