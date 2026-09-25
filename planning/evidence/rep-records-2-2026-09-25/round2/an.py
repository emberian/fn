import re,sys,glob,statistics as st
def load(f):
    t=open(f).read(); n=int(re.search(r"Number of samples:\s+(\d+)",t).group(1))
    tot={}
    for line in t.splitlines():
        m=re.match(r"^\s+(\d+)\s+[\d.]+\s+(\d+)\s+([\d.]+)\s+(\S.*?) \[\d+\]$",line)
        if m and m.group(4) not in tot: tot[m.group(4)]=int(m.group(2))
    return n,tot
names=["FN-RECORD-P","FN-RCON-RECORD-P","FN-RECORD-STRING-OCTETS-AUX","FN-RECORD-ENCODE-IMPL","FN-RCON-RECORD-ENCODE-IMPL","FN-PCAR-SPC-PREPARE","FN-SN-RECORD-BINDSP","FN-CPE-PROJECTION-STEP","FN-STORE-EVENT-TXID","FN-OWNER-PENDING-OCTETS","FN-OWNER-IO","FN-FRAME-DIGEST"]
for L in ["base2","after","after2"]:
    fs=sorted(glob.glob(f"p2-{L}-n120-r*-graph.txt"))
    rows=[load(f) for f in fs]
    ns=[n for n,_ in rows]; N=sum(ns)
    print(f"{L}: rounds {len(fs)} samples/48POST min {min(ns)} median {st.median(ns)} max {max(ns)} total {N}")
    for k in names:
        s=sum(t.get(k,0) for _,t in rows)
        print(f"   {k:30s} total {s:4d}  {100*s/N:5.2f}%  per-round median {st.median([t.get(k,0) for _,t in rows])}")
    w=[float(re.search(r'per_ms (\S+)',open(f"p2-{L}-r{i}.out").read()).group(1)) for i in range(1,14)]
    print("   wall per POST under sprof ms: median %.1f min %.1f max %.1f"%(st.median(w),min(w),max(w)))
