import re,sys,collections
target=sys.argv[1]; agg=collections.Counter()
for f in sys.argv[2:]:
    t=open(f).read()
    for blk in re.split(r"\n-{20,}\n",t):
        lines=blk.splitlines()
        for i,l in enumerate(lines):
            if re.match(r"^\s+\d+\s+[\d.]+\s+\d+\s+[\d.]+\s+"+re.escape(target)+r" \[\d+\]$",l):
                for c in lines[:i]:
                    m=re.match(r"^\s+(\d+)\s+[\d.]+\s+(\S.*?) \[\d+\]$",c)
                    if m: agg[m.group(2)]+=int(m.group(1))
print(agg.most_common(12))
