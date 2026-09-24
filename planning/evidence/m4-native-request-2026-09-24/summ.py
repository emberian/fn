import json,sys
d=json.load(open(sys.argv[1]))
print("setup", d["setup_rcs"], "native", d.get("native"), "b_trusts", d.get("b_trusts"))
for s in d["steps"]:
    print("==", s["step"], "|", s["outcome"])
    for k,v in s.items():
        if k in ("step","outcome","logs","b_fnbs_frame_names"): continue
        print("   ", k, str(v)[:400])
    for t,l in s["logs"].items(): print("   log", t, l["sha256_16"], l["lines"][-3:])
print("final", d.get("a_final_status"))
print("procs", [(p["tag"],p["pid"],p["stopped"]) for p in d["processes"]])
print("dtnd", {k:[(x.get("pid"),x.get("stopped")) for x in v] for k,v in d.get("dtnd_processes",{}).items()})
