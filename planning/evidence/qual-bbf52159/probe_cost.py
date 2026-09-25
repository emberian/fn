import os, subprocess, socket, time, sys
IMGS={"bbf52159":"/tank/fn/gates/qual-bbf52159-20260925/build/images/bbf52159dcab19228bd6cd0b855b99dd6d68758d/fn-host",
      "c3420013":"/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host"}
base="/tank/fn/scratch/qual-bbf52159/probe-cost"
subprocess.run(["rm","-rf",base]); os.makedirs(base)
env=dict(os.environ, ACL2_CUSTOMIZATION="NONE")
for name,img in IMGS.items():
    D=base+"/"+name; os.makedirs(D)
    subprocess.run([img,"--fn","store",D+"/store","init","fn.test"],env=env,check=True,capture_output=True)
    s=socket.socket(); s.bind(("127.0.0.1",0)); port=s.getsockname()[1]; s.close()
    open(D+"/fn.toml","w").write('[store]\npath = "%s/store"\n[listener]\nhost = "127.0.0.1"\nport = %d\n[control]\npath = "%s/control.sock"\n'%(D,port,D))
    o=subprocess.Popen([img,"--fn","operator",D+"/fn.toml","run"],env=env,stdout=subprocess.PIPE,stderr=subprocess.DEVNULL)
    while not o.stdout.readline().startswith(b"LISTENING"): pass
    times=[]
    for i in range(6):
        body=(b"x"*70+b"\r\n")*420   # ~30 KB
        art=(b"From: a@example.invalid\r\nNewsgroups: fn.test\r\nSubject: s%d\r\nMessage-ID: <c%d@example.invalid>\r\nDate: Fri, 25 Sep 2026 12:00:00 +0000\r\n\r\n"%(i,i))+body
        c=socket.create_connection(("127.0.0.1",port),60); f=c.makefile("rwb",buffering=0); f.readline()
        t=time.time(); f.write(b"POST\r\n"); f.readline(); f.write(art+b".\r\n"); rep=f.readline(); times.append(round(time.time()-t,3)); c.close()
    o.terminate(); o.wait(60)
    print(name, "reply", rep.strip(), "seconds per 30KB POST", times, flush=True)
