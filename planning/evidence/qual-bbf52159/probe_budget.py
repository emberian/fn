import os, subprocess, socket, time
img="/tank/fn/gates/qual-bbf52159-20260925/build/images/bbf52159dcab19228bd6cd0b855b99dd6d68758d/fn-host"
D="/tank/fn/scratch/qual-bbf52159/probe-budget"
subprocess.run(["rm","-rf",D]); os.makedirs(D)
env=dict(os.environ, ACL2_CUSTOMIZATION="NONE")
subprocess.run([img,"--fn","store",D+"/store","init","fn.test"],env=env,check=True,capture_output=True)
s=socket.socket(); s.bind(("127.0.0.1",0)); port=s.getsockname()[1]; s.close()
open(D+"/fn.toml","w").write('[store]\npath = "%s/store"\n[listener]\nhost = "127.0.0.1"\nport = %d\n[control]\npath = "%s/control.sock"\n'%(D,port,D))
err=open(D+"/owner.err","wb")
o=subprocess.Popen([img,"--fn","operator",D+"/fn.toml","run"],env=env,stdout=subprocess.PIPE,stderr=err)
while not o.stdout.readline().startswith(b"LISTENING"): pass
def post(i):
    art=(b"From: a@example.invalid\r\nNewsgroups: fn.test\r\nSubject: s%d\r\nMessage-ID: <b%d@example.invalid>\r\nDate: Fri, 25 Sep 2026 12:00:00 +0000\r\n\r\nbody\r\n"%(i,i))
    try:
        c=socket.create_connection(("127.0.0.1",port),60); f=c.makefile("rwb",buffering=0); f.readline()
        f.write(b"POST\r\n"); r1=f.readline(); f.write(art+b".\r\n"); rep=f.readline(); c.close(); return (r1+rep).decode().replace("\r\n"," | ")
    except Exception as e: return "EXC %r"%e
rs=[post(i) for i in range(128)]
print("first 128:", {r:rs.count(r) for r in set(rs)})
for i in (128,129):
    print("POST", i, "->", post(i), "owner poll", o.poll())
time.sleep(1); print("owner exit", o.poll())
if o.poll() is None: o.terminate(); o.wait(60)
print("owner.err tail:", open(D+"/owner.err","rb").read()[-900:].decode("utf-8","replace"))
r=subprocess.run([img,"--fn","operator",D+"/fn.toml","status"],env=env,capture_output=True); print("status rc",r.returncode, r.stdout.decode()[:300])
