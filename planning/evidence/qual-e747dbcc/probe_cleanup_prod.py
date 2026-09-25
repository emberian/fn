import os, subprocess, signal, socket, time, select
I="/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6"
D="/tank/fn/scratch/qual-e747dbcc/probe-cleanup-prod"
subprocess.run(["rm","-rf",D]); os.makedirs(D)
env=dict(os.environ, ACL2_CUSTOMIZATION="NONE")
subprocess.run([I+"/fn-host-developer","--fn","store",D+"/store","init","fn.test"],env=env,check=True,capture_output=True)
s=socket.socket(); s.bind(("127.0.0.1",0)); port=s.getsockname()[1]; s.close()
open(D+"/fn.toml","w").write('[store]\npath = "%s/store"\n[listener]\nhost = "127.0.0.1"\nport = %d\n[control]\npath = "%s/control.sock"\n'%(D,port,D))
o=subprocess.Popen([I+"/fn-host","--fn","operator",D+"/fn.toml","run"],env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
lines=[]
while True:
    l=o.stdout.readline(); lines.append(l)
    if l.startswith(b"LISTENING") or not l: break
art=D+"/a.eml"; open(art,"wb").write(b"From: a@example.invalid\r\nNewsgroups: fn.test\r\nSubject: s\r\nMessage-ID: <p1@example.invalid>\r\nDate: Fri, 25 Sep 2026 12:00:00 +0000\r\n\r\nbody\r\n")
r=subprocess.run([I+"/fn-host","--fn","operator",D+"/fn.toml","post","--message-id","<p1@example.invalid>","--payload",art,"--group","fn.test"],env=dict(os.environ, ACL2_CUSTOMIZATION="NONE"),capture_output=True); print("post",r.returncode,r.stdout,r.stderr[-200:])
r=subprocess.run([I+"/fn-host-developer","--fn","operator",D+"/fn.toml","status"],env=env,capture_output=True); print("status",r.returncode)
o.send_signal(signal.SIGTERM)
select.select([o.stdout],[],[],30)
for _ in range(12):
    r=select.select([o.stdout],[],[],3)[0]
    if not r: break
    lines.append(o.stdout.readline())
o.send_signal(signal.SIGTERM); o.wait(30)
print("stdout lines:", lines, "rc", o.returncode)
print("stderr tail:", o.stderr.read()[-600:])
