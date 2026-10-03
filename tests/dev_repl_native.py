#!/usr/bin/env python3
"""Exercise a real developer owner attachment using an existing executable.

Run under the build host's resource wrapper. --root must be a new scratch
coordinate; logs and Store are retained. No image construction or qualification.
"""
import argparse,os,signal,socket,subprocess,time,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import fn_dev
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--executable',type=Path,required=True)
parser.add_argument('--root',type=Path,required=True)
args=parser.parse_args()
root=args.root.resolve()
root.mkdir(parents=True,exist_ok=False)
wrapper=args.executable.resolve()
with socket.socket() as sock:
 sock.bind(('127.0.0.1',0));port=sock.getsockname()[1]
config=root/'fn.toml'
config.write_text(f'[store]\npath = "{root}/store"\n[listener]\nhost = "127.0.0.1"\nport = {port}\n[control]\npath = "{root}/control.sock"\n')
init=subprocess.run([str(wrapper),'--fn','operator',str(config),'init','--budget','2048','fn.test'],capture_output=True,text=True,timeout=60)
(root/'init.log').write_text(init.stdout+init.stderr)
assert init.returncode==0, (init.returncode,init.stdout,init.stderr)
print('INIT PASS',flush=True)
for phase in ['normal','fault']:
 path=root/'dev.sock'
 env=dict(os.environ,FN_NATIVE_DEV_REPL=str(path))
 with (root/(phase+'.log')).open('w') as log:
  owner=subprocess.Popen([str(wrapper),'--fn','operator',str(config),'run'],env=env,stdout=log,stderr=log)
  try:
   until=time.monotonic()+45
   while not path.exists():
    assert owner.poll() is None, (owner.returncode,(root/(phase+'.log')).read_text())
    assert time.monotonic()<until,'owner startup timeout'
    time.sleep(.05)
   assert path.stat().st_mode&0o777==0o600
   ok,text=fn_dev.evaluate(path,'(+ 1 2)',5)
   assert ok and text.strip()=='3',(ok,text)
   print(phase,'ACTUAL OWNER EVAL PASS',flush=True)
   if phase=='normal':
    ok,text=fn_dev.evaluate(path,"(fnn-dev-admit '((defun fn-dev-native-id (x) x)))",10)
    assert ok and ':ADMITTED' in text,(ok,text)
    ok,text=fn_dev.evaluate(path,"(fnn-dev-admit '((defthm fn-dev-native-false nil)))",10)
    assert not ok and 'admission incomplete' in text,(ok,text)
    assert fn_dev.evaluate(path,'(+ 20 22)',5)==(True,'42\n')
    assert owner.poll() is None
    print('ACTUAL OWNER LD REFUSAL/CONTINUATION PASS',flush=True)
    owner.send_signal(signal.SIGTERM)
    code=owner.wait(timeout=20)
    assert code==0,(code,(root/(phase+'.log')).read_text())
   else:
    try:
     ok,text=fn_dev.evaluate(path,'(error "intentional developer fence test")',10)
     assert not ok,(ok,text)
    except (ValueError,OSError):
     # Fault fencing may close the client before an ERROR envelope is sent.
     # Independently verify the actual owner exit and physical cleanup below.
     pass
    code=owner.wait(timeout=20)
    assert code==4,(code,(root/(phase+'.log')).read_text())
    print('ACTUAL OWNER FAULT/FENCE PASS',flush=True)
   assert not path.exists(), 'developer socket survived owner shutdown'
   print(phase,'CLEANUP PASS',flush=True)
  finally:
   if owner.poll() is None:
    owner.terminate()
    try:owner.wait(timeout=10)
    except subprocess.TimeoutExpired:owner.kill();owner.wait()
print('DEV-REPL-NATIVE-OWNER-PASS',flush=True)
