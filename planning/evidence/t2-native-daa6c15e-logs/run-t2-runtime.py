from pathlib import Path
import hashlib, json, os, subprocess, sys, time
root=Path('/tank/fn/gates/takeover-t2-image-daa6c15e')
rev='daa6c15ef9d5c900b6e31ec9c9b51b9aaa708789'
image=root/'build/images'/rev
old=Path('/tank/fn/gates/takeover-image-upgrade-f0b8b166/build/images/f0b8b166a3d5d56124ba45114bda0bd34affa5b8/fn-host-developer')
wrapper=root/'build/freeze/acl2-test-slotted'
wrapper.write_text('#!/bin/sh\nexport FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g\nexec '+str(root/'tools/acl2')+' --timeout 300 "$@"\n')
wrapper.chmod(0o755)
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
env=dict(os.environ,FN_ACL2=str(wrapper),ACL2_CUSTOMIZATION='NONE',ACL2_BOOK_HASH_ALISTP='NIL',FN_OPENSSL_PREFIX=str(image/'openssl'),FN_NATIVE_HOST=str(image/'fn-host'),FN_NATIVE_DEVELOPER_HOST=str(image/'fn-host-developer'),FN_NATIVE_CRASH_HOST=str(image/'fn-host-developer'),FN_NATIVE_IMAGE_SOURCE_SHA=rev,FN_PRE_T2_NATIVE_DEVELOPER_HOST=str(old),FN_T2_NATIVE_DEVELOPER_HOST=str(image/'fn-host-developer'))
for key,file in [('FN_NATIVE_LAUNCHER_SHA256','fn-host'),('FN_NATIVE_CORE_SHA256','fn-host.core'),('FN_NATIVE_RUNTIME_SHA256','runtime/sbcl'),('FN_NATIVE_DEVELOPER_LAUNCHER_SHA256','fn-host-developer'),('FN_NATIVE_DEVELOPER_CORE_SHA256','fn-host-developer.core')]: env[key]=digest(image/file)
modules=sys.argv[1:] or ['tests.test_native_stamp_migration','tests.test_native_checkpoint','tests.test_native_admin','tests.test_bp_obligation_native','tests.test_native_protected_peering']
results=[]
for module in modules:
 start=time.monotonic();log=root/'build/freeze'/(module.rsplit('.',1)[-1]+'.log')
 with log.open('w') as f:
  command=[sys.executable,'-m','unittest','-v',module]
  if module=='tests.test_native_stamp_migration':
   repaired=root/'build/freeze/test_native_stamp_migration_repaired.py'
   code='import types, unittest; from pathlib import Path; p=Path('+repr(str(repaired))+'); m=types.ModuleType("migration_repaired"); m.__file__='+repr(str(root/'tests/test_native_stamp_migration.py'))+'; exec(compile(p.read_text(),str(p),"exec"),m.__dict__); suite=unittest.defaultTestLoader.loadTestsFromModule(m); assert suite.countTestCases()==1; result=unittest.TextTestRunner(verbosity=2).run(suite); raise SystemExit(not result.wasSuccessful() or bool(result.skipped))'
   command=[sys.executable,'-c',code]
  result=subprocess.run(command,cwd=root,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=480)
 entry=dict(module=module,exit=result.returncode,seconds=round(time.monotonic()-start,3),log=str(log),log_sha256=digest(log))
 results.append(entry);print(json.dumps(entry),flush=True)
(root/'build/freeze'/('runtime-'+str(os.getpid())+'.json')).write_text(json.dumps(dict(source=rev,results=results),indent=2)+'\n')
raise SystemExit(any(r['exit'] for r in results))
