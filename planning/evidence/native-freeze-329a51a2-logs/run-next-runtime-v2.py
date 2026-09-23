from pathlib import Path
import hashlib, json, os, subprocess, sys, time
root=Path(sys.argv[1]).resolve(); rev=sys.argv[2]; image=root/'build/images'/rev
old=Path('/tank/fn/gates/takeover-image-upgrade-f0b8b166/build/images/f0b8b166a3d5d56124ba45114bda0bd34affa5b8/fn-host-developer')
freeze=Path(os.environ.get('FN_QUALIFICATION_DIR', str(root/'build/freeze'))); freeze.mkdir(parents=True,exist_ok=True)
wrapper=freeze/'acl2-test-slotted'
wrapper.write_text('#!/bin/sh\nexport FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g\nexec '+str(root/'tools/acl2')+' --timeout 300 "$@"\n');wrapper.chmod(0o755)
openssl_wrapper=freeze/'openssl-test'
openssl_wrapper.write_text('#!/bin/sh\nexec env LD_LIBRARY_PATH='+str(image/'openssl/lib')+' /tank/fn/toolchains/openssl-3.5.8/bin/openssl \"$@\"\n');openssl_wrapper.chmod(0o755)
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
env=dict(os.environ,FN_ACL2=str(wrapper),ACL2_CUSTOMIZATION='NONE',ACL2_BOOK_HASH_ALISTP='NIL',FN_OPENSSL_PREFIX=str(image/'openssl'),FN_NATIVE_HOST=str(image/'fn-host'),FN_NATIVE_DEVELOPER_HOST=str(image/'fn-host-developer'),FN_NATIVE_DTN_DEVELOPER_HOST=str(image/'fn-host-dtn-developer'),FN_NATIVE_CRASH_HOST=str(image/'fn-host-developer'),FN_NATIVE_IMAGE_SOURCE_SHA=rev,FN_PRE_T2_NATIVE_DEVELOPER_HOST=str(old),FN_T2_NATIVE_DEVELOPER_HOST=str(image/'fn-host-developer'),FN_T2B_NATIVE_DEVELOPER_HOST=str(image/'fn-host-developer'),FN_TEST_OPENSSL=str(openssl_wrapper),FN_RUN_HYBRID_E2E='1',FN_PRE_T2_IMAGE=str(old),FN_T2_IMAGE=str(image/'fn-host-developer'),FN_T2_PROBE_ROOT=str(freeze/'migration-stores'))
for key,file in [('FN_NATIVE_LAUNCHER_SHA256','fn-host'),('FN_NATIVE_CORE_SHA256','fn-host.core'),('FN_NATIVE_RUNTIME_SHA256','runtime/sbcl'),('FN_NATIVE_DEVELOPER_LAUNCHER_SHA256','fn-host-developer'),('FN_NATIVE_DEVELOPER_CORE_SHA256','fn-host-developer.core')]:env[key]=digest(image/file)
modules=sys.argv[3:] or ['tests.test_native_stamp_migration','tests.test_native_newnews_migration','tests.test_native_hybrid_author','tests.test_bp_app_native','tests.test_native_app_journal','tests.test_native_checkpoint','tests.test_native_admin','tests.test_bp_obligation_native','tests.test_native_protected_peering','tests.test_native_served_crash_model','tests.test_native_crash_model']
results=[]
for module in modules:
 start=time.monotonic(); log=freeze/(module.rsplit('.',1)[-1]+'.log')
 code='import unittest; suite=unittest.defaultTestLoader.loadTestsFromName('+repr(module)+'); assert suite.countTestCases()>0; result=unittest.TextTestRunner(verbosity=2).run(suite); raise SystemExit(not result.wasSuccessful() or bool(result.skipped))'
 command=[sys.executable,'-c',code]
 if module=='checkpoint-migration-probe':command=[sys.executable,'tests/campaign/t2_checkpoint_migration_probe.py']
 with log.open('w') as f:
  try: result=subprocess.run(command,cwd=root,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=480);status=result.returncode
  except subprocess.TimeoutExpired: status=124;f.write('\nDRIVER TIMEOUT\n')
 entry=dict(module=module,exit=status,seconds=round(time.monotonic()-start,3),log=str(log),log_sha256=digest(log));results.append(entry); print(json.dumps(entry),flush=True)
 (freeze/'runtime-results.json').write_text(json.dumps(dict(source=rev,driver_sha256=digest(Path(__file__)),results=results),indent=2)+'\n')
raise SystemExit(any(r['exit'] for r in results))
