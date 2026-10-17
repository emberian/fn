#!/bin/sh
# builds launchers + compiles hook.  B = developer image (hooked copy of its launcher); A = fn-core
cd /tank/fn/scratch/n-mem3
export SBCL_HOME='/tank/fn/sbcl/lib/sbcl/'
/tank/fn/sbcl/bin/sbcl --dynamic-space-size 2000 --core /tank/fn/scratch/attach-gate/native-ag4-6679dae0e/tree/build/fn-host-developer.core --noinform --end-runtime-options --no-userinit --eval '(progn (compile-file "/tank/fn/scratch/n-mem3/mem3hook.lisp") (sb-ext:exit))' --disable-debugger --end-toplevel-options > compile.log 2>&1
I=/tank/fn/scratch/mini-fnbin/6679dae0e/fn-6679dae0e
cat > fn-host-mem3.sh <<EOS
#!/bin/sh
here=$I
export SBCL_HOME="\$here/runtime/sbcl-home/"
export LD_LIBRARY_PATH="\$here/lib\${LD_LIBRARY_PATH:+:\$LD_LIBRARY_PATH}"
FN_OPENSSL_PREFIX="\${FN_OPENSSL_PREFIX:-\$here/openssl}"; export FN_OPENSSL_PREFIX
exec "\$here/runtime/sbcl" --tls-limit 65536 --dynamic-space-size 32000 --control-stack-size 1024KB --disable-ldb --core "\$here/fn-host-developer.core" --noinform \${SBCL_USER_ARGS} --end-runtime-options --no-userinit --eval '(load "/tank/fn/scratch/n-mem3/mem3hook.fasl")' --eval '(acl2::sbcl-restart)' --disable-debugger --end-toplevel-options "\$@"
EOS
cat > fn-core-mem3.sh <<'EOS'
#!/bin/sh
export SBCL_HOME='/tank/fn/sbcl/lib/sbcl/'
exec "/tank/fn/sbcl/bin/sbcl" --tls-limit 65536 --dynamic-space-size 32000 --control-stack-size 1024KB --disable-ldb --core "/tank/fn/scratch/extract-core/tree2/build/core-e3/fn-core.core" --noinform ${SBCL_USER_ARGS} --end-runtime-options --no-userinit --no-sysinit --eval '(load "/tank/fn/scratch/n-mem3/mem3hook.fasl")' --eval '(cl-user::xl-toplevel)' --disable-debugger --end-toplevel-options "$@"
EOS
chmod +x fn-host-mem3.sh fn-core-mem3.sh
echo made
