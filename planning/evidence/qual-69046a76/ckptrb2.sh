#!/bin/sh
# qual-69046a76: the reverse: a 69046a76-written checkpoint on a copy of the live store, then bbf52159 opens it
# (the deploy note's sentence: an older image rejects a newer checkpoint file and falls back to a full replay).
set -u
S=/tank/fn/scratch/qual-69046a76
I=/tank/fn/gates/qual-69046a76-20260926/build/images/69046a76798b8be6169eeed5a66cc46fbe399e51
O=/tank/fn/gates/qual-bbf52159-20260925/build/images/bbf52159dcab19228bd6cd0b855b99dd6d68758d
for v in $(env | grep -o '^FN_NATIVE_[A-Z_]*'); do unset $v; done
unset LD_LIBRARY_PATH
export ACL2_CUSTOMIZATION=NONE
C=$S/ckpt-rb2; rm -rf $C; mkdir -p $C
cp -a /tank/fn/node/store $C/store; rm -f $C/store/control.sock
printf '[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = 1\n[control]\npath = "%s"\n' $C/store $C/control.sock > $C/fn.toml
sha256sum $O/fn-host.core $I/fn-host.core
t() { s=$(date +%s.%N); "$@" 2>&1 | sed 's/^/  | /'; echo "  rc=$? wall=$(echo "$(date +%s.%N) - $s" | bc)"; }
echo "== 69046a76 --version"; t $I/fn-host --fn --version
echo "== bbf52159 --version (a verb it lacks: proves the old image answered)"; t $O/fn-host --fn --version
echo "== 69046a76 store checkpoint"; t $I/fn-host --fn operator $C/fn.toml store checkpoint
echo "== 69046a76 status (opens its own checkpoint)"; t $I/fn-host --fn operator $C/fn.toml status
ls -la $C/store
echo "== bbf52159 status on the 69046a76 checkpoint"; t $O/fn-host --fn operator $C/fn.toml status
echo "== bbf52159 recover"; t $O/fn-host --fn operator $C/fn.toml recover
