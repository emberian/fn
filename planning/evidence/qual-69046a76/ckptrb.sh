#!/bin/sh
# qual-69046a76: a bbf52159-written checkpoint on a copy of the live store, then 69046a76 opens it
# (expected: checkpoint-open-refused, a full replay) with wall times; FN_NATIVE_* popped; versions proven.
set -u
S=/tank/fn/scratch/qual-69046a76
I=/tank/fn/gates/qual-69046a76-20260926/build/images/69046a76798b8be6169eeed5a66cc46fbe399e51
O=/tank/fn/gates/qual-bbf52159-20260925/build/images/bbf52159dcab19228bd6cd0b855b99dd6d68758d
for v in $(env | grep -o '^FN_NATIVE_[A-Z_]*'); do unset $v; done
unset LD_LIBRARY_PATH
export ACL2_CUSTOMIZATION=NONE
C=$S/ckpt-rb; rm -rf $C; mkdir -p $C
cp -a /tank/fn/node/store $C/store; rm -f $C/store/control.sock
printf '[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = 1\n[control]\npath = "%s"\n' $C/store $C/control.sock > $C/fn.toml
sha256sum $O/fn-host.core $I/fn-host.core
t() { s=$(date +%s.%N); "$@" 2>&1 | sed 's/^/  | /'; echo "  rc=$? wall=$(echo "$(date +%s.%N) - $s" | bc)"; }
echo "== bbf52159 status (before)"; t $O/fn-host --fn operator $C/fn.toml status
echo "== bbf52159 store checkpoint"; t $O/fn-host --fn operator $C/fn.toml store checkpoint
echo "== bbf52159 status (opens its own checkpoint)"; t $O/fn-host --fn operator $C/fn.toml status
ls -la $C/store
echo "== 69046a76 status on the bbf52159 checkpoint"; t $I/fn-host --fn operator $C/fn.toml status
echo "== 69046a76 status again"; t $I/fn-host --fn operator $C/fn.toml status
echo "== 69046a76 recover"; t $I/fn-host --fn operator $C/fn.toml recover
