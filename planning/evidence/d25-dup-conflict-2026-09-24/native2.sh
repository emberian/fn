#!/bin/sh
S=/tank/fn/scratch/d25-dup
T=$S/img
BEFORE=/tank/fn/gates/qual-47bdb9a4-20260924/build/images/47bdb9a4/fn-host-developer
AFTER=$T/build/fn-host-developer
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
export LD_LIBRARY_PATH=$FN_OPENSSL_PREFIX/lib PYTHONDONTWRITEBYTECODE=1
export ACL2_CUSTOMIZATION=NONE; unset ACL2_SYSTEM_BOOKS
cd $T || exit 1
python3 -c "import sys; sys.path.insert(0,'tools'); import v0_matrix as m; open('$S/matrix.py','w').write(m.MATRIX_DRIVER)"
python3 -c "import sys; sys.path.insert(0,'tools'); import deploy_gate as d; open('$S/drive.py','w').write(d.DRIVER)"
sha256sum $S/drive.py $S/matrix.py tools/v0_matrix.py > $S/matrix-driver.sha256
postcycles () { # label image port
  W=$S/pc-$1; rm -rf $W; mkdir -p $W
  "$2" --fn store $W/store init fn.letters > $W/init.out 2>&1
  printf '[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %s\n[control]\npath = "%s"\n' "$W/store" "$3" "$W/control.sock" > $W/fn.toml
  "$2" --fn operator $W/fn.toml run > $W/owner.out 2> $W/owner.err &
  OWNER=$!
  i=0; while [ $i -lt 120 ] && ! grep -q '^LISTENING' $W/owner.out; do sleep 1; i=$((i+1)); done
  for n in 1 2 3; do
    date -u +%FT%T.%NZ > $W/pc$n.start
    python3 $S/matrix.py postcycle --port $3 --group fn.letters --msgid '<d25-matrix@example.invalid>' > $W/pc$n.json 2> $W/pc$n.err
    sleep 2
  done
  kill -TERM $OWNER; wait $OWNER; echo "owner exit $?" > $W/owner.exit
}
ss -ltn | grep -qE ':(11390|11391) ' && { echo ports busy; exit 1; }
postcycles before $BEFORE 11390
postcycles after $AFTER 11391
echo PC-DONE
