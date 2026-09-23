#!/bin/bash
# persvati-acl2p.sh: build ACL2(p) 8.7 beside the plain w25 toolchain on
# persvati, and measure one book's certification under it.  A measurement
# runbook, not a gate: nothing here publishes to /home/ember/fn-certcache.
# Evidence and numbers: planning/evidence/acl2p-2026-09-23.md.
#
#   persvati-acl2p.sh build
#   persvati-acl2p.sh measure <book> <mode> [cpus]   (run inside the gate)
#
# modes: plain | par-nil | par-rb | par-full | par-full-serialfallback | par-full-sf32
set -u
TC=/home/ember/fn-gates/toolchains
GATE=/home/ember/fn-gates/acl2p

build() {
  # Same source as w25: /home/ember/fn-tools/acl2.tar.gz, the ACL2 8.7
  # release tarball (sha256 d6013c22e190cbd702870d296b5370a068c14625bf7f9d305d2d87292b594d52),
  # same SBCL 2.6.8.  About 32 s of wall; the bootstrap is single-threaded.
  mkdir -p $TC/w25p && cd $TC/w25p
  tar xzf /home/ember/fn-tools/acl2.tar.gz
  cd acl2-8.7
  nice -n 15 taskset -c 0-7 make LISP=/home/ember/fn-tools/sbcl/bin/sbcl ACL2_PAR=t > ../acl2p-build.log 2>&1
  # The launcher: w25/acl2-literal with only the core swapped (8 GB heap).
  sed "s|/home/ember/fn-tools/acl2-8.7/saved_acl2.core|$TC/w25p/acl2-8.7/saved_acl2p.core|" \
      $TC/w25/acl2-literal > $TC/w25p/acl2-literal
  chmod +x $TC/w25p/acl2-literal
  # The 98 system-book certificates w25 has, certified by ACL2(p) in the
  # DEFAULT book-hash mode (no ACL2_BOOK_HASH_ALISTP), as w25's were: fn's
  # certificates record each system book by (length, write-date), and the
  # tarball preserves write dates, so both trees then agree.
  cd /home/ember/fn-tools/acl2-8.7/books && find . -name '*.cert' | sed 's|^\./||' > $TC/w25p/sysbook-targets.txt
  cd $TC/w25p/acl2-8.7/books
  ACL2_CUSTOMIZATION=NONE nice -n 15 taskset -c 0-7 ./build/cert.pl \
      --acl2 $TC/w25p/acl2-literal -j 8 $(cat $TC/w25p/sysbook-targets.txt) > $TC/w25p/sysbooks.log 2>&1
}

measure() {
  BOOK=$1; MODE=$2; CPUS=${3:-8-15}
  OUT=$GATE/build/acl2p-runs/$BOOK.$MODE
  mkdir -p $OUT && cd $GATE
  PAR=$TC/w25p/acl2-literal
  case $MODE in
    plain)    ACL2=$TC/w25/acl2-literal; PRE="";;
    par-nil)  ACL2=$PAR; PRE="(set-waterfall-parallelism nil)";;
    par-rb)   ACL2=$PAR; PRE="(set-waterfall-parallelism :resource-based)";;
    par-full) ACL2=$PAR; PRE="(set-waterfall-parallelism :full)";;
    par-full-serialfallback) ACL2=$PAR; PRE="(set-waterfall-parallelism :full)
(set-total-parallelism-work-limit-error nil)";;
    # ACL2's generated launcher: the same core with a 32000 MB heap.
    par-full-sf32) ACL2=$TC/w25p/acl2-8.7/saved_acl2p; PRE="(set-waterfall-parallelism :full)
(set-total-parallelism-work-limit-error nil)";;
    *) echo "unknown mode $MODE" >&2; return 2;;
  esac
  NCPU=$(taskset -c "$CPUS" python3 -c 'import os; print(len(os.sched_getaffinity(0)))')
  # SBCL gives ACL2(p) no core count; without this it assumes 16.
  export ACL2_CUSTOMIZATION=NONE ACL2_BOOK_HASH_ALISTP=NIL ACL2_CORE_COUNT=$NCPU
  unset ACL2_SYSTEM_BOOKS
  rm -f books/$BOOK.cert books/$BOOK.fasl books/$BOOK.port
  cat > $OUT/driver.lsp <<DRV
$PRE
(ld '((certify-book "books/$BOOK" ? t)
      (value-triple (cw "~%FN_ACL2P_OK $BOOK $MODE~%")))
    :ld-error-action :return
    :ld-error-triples t)
(quit)
DRV
  date -u +%FT%TZ > $OUT/start
  # time -> nice -> taskset exec into the launcher, which execs sbcl: the
  # child pid is the ACL2 pid.  Stop it by that pid, never by pattern.
  /usr/bin/time -v -o $OUT/time.txt nice -n 10 taskset -c "$CPUS" $ACL2 < $OUT/driver.lsp > $OUT/log.txt 2>&1 &
  TPID=$!
  sleep 3
  SB=$(pgrep -P $TPID | head -1); [ -z "$SB" ] && SB=$TPID
  echo $SB > $OUT/acl2.pid
  : > $OUT/threads.tsv
  # epoch, threads, threads over 20% CPU (top -H), utime+stime ticks
  while kill -0 $TPID 2>/dev/null; do
    T=$(ls /proc/$SB/task 2>/dev/null | wc -l)
    BUSY=$(top -H -b -n 1 -p $SB 2>/dev/null | awk 'NR>7 && $9+0>=20 {n++} END{print n+0}')
    TICKS=$(awk '{print $14+$15}' /proc/$SB/stat 2>/dev/null)
    echo -e "$(date +%s)\t$T\t$BUSY\t$TICKS" >> $OUT/threads.tsv
    sleep 10
  done
  wait $TPID; echo "exit $?" > $OUT/exit
  date -u +%FT%TZ > $OUT/end
  cp -p books/$BOOK.cert books/$BOOK.fasl books/$BOOK.port $OUT/ 2>/dev/null
  grep -c "FN_ACL2P_OK $BOOK $MODE" $OUT/log.txt > $OUT/ok
}

case ${1:-} in
  build) build;;
  measure) shift; measure "$@";;
  *) sed -n 2,12p "$0"; exit 2;;
esac
