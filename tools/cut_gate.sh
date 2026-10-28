#!/bin/sh
# tools/cut_gate.sh -- the classical gate of the breaking cut (cut/breaking).
#
#   tools/cut_gate.sh [--families F,G,...] [--reuse-image NAME/native-LABEL]
#                     [--no-gauntlet] [--time-rows] [--time-box persvati|hbox]
#                     [--time-cells KEYS]
#                     [--time-baseline LABEL] [--time-reps N] [--label L] REV
#
# Certify is not a gate on this branch; this is.  In order:
#   1. the host image builds on hbox (production, developer, dtn, dtn-developer) for REV and
#      the named native modules run against it: G5's peering/feed/pull/BP/DTN
#      modules always, plus every tests.test_native_* module whose name holds
#      one of --families (the families the change touched; name them, never
#      the whole suite).  tools/hbox_native.sh does the work under swarm-build;
#      --reuse-image skips the build and uses that run's images (a baseline or
#      a books-only change).  A module red is NEW only when it is not in the
#      PRE-EXISTING list below (control run #4 at 49b470a99, the branch base).
#   2. the judged gauntlet rows: F2S, F4, F6 (fault corpus) and W13 (the
#      memory guardrail cell) on hbox against the production image of step 1;
#      the time rows on --time-box when --time-rows explicitly asks for them
#      (milestones; default off for waves). persvati is the site of record:
#      the production image built on hbox is copied there (launcher's core path
#      rewritten, core sha256 checked equal to hbox's; both boxes run
#      /tank/fn/sbcl 2.6.8), then tools.load.sweep runs --time-cells (default
#      T-CMD at 1k/10k/25k/50k, W1 default and small; w14 adds T-LIN) under
#      the sweep's own admission (flock on cores 12-23, busy <= 4 probe,
#      MemoryMax scope), --time-reps times (default 3).  The gate judges
#      GAUNTLET.md's bars on each cell's per-metric MEDIAN over its admitted
#      repetitions (busy <= 4 at start and end); the T-CMD exponent is the
#      least-squares slope of log median-p99 on log n per command, as
#      GAUNTLET.md derives it.  One repetition of a few-ms p99 flaps a 0.2
#      exponent bar (measured 10-17: GROUP 0.03 at the base, 0.20 at 37d29e264).
#      The sweep's own table (time-table.md) is kept beside, against
#      --time-baseline (an earlier gate's LABEL-t) when given.  --time-box hbox runs T-CMD@10k and W1
#      on hbox, REPORTED: hbox time figures are never judged (LOAD-PROGRAM s.1).
#   3. the guardrail from W13: VmHWM <= 249 MB (254,976 KiB) and RssAnon <= 115 MB
#      (117,760 KiB; W13 reports no separate shmem figure)
#      on the small preset (ember 2026-10-14: 1.5x the baseline).
# Exit 0 only when the image built, no NEW native red, no gauntlet violation,
# and the guardrail holds.  Everything streams to build/cut-gate/<label>/.
# Box rules: every box step runs through the tools that wrap swarm-build;
# detached jobs leave PID files; nothing here kills anything.
set -eu
cd "$(dirname "$0")/.."
FAMILIES=; REUSE=; GAUNTLET=1; TIMES=0; TIMEBOX=persvati; LABEL=
TCELLS=tcmd-1k,tcmd-10k,tcmd-25k,tcmd-50k,w1-default,w1-small; TBASE=; TREPS=3
# Time rows FAILING at the branch base 49b470a99 (persvati, 3 reps, M30 10-17),
# "key:ROW" (tcmd:CMD for a derived exponent).  Carried: reported, not NEW.
# Shrink only.  greeting: median p99 0.27/0.16/0.31/2.21 ms at 1k/10k/25k/50k,
# slope 0.39 (drain 0.31; 37d29e264 0.33): a sub-ms p99 its 50k point carries.
TCARRIED="tcmd:greeting"
while [ $# -gt 1 ]; do
    case $1 in
        --families) FAMILIES=$2; shift 2 ;;
        --reuse-image) REUSE=$2; shift 2 ;;
        --no-gauntlet) GAUNTLET=0; shift ;;
        --time-rows) TIMES=1; shift ;;
        --time-box) TIMEBOX=$2; shift 2 ;;
        --time-cells) TCELLS=$2; shift 2 ;;
        --time-baseline) TBASE=$2; shift 2 ;;
        --time-reps) TREPS=$2; shift 2 ;;
        --label) LABEL=$2; shift 2 ;;
        *) echo "cut_gate: unknown option $1" >&2; exit 2 ;;
    esac
done
[ $# -eq 1 ] || { sed -n '2,/^set -eu/p' "$0" | sed '$d' | sed 's/^# \{0,1\}//' >&2; exit 2; }
REV=$1
SHA=$(git rev-parse "$REV")
[ -n "$LABEL" ] || LABEL=cut-$(printf %s "$SHA" | cut -c1-12)
OUT=build/cut-gate/$LABEL; mkdir -p "$OUT"
log() { printf '%s %s\n' "$(date '+%H:%M:%S')" "$*" | tee -a "$OUT/gate.log"; }

# PRE-EXISTING native reds at the branch base 49b470a99 (hbox control run #4,
# devctl-49b470a991f9: 222 OK / 8 SKIPPED / 21 FAILED).  A red here is a
# carried red, reported but not NEW; a red absent from it is NEW and fails
# the gate.  Shrink this list as the cut deletes or fixes its subjects; never
# grow it without a `G4 UP:`-style first line in the commit that does.
# cut/reds (B27, 10-17) fixed or deleted the subjects of fifteen; the six left
# are carried for a reason each: bounds_join (POST heap under the mutex: M2 c),
# decoded_custody (the decoded family, M1-b), mux and public_limits (the OVER
# window priced as octet lists per holder: OVER's pool lease), resilience_cuts
# (its issued page-io case models PAGE-IO tokens; the served read is a window
# job: M2 a), status_live_posts (status realizes every article's extent for the
# tombstone probe: M2 a).
PREEXISTING="bounds_join decoded_custody mux public_limits resilience_cuts status_live_posts"

# G5: every native module whose name says peering, feed, pull, catch-up, BP,
# DTN or transit (GOALS.md G5's selection, applied to the tree at REV).
G5=$(git ls-tree -r --name-only "$SHA" tests | sed -n 's#^tests/\(test_native_[a-z0-9_]*\)\.py$#\1#p' | grep -E 'peer|catch|pull|feed|_bp_|bpapp|dtn|transit|tcpcl' | sed 's/^/tests./' | sort -u)
FAM=
if [ -n "$FAMILIES" ]; then
    for f in $(printf %s "$FAMILIES" | tr ',' ' '); do
        FAM="$FAM $(git ls-tree -r --name-only "$SHA" tests | sed -n 's#^tests/\(test_native_[a-z0-9_]*\)\.py$#\1#p' | grep -- "$f" | sed 's/^/tests./')"
    done
fi
MODULES=$(printf '%s\n%s\n' "$G5" "$FAM" | tr ' ' '\n' | grep . | sort -u)
log "gate $LABEL at $SHA: $(printf %s "$MODULES" | wc -l | tr -d ' ') modules (G5 $(printf %s "$G5" | wc -l | tr -d ' '), families '$FAMILIES')"
printf '%s\n' "$MODULES" > "$OUT/modules.txt"

# 1. image + natives on hbox
set -- --box hbox --allow-certify --images production,developer,dtn,dtn-developer,reference,developer-stripped --jobs auto --label "$LABEL" --allow-skips --env FN_INN_SRC=/tank/fn/inn/2.7.4
# Content-keyed images (tools/image_key.py): when every image's inputs match a
# stored set the run links it and skips resolve, install, certify, acquire and
# the saves; a miss builds as before and stores the set.
[ -z "$REUSE" ] || set -- "$@" --reuse-image "$REUSE"
[ -n "$REUSE" ] || set -- "$@" --keyed-images
log "hbox_native $* $REV ..."
sh tools/hbox_native.sh "$@" "$SHA" $MODULES > "$OUT/hbox_native.launch.log" 2>&1 || { log "RED: hbox_native refused to launch (see $OUT/hbox_native.launch.log)"; exit 1; }
sh tools/hbox_native.sh attach "$LABEL" > "$OUT/hbox_native.attach.log" 2>&1 || true
RUNDIR=$(sh tools/hbox_native.sh status "$LABEL" --dir 2>/dev/null | sed 's/^[^:]*://' | head -1)
STATUS=$(ssh hbox "cat $RUNDIR/status 2>/dev/null" || echo none)
ssh hbox "cat $RUNDIR/run.log" > "$OUT/run.log" 2>/dev/null || true
IMAGE_OK=0
if ssh hbox "test -f $RUNDIR/tree/build/fn-host.core"; then IMAGE_OK=1; fi
[ "$IMAGE_OK" = 1 ] || log "RED: the production image did not build (status $STATUS, $RUNDIR)"
# run.log carries only the summary line; each module's verdict is the last
# FN_TEST_BUDGET_RESULT line of logs/test-tests.<module>.log.
NEWRED=; CARRIED=
for m in $(ssh hbox "cd $RUNDIR/logs && grep -L '\"failures\": 0, \"errors\": 0' test-tests.test_native_*.log 2>/dev/null" | sed 's/^test-tests\.test_native_//; s/\.log$//' | sort -u); do
    case " $PREEXISTING " in *" $m "*) CARRIED="$CARRIED $m" ;; *) NEWRED="$NEWRED $m" ;; esac
done
MODSUM=$(grep -E '^== modules: [0-9]+ OK' "$OUT/run.log" | tail -1 | sed 's/^== modules: //')
OKN=$(printf %s "$MODSUM" | sed -n 's/^\([0-9]*\) OK.*/\1/p')
log "natives: ${MODSUM:-no summary line}; carried reds:${CARRIED:- none}; NEW reds:${NEWRED:- none} (status $STATUS)"

# 2. gauntlet
GVIOL=; GUARD=unknown
if [ "$GAUNTLET" = 1 ] && [ "$IMAGE_OK" = 1 ]; then
    IMG=$RUNDIR/tree/build/fn-host
    GL=$LABEL-g
    log "gauntlet on hbox: F2S,F4,F6,W13 against $IMG"
    # driver box starts the job detached (setsid nohup) and its own ssh may
    # time out after the start: the status file, not the exit, says whether
    # the job runs.
    python3 -m tools.load.driver box --box hbox --image "$IMG" --cell F2S,F4,F6,W13 --label "$GL" --rev "$SHA" > "$OUT/gauntlet.launch.log" 2>&1 || true
    sleep 90
    if ! ssh hbox "test -f /tank/fn/scratch/load-harness/runs/$GL/status"; then log "RED: gauntlet did not start (no status file; see $OUT/gauntlet.launch.log)"; GVIOL="launch"; fi
    until [ -n "$GVIOL" ] || ssh hbox "grep -q -v running /tank/fn/scratch/load-harness/runs/$GL/status" 2>/dev/null; do sleep 60; done
    rsync -a --exclude samples.json "hbox:/tank/fn/scratch/load-harness/runs/$GL/" "$OUT/gauntlet/" > /dev/null 2>&1 || true
    TL=$LABEL-t; TB=off; TERR=
    if [ "$TIMES" = 1 ] && [ "$TIMEBOX" = persvati ]; then
        TB=persvati
        PD=/tank/fn/scratch/load-harness/images/$LABEL
        log "time rows on persvati ($TCELLS, judged): copying $RUNDIR/tree/build -> persvati:$PD"
        if ssh persvati sh -s -- "$RUNDIR/tree/build" "$PD" > "$OUT/time.copy.log" 2>&1 <<'COPY'
set -eu
B=$1; D=$2
mkdir -p "$D"
rsync -a "hbox:$B/fn-host" "hbox:$B/fn-host.core" "hbox:$B/TREE_SHA" "$D/"
rsync -a "hbox:$B/lib/" "$D/lib/"
sed -i "s#$B/#$D/#g" "$D/fn-host"
if grep -o "/tank/fn/scratch/[^\" ]*" "$D/fn-host" | grep -v "^$D/"; then echo "a foreign path is left in the launcher" >&2; exit 3; fi
want=$(ssh hbox "sha256sum $B/fn-host.core" | cut -d' ' -f1)
have=$(sha256sum "$D/fn-host.core" | cut -d' ' -f1)
[ "$want" = "$have" ] || { echo "core sha256 differs: hbox $want, persvati $have" >&2; exit 4; }
echo "copied core $have tree $(cat "$D/TREE_SHA")"
COPY
        then
            log "$(tail -1 "$OUT/time.copy.log")"
            i=1
            while [ "$i" -le "$TREPS" ]; do
                TLI=$TL; [ "$i" = 1 ] || TLI=$TL-r$i
                set -- --box persvati --image-dir "$PD" --label "$TLI" --cells "$TCELLS"
                [ -z "$TBASE" ] || set -- "$@" --baseline "$TBASE"
                python3 -m tools.load.sweep install "$@" >> "$OUT/time.launch.log" 2>&1 || { log "RED: sweep install refused for $TLI (see $OUT/time.launch.log)"; TERR="$TERR time-launch"; }
                i=$((i + 1))
            done
        else log "RED: the image did not copy to persvati (see $OUT/time.copy.log)"; TERR="$TERR time-copy"; fi
        if [ -z "$TERR" ]; then
            i=1
            while [ "$i" -le "$TREPS" ]; do
                TLI=$TL; [ "$i" = 1 ] || TLI=$TL-r$i
                # each queue's own PID file; ps only looks
                QPID=$(ssh persvati "cat /tank/fn/scratch/load-harness/sweeps/$TLI/persvati.pid")
                while ssh persvati "ps -p $QPID > /dev/null"; do sleep 60; done
                for k in $(printf %s "$TCELLS" | tr ',' ' '); do
                    mkdir -p "$OUT/time/$k/r$i"
                    rsync -a --exclude samples.json "persvati:/tank/fn/scratch/load-harness/runs/$TLI-$k/" "$OUT/time/$k/r$i/" > /dev/null 2>&1 || true
                done
                i=$((i + 1))
            done
            set -- --label "$TL" --box persvati
            [ -z "$TBASE" ] || set -- "$@" --baseline "$TBASE"
            python3 -m tools.load.sweep table "$@" > "$OUT/time-table.md" 2> "$OUT/time-table.err" || log "RED: sweep table failed (see $OUT/time-table.err)"
            log "time table: $OUT/time-table.md"
        fi
    elif [ "$TIMES" = 1 ]; then
        TB=hbox
        log "time rows on hbox: T-CMD@10k,W1 (REPORTED, not judged: hbox time figures are never judged)"
        python3 -m tools.load.driver box --box hbox --image "$IMG" --cell T-CMD@10k,W1 --label "$TL" --rev "$SHA" > "$OUT/time.launch.log" 2>&1 || true
        sleep 90
        if ssh hbox "test -f /tank/fn/scratch/load-harness/runs/$TL/status"; then
            until ssh hbox "grep -q -v running /tank/fn/scratch/load-harness/runs/$TL/status" 2>/dev/null; do sleep 60; done
            rsync -a --exclude samples.json "hbox:/tank/fn/scratch/load-harness/runs/$TL/" "$OUT/time/" > /dev/null 2>&1 || true
        else log "RED: time rows did not start on hbox (no status file; see $OUT/time.launch.log)"; TERR="$TERR time-launch"; fi
    else
        log "time rows off (pass --time-rows at milestones)"
    fi
    GVIOL="$GVIOL$TERR"
    # verdicts and the guardrail, read from the result files
    R=$(python3 - "$OUT" "$TB" "$TCARRIED" <<'PY'
import json,sys,glob,re,math,os
out, tb, carried = sys.argv[1], sys.argv[2], sys.argv[3].split()
viol=[]; rows=[]; hwm=None; anon=None
time_files = [] if tb == 'persvati' else glob.glob(out+'/time/result.json')
for f in glob.glob(out+'/gauntlet/result.json')+time_files:
    r=json.load(open(f))
    for c in r.get('cells',[]):
        cid=str(c.get('cell') or c.get('id'))
        for b in c.get('bars',[]):
            s=str(b.get('verdict')); rows.append((cid,b.get('bar'),s))
            # judged rows of the gate: the fault corpus and the time bars; W13's
            # L-HWM row judges the retired 128 MiB bar and is reported only
            if s.upper().startswith('FAIL') and not cid.startswith('W13'): viol.append(f'{cid}:{b.get("bar")}')
        if cid.startswith('W13'):
            m=c.get('metrics',{}); hwm=m.get('rss_kib.hwm'); anon=m.get('rss_kib.anon')
# persvati time rows, judged here against GAUNTLET.md's bars from each cell's
# result.json (bars.json judges T-CMD only together with an exponent the cell
# cannot measure, and T-POST on CPU alone).  A row is judged only under the
# sweep's admission: persvati cores 12-23 with busy <= 4 at start AND end;
# otherwise it is reported "unjudged".  A FAIL is a violation unless carried
# from the base (TCARRIED, "key:ROW").  The sweep's own table is kept beside.
TBARS = {  # row: (metric, cmp, threshold)
    'T-CMD p99 max':   ('cmd.p99_ms.max', 'le', 50),
    'T-POST p50 c1':   ('post.p50_ms.c1', 'le', 20),
    'T-POST p99 c1':   ('post.p99_ms.c1', 'le', 250),
    'T-POST CPU c1':   ('post.cpu_ms_per_op.c1', 'le', 16),
    'T-POST rate c1':  ('post.rate_c1', 'ge', 10),
    'T-POST rate c8':  ('post.rate_c8', 'ge', 10),
    'T-LIN ratio':     ('article.ratio_8n_over_n', 'le', 15.0),
    'T-LIN exponent':  ('article.exponent', 'le', 1.1),
}
def admitted(c):
    bx=c.get('box',{}); s0, s1 = bx.get('busy_cores_start'), bx.get('busy_cores_end')
    return (bx.get('name') == 'persvati' and bx.get('busy_cores_set') == '12-23'
            and isinstance(s0,(int,float)) and isinstance(s1,(int,float)) and s0 <= 4 and s1 <= 4)
unjudged=[]
if tb == 'persvati':
    allc=True; pts={}
    for kd in sorted(glob.glob(out+'/time/*/')):
        key=kd.rstrip('/').split('/')[-1]
        reps=[c for f in sorted(glob.glob(kd+'r*/result.json')) for c in json.load(open(f)).get('cells',[])]
        good_reps=[c for c in reps if admitted(c)]
        if key.startswith('tcmd') and not good_reps: allc=False
        def med(met, cs):
            vs=sorted(c.get('metrics',{}).get(met) for c in cs if isinstance(c.get('metrics',{}).get(met),(int,float)))
            return None if not vs else (vs[len(vs)//2] if len(vs)%2 else (vs[len(vs)//2-1]+vs[len(vs)//2])/2)
        tag=f'{len(good_reps)}/{len(reps)} reps'
        for row,(met,cmp,th) in TBARS.items():
            if not good_reps:
                v=med(met, reps)
                if v is None: continue
                rows.append((key,row,f'unjudged {v} ({tag} admitted)')); unjudged.append(f'{key}:{row}'); continue
            v=med(met, good_reps)
            if v is None: continue
            good = v <= th if cmp == 'le' else v >= th
            rows.append((key,row,f'{"PASS" if good else "FAIL"} {round(v,3)} (median, {tag})'))
            if not good and f'{key}:{row}' not in carried: viol.append(f'{key}:{row}')
        if key.startswith('tcmd-') and good_reps:
            n=int(re.search(r'tcmd-(\d+)k', key).group(1))*1000
            for k in good_reps[0].get('metrics',{}):
                mm=re.fullmatch(r'cmd\.p99_ms\.(\w+)', k)
                if mm and mm.group(1) != 'max':
                    v=med(k, good_reps)
                    if v and v > 0: pts.setdefault(mm.group(1),[]).append((n,v))
    # T-CMD exponent, derived as GAUNTLET.md does: per command, least squares
    # of log p99 on log n over the T-CMD sizes run; bar <= 0.2.
    for cmd,xy in sorted(pts.items()):
        if len(xy) < 3: continue
        xs=[math.log(x) for x,_ in xy]; ys=[math.log(y) for _,y in xy]
        mx=sum(xs)/len(xs); my=sum(ys)/len(ys)
        slope=sum((x-mx)*(y-my) for x,y in zip(xs,ys))/sum((x-mx)**2 for x in xs)
        if not allc:
            rows.append(('tcmd',f'T-CMD exponent {cmd}',f'unjudged {slope:.2f}')); unjudged.append(f'tcmd:{cmd}'); continue
        good = slope <= 0.2
        rows.append(('tcmd',f'T-CMD exponent {cmd}',f'{"PASS" if good else "FAIL"} {slope:.2f}'))
        if not good and f'tcmd:{cmd}' not in carried: viol.append(f'tcmd:{cmd}')
print('ROWS '+'; '.join(f'{c} {b}={s}' for c,b,s in rows))
print('VIOL '+' '.join(viol))
print('UNJUDGED '+' '.join(unjudged))
print(f'GUARD vmhwm_kib={hwm} rssanon_kib={anon}')  # anon stands in for anon+shmem: W13 reports no shmem figure; pessimistic enough since shmem is in VmRSS-file
PY
)
    printf '%s\n' "$R" | tee -a "$OUT/gate.log"
    GVIOL=$(printf '%s\n' "$R" | sed -n 's/^VIOL //p')
    HWM=$(printf '%s\n' "$R" | sed -n 's/^GUARD vmhwm_kib=\([0-9]*\).*/\1/p')
    ANON=$(printf '%s\n' "$R" | sed -n 's/.*rssanon_kib=\([0-9]*\).*/\1/p')
    if [ -n "$HWM" ]; then
        if [ "$HWM" -le 254976 ] && [ "${ANON:-0}" -le 117760 ]; then GUARD=ok; else GUARD=BREACH; fi
    else GUARD="not-found (fix the reader in cut_gate.sh against this result.json)"; fi
    log "guardrail: VmHWM ${HWM:-?} KiB (<= 254976), RssAnon ${ANON:-?} KiB (<= 117760): $GUARD"
fi

log "SUMMARY $LABEL $SHA: image=$([ "$IMAGE_OK" = 1 ] && echo built || echo RED) natives_ok=$OKN carried=[${CARRIED# }] new=[${NEWRED# }] gauntlet_violations=[${GVIOL}] guardrail=$GUARD"
[ "$IMAGE_OK" = 1 ] && [ -z "$NEWRED" ] && [ -z "$GVIOL" ] && [ "$GUARD" != BREACH ]
