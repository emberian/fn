#!/bin/sh
# tools/cut_gate.sh -- the classical gate of the breaking cut (cut/breaking).
#
#   tools/cut_gate.sh [--families F,G,...] [--reuse-image NAME/native-LABEL]
#                     [--no-gauntlet] [--time-box persvati|none] [--label L] REV
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
#      T-CMD@10k and W1 (T-POST) on --time-box (persvati by default: hbox time
#      figures are reported, never judged, LOAD-PROGRAM s.1) when the image
#      can be copied there, else on hbox marked REPORTED.
#   3. the guardrail from W13: VmHWM <= 249 MB (254,976 KiB) and RssAnon <= 115 MB
#      (117,760 KiB; W13 reports no separate shmem figure)
#      on the small preset (ember 2026-10-14: 1.5x the baseline).
# Exit 0 only when the image built, no NEW native red, no gauntlet violation,
# and the guardrail holds.  Everything streams to build/cut-gate/<label>/.
# Box rules: every box step runs through the tools that wrap swarm-build;
# detached jobs leave PID files; nothing here kills anything.
set -eu
cd "$(dirname "$0")/.."
FAMILIES=; REUSE=; GAUNTLET=1; TIMEBOX=persvati; LABEL=
while [ $# -gt 1 ]; do
    case $1 in
        --families) FAMILIES=$2; shift 2 ;;
        --reuse-image) REUSE=$2; shift 2 ;;
        --no-gauntlet) GAUNTLET=0; shift ;;
        --time-box) TIMEBOX=$2; shift 2 ;;
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
PREEXISTING="auth_admin_fidelity bounds_join control_evidence decoded_custody expiry fitness foreign_format_open image_differential image_floor mux operator_verbs operator_verdicts owner_measure public_limits raw_scripts resilience_cuts status_live_posts store_lineage store_mount_identity topic_local verdicts"

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
set -- --box hbox --allow-certify --images production,developer,dtn,dtn-developer --label "$LABEL" --allow-skips --env FN_INN_SRC=/tank/fn/inn/2.7.4
[ -z "$REUSE" ] || set -- "$@" --reuse-image "$REUSE"
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
    TL=$LABEL-t
    if [ "$TIMEBOX" = persvati ] && ssh hbox "rsync -a $IMG $IMG.core $IMG.catalog persvati:/tank/fn/scratch/load-harness/images/$LABEL/ 2>/dev/null"; then
        log "time rows on persvati: T-CMD@10k,W1 (judged)"
        python3 -m tools.load.driver box --box persvati --image "/tank/fn/scratch/load-harness/images/$LABEL/fn-host" --cell T-CMD@10k,W1 --label "$TL" --rev "$SHA" --cores 12-23 > "$OUT/time.launch.log" 2>&1 || true
        TB=persvati
    else
        log "time rows on hbox: T-CMD@10k,W1 (REPORTED, not judged: hbox time figures are never judged)"
        python3 -m tools.load.driver box --box hbox --image "$IMG" --cell T-CMD@10k,W1 --label "$TL" --rev "$SHA" > "$OUT/time.launch.log" 2>&1 || true
        TB=hbox
    fi
    sleep 90
    if ssh "$TB" "test -f /tank/fn/scratch/load-harness/runs/$TL/status"; then
        until ssh "$TB" "grep -q -v running /tank/fn/scratch/load-harness/runs/$TL/status" 2>/dev/null; do sleep 60; done
        rsync -a --exclude samples.json "$TB:/tank/fn/scratch/load-harness/runs/$TL/" "$OUT/time/" > /dev/null 2>&1 || true
    else log "RED: time rows did not start on $TB (no status file; see $OUT/time.launch.log)"; GVIOL="$GVIOL time-launch"; fi
    # verdicts and the guardrail, read from the result files
    R=$(python3 - "$OUT" <<'PY'
import json,sys,glob,re
out=sys.argv[1]; viol=[]; rows=[]; hwm=None; anon=None
for f in glob.glob(out+'/gauntlet/result.json')+glob.glob(out+'/time/result.json'):
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
print('ROWS '+'; '.join(f'{c} {b}={s}' for c,b,s in rows))
print('VIOL '+' '.join(viol))
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
