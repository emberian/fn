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
#   3. the guardrail from W13: VmHWM <= 249 MB and RssAnon+RssShmem <= 115 MB
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
NEWRED=; CARRIED=
for m in $(grep -E '^tests\.test_native_[a-z0-9_]+ .*FAILED' "$OUT/run.log" | sed 's/^tests\.test_native_\([a-z0-9_]*\) .*/\1/' | sort -u); do
    case " $PREEXISTING " in *" $m "*) CARRIED="$CARRIED $m" ;; *) NEWRED="$NEWRED $m" ;; esac
done
OKN=$(grep -c -E '^tests\.test_native_[a-z0-9_]+ .*OK' "$OUT/run.log" || true)
log "natives: $OKN OK; carried reds:${CARRIED:- none}; NEW reds:${NEWRED:- none} (status $STATUS)"

# 2. gauntlet
GVIOL=; GUARD=unknown
if [ "$GAUNTLET" = 1 ] && [ "$IMAGE_OK" = 1 ]; then
    IMG=$RUNDIR/tree/build/fn-host
    GL=$LABEL-g
    log "gauntlet on hbox: F2S,F4,F6,W13 against $IMG"
    python3 -m tools.load.driver box --box hbox --image "$IMG" --cell F2S,F4,F6,W13 --label "$GL" --rev "$SHA" > "$OUT/gauntlet.launch.log" 2>&1 || log "RED: gauntlet launch refused"
    sh tools/wait_for.sh --host hbox --file "/tank/fn/scratch/load-harness/runs/$GL/status" --deadline 7200 > /dev/null 2>&1 || true
    until ssh hbox "grep -q -v running /tank/fn/scratch/load-harness/runs/$GL/status" 2>/dev/null; do sleep 60; done
    rsync -a "hbox:/tank/fn/scratch/load-harness/runs/$GL/" "$OUT/gauntlet/" > /dev/null 2>&1 || true
    TL=$LABEL-t
    if [ "$TIMEBOX" = persvati ] && ssh hbox "rsync -a $IMG $IMG.core $IMG.catalog persvati:~/fn-gates/cut-images/$LABEL/ 2>/dev/null"; then
        log "time rows on persvati: T-CMD@10k,W1 (judged)"
        python3 -m tools.load.driver box --box persvati --image "fn-gates/cut-images/$LABEL/fn-host" --cell T-CMD@10k,W1 --label "$TL" --rev "$SHA" --cores 12-23 > "$OUT/time.launch.log" 2>&1 || log "RED: time-row launch refused on persvati"
        TB=persvati
    else
        log "time rows on hbox: T-CMD@10k,W1 (REPORTED, not judged: hbox time figures are never judged)"
        python3 -m tools.load.driver box --box hbox --image "$IMG" --cell T-CMD@10k,W1 --label "$TL" --rev "$SHA" > "$OUT/time.launch.log" 2>&1 || log "RED: time-row launch refused on hbox"
        TB=hbox
    fi
    until ssh "$TB" "grep -q -v running /tank/fn/scratch/load-harness/runs/$TL/status 2>/dev/null || grep -q -v running ~/fn-gates/load-harness/runs/$TL/status 2>/dev/null"; do sleep 60; done
    rsync -a "$TB:/tank/fn/scratch/load-harness/runs/$TL/" "$OUT/time/" > /dev/null 2>&1 || rsync -a "$TB:fn-gates/load-harness/runs/$TL/" "$OUT/time/" > /dev/null 2>&1 || true
    # verdicts and the guardrail, read from the result files
    R=$(python3 - "$OUT" <<'PY'
import json,sys,glob,re
out=sys.argv[1]; viol=[]; rows=[]; hwm=None; anon=None
def walk(o,path=''):
    global hwm,anon
    if isinstance(o,dict):
        for k,v in o.items():
            kl=k.lower()
            if isinstance(v,(int,float)):
                if 'vmhwm' in kl and hwm is None: hwm=v
                if ('rssanon' in kl or 'rss_anon' in kl) and anon is None: anon=v
            walk(v,path+'/'+k)
    elif isinstance(o,list):
        for x in o: walk(x,path)
for f in glob.glob(out+'/gauntlet/result.json')+glob.glob(out+'/time/result.json'):
    r=json.load(open(f))
    for c in r.get('cells',[]):
        cid=c.get('cell') or c.get('id'); v=c.get('verdict') or c.get('judged') or {}
        bars=c.get('bars') or v if isinstance(v,dict) else {}
        for b,res in (bars.items() if isinstance(bars,dict) else []):
            s=str(res.get('verdict',res) if isinstance(res,dict) else res)
            rows.append((cid,b,s))
            if 'FAIL' in s.upper() and 'F' in str(cid)[:1]: viol.append(f'{cid}:{b}')
        if str(cid).startswith('W13'): walk(c)
print('ROWS '+'; '.join(f'{c} {b}={s}' for c,b,s in rows))
print('VIOL '+' '.join(viol))
print(f'GUARD vmhwm_kib={hwm} rssanon_kib={anon}')
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
