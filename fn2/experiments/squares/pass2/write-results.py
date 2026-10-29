#!/usr/bin/env python3
from pathlib import Path
import re
import summarize as s
rs=s.measured(s.load_reports());assert len(rs)==100
exp=s.EXP
main=[r for r in rs if r[':PROFILE']=='c1' and r[':PREFIX']=='initial']
loads=[]
for r in rs:loads += list(map(float,re.findall(r'E2 LOAD seconds=([\d.]+)',(exp/r['path'].replace('.sexp','.log')).read_text())))
text='''# Experiment E1 pass 2 — measured with matched search budgets

**ORIGINAL first:** the baseline's first live phase still returns `:PASS` with
200 physical accepts, 67 echoes and133 unattributed drops on each declared
campaign seed. Pass2 now records that known failure and continues. The first
actual drop has been traced: the listener refuses a new capability while the
previous echo row remains occupied; the server closes it with703 bytes supplied
and zero returned. QA=5 reproduces the QA=4 witness with strict capacity slack.
Thus the numerical capacity check does not establish admission reservation;
this is not an accounting-only artifact, nor a refutation of C.3's conditional
scheduling-opportunity bound. [Notes to A](NOTES-TO-A.md) and the
[executed QA4/QA5 witness](mutants/PASS2-LIVENESS.md) give the source citations.

## The main verdict table

C1/default/initial only. Each cell reports detection fraction, **slowest
successful seed** (or slowest censoring when none succeeds), trials,
`C/R/PC/PR/OC/OR` transitions, and a saved record. C/R are direct core/reference;
PC/PR are replayed core/reference; OC/OR are original counterfactual work.
All categories consume the same 200,000-transition budget in configurations2,
3 and3b; wall budget is120 s. Original baseline control campaigns are reused
by trial seed rather than rerun inside each mutant campaign. Their cost is
published in the ORIGINAL row. M1 has no baseline diamond checker.

A mutation hit requires a different first contract or boundary from ORIGINAL
on that trial. Inapplicable original choices are unqualified candidates and
search continues. Explicit counterfactuals retain occurrence identity, fault
and word; descriptor-field differences are recorded as a correspondence.
No operation, generation or capability is renamed. Every found record carries
its original comparison. Timing includes inline validation and both diamond
routes, excludes loading. These are fixed-seed observations, not statistical
tail estimates. The [full100-campaign ledger](CAMPAIGNS.md) gives every seed,
first boundary, counter category, horizon and schedule.

| Mutation | (1) Baseline, known ORIGINAL failures continued | (2) Random explicit choices | (3) Iterative deepening | (3b) Exact-state cache |
|---|---|---|---|---|
'''
for m in ['ORIGINAL']+[f'M{i}' for i in range(1,7)]:
 cells=[]
 for config in ['baseline','random','iterative','dedup']:
  a=[r for r in main if r[':MUTANT']==m and r[':CONFIG']==config];hits=[r for r in a if r['hit']];r=max(hits or a,key=lambda r:r[':SECONDS'])
  status=f'{len(hits)}/{len(a)} found' if hits else f'0/{len(a)}; censored'
  if m=='M1' and config=='baseline':status='not detectable; censored'
  if m=='ORIGINAL':status='control; censored'
  horizon=f"; full h{r[':DEEPEST-COMPLETED']}, partial h{r[':HORIZONS'][-1][':DEPTH']}" if r[':HORIZONS'] else ''
  cells.append(f"{status}; {r[':SECONDS']:.6f}s; {r[':TRIALS']} trials; `{s.transitions(r)}`{horizon}; [s{r[':SEED']}]({s.evidence(r)})")
 text+='| '+m+' | '+' | '.join(cells)+' |\n'
text+=f'''
All100 final campaigns exited normally. Every non-finding campaign exhausted
its transition budget; none stopped merely because a finite horizon completed.
The maximum load time across these100 processes was **{max(loads):.6f} s**
(minimum{min(loads):.6f} s), excluded from campaign timing. No wall timeout
occurred. Some subsecond timings reflect laptop contention and fixed execution
order; no speedup distribution is inferred.

## What changed in attribution

The baseline now finds M2–M6 on all three seeds. M4 seeds1/20261028 and M6 seed1
continue past the known live failure and find their mutation on trial2. M1
repeats the original's known failures and reaches the transition cap; it is
not counted as found. Each ORIGINAL campaign records two complete trial
failures and a partial third trial. The raw `last-boundary` on a partial trial
is its entered turn; comparison uses the preceding fully checked turn. The
ledger lists the actual trial seeds and original first-failure signatures.

Counterfactual qualification matters for explicit search too. M2/M4 schedules
can cease to be legal on ORIGINAL after their states diverge; those are not
credited. For C1/random, M2 rejects13/7/4 such candidates before its three
qualified detections; M4 rejects9/1/1. The selected seed1 witnesses now fail at
explicit boundaries115 (M2) and123 (M4), while ORIGINAL completes those same
input choices under the recorded descriptor correspondence. Their byte
oracle failures remain invisible to shared-handler G1 equality.

## Reading the mode comparison

**No demonstrated search improvement in this demonstrator.** This conclusion
now compares budget-exhausting modes rather than a four-choice cutoff:

- **Same bugs found faster:** not established for (3) or (3b). They find M3/M5/M6,
  whereas random explicit choices find all six. Repeated prefix replay and G2
  checking consume their transition budget. The exact-state cache buys one
  deeper completed horizon, but costs more wall time and adds no mutation hit.
- **New bugs found within budget:** neither enumerator finds a qualified defect
  missed by random explicit choices. The original liveness issue remains a
  separate finding in the baseline/control claim.
- **No demonstrated difference:** this is still COHERENCE §6.1's supported
  reading for generator-mode search. It remains an exercise for layer A's
  workload at this budget. The positive contract-relative G2 result below is
  a useful result about local observations, credited to the checker and its
  reached states, not to enumeration superiority.

For ORIGINAL C1, ordinary iterative deepening completes horizons0–4, then
visits4,865 prefixes of horizon5 before censoring (5,627 prefix attempts total).
3b completes horizons0–5 and visits771 prefixes of horizon6 (5,374 total).
The former uses3.952521 s and the latter14.974495 s, each at200,000 transitions.
3b prunes770 exact duplicate keys and clears its64-key retention table69 times.
Every eviction permits re-exploration, so the bounded cache loses efficiency,
not choices. A key contains remaining depth, exact copied concrete/reference/
simulator/OWN/client/cursor/queue state, and ordered observation histories.
EQUALP resolves hash collisions. There is no hash-only semantic comparison and
no restore/checkpoint mechanism. The initial unbounded cache exhausted its
heap; that attempt is preserved as development evidence, not a censored or
successful final campaign.

## Positive independence under the client contract

The third declaration, `data-different-echo-capability`, admits receive/send
terminal completions and their borrow-release cells on different echo
capabilities, excluding accept/close. It deliberately allows shared posted-FIFO
effects. Rows below use C=2, QA=8 with the same words/fault domain for both modes.
They are separate from the C1 main matrix. The named contract remains
`E1-CLIENT-OWN-STOP-v1`: ordered bytes per capability, effective closes, client
terminal/drop outcomes, OWN verdict and stop reason, with identity
correspondence and a fixed finite observing continuation.

| Runtime | Start | Mode | Qualified mutation hits | Positive G2 | With byte observations | Refutations | Budget result / completed horizon |
|---|---|---|---|---:|---:|---:|---|
'''
for m in ['ORIGINAL','M2','M4']:
 for prefix in ['initial','data']:
  for config in ['random','iterative','dedup']:
   a=[r for r in rs if r[':MUTANT']==m and r[':PROFILE']=='c2' and r[':PREFIX']==prefix and r[':CONFIG']==config]
   text+='| '+' | '.join([m,'initialization' if prefix=='initial' else '**supplied two-Send prefix**',config,f"{sum(r['hit'] for r in a)}/{len(a)}",str(sum(s.count(r,':G2-POSITIVE') for r in a)),str(sum(s.count(r,':G2-POSITIVE-WITH-BYTES') for r in a)),str(sum(s.count(r,':G2-REFUTATIONS') for r in a)),f"{sum(r['status']==':CENSORED' for r in a)} censored"+(f"; full h{a[0][':DEEPEST-COMPLETED']}" if config!='random' else '')])+' |\n'
text+='''
ORIGINAL random exploration from initialization checks **377 legal equal
pairs**, 347 with nonempty client-byte observations, and finds no refutation
within the three200,000-transition campaigns. These are instances including
repeats, not377 independent laws; byte history can include the common prefix.
Ordinary and deduplicated initialization enumeration reach no admitted data
pair before their budgets end. That zero is unexercised, not passing.

The supplied28-choice C2 prefix reaches two pending Sends. Its first positive
pair sends60 bytes on capability (0,2) and40 bytes on (1,1). In both orders the
clients receive exactly their messages, both become `:ECHOED` and close, OWN
passes, and stop reason is0. There are no earlier Send completions in this
prefix: these byte observations are caused by the tested pair. The100 fault/
word pairings at that state all compare equal; 91 contain byte observations.
The measured local searches repeat and extend those checks, as counted above.
[The state](pass2/data-state.sexp), [prefix](pass2/data-prefix.sexp), and
[first positive routes](pass2/results/ORIGINAL-iterative-c2-data-data-1.sexp)
are saved. Fresh-process replay reproduced selected positive pairs from each
ORIGINAL random seed exactly.

This is nonempty positive evidence that shared FIFO effects need not destroy
commutation of these finite client observations. It is not a universal
independence theorem or a proof of equal future behavior. No third-declaration
refutation occurred in any of the 30 data campaigns. Positive diamonds also
occur under M2/M4, so passing a local diamond does not establish handler
correctness: client-oracle mutation detections and positive local commutation
can coexist. Starting from the supplied Sends spends much of the budget
replaying/checking that state and does not itself expose M2/M4 within budget.

## Local claims from the supplied C1 prefixes

These rows start from the existing listener/send prefixes, not initialization.
Their horizons count additional choices; prefix replay and both diamond
routes are charged. Failures in setup are distinguished from suffix discoveries.

| Runtime | Listener prefix | Send prefix |
|---|---|---|
'''
for m in ['ORIGINAL']+[f'M{i}' for i in range(1,7)]:
 cells=[]
 for prefix in ['listener','send']:
  r=next(r for r in rs if r[':MUTANT']==m and r[':PREFIX']==prefix)
  cells.append(f"{r['status'].lower().lstrip(':')}/{r['contract'].lower().lstrip(':')}; {r[':SECONDS']:.6f}s; full h{r[':DEEPEST-COMPLETED']}; [record]({s.evidence(r)})")
 text+='| '+m+' | '+' | '.join(cells)+' |\n'
text+='''
M1's listener row is the original allocator false diamond, detected at suffix
horizon 0. The original conservative declaration rejects it. M3/M5 fail during
prefix replay, before the supplied state is reached; they are valid mutation
witnesses but provide no suffix reachability evidence. M6 fails in the first
suffix horizon. M2/M4 and ORIGINAL complete suffix horizon 2 and censor in 3.
No local row is counted as discovering its supplied prefix.

## Pass 1, retained for comparison

Pass 1's fixed-horizon 4 ORIGINAL run exhausted 657 prefixes in 0.384758 s,
performing 5,347 G1 checks and 21,388 core+reference replay transitions
(10,694 on each side). It exercised 9/39 labels. Its random mode found all six
mutations, and enumeration found M3/M5/M6. Baseline fractions were M4=1/3 and
M6=2/3 because the original liveness failure stopped the other seeds. Pass 2
spends the enumerators' budget, removes those baseline stops as mutation
findings, and adds same-trial original qualification and positive G2 checks.
[Pass 1's full write-up](pass2/PASS1-E1-RESULTS.md) and
[ledger](pass2/PASS1-CAMPAIGNS.md) retain those measurements; raw pass1 evidence
is unchanged. Direct pass1/pass2 timing differences include changed checking
work and are not a search-only speed comparison.

## Scope and validation

There are 100 final campaigns: 56 main matrix, 14 supplied-C1-prefix local claims,
and 30 C2/data campaigns. The six mutant hashes are unchanged. The fixed seeds,
choice domain, budgets, iterative order and exact-key policy are recorded in
the [pass2 manifest](pass2/MANIFEST.md). Layer-A source is unchanged; no new
book was required, and the two pass1 book certificates are reused. No farm or
record-toolchain certification claim is made.

The first fixture used the same network capability for both accepts; its
failed attempt is retained, and the second accept now explicitly chooses
capability 1. Four first random campaigns stopped on an unclassified invalid
original handoff. The implementation was repaired to follow the manifest's
unqualified-candidate rule and all four cells were rerun; their earlier
records remain under `pass2/results/development-invalid-control/`. A partial
baseline control's entered turn is conservatively excluded from its checked
coverage. These corrections change no frozen mutation. No failed attempt
is counted as a counterexample or silently discarded.

The work still excludes the full 26-fault explicit domain, pool/scribe campaigns,
near-retired states, harvest-only boundaries inside a turn, a second ordering,
large-seed distributions and general checkpointing. Three seeds and tiny
profiles do not characterize production workloads. All shared monitors remain
in place; conservative independence still admits zero pairs. The data
relation is tested only under the finite observation contract, with no claim
that equal observations establish a future bisimulation.

## Completed G1 coverage (39 labels)

The C1 columns are ORIGINAL runs from initialization. C2/data includes ORIGINAL
initialization and supplied-prefix runs, clearly separated from C1. The mutant
column is diagnostic execution, not passing coverage. An interrupted G1
attempt at budget exhaustion is reported separately and excluded here.

'''+(s.P/'results/coverage.md').read_text()+'''
## Reproduction

Run `pass2/campaigns.py controls` first, then `main`, `local`, and `data`, each
under the PID/timeout discipline in the manifest. `fixture` constructs the
C2 supplied prefix; its result is a control, not a search measurement.
Each launcher permits at most two fresh ACL2 processes. Do not overlap
launchers. `retry-jobs.json` records the four corrected reruns;
`replay-jobs.json` records selected exact replays. Paths are relative to
`fn2/experiments/squares/` for saved replay sources. Loading remains outside
campaign time. Preserve named outputs before a new measurement.

`pass2/summarize.py` regenerates CAMPAIGNS.md and coverage;
`pass2/write-results.py` regenerates this write-up; `verify-evidence.py` checks
both passes, counterfactual qualification, all 100 final process results,
horizons, positive routes, replays, frozen hashes and source fences.
'''
# Keep paths and evidence identifiers byte-for-byte; prose edits belong above.
(exp/'E1-RESULTS.md').write_text(text)
print('E2 WRITE RESULTS',len(rs),'campaigns')
