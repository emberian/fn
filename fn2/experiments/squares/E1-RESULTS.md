# Experiment E1 pass 2 — measured with matched search budgets

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
| ORIGINAL | control; censored; 0.678375s; 3 trials; `99995/100005/0/0/0/0`; [s314159265](pass2/results/ORIGINAL-baseline-c1-default-initial-314159265.sexp) | control; censored; 2.588588s; 218 trials; `100000/100000/0/0/0/0`; [s314159265](pass2/results/ORIGINAL-random-c1-default-initial-314159265.sexp) | control; censored; 3.952521s; 5627 trials; `0/0/100000/100000/0/0`; full h4, partial h5; [s1](pass2/results/ORIGINAL-iterative-c1-default-initial-1.sexp) | control; censored; 14.974495s; 5374 trials; `0/0/100000/100000/0/0`; full h5, partial h6; [s1](pass2/results/ORIGINAL-dedup-c1-default-initial-1.sexp) |
| M1 | not detectable; censored; 0.863454s; 3 trials; `99995/100005/0/0/0/0`; [s1](pass2/results/M1-baseline-c1-default-initial-1.sexp) | 3/3 found; 0.526972s; 1 trials; `112/112/18376/18376/0/0`; [s20261028](pass2/results/M1-random-c1-default-initial-20261028-schedule.sexp) | 0/1; censored; 5.597152s; 5627 trials; `0/0/100000/100000/0/0`; full h4, partial h5; [s1](pass2/results/M1-iterative-c1-default-initial-1.sexp) | 0/1; censored; 18.629313s; 5374 trials; `0/0/100000/100000/0/0`; full h5, partial h6; [s1](pass2/results/M1-dedup-c1-default-initial-1.sexp) |
| M2 | 3/3 found; 0.009501s; 1 trials; `266/266/0/0/0/0`; [s1](pass2/results/M2-baseline-c1-default-initial-1-schedule.sexp) | 3/3 found; 0.649265s; 50 trials; `19340/19340/0/0/3174/3174`; [s1](pass2/results/M2-random-c1-default-initial-1-schedule.sexp) | 0/1; censored; 5.630289s; 5627 trials; `0/0/100000/100000/0/0`; full h4, partial h5; [s1](pass2/results/M2-iterative-c1-default-initial-1.sexp) | 0/1; censored; 18.579044s; 5374 trials; `0/0/100000/100000/0/0`; full h5, partial h6; [s1](pass2/results/M2-dedup-c1-default-initial-1.sexp) |
| M3 | 3/3 found; 0.001647s; 1 trials; `11/19/0/0/0/0`; [s20261028](pass2/results/M3-baseline-c1-default-initial-20261028-schedule.sexp) | 3/3 found; 0.003894s; 1 trials; `19/19/0/0/38/38`; [s314159265](pass2/results/M3-random-c1-default-initial-314159265-schedule.sexp) | 1/1 found; 0.183651s; 208 trials; `0/0/3049/3049/36/36`; full h3, partial h4; [s1](pass2/results/M3-iterative-c1-default-initial-1-schedule.sexp) | 1/1 found; 0.649553s; 174 trials; `0/0/2651/2651/36/36`; full h3, partial h4; [s1](pass2/results/M3-dedup-c1-default-initial-1-schedule.sexp) |
| M4 | 3/3 found; 0.387680s; 2 trials; `50423/50423/0/0/0/0`; [s20261028](pass2/results/M4-baseline-c1-default-initial-20261028-schedule.sexp) | 3/3 found; 1.437136s; 108 trials; `47620/47620/0/0/2970/2970`; [s1](pass2/results/M4-random-c1-default-initial-1-schedule.sexp) | 0/1; censored; 4.082319s; 5627 trials; `0/0/100000/100000/0/0`; full h4, partial h5; [s1](pass2/results/M4-iterative-c1-default-initial-1.sexp) | 0/1; censored; 17.341163s; 5374 trials; `0/0/100000/100000/0/0`; full h5, partial h6; [s1](pass2/results/M4-dedup-c1-default-initial-1.sexp) |
| M5 | 3/3 found; 0.000896s; 1 trials; `8/8/0/0/0/0`; [s1](pass2/results/M5-baseline-c1-default-initial-1-schedule.sexp) | 3/3 found; 0.002884s; 1 trials; `0/0/0/0/16/16`; [s1](pass2/results/M5-random-c1-default-initial-1-schedule.sexp) | 1/1 found; 0.002744s; 3 trials; `0/0/0/0/16/16`; full h0, partial h1; [s1](pass2/results/M5-iterative-c1-default-initial-1-schedule.sexp) | 1/1 found; 0.005125s; 3 trials; `0/0/0/0/16/16`; full h0, partial h1; [s1](pass2/results/M5-dedup-c1-default-initial-1-schedule.sexp) |
| M6 | 3/3 found; 0.391370s; 2 trials; `50137/50137/0/0/0/0`; [s1](pass2/results/M6-baseline-c1-default-initial-1-schedule.sexp) | 3/3 found; 0.008032s; 1 trials; `70/70/0/0/70/70`; [s1](pass2/results/M6-random-c1-default-initial-1-schedule.sexp) | 1/1 found; 0.031927s; 38 trials; `0/0/430/430/16/16`; full h2, partial h3; [s1](pass2/results/M6-iterative-c1-default-initial-1-schedule.sexp) | 1/1 found; 0.105229s; 35 trials; `0/0/414/414/16/16`; full h2, partial h3; [s1](pass2/results/M6-dedup-c1-default-initial-1-schedule.sexp) |

All100 final campaigns exited normally. Every non-finding campaign exhausted
its transition budget; none stopped merely because a finite horizon completed.
The maximum load time across these100 processes was **7.049041 s**
(minimum4.390563 s), excluded from campaign timing. No wall timeout
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
| ORIGINAL | initialization | random | 0/3 | 377 | 347 | 0 | 3 censored |
| ORIGINAL | initialization | iterative | 0/1 | 0 | 0 | 0 | 1 censored; full h4 |
| ORIGINAL | initialization | dedup | 0/1 | 0 | 0 | 0 | 1 censored; full h5 |
| ORIGINAL | **supplied two-Send prefix** | random | 0/3 | 727 | 672 | 0 | 3 censored |
| ORIGINAL | **supplied two-Send prefix** | iterative | 0/1 | 244 | 226 | 0 | 1 censored; full h0 |
| ORIGINAL | **supplied two-Send prefix** | dedup | 0/1 | 244 | 226 | 0 | 1 censored; full h0 |
| M2 | initialization | random | 1/3 | 269 | 239 | 0 | 2 censored |
| M2 | initialization | iterative | 0/1 | 0 | 0 | 0 | 1 censored; full h4 |
| M2 | initialization | dedup | 0/1 | 0 | 0 | 0 | 1 censored; full h5 |
| M2 | **supplied two-Send prefix** | random | 0/3 | 731 | 676 | 0 | 3 censored |
| M2 | **supplied two-Send prefix** | iterative | 0/1 | 244 | 226 | 0 | 1 censored; full h0 |
| M2 | **supplied two-Send prefix** | dedup | 0/1 | 244 | 226 | 0 | 1 censored; full h0 |
| M4 | initialization | random | 1/3 | 349 | 307 | 0 | 2 censored |
| M4 | initialization | iterative | 0/1 | 0 | 0 | 0 | 1 censored; full h4 |
| M4 | initialization | dedup | 0/1 | 0 | 0 | 0 | 1 censored; full h5 |
| M4 | **supplied two-Send prefix** | random | 0/3 | 727 | 672 | 0 | 3 censored |
| M4 | **supplied two-Send prefix** | iterative | 0/1 | 244 | 226 | 0 | 1 censored; full h0 |
| M4 | **supplied two-Send prefix** | dedup | 0/1 | 244 | 226 | 0 | 1 censored; full h0 |

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
| ORIGINAL | censored/transitions; 2.662888s; full h2; [record](pass2/results/ORIGINAL-iterative-c1-default-listener-1.sexp) | censored/transitions; 2.821956s; full h2; [record](pass2/results/ORIGINAL-iterative-c1-default-send-1.sexp) |
| M1 | found/g2; 0.010212s; full h-1; [record](pass2/results/M1-iterative-c1-default-listener-1-schedule.sexp) | found/g2; 0.368716s; full h-1; [record](pass2/results/M1-iterative-c1-default-send-1-schedule.sexp) |
| M2 | censored/transitions; 2.365245s; full h2; [record](pass2/results/M2-iterative-c1-default-listener-1.sexp) | censored/transitions; 2.387922s; full h2; [record](pass2/results/M2-iterative-c1-default-send-1.sexp) |
| M3 | found/g1; 0.003516s; full h-1; [record](pass2/results/M3-iterative-c1-default-listener-1-schedule.sexp) | found/g1; 0.003736s; full h-1; [record](pass2/results/M3-iterative-c1-default-send-1-schedule.sexp) |
| M4 | censored/transitions; 2.659340s; full h2; [record](pass2/results/M4-iterative-c1-default-listener-1.sexp) | censored/transitions; 2.745536s; full h2; [record](pass2/results/M4-iterative-c1-default-send-1.sexp) |
| M5 | found/g1-entry; 0.001519s; full h-1; [record](pass2/results/M5-iterative-c1-default-listener-1-schedule.sexp) | found/g1-entry; 0.001548s; full h-1; [record](pass2/results/M5-iterative-c1-default-send-1-schedule.sexp) |
| M6 | found/adapter-class-latency; 0.043147s; full h0; [record](pass2/results/M6-iterative-c1-default-listener-1-schedule.sexp) | found/adapter-class-latency; 0.044080s; full h0; [record](pass2/results/M6-iterative-c1-default-send-1-schedule.sexp) |

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

| Label | C1 random | C1 iterative | C1 3b | C2/data ORIGINAL | All mutants |
|---|---:|---:|---:|---:|---:|
| `(:run fn2-listener :accepting)` | 8181 | 5597 | 5487 | 29930 | 108250 |
| `(:run fn2-listener :closing)` | 1201 | unexercised | unexercised | 27 | 656 |
| `(:observe fn2-listener :accept-result)` | 4899 | 376 | 478 | 9382 | 26380 |
| `(:observe fn2-listener :close-result)` | 1127 | unexercised | unexercised | 22 | 626 |
| `(:run fn2-echo :free)` | unexercised | unexercised | unexercised | unexercised | unexercised |
| `(:run fn2-echo :command)` | 2150 | unexercised | 8 | 7957 | 19373 |
| `(:run fn2-echo :reply)` | 2031 | unexercised | unexercised | 14236 | 29489 |
| `(:run fn2-echo :closing)` | 1289 | unexercised | unexercised | 1270 | 4803 |
| `(:run fn2-echo :draining)` | 1163 | unexercised | unexercised | 1245 | 2538 |
| `(:run fn2-echo :retired)` | unexercised | unexercised | unexercised | unexercised | unexercised |
| `(:observe fn2-echo :receive-result)` | 2029 | unexercised | unexercised | 7775 | 19109 |
| `(:observe fn2-echo :send-result)` | 1349 | unexercised | unexercised | 6739 | 13003 |
| `(:observe fn2-echo :borrow-released)` | 1347 | unexercised | unexercised | 3027 | 5685 |
| `(:observe fn2-echo :close-result)` | 1194 | unexercised | unexercised | 1259 | 2564 |
| `(:run fn2-scribe :free)` | unexercised | unexercised | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :reserve)` | 659 | 1871 | 2381 | 7513 | 32718 |
| `(:run fn2-scribe :fill)` | unexercised | unexercised | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :patch)` | unexercised | unexercised | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :write)` | unexercised | unexercised | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :write-result)` | unexercised | unexercised | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :fence)` | unexercised | unexercised | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :fence-result)` | unexercised | unexercised | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :reset)` | unexercised | unexercised | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :read)` | unexercised | unexercised | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :read-result)` | unexercised | unexercised | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :verify)` | unexercised | unexercised | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :next)` | unexercised | unexercised | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :stopped)` | unexercised | unexercised | unexercised | unexercised | unexercised |
| `(:observe fn2-scribe :write-result)` | unexercised | unexercised | unexercised | unexercised | unexercised |
| `(:observe fn2-scribe :fence-result)` | unexercised | unexercised | unexercised | unexercised | unexercised |
| `(:observe fn2-scribe :read-result)` | unexercised | unexercised | unexercised | unexercised | unexercised |
| `(:router :fallback)` | unexercised | unexercised | unexercised | unexercised | unexercised |
| `(:executor :clock)` | 9278 | 629 | 801 | 22230 | 58529 |
| `(:executor :signal)` | unexercised | unexercised | unexercised | unexercised | unexercised |
| `(:executor :service 0)` | 16015 | 5933 | 5835 | 55344 | 168498 |
| `(:executor :service 1)` | 16015 | 5933 | 5835 | 55344 | 168498 |
| `(:executor :service 2)` | 16015 | 5933 | 5835 | 55343 | 168495 |
| `(:executor :service 3)` | 16015 | 5932 | 5835 | 55342 | 168490 |
| `(:executor :empty-principal)` | 48045 | 17799 | 17505 | 166033 | 505500 |

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
