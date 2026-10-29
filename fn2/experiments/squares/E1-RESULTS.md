# Experiment E1 — the generator mode, measured

**ORIGINAL finding first:** all three baseline seeds return the echo driver's
`:PASS` while its live phase records accepted=200, echoed=67, dropped=133,
all 133 drops `:unattributed`. The existing A4 accepted/echoed/drop assertion
fails on this admitted one-row tiny profile. The slowest of these three
baseline findings took **0.284848 s**, excluding loading. An exact replay
reproduced seed 1's final assertion and transition counts. This is a workload
liveness/applicability and summary defect, not evidence that capacity refusal
is a server safety bug. [Notes to A](NOTES-TO-A.md) gives the source locations
and the separate original qualification replay. No A source was edited.

## The verdict table

Each cell gives detection fraction; **slowest successful seed** in seconds;
trials; `C/R/PC/PR` transitions (direct core/reference, replayed core/reference);
and its saved schedule. For a cell without a hit, the slowest stop is shown.
These are pessimistic observed timings over these three fixed random seeds,
not distribution tails. G1 copies and both diamond routes count as execution.
`O-stop` means the original liveness failure stopped the campaign; it is not
a mutation detection or a timeout. `exhausted` means all 657 declared prefixes,
not the full input language. Full per-seed contracts, first boundaries, G2
instances, counters and schedules are in [the 49-run ledger](CAMPAIGNS.md).

| Mutation | (1) Existing random driver | (2) Random explicit choices + G1/G2 | (3) Exhaustive prefixes + G1/G2 |
|---|---|---|---|
| ORIGINAL control | O-stop 3/3; 0.284848s; 1 trials; `50158/50158/0/0`; [s20261028](results/ORIGINAL-baseline-20261028-schedule.sexp) | 0/3; transition-censored; 2.758115s; 221 trials; `99996/100004/0/0`; [s20261028](results/ORIGINAL-random-20261028.sexp) | 0/1; exhausted; 0.384758s; 657 trials; `0/0/10694/10694`; [s1](results/ORIGINAL-exhaustive-1.sexp) |
| M1 false independence | not detectable; 3 O-stop; 0.292999s; 1 trials; `50062/50062/0/0`; [s1](results/M1-baseline-1-schedule.sexp) | found 3/3; 0.520415s; 1 trials; `112/112/18376/18376`; [s20261028](results/M1-random-20261028-schedule.sexp) | 0/1; exhausted; 0.448466s; 657 trials; `0/0/10694/10694`; [s1](results/M1-exhaustive-1.sexp) |
| M2 stale row snapshot | found 3/3; 0.004717s; 1 trials; `106/106/0/0`; [s20261028](results/M2-baseline-20261028-schedule.sexp) | found 3/3; 0.013961s; 2 trials; `578/578/0/0`; [s1](results/M2-random-1-schedule.sexp) | 0/1; exhausted; 0.335698s; 657 trials; `0/0/10694/10694`; [s1](results/M2-exhaustive-1.sexp) |
| M3 dropped routing | found 3/3; 0.000817s; 1 trials; `11/19/0/0`; [s314159265](results/M3-baseline-314159265-schedule.sexp) | found 3/3; 0.001387s; 1 trials; `19/19/0/0`; [s314159265](results/M3-random-314159265-schedule.sexp) | found 1/1; 0.070293s; 103 trials; `0/0/1761/1761`; [s1](results/M3-exhaustive-1-schedule.sexp) |
| M4 short-send summary | found 1/3; 2 O-stop; 0.001496s; 1 trials; `135/135/0/0`; [s314159265](results/M4-baseline-314159265-schedule.sexp) | found 3/3; 0.266941s; 28 trials; `12692/12692/0/0`; [s314159265](results/M4-random-314159265-schedule.sexp) | 0/1; exhausted; 0.450504s; 657 trials; `0/0/10694/10694`; [s1](results/M4-exhaustive-1.sexp) |
| M5 FIFO head insertion | found 3/3; 0.001011s; 1 trials; `8/8/0/0`; [s314159265](results/M5-baseline-314159265-schedule.sexp) | found 3/3; 0.000664s; 1 trials; `0/0/0/0`; [s1](results/M5-random-1-schedule.sexp) | found 1/1; 0.000867s; 2 trials; `0/0/0/0`; [s1](results/M5-exhaustive-1-schedule.sexp) |
| M6 swapped latency | found 2/3; 1 O-stop; 0.002521s; 1 trials; `241/241/0/0`; [s314159265](results/M6-baseline-314159265-schedule.sexp) | found 3/3; 0.002985s; 1 trials; `110/110/0/0`; [s20261028](results/M6-random-20261028-schedule.sexp) | found 1/1; 0.008317s; 13 trials; `0/0/214/214`; [s1](results/M6-exhaustive-1-schedule.sexp) |

The three precommitted seeds are 1, 20261028 and 314159265; enumeration has one
order. Every campaign had a 120 s wall budget and a 200,000 combined transition
cap, stopping at the first failure. All 49 processes exited normally. ORIGINAL
random reached the transition cap on each seed; its slowest campaign was
2.758115 s. There was no wall-time censoring. Loading the same laptop ACL2/SBCL
closure took **at most 6.625848 s across these 49 campaigns** (minimum 3.575637 s),
excluded from the table; per-process load lines remain in the raw logs.

## Reading the experiment

**No demonstrated difference. The generator mode is an exercise for layer A's
workload in this demonstrator.** Applying COHERENCE §6.1's readings to (2)
versus (3), rather than crediting the new instrumentation as a search result:

- **Same bugs found faster:** not established. Enumeration finds only M3/M5/M6;
  random explicit choices find all six. Enumeration's M3 and M6 detections
  use more replay transitions and wall time than these random seeds. M5 is
  an initialization-order discrepancy, caught before any G1 transition; that
  is a sharper diagnostic, not evidence for systematic reachability.
- **New bugs found within budget:** none in (3) that (2) missed. M1 is a real
  declaration refutation found only by a diamond checker, but (2) already
  finds it on all three seeds. It is not a runtime defect. The ORIGINAL
  liveness-summary defect is separate, and was exposed by the baseline's
  existing final assertion, not by prefix enumeration.
- **No demonstrated difference:** this is the supported reading. Keep the
  explicit replay seam, normalized G1 diagnostics, allocator monitor and
  negative controls. This table does not justify a larger generator framework
  or a claim about summary composition or representation transport.

M4 remains the discriminating shared-handler example: concrete and reference
agree on the wrong accumulated offset, while the client byte oracle fails.
M5 uses coherent FIFO head insertion rather than an unobservable reordered
notification. The baseline catches it in TRACE; G1 detects the queue mismatch
at entry. M6 is detected by the same added latency-contract monitor in all
three configurations; its result cannot be credited to an oracle withheld
from baseline sampling. The baseline's native broad fault domain and cadence
are different from the explicit domain, so (1)/(2) are not an equal-domain
search comparison. M4's two and M6's one original-liveness stops limit their
baseline detection fractions; they do not prove those seeds cannot find the
mutation under a different stopping policy.

## What ran, and what is missing

`choices.lisp` drives the actual echo adapter with explicit full occurrence
identities: operation slot, generation, terminal/release state, kind,
capability, retained payload, fault and word. Any active flight can land,
including a non-earliest flight. Registration latency, client actions and
turns are explicit boundaries. `checks.lisp` derives the catalogue from the
machine registry; each G1 preflight uses fresh core/reference copies,
compares all five transition results, accounts work on both sides as their
loops do, normalizes only the reference work counters, checks representation
agreement and shape invariants, and checks loop continuation/exit. TRACE then
checks the composed turn independently. These are executable checks, not
universal correspondence theorems or guard-verified served code.

The [manifest](MANIFEST.md) fixes a one-row tiny profile, two concrete generated
payloads, seven fault codes and words 0/1; every choice prefix of length 0–4 is
in the enumeration tree. ORIGINAL reaches **657 prefix endpoints**, including
repeats, performs **5,347 G1 instances**, rejects **10,170 candidate occurrence
pairs**, and admits **zero G2 instances**. Its three random campaigns visit
84,849 endpoints and perform 150,002 G1 instances. Counts include replay work;
none of these endpoint counts denotes distinct states. The full ledger keeps
states, enumerated prefixes, G1, G2, rejected candidates and illegal residuals
separate. The three M1 random campaigns check 61,61,1 diamonds respectively
before their first refutation. Conservative-declaration campaigns check zero.

The conservative `different-capability-and-allocator-disjoint` footprint
names the posted FIFO, shared counts, clock mailbox and, for admission/close,
the allocator and principal 0 FIFO. Those shared resources make it reject every
completion pair in this implementation. **It has no positive G2 coverage and
no independence theorem.** This deliberately conservative first declaration
is a substantial limitation: the experiment exercises a false declaration
and its counterexample search, not a useful nonempty independence relation.

This is not the pessimistic 12-engineer-day experiment. There are no pool
scenario campaigns, no separate scribe progression campaign, no near-retired
or crowded-prefix search, no stale/duplicate/death faults in the explicit
domain, no harvest-only choice boundary inside a turn, no second enumeration
rotation, no 20-seed distribution, no ten-minute campaigns, no checkpoint
library, no partial-order reduction, and no proof that the finite observation
continuation is complete. Enumeration starts only at initialization; the
16-choice negative-control prefix is supplied separately and is not search
coverage. Nineteen of the 39 dispatch labels are exercised by ORIGINAL random;
only nine are exercised by ORIGINAL enumeration. Unexercised labels below
are not passing cases. The two new books certify in 3.671 s and 2.813 s on this
laptop; their imported A closure took about 26.5 minutes, with its slowest book
810.697 s. No farm certification or record-toolchain green claim is made.

## G2 negative control and replay evidence

The named observation contract is `E1-CLIENT-OWN-STOP-v1`: ordered actual bytes
per(cap-index,nonce), effective client closes, client terminal/drop markers,
OWN verdict and stop reason. Identifier correspondence is identity; there is
no implicit identifier renaming. Both branches replay the common prefix into
fresh state, then run a fixed observing policy of turns, handoffs, client
reads and pending closes. Equality under that finite policy does not establish
future congruence. Array or hash inequality alone is never a finding.

The [listener state](results/listener-state.sexp) has one occupied echo row,
free-head 4294967295, active-count=capacity=1, an outstanding Accept on listener
capability(0,0), and an outstanding Close on echo capability(0,2), in principal 0's
FIFO. The common prefix has 16 choices. AcceptResult;CloseResult closes new
client(0,3) and records an unattributed drop; CloseResult;AcceptResult admits
that client and does not close it. OWN passes and stop reason 0 on both routes.
[Both complete routes](results/listener-routes.sexp) and the
[prefix](results/listener-prefix.sexp) are saved. The naive declaration admits
the pair; the allocator-aware declaration rejects it. This is the required
listener/reclamation false diamond, not an assertion that the node should
admit a connection before capacity is reclaimed. The searched M1 witnesses
also refute the naive declaration; their found pairs need not be this fixture.

All six mutation files were read in full and hashed before the 49 measured
campaigns; [freeze.json](freeze.json) and the manifest retain the hashes.
[Qualification](mutants/QUALIFICATION.md) gives the concrete source-line
citations and legal original/mutant controls. M2–M5 have exact baseline-tape
replays and original-prefix controls; M1 has the negative-control routes;
M6 has an original-passing delay schedule and a mutant latency failure.
Fresh processes redefine both ACL2 executable forms; no runtime restoration
is relied upon.

Postmeasurement replay reproduced a selected random failing schedule for
**each M1–M6**, including both complete M1 routes and their exact observations.
Original replays of M3/M5/M6 explicit prefixes pass. M2/M4 explicit occurrence
lists retain mutated range fields and become inapplicable on the original
once its descriptors diverge; those are **invalid original prefixes**, not
original passes. Their baseline qualification tapes supply the legal paired
witnesses. The first two original-prefix replay attempts exposed an uncaught
invalid-prefix report in the replay helper; the helper was fixed to return
`:INVALID-PREFIX` and both retries are retained. Measured search logic and
frozen mutations were unchanged. The replay helper also now reapplies the
baseline final assertion and reconstructs saved G2 routes. No failed trial
was removed or relabeled as a semantic counterexample.

`results/domain-payloads.sexp` records the exact two byte messages.
`ORIGINAL-replay-control-1.sexp` checks complete concrete/ref/simulator/OWN/client
state equality across fresh replay and verifies that advancing one branch
does not mutate the other's fresh state. Raw PRNG tapes are retained for the
legacy baseline. Full occurrence schedules are retained for explicit search;
G2 records include common prefix, occurrences and both observing routes.

## G1 per-label coverage (all 39 labels)

Counts below are completed G1 calls, including failing calls and replayed
prefixes. They exclude the separate untimed qualification/negative controls.
The mutant aggregate is diagnostic execution, not passing coverage. No
outside-catalogue label was observed in the measured campaigns.

| G1 label | ORIGINAL random (3 seeds) | ORIGINAL exhaustive | All mutant campaigns |
|---|---:|---:|---:|
| `(:run fn2-listener :accepting)` | 8181 | 626 | 3714 |
| `(:run fn2-listener :closing)` | 1201 | unexercised | 80 |
| `(:observe fn2-listener :accept-result)` | 4899 | 20 | 1048 |
| `(:observe fn2-listener :close-result)` | 1127 | unexercised | 77 |
| `(:run fn2-echo :free)` | unexercised | unexercised | unexercised |
| `(:run fn2-echo :command)` | 2150 | unexercised | 403 |
| `(:run fn2-echo :reply)` | 2031 | unexercised | 517 |
| `(:run fn2-echo :closing)` | 1289 | unexercised | 92 |
| `(:run fn2-echo :draining)` | 1163 | unexercised | 85 |
| `(:run fn2-echo :retired)` | unexercised | unexercised | unexercised |
| `(:observe fn2-echo :receive-result)` | 2029 | unexercised | 390 |
| `(:observe fn2-echo :send-result)` | 1349 | unexercised | 229 |
| `(:observe fn2-echo :borrow-released)` | 1347 | unexercised | 108 |
| `(:observe fn2-echo :close-result)` | 1194 | unexercised | 85 |
| `(:run fn2-scribe :free)` | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :reserve)` | 659 | 151 | 831 |
| `(:run fn2-scribe :fill)` | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :patch)` | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :write)` | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :write-result)` | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :fence)` | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :fence-result)` | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :reset)` | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :read)` | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :read-result)` | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :verify)` | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :next)` | unexercised | unexercised | unexercised |
| `(:run fn2-scribe :stopped)` | unexercised | unexercised | unexercised |
| `(:observe fn2-scribe :write-result)` | unexercised | unexercised | unexercised |
| `(:observe fn2-scribe :fence-result)` | unexercised | unexercised | unexercised |
| `(:observe fn2-scribe :read-result)` | unexercised | unexercised | unexercised |
| `(:router :fallback)` | unexercised | unexercised | unexercised |
| `(:executor :clock)` | 9278 | 28 | 1630 |
| `(:executor :signal)` | unexercised | unexercised | unexercised |
| `(:executor :service 0)` | 16015 | 646 | 4951 |
| `(:executor :service 1)` | 16015 | 646 | 4951 |
| `(:executor :service 2)` | 16015 | 646 | 4951 |
| `(:executor :service 3)` | 16015 | 646 | 4951 |
| `(:executor :empty-principal)` | 48045 | 1938 | 14853 |

Final review found that the first random harness omitted G2 at the endpoint
following choice 128. All 21 affected random campaigns were rerun with that
endpoint checked, after the unchanged mutant freeze. The table uses only the
corrected measurements; the earlier records remain under
`results/superseded-random-endpoint/`. Baseline and enumeration were unaffected.
The selected failure schedules have the same exact failure details on replay.
Timing order was not rotated, and laptop contention can affect these short
runs; no statistical speedup is inferred from their subsecond differences.

## Reproduction

From this worktree, after the certified A closure and `build/scenario-revision.lsp`
exist, the launchers are `python 3 fn2/experiments/squares/campaigns.py
--controls-only`, then `--mutants-only`. Launch under detached `timeout -k5`
with a PID file, as the recorded `build/e1-controls.pid` and
`build/e1-mutants.pid` runs did. Each launcher checks the freeze and free disk,
limits itself to two fresh processes, and writes a PID/log/result per campaign.
Do not run a second launcher concurrently. `replay-campaigns.py` runs the
selected postmeasurement replays; `summarize.py` regenerates the ledger and
coverage from the immutable measured records. These launchers overwrite their
named outputs, so preserve this experiment's evidence before a new campaign.

For one saved witness, run `tools/acl2 < fn2/experiments/squares/driver.lsp`
under the same PID/timeout discipline with `E1_MUTANT=M3`, `E1_CONFIG=replay`,
`E1_SEED=1`, `E1_REPLAY` set to the absolute path of
`results/M3-random-1-schedule.sexp`, and `E1_OUTPUT_TAG` set to a fresh suffix.
Set `FN_ACL2_SLOT_DIR=/tmp/fn2-a4-acl2-slots` and `FN_ACL2_SLOTS=6` as in the
recorded launchers. Replay time is diagnostic, excluded from campaign results.
