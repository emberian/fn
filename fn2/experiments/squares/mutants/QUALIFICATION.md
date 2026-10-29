# E1 mutation qualification

The unmodified control exposes a separate liveness-summary failure under the
admitted tiny profile. It must be reported before the mutation findings.
`fn2-sim-run-echo` returns an outer `:PASS` and a live-phase `:PASS`, but its
200 live connections produce **67 echoed and 133 unattributed drops** at seed
20261028. The existing A4 driver's assertions at
`fn2/tests/sim-layer-a-a4-driver.lsp:87-90` require 200 echoes and zero drops.
Its displayed numeric premises hold: H=4>3 and min(O=8,QA=4)=4 >=
2*C+accept-credits+1=4. `fn2-core-profilep` also passes. The live-phase
`:UNATTRIBUTED . 133` histogram is separate from the safety phase's single
`:PROCESS-DEATH` drop; it is not an accidental reuse of safety statistics.

The source mechanism is a candidate explanation, not a proven root cause:
`fn2-echo-live-advance` permits the next Accept while a previous echo row can
still await reclamation, and `fn2-echo-clients-step` counts a changed network
nonce as accepted before listener admission. In the one-row profile the
allocator may legally refuse that admission. The return-value summary does
not promote the resulting drop count to failure. This is an observed defect
in the liveness claim/driver applicability on this profile, not evidence that
ordinary capacity refusal is a server safety violation.

The original control and exact replay have 25,921 identical interior event
records, 16,923 PRNG words, 47,230 core transitions, 47,230 reference transitions
and 4,891 turns. The replay consumes all saved words and leaves none. Raw tapes:
`qualification-ORIGINAL-20261028.sexp` and `replay-ORIGINAL-20261028.sexp`.
The printed `:PASS` in those raw records is the function's return value, **not**
a passing verdict on the A4 liveness assertions above.

## Qualified defects and prefixes

These untimed qualification results precede the frozen comparative campaigns.
Each run used a fresh ACL2 process, existing `fn2-sim-run-echo`, target one
connection, seed 20261028 and tiny profile with C=1/accept-credits=1. The original
200-connection liveness suffix remained present. The following failures occur
before that suffix. Every M2–M5 failing tape has an exact same-mutant replay;
every original replay consumes the entire saved prefix without a checker
failure, then explicitly returns `:REPLAY-PREFIX-EXHAUSTED`. Prefix exhaustion
is not a full-run pass and does not erase the later original liveness failure.

| Mutation | Named failure | First boundary | Core / reference | PRNG words | Recorded environment choices | Execution seconds |
|---|---|---:|---:|---:|---:|---:|
| M2 | client byte: expected 240, read 199, capability (0,2) | turn 11 | 77 / 77 | 72 | 7 | 0.004359 |
| M3 | TRACE runnable-count mismatch | turn 3 | 11 / 19 | 35 | 1 | 0.001217 |
| M4 | client byte: expected 151, read 203, capability (0,2) | turn 14 | 98 / 98 | 86 | 10 | 0.002234 |
| M5 | TRACE principal FIFO: (2 0) versus (0 2) | turn 1 | 8 / 8 | 27 | 0 | 0.005027 |

For each M in M2–M5, `qualification-M-20261028.sexp` is the failing tape,
`replay-M-20261028.sexp` its exact replay, and
`original-prefix-M-20261028.sexp` the unmodified prefix control. All recorded
`:CHOICE` occurrence records match between each mutant and original prefix,
including operation/generation/cell, capability, fault and word. Original M3
performs 19 core transitions because its routed completion wakes runnable
work; the mutant performs only 11. The other original prefix transition
counts equal the mutant counts. The same-mutant interior event counts are
respectively 110, 43, 138 and 29, all byte-for-byte equal on replay.

M1 is a declaration defect, qualified by the parent's executed
`../results/listener-prefix.sexp`, `listener-state.sexp` and
`listener-routes.sexp`. The 16-choice prefix reaches one occupied row,
free-head=4294967295 and active=capacity=1. Accept-first closes new capability
(0,3); Close-first admits it. Both OWN verdicts pass and both stop reasons are
zero. Loading M1 into the baseline driver changes no runtime behavior; that
configuration has no diamond checker. Its baseline run repeats the separate
unmodified liveness-summary failure.

M6 loads successfully, but seed 20261028's baseline qualification lands neither
fault 2 nor fault 14, so it is **unexercised**, not passing, there. The parent
qualified it with the first pending Accept, fault 2, word 0: original passes,
M6 violates `ADAPTER-CLASS-LATENCY` at explicit boundary 3 (expected due 101,
actual 1001). The saved schedule and original control are
`../results/M6-latency-control-1-schedule.sexp` and
`../results/ORIGINAL-latency-control-1.sexp`. The parent's M6 result counts 16
core and 16 reference transitions, including G1/TRACE execution.

The slowest load among the first ORIGINAL/M1–M6 qualification processes was
4.988849 seconds (M5), excluding execution; individual load lines remain in
the logs. These measurements are diagnostic, not the comparative campaign
table. All six mutation definitions loaded successfully before the parent
froze their hashes. No mutation file changed after that confirmation.

## Reproduction and limits

`qualify.lsp` and `qualification-hooks.lsp` implement the baseline recorder;
`replay-batch.sh` runs the fresh-process replays sequentially. Output includes
all PRNG words, simulator observations, explicit occurrence choices and first
failing monitor boundaries. Replay never falls back to a fresh PRNG word when
the supplied tape is exhausted. The driver preserves raw return values; this
write-up separately applies A4's post-run liveness assertions.

`SUMMARY-LINES.txt` extracts the verbatim qualification load/result lines from
each individual process log, including wrapped lines. The batch log repeats
these summaries and is not counted as another run. One initial M6 launcher
left an empty log and its PID was no longer running; it produced no measurement
or qualification result. `qualification-M6-retry-20261028` is the actual M6
baseline qualification. No qualification process remains running.
