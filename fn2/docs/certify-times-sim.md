# fn2/sim certify times (slice `sim`, fast-books lane)

Baseline at dev 8a4875e89, 2026-10-29, `fn2/tools/certify.sh -j 2` on the laptop while other seats certified
(load average 90-150, so wall seconds are inflated and noisy; the per-event ratios are the signal).
`seconds` is cert.pl's Built time, `prove` the CERTIFY-BOOK prove time, top event the largest single
non-wrapper event in the book's .cert.out. LD-only files (abi-evidence, echo-evidence, echo-scenario) are not books.

| book | seconds | prove | top event (seconds) |
|---|---|---|---|
| sim-adapter-base | 61.6 | 56.9 | DEFTHM FN2-SIM-PHYSICAL-SIM-TYPE (11.65) |
| sim | 43.7 | 34.0 | DEFTHM FN2-SIM-CRASH-FLIGHT-ONE-SIM-TYPE (3.12) |
| sim-state-data | 15.6 | 11.4 | ENCAPSULATE NIL (LOCAL (9.35) |
| sim-state | 14.6 | 13.2 | DEFTHM FN2-SIM-EARLIEST-RESULT (4.42) |
| sim-transfer | 8.6 | 4.5 | DEFTHM FN2-SIM-TRANSFER-POOL-WFP (0.69) |
| sim-recovery | 8.3 | 3.1 | DEFTHM FN2-SIM-RECOVER-LOOP-IMAGE-TYPE (0.53) |
| check-own | 4.8 | 3.0 | ENCAPSULATE NIL (LOCAL (0.62) |
| echo | 4.7 | 0.0 | DEFTHM FN2-SIM-ECHO-NETWORK-RESET-READY (0.03) |
| check-work | 3.5 | 0.0 | DEFUN FN2-WORK-POSTED-BYTES (0.02) |
| check | 2.9 | 0.0 | DEFCONST *FN2-CHECKER-NAMES* (0.00) |
| check-trace | 2.9 | 0.0 | DEFUN FN2-TRACE-SELECTION-DIFFERENCE (0.01) |
| network | 2.8 | 1.3 | ENCAPSULATE NIL (LOCAL (1.06) |
| prng | 2.2 | 1.5 | DEFUN FN2-PRNG-MIX32 (1.22) |
| storage | 1.8 | 0.8 | ENCAPSULATE NIL (LOCAL (0.55) |
| recover-stub | 1.0 | 0.2 | ENCAPSULATE NIL (LOCAL (0.11) |

Total 179.1 s over 15 books; over 15 s: 3; under 5 s: 9.

## For the DSL seat: sim-state-data's defcolumns encapsulate (measured 2026-10-29, laptop, loaded)

sim-state-data certifies in 13.5-14.6 s (9.35 s in the one `defcolumns fn2-sim` MAKE-EVENT/ENCAPSULATE,
15.6 s when the laptop was at load 90+). I replayed the 1,227 events that `fn2-columns-events` returns for it
as top-level forms (same theory, same constants) and timed each:

- Total 5.8 s over 1,101 timed events; no rule family dominates, the tail is flat.
- Largest: `CREATE-FN2-SIM-TYPE` 0.86 s (one event, `:in-theory (enable p create)` over a 90-field stobj),
  the 22 `*-FIELD-TYPE` theorems 0.54 s, the `defstobj` 0.34 s, `FN2-SIM-RECORD-P-UPDATE` 0.18 s, the 21
  `*-NTH-NATP` and 21 `*-NTH-BOUND` theorems 0.13 s each, the 20 `*-PRESERVES-WFP` 0.11 s.
- The remaining ~3.5 s of the 9.35 s is encapsulate and world-extension overhead that per-event times do not show.
- Ruled out: the per-field `*-NTH-NATP` type-prescription rules (307 of them in the sim world) look
  expensive in accumulated-persistence (16,000+ useless tries each in every downstream proof), but disabling
  all 307 before proving sim-adapter-base changed its total from 27-28.5 s to 26.1 s in one ld session, which is noise.
  Do not spend generator effort there.

Change I would try, in the generator, none measured beyond the numbers above: (1) prove `CREATE-...-TYPE`
by a `:use` of the per-field `*-FIELD-TYPE` facts instead of enabling `p` and `create` together (the one
0.86 s event); (2) emit the five scalar families (`-NATP`, `-BOUND`, `-NTH-NATP`, `-NTH-BOUND`, `-RAW-NTH-*`,
about 0.5 s together) only for fields some proof uses. The most this can buy is about 1.5 s of 14 s, below the
2 s noise floor of the laptop, so I would not prioritise it: sim-state-data is already under 15 s. Re-measure on
dregg-forge before touching the generator.

## On dregg-forge after the physical-dispatch commit (2026-10-29, `-j 8`, quiet box, cert.pl wall = CPU)

Runs vary by about 1.5 s between repeats (sim-adapter-base 18.8, 19.1, 20.0, 20.7), so read these as +-1.5 s.

| book | forge s | status |
|---|---|---|
| sim-adapter-base | ~19 | over 15: flat spread, see below |
| sim | ~16 | over 15: 2.1 s of it is including sim-adapter-base |
| sim-state-data | ~12 | one defcolumns encapsulate (DSL seat section above) |
| sim-state | ~10 | `fn2-sim-earliest-result` 4.4 s under load is the one big event |
| sim-transfer | 5.5 | |
| sim-recovery | 4.1 | |
| check-own | 3.4 | |
| echo, check, check-work, check-trace, network | 1.8-2.3 | |
| recover-stub, prng, storage | under 1.5 | |

What did not move the two over-15 books (each tried on forge or in an ld session, then reverted):
- Splitting `fn2-sim-terminal-post`'s two post calls into a helper (sim 16.5 -> 16.6 s): its branch product is not the cost.
- `(local (in-theory (disable (tau-system))))` in sim-adapter-base, sim-state, sim-transfer (sim 16.5 -> 17.6 s, no gain).
- Disabling all 307 `*-nth-natp` type-prescription rules (no change).
- Removing the `(enable fn2-sim-ready)` hint from `fn2-sim-register-type`: the proof then does not finish (192 s, cut off), so the hint is load-bearing.

What is left in sim-adapter-base after the physical fix is a flat spread: register family 3.4 s (a 13-setter chain, each fact re-walks it), take-one 2.5 s, inject 1.2 s, environment 0.7 s, then 100+ events under 0.5 s. Getting under 15 s needs a structural change (for example a generated setter-chain lemma for `register`, or splitting the book at the register/take-one boundary), not a hint.
