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
