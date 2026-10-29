# E1 complete campaign ledger

C/R are direct core/reference transitions; PC/PR are replayed core/reference transitions. G1/TRACE copies are counted, not subtracted. Trials are whole baseline runs, random choice-list runs, or enumerated prefixes. A liveness stop is an ORIGINAL finding, not a mutation hit. All seconds exclude loading.

| Mutation | Configuration | Seed | Result / contract | Seconds | Trials | C / R / PC / PR | G1 / G2 | Boundary | Evidence |
|---|---|---:|---|---:|---:|---|---|---:|---|
| ORIGINAL | baseline | 1 | found/baseline-liveness | 0.276447 | 1 | 50062 / 50062 / 0 / 0 | 0 / 0 | 5178 | record (`../results/ORIGINAL-baseline-1-schedule.sexp`) |
| ORIGINAL | baseline | 20261028 | found/baseline-liveness | 0.284848 | 1 | 50158 / 50158 / 0 / 0 | 0 / 0 | 5190 | record (`../results/ORIGINAL-baseline-20261028-schedule.sexp`) |
| ORIGINAL | baseline | 314159265 | found/baseline-liveness | 0.281520 | 1 | 49796 / 49796 / 0 / 0 | 0 / 0 | 5152 | record (`../results/ORIGINAL-baseline-314159265-schedule.sexp`) |
| ORIGINAL | random | 1 | censored/transitions | 2.751965 | 220 | 100000 / 100000 / 0 / 0 | 50000 / 0 | — | record (`../results/ORIGINAL-random-1.sexp`) |
| ORIGINAL | random | 20261028 | censored/transitions | 2.758115 | 221 | 99996 / 100004 / 0 / 0 | 50002 / 0 | — | record (`../results/ORIGINAL-random-20261028.sexp`) |
| ORIGINAL | random | 314159265 | censored/transitions | 2.563844 | 218 | 100000 / 100000 / 0 / 0 | 50000 / 0 | — | record (`../results/ORIGINAL-random-314159265.sexp`) |
| ORIGINAL | exhaustive | 1 | completed/domain-exhausted | 0.384758 | 657 | 0 / 0 / 10694 / 10694 | 5347 / 0 | — | record (`../results/ORIGINAL-exhaustive-1.sexp`) |
| M1 | baseline | 1 | found/baseline-liveness | 0.292999 | 1 | 50062 / 50062 / 0 / 0 | 0 / 0 | 5178 | record (`../results/M1-baseline-1-schedule.sexp`) |
| M1 | baseline | 20261028 | found/baseline-liveness | 0.276662 | 1 | 50158 / 50158 / 0 / 0 | 0 / 0 | 5190 | record (`../results/M1-baseline-20261028-schedule.sexp`) |
| M1 | baseline | 314159265 | found/baseline-liveness | 0.288490 | 1 | 49796 / 49796 / 0 / 0 | 0 / 0 | 5152 | record (`../results/M1-baseline-314159265-schedule.sexp`) |
| M1 | random | 1 | found/g2 | 0.376915 | 1 | 70 / 70 / 13252 / 13252 | 6661 / 61 | 27 | record (`../results/M1-random-1-schedule.sexp`) |
| M1 | random | 20261028 | found/g2 | 0.520415 | 1 | 112 / 112 / 18376 / 18376 | 9244 / 61 | 39 | record (`../results/M1-random-20261028-schedule.sexp`) |
| M1 | random | 314159265 | found/g2 | 0.019126 | 2 | 540 / 540 / 324 / 324 | 432 / 1 | 37 | record (`../results/M1-random-314159265-schedule.sexp`) |
| M1 | exhaustive | 1 | completed/domain-exhausted | 0.448466 | 657 | 0 / 0 / 10694 / 10694 | 5347 / 0 | — | record (`../results/M1-exhaustive-1.sexp`) |
| M2 | baseline | 1 | found/client-oracle | 0.003141 | 1 | 266 / 266 / 0 / 0 | 0 / 0 | 30 | record (`../results/M2-baseline-1-schedule.sexp`) |
| M2 | baseline | 20261028 | found/client-oracle | 0.004717 | 1 | 106 / 106 / 0 / 0 | 0 / 0 | 13 | record (`../results/M2-baseline-20261028-schedule.sexp`) |
| M2 | baseline | 314159265 | found/client-oracle | 0.001282 | 1 | 105 / 105 / 0 / 0 | 0 / 0 | 12 | record (`../results/M2-baseline-314159265-schedule.sexp`) |
| M2 | random | 1 | found/client-oracle | 0.013961 | 2 | 578 / 578 / 0 / 0 | 289 / 0 | 43 | record (`../results/M2-random-1-schedule.sexp`) |
| M2 | random | 20261028 | found/client-oracle | 0.004251 | 1 | 160 / 160 / 0 / 0 | 80 / 0 | 46 | record (`../results/M2-random-20261028-schedule.sexp`) |
| M2 | random | 314159265 | found/client-oracle | 0.013653 | 2 | 708 / 708 / 0 / 0 | 354 / 0 | 80 | record (`../results/M2-random-314159265-schedule.sexp`) |
| M2 | exhaustive | 1 | completed/domain-exhausted | 0.335698 | 657 | 0 / 0 / 10694 / 10694 | 5347 / 0 | — | record (`../results/M2-exhaustive-1.sexp`) |
| M3 | baseline | 1 | found/turn-monitors | 0.000725 | 1 | 11 / 19 / 0 / 0 | 0 / 0 | 3 | record (`../results/M3-baseline-1-schedule.sexp`) |
| M3 | baseline | 20261028 | found/turn-monitors | 0.000728 | 1 | 11 / 19 / 0 / 0 | 0 / 0 | 3 | record (`../results/M3-baseline-20261028-schedule.sexp`) |
| M3 | baseline | 314159265 | found/turn-monitors | 0.000817 | 1 | 11 / 19 / 0 / 0 | 0 / 0 | 3 | record (`../results/M3-baseline-314159265-schedule.sexp`) |
| M3 | random | 1 | found/g1 | 0.001122 | 1 | 17 / 17 / 0 / 0 | 9 / 0 | 7 | record (`../results/M3-random-1-schedule.sexp`) |
| M3 | random | 20261028 | found/g1 | 0.001165 | 1 | 17 / 17 / 0 / 0 | 9 / 0 | 4 | record (`../results/M3-random-20261028-schedule.sexp`) |
| M3 | random | 314159265 | found/g1 | 0.001387 | 1 | 19 / 19 / 0 / 0 | 10 / 0 | 10 | record (`../results/M3-random-314159265-schedule.sexp`) |
| M3 | exhaustive | 1 | found/g1 | 0.070293 | 103 | 0 / 0 / 1761 / 1761 | 881 / 0 | 4 | record (`../results/M3-exhaustive-1-schedule.sexp`) |
| M4 | baseline | 1 | found/baseline-liveness | 0.249674 | 1 | 50062 / 50062 / 0 / 0 | 0 / 0 | 5178 | record (`../results/M4-baseline-1-schedule.sexp`) |
| M4 | baseline | 20261028 | found/baseline-liveness | 0.261707 | 1 | 50158 / 50158 / 0 / 0 | 0 / 0 | 5190 | record (`../results/M4-baseline-20261028-schedule.sexp`) |
| M4 | baseline | 314159265 | found/client-oracle | 0.001496 | 1 | 135 / 135 / 0 / 0 | 0 / 0 | 15 | record (`../results/M4-baseline-314159265-schedule.sexp`) |
| M4 | random | 1 | found/client-oracle | 0.017442 | 2 | 906 / 906 / 0 / 0 | 453 / 0 | 116 | record (`../results/M4-random-1-schedule.sexp`) |
| M4 | random | 20261028 | found/client-oracle | 0.162409 | 14 | 5826 / 5826 / 0 / 0 | 2913 / 0 | 54 | record (`../results/M4-random-20261028-schedule.sexp`) |
| M4 | random | 314159265 | found/client-oracle | 0.266941 | 28 | 12692 / 12692 / 0 / 0 | 6346 / 0 | 71 | record (`../results/M4-random-314159265-schedule.sexp`) |
| M4 | exhaustive | 1 | completed/domain-exhausted | 0.450504 | 657 | 0 / 0 / 10694 / 10694 | 5347 / 0 | — | record (`../results/M4-exhaustive-1.sexp`) |
| M5 | baseline | 1 | found/turn-monitors | 0.000658 | 1 | 8 / 8 / 0 / 0 | 0 / 0 | 1 | record (`../results/M5-baseline-1-schedule.sexp`) |
| M5 | baseline | 20261028 | found/turn-monitors | 0.000596 | 1 | 8 / 8 / 0 / 0 | 0 / 0 | 1 | record (`../results/M5-baseline-20261028-schedule.sexp`) |
| M5 | baseline | 314159265 | found/turn-monitors | 0.001011 | 1 | 8 / 8 / 0 / 0 | 0 / 0 | 1 | record (`../results/M5-baseline-314159265-schedule.sexp`) |
| M5 | random | 1 | found/g1-entry | 0.000664 | 1 | 0 / 0 / 0 / 0 | 0 / 0 | 1 | record (`../results/M5-random-1-schedule.sexp`) |
| M5 | random | 20261028 | found/g1-entry | 0.000621 | 1 | 0 / 0 / 0 / 0 | 0 / 0 | 1 | record (`../results/M5-random-20261028-schedule.sexp`) |
| M5 | random | 314159265 | found/g1-entry | 0.000607 | 1 | 0 / 0 / 0 / 0 | 0 / 0 | 1 | record (`../results/M5-random-314159265-schedule.sexp`) |
| M5 | exhaustive | 1 | found/g1-entry | 0.000867 | 2 | 0 / 0 / 0 / 0 | 0 / 0 | 1 | record (`../results/M5-exhaustive-1-schedule.sexp`) |
| M6 | baseline | 1 | found/baseline-liveness | 0.254690 | 1 | 50062 / 50062 / 0 / 0 | 0 / 0 | 5178 | record (`../results/M6-baseline-1-schedule.sexp`) |
| M6 | baseline | 20261028 | found/adapter-class-latency | 0.001078 | 1 | 45 / 45 / 0 / 0 | 0 / 0 | 6 | record (`../results/M6-baseline-20261028-schedule.sexp`) |
| M6 | baseline | 314159265 | found/adapter-class-latency | 0.002521 | 1 | 241 / 241 / 0 / 0 | 0 / 0 | 28 | record (`../results/M6-baseline-314159265-schedule.sexp`) |
| M6 | random | 1 | found/adapter-class-latency | 0.001926 | 1 | 70 / 70 / 0 / 0 | 35 / 0 | 19 | record (`../results/M6-random-1-schedule.sexp`) |
| M6 | random | 20261028 | found/adapter-class-latency | 0.002985 | 1 | 110 / 110 / 0 / 0 | 55 / 0 | 24 | record (`../results/M6-random-20261028-schedule.sexp`) |
| M6 | random | 314159265 | found/adapter-class-latency | 0.001986 | 1 | 54 / 54 / 0 / 0 | 27 / 0 | 13 | record (`../results/M6-random-314159265-schedule.sexp`) |
| M6 | exhaustive | 1 | found/adapter-class-latency | 0.008317 | 13 | 0 / 0 / 214 / 214 | 107 / 0 | 4 | record (`../results/M6-exhaustive-1-schedule.sexp`) |

## Reachability counters

Endpoints include duplicates and replay work. G1 counts include preflight/replayed transitions. Zero G2 means unexercised; rejected candidates are occurrence alternatives, not distinct states.

| Mutation | Config | Seed | States reached | Prefixes enumerated | G1 | G2 | Rejected candidates | Illegal residual | Rejected prefixes | Non-earliest land selections |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| ORIGINAL | baseline | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| ORIGINAL | baseline | 20261028 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| ORIGINAL | baseline | 314159265 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| ORIGINAL | random | 1 | 28366 | 0 | 50000 | 0 | 369650 | 0 | 0 | 141 |
| ORIGINAL | random | 20261028 | 28408 | 0 | 50002 | 0 | 378880 | 0 | 0 | 159 |
| ORIGINAL | random | 314159265 | 28075 | 0 | 50000 | 0 | 371680 | 0 | 0 | 159 |
| ORIGINAL | exhaustive | 1 | 657 | 657 | 5347 | 0 | 10170 | 0 | 0 | 0 |
| M1 | baseline | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M1 | baseline | 20261028 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M1 | baseline | 314159265 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M1 | random | 1 | 18 | 0 | 6661 | 61 | 132 | 0 | 0 | 62 |
| M1 | random | 20261028 | 30 | 0 | 9244 | 61 | 447 | 0 | 0 | 64 |
| M1 | random | 314159265 | 156 | 0 | 432 | 1 | 1854 | 0 | 0 | 1 |
| M1 | exhaustive | 1 | 657 | 657 | 5347 | 0 | 10170 | 0 | 0 | 0 |
| M2 | baseline | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M2 | baseline | 20261028 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M2 | baseline | 314159265 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M2 | random | 1 | 172 | 0 | 289 | 0 | 3870 | 0 | 0 | 4 |
| M2 | random | 20261028 | 46 | 0 | 80 | 0 | 1010 | 0 | 0 | 2 |
| M2 | random | 314159265 | 209 | 0 | 354 | 0 | 2710 | 0 | 0 | 0 |
| M2 | exhaustive | 1 | 657 | 657 | 5347 | 0 | 10170 | 0 | 0 | 0 |
| M3 | baseline | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M3 | baseline | 20261028 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M3 | baseline | 314159265 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M3 | random | 1 | 7 | 0 | 9 | 0 | 45 | 0 | 0 | 0 |
| M3 | random | 20261028 | 4 | 0 | 9 | 0 | 45 | 0 | 0 | 0 |
| M3 | random | 314159265 | 10 | 0 | 10 | 0 | 45 | 0 | 0 | 0 |
| M3 | exhaustive | 1 | 102 | 103 | 881 | 0 | 1890 | 0 | 0 | 0 |
| M4 | baseline | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M4 | baseline | 20261028 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M4 | baseline | 314159265 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M4 | random | 1 | 245 | 0 | 453 | 0 | 4335 | 0 | 0 | 4 |
| M4 | random | 20261028 | 1731 | 0 | 2913 | 0 | 24675 | 0 | 0 | 16 |
| M4 | random | 314159265 | 3554 | 0 | 6346 | 0 | 45545 | 0 | 0 | 10 |
| M4 | exhaustive | 1 | 657 | 657 | 5347 | 0 | 10170 | 0 | 0 | 0 |
| M5 | baseline | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M5 | baseline | 20261028 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M5 | baseline | 314159265 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M5 | random | 1 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M5 | random | 20261028 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M5 | random | 314159265 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M5 | exhaustive | 1 | 1 | 2 | 0 | 0 | 0 | 0 | 0 | 0 |
| M6 | baseline | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M6 | baseline | 20261028 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M6 | baseline | 314159265 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M6 | random | 1 | 19 | 0 | 35 | 0 | 325 | 0 | 0 | 0 |
| M6 | random | 20261028 | 24 | 0 | 55 | 0 | 180 | 0 | 0 | 0 |
| M6 | random | 314159265 | 13 | 0 | 27 | 0 | 90 | 0 | 0 | 0 |
| M6 | exhaustive | 1 | 12 | 13 | 107 | 0 | 135 | 0 | 0 | 0 |

Records named here are regenerable and git-ignored; `E1-RESULTS.md` ("Raw records") gives the commands.
