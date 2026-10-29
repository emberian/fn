# E1 pass 2 campaign ledger

Main matrix: c1/default/initial. Supplied listener/send/data rows are local claims, not search from initialization. C2/data rows use a separate two-capability profile. 3b is bounded-retention exact-state deduplication. Times include original counterfactual replay, exclude loading. C/R/PC/PR/OC/OR are direct core/reference, replayed core/reference, and original-counterfactual core/reference totals. All six categories consume the same 200,000-transition budget.

| Mutation | Mode | Profile/declaration/start | Seed | Result/contract | Seconds | Trials | C/R/PC/PR/OC/OR | Boundary | Known ORIGINAL | Evidence |
|---|---|---|---:|---|---:|---:|---|---:|---:|---|
| M1 | baseline | c1/default/initial | 1 | :CENSORED/:TRANSITIONS | 0.863454 | 3 | 99995/100005/0/0/0/0 | — | 2 | record (`pass2/results/M1-baseline-c1-default-initial-1.sexp`) |
| M1 | baseline | c1/default/initial | 20261028 | :CENSORED/:TRANSITIONS | 0.774047 | 3 | 99997/100003/0/0/0/0 | — | 2 | record (`pass2/results/M1-baseline-c1-default-initial-20261028.sexp`) |
| M1 | baseline | c1/default/initial | 314159265 | :CENSORED/:TRANSITIONS | 0.686899 | 3 | 99995/100005/0/0/0/0 | — | 2 | record (`pass2/results/M1-baseline-c1-default-initial-314159265.sexp`) |
| M1 | dedup | c1/default/initial | 1 | :CENSORED/:TRANSITIONS | 18.629313 | 5374 | 0/0/100000/100000/0/0 | — | 0 | record (`pass2/results/M1-dedup-c1-default-initial-1.sexp`) |
| M1 | iterative | c1/default/initial | 1 | :CENSORED/:TRANSITIONS | 5.597152 | 5627 | 0/0/100000/100000/0/0 | — | 0 | record (`pass2/results/M1-iterative-c1-default-initial-1.sexp`) |
| M1 | iterative | c1/default/listener | 1 | :FOUND/:G2 | 0.010212 | 1 | 0/0/414/414/0/0 | 27 | 0 | record (`pass2/results/M1-iterative-c1-default-listener-1-schedule.sexp`) |
| M1 | iterative | c1/default/send | 1 | :FOUND/:G2 | 0.368716 | 1 | 0/0/15782/15782/0/0 | 26 | 0 | record (`pass2/results/M1-iterative-c1-default-send-1-schedule.sexp`) |
| M1 | random | c1/default/initial | 1 | :FOUND/:G2 | 0.375256 | 1 | 70/70/13252/13252/0/0 | 27 | 0 | record (`pass2/results/M1-random-c1-default-initial-1-schedule.sexp`) |
| M1 | random | c1/default/initial | 20261028 | :FOUND/:G2 | 0.526972 | 1 | 112/112/18376/18376/0/0 | 39 | 0 | record (`pass2/results/M1-random-c1-default-initial-20261028-schedule.sexp`) |
| M1 | random | c1/default/initial | 314159265 | :FOUND/:G2 | 0.022960 | 2 | 540/540/324/324/0/0 | 37 | 0 | record (`pass2/results/M1-random-c1-default-initial-314159265-schedule.sexp`) |
| M2 | baseline | c1/default/initial | 1 | :FOUND/:CLIENT-ORACLE | 0.009501 | 1 | 266/266/0/0/0/0 | 30 | 0 | record (`pass2/results/M2-baseline-c1-default-initial-1-schedule.sexp`) |
| M2 | baseline | c1/default/initial | 20261028 | :FOUND/:CLIENT-ORACLE | 0.001722 | 1 | 106/106/0/0/0/0 | 13 | 0 | record (`pass2/results/M2-baseline-c1-default-initial-20261028-schedule.sexp`) |
| M2 | baseline | c1/default/initial | 314159265 | :FOUND/:CLIENT-ORACLE | 0.002560 | 1 | 105/105/0/0/0/0 | 12 | 0 | record (`pass2/results/M2-baseline-c1-default-initial-314159265-schedule.sexp`) |
| M2 | dedup | c1/default/initial | 1 | :CENSORED/:TRANSITIONS | 18.579044 | 5374 | 0/0/100000/100000/0/0 | — | 0 | record (`pass2/results/M2-dedup-c1-default-initial-1.sexp`) |
| M2 | dedup | c2/data/data | 1 | :CENSORED/:TRANSITIONS | 3.003948 | 3 | 0/0/99998/100002/0/0 | — | 0 | record (`pass2/results/M2-dedup-c2-data-data-1.sexp`) |
| M2 | dedup | c2/data/initial | 1 | :CENSORED/:TRANSITIONS | 16.987952 | 5374 | 0/0/100000/100000/0/0 | — | 0 | record (`pass2/results/M2-dedup-c2-data-initial-1.sexp`) |
| M2 | iterative | c1/default/initial | 1 | :CENSORED/:TRANSITIONS | 5.630289 | 5627 | 0/0/100000/100000/0/0 | — | 0 | record (`pass2/results/M2-iterative-c1-default-initial-1.sexp`) |
| M2 | iterative | c1/default/listener | 1 | :CENSORED/:TRANSITIONS | 2.365245 | 1104 | 0/0/99996/100004/0/0 | — | 0 | record (`pass2/results/M2-iterative-c1-default-listener-1.sexp`) |
| M2 | iterative | c1/default/send | 1 | :CENSORED/:TRANSITIONS | 2.387922 | 1106 | 0/0/99998/100002/0/0 | — | 0 | record (`pass2/results/M2-iterative-c1-default-send-1.sexp`) |
| M2 | iterative | c2/data/data | 1 | :CENSORED/:TRANSITIONS | 2.660158 | 3 | 0/0/99998/100002/0/0 | — | 0 | record (`pass2/results/M2-iterative-c2-data-data-1.sexp`) |
| M2 | iterative | c2/data/initial | 1 | :CENSORED/:TRANSITIONS | 3.834288 | 5627 | 0/0/100000/100000/0/0 | — | 0 | record (`pass2/results/M2-iterative-c2-data-initial-1.sexp`) |
| M2 | random | c1/default/initial | 1 | :FOUND/:CLIENT-ORACLE | 0.649265 | 50 | 19340/19340/0/0/3174/3174 | 115 | 0 | record (`pass2/results/M2-random-c1-default-initial-1-schedule.sexp`) |
| M2 | random | c1/default/initial | 20261028 | :FOUND/:CLIENT-ORACLE | 0.253380 | 17 | 6030/6030/0/0/1946/1946 | 44 | 0 | record (`pass2/results/M2-random-c1-default-initial-20261028-schedule.sexp`) |
| M2 | random | c1/default/initial | 314159265 | :FOUND/:CLIENT-ORACLE | 0.248791 | 21 | 8744/8744/0/0/1302/1302 | 52 | 0 | record (`pass2/results/M2-random-c1-default-initial-314159265-schedule.sexp`) |
| M2 | random | c2/data/data | 1 | :CENSORED/:TRANSITIONS | 2.133743 | 1 | 0/0/100000/100000/0/0 | — | 0 | record (`pass2/results/M2-random-c2-data-data-1.sexp`) |
| M2 | random | c2/data/data | 20261028 | :CENSORED/:TRANSITIONS | 2.019519 | 1 | 0/0/100000/100000/0/0 | — | 0 | record (`pass2/results/M2-random-c2-data-data-20261028.sexp`) |
| M2 | random | c2/data/data | 314159265 | :CENSORED/:TRANSITIONS | 2.845353 | 1 | 0/0/100000/100000/0/0 | — | 0 | record (`pass2/results/M2-random-c2-data-data-314159265.sexp`) |
| M2 | random | c2/data/initial | 1 | :FOUND/:CLIENT-ORACLE | 0.095922 | 6 | 2476/2476/0/0/646/646 | 110 | 0 | record (`pass2/results/M2-random-c2-data-initial-1-schedule.sexp`) |
| M2 | random | c2/data/initial | 20261028 | :CENSORED/:TRANSITIONS | 2.489630 | 23 | 8772/8772/89138/89138/2090/2090 | — | 0 | record (`pass2/results/M2-random-c2-data-initial-20261028.sexp`) |
| M2 | random | c2/data/initial | 314159265 | :CENSORED/:TRANSITIONS | 2.391383 | 2 | 502/502/99232/99232/266/266 | — | 0 | record (`pass2/results/M2-random-c2-data-initial-314159265.sexp`) |
| M3 | baseline | c1/default/initial | 1 | :FOUND/:TURN-MONITORS | 0.000799 | 1 | 11/19/0/0/0/0 | 3 | 0 | record (`pass2/results/M3-baseline-c1-default-initial-1-schedule.sexp`) |
| M3 | baseline | c1/default/initial | 20261028 | :FOUND/:TURN-MONITORS | 0.001647 | 1 | 11/19/0/0/0/0 | 3 | 0 | record (`pass2/results/M3-baseline-c1-default-initial-20261028-schedule.sexp`) |
| M3 | baseline | c1/default/initial | 314159265 | :FOUND/:TURN-MONITORS | 0.001625 | 1 | 11/19/0/0/0/0 | 3 | 0 | record (`pass2/results/M3-baseline-c1-default-initial-314159265-schedule.sexp`) |
| M3 | dedup | c1/default/initial | 1 | :FOUND/:G1 | 0.649553 | 174 | 0/0/2651/2651/36/36 | 4 | 0 | record (`pass2/results/M3-dedup-c1-default-initial-1-schedule.sexp`) |
| M3 | iterative | c1/default/initial | 1 | :FOUND/:G1 | 0.183651 | 208 | 0/0/3049/3049/36/36 | 4 | 0 | record (`pass2/results/M3-iterative-c1-default-initial-1-schedule.sexp`) |
| M3 | iterative | c1/default/listener | 1 | :FOUND/:G1 | 0.003516 | 1 | 0/0/19/19/38/38 | 7 | 0 | record (`pass2/results/M3-iterative-c1-default-listener-1-schedule.sexp`) |
| M3 | iterative | c1/default/send | 1 | :FOUND/:G1 | 0.003736 | 1 | 0/0/19/19/38/38 | 7 | 0 | record (`pass2/results/M3-iterative-c1-default-send-1-schedule.sexp`) |
| M3 | random | c1/default/initial | 1 | :FOUND/:G1 | 0.002352 | 1 | 17/17/0/0/36/36 | 7 | 0 | record (`pass2/results/M3-random-c1-default-initial-1-schedule.sexp`) |
| M3 | random | c1/default/initial | 20261028 | :FOUND/:G1 | 0.002823 | 1 | 17/17/0/0/36/36 | 4 | 0 | record (`pass2/results/M3-random-c1-default-initial-20261028-schedule.sexp`) |
| M3 | random | c1/default/initial | 314159265 | :FOUND/:G1 | 0.003894 | 1 | 19/19/0/0/38/38 | 10 | 0 | record (`pass2/results/M3-random-c1-default-initial-314159265-schedule.sexp`) |
| M4 | baseline | c1/default/initial | 1 | :FOUND/:CLIENT-ORACLE | 0.346015 | 2 | 50386/50386/0/0/0/0 | 41 | 1 | record (`pass2/results/M4-baseline-c1-default-initial-1-schedule.sexp`) |
| M4 | baseline | c1/default/initial | 20261028 | :FOUND/:CLIENT-ORACLE | 0.387680 | 2 | 50423/50423/0/0/0/0 | 34 | 1 | record (`pass2/results/M4-baseline-c1-default-initial-20261028-schedule.sexp`) |
| M4 | baseline | c1/default/initial | 314159265 | :FOUND/:CLIENT-ORACLE | 0.001902 | 1 | 135/135/0/0/0/0 | 15 | 0 | record (`pass2/results/M4-baseline-c1-default-initial-314159265-schedule.sexp`) |
| M4 | dedup | c1/default/initial | 1 | :CENSORED/:TRANSITIONS | 17.341163 | 5374 | 0/0/100000/100000/0/0 | — | 0 | record (`pass2/results/M4-dedup-c1-default-initial-1.sexp`) |
| M4 | dedup | c2/data/data | 1 | :CENSORED/:TRANSITIONS | 2.458866 | 3 | 0/0/99998/100002/0/0 | — | 0 | record (`pass2/results/M4-dedup-c2-data-data-1.sexp`) |
| M4 | dedup | c2/data/initial | 1 | :CENSORED/:TRANSITIONS | 18.720881 | 5374 | 0/0/100000/100000/0/0 | — | 0 | record (`pass2/results/M4-dedup-c2-data-initial-1.sexp`) |
| M4 | iterative | c1/default/initial | 1 | :CENSORED/:TRANSITIONS | 4.082319 | 5627 | 0/0/100000/100000/0/0 | — | 0 | record (`pass2/results/M4-iterative-c1-default-initial-1.sexp`) |
| M4 | iterative | c1/default/listener | 1 | :CENSORED/:TRANSITIONS | 2.659340 | 1104 | 0/0/99996/100004/0/0 | — | 0 | record (`pass2/results/M4-iterative-c1-default-listener-1.sexp`) |
| M4 | iterative | c1/default/send | 1 | :CENSORED/:TRANSITIONS | 2.745536 | 1106 | 0/0/99998/100002/0/0 | — | 0 | record (`pass2/results/M4-iterative-c1-default-send-1.sexp`) |
| M4 | iterative | c2/data/data | 1 | :CENSORED/:TRANSITIONS | 2.545903 | 3 | 0/0/99998/100002/0/0 | — | 0 | record (`pass2/results/M4-iterative-c2-data-data-1.sexp`) |
| M4 | iterative | c2/data/initial | 1 | :CENSORED/:TRANSITIONS | 5.134768 | 5627 | 0/0/100000/100000/0/0 | — | 0 | record (`pass2/results/M4-iterative-c2-data-initial-1.sexp`) |
| M4 | random | c1/default/initial | 1 | :FOUND/:CLIENT-ORACLE | 1.437136 | 108 | 47620/47620/0/0/2970/2970 | 123 | 0 | record (`pass2/results/M4-random-c1-default-initial-1-schedule.sexp`) |
| M4 | random | c1/default/initial | 20261028 | :FOUND/:CLIENT-ORACLE | 0.277536 | 21 | 8924/8924/0/0/348/348 | 70 | 0 | record (`pass2/results/M4-random-c1-default-initial-20261028-schedule.sexp`) |
| M4 | random | c1/default/initial | 314159265 | :FOUND/:CLIENT-ORACLE | 0.373756 | 36 | 16104/16104/0/0/506/506 | 90 | 0 | record (`pass2/results/M4-random-c1-default-initial-314159265-schedule.sexp`) |
| M4 | random | c2/data/data | 1 | :CENSORED/:TRANSITIONS | 2.588798 | 1 | 0/0/100000/100000/0/0 | — | 0 | record (`pass2/results/M4-random-c2-data-data-1.sexp`) |
| M4 | random | c2/data/data | 20261028 | :CENSORED/:TRANSITIONS | 2.286784 | 1 | 0/0/100000/100000/0/0 | — | 0 | record (`pass2/results/M4-random-c2-data-data-20261028.sexp`) |
| M4 | random | c2/data/data | 314159265 | :CENSORED/:TRANSITIONS | 2.159807 | 1 | 0/0/100000/100000/0/0 | — | 0 | record (`pass2/results/M4-random-c2-data-data-314159265.sexp`) |
| M4 | random | c2/data/initial | 1 | :FOUND/:CLIENT-ORACLE | 0.981844 | 11 | 5218/5218/36800/36800/338/338 | 101 | 0 | record (`pass2/results/M4-random-c2-data-initial-1-schedule.sexp`) |
| M4 | random | c2/data/initial | 20261028 | :CENSORED/:TRANSITIONS | 2.361636 | 23 | 10490/10490/89508/89512/0/0 | — | 0 | record (`pass2/results/M4-random-c2-data-initial-20261028.sexp`) |
| M4 | random | c2/data/initial | 314159265 | :CENSORED/:TRANSITIONS | 2.442590 | 16 | 7060/7060/92622/92622/318/318 | — | 0 | record (`pass2/results/M4-random-c2-data-initial-314159265.sexp`) |
| M5 | baseline | c1/default/initial | 1 | :FOUND/:TURN-MONITORS | 0.000896 | 1 | 8/8/0/0/0/0 | 1 | 0 | record (`pass2/results/M5-baseline-c1-default-initial-1-schedule.sexp`) |
| M5 | baseline | c1/default/initial | 20261028 | :FOUND/:TURN-MONITORS | 0.000702 | 1 | 8/8/0/0/0/0 | 1 | 0 | record (`pass2/results/M5-baseline-c1-default-initial-20261028-schedule.sexp`) |
| M5 | baseline | c1/default/initial | 314159265 | :FOUND/:TURN-MONITORS | 0.000690 | 1 | 8/8/0/0/0/0 | 1 | 0 | record (`pass2/results/M5-baseline-c1-default-initial-314159265-schedule.sexp`) |
| M5 | dedup | c1/default/initial | 1 | :FOUND/:G1-ENTRY | 0.005125 | 3 | 0/0/0/0/16/16 | 1 | 0 | record (`pass2/results/M5-dedup-c1-default-initial-1-schedule.sexp`) |
| M5 | iterative | c1/default/initial | 1 | :FOUND/:G1-ENTRY | 0.002744 | 3 | 0/0/0/0/16/16 | 1 | 0 | record (`pass2/results/M5-iterative-c1-default-initial-1-schedule.sexp`) |
| M5 | iterative | c1/default/listener | 1 | :FOUND/:G1-ENTRY | 0.001519 | 1 | 0/0/0/0/16/16 | 1 | 0 | record (`pass2/results/M5-iterative-c1-default-listener-1-schedule.sexp`) |
| M5 | iterative | c1/default/send | 1 | :FOUND/:G1-ENTRY | 0.001548 | 1 | 0/0/0/0/16/16 | 1 | 0 | record (`pass2/results/M5-iterative-c1-default-send-1-schedule.sexp`) |
| M5 | random | c1/default/initial | 1 | :FOUND/:G1-ENTRY | 0.002884 | 1 | 0/0/0/0/16/16 | 1 | 0 | record (`pass2/results/M5-random-c1-default-initial-1-schedule.sexp`) |
| M5 | random | c1/default/initial | 20261028 | :FOUND/:G1-ENTRY | 0.001486 | 1 | 0/0/0/0/16/16 | 1 | 0 | record (`pass2/results/M5-random-c1-default-initial-20261028-schedule.sexp`) |
| M5 | random | c1/default/initial | 314159265 | :FOUND/:G1-ENTRY | 0.002065 | 1 | 0/0/0/0/16/16 | 1 | 0 | record (`pass2/results/M5-random-c1-default-initial-314159265-schedule.sexp`) |
| M6 | baseline | c1/default/initial | 1 | :FOUND/:ADAPTER-CLASS-LATENCY | 0.391370 | 2 | 50137/50137/0/0/0/0 | 9 | 1 | record (`pass2/results/M6-baseline-c1-default-initial-1-schedule.sexp`) |
| M6 | baseline | c1/default/initial | 20261028 | :FOUND/:ADAPTER-CLASS-LATENCY | 0.001281 | 1 | 45/45/0/0/0/0 | 6 | 0 | record (`pass2/results/M6-baseline-c1-default-initial-20261028-schedule.sexp`) |
| M6 | baseline | c1/default/initial | 314159265 | :FOUND/:ADAPTER-CLASS-LATENCY | 0.004723 | 1 | 241/241/0/0/0/0 | 28 | 0 | record (`pass2/results/M6-baseline-c1-default-initial-314159265-schedule.sexp`) |
| M6 | dedup | c1/default/initial | 1 | :FOUND/:ADAPTER-CLASS-LATENCY | 0.105229 | 35 | 0/0/414/414/16/16 | 3 | 0 | record (`pass2/results/M6-dedup-c1-default-initial-1-schedule.sexp`) |
| M6 | iterative | c1/default/initial | 1 | :FOUND/:ADAPTER-CLASS-LATENCY | 0.031927 | 38 | 0/0/430/430/16/16 | 3 | 0 | record (`pass2/results/M6-iterative-c1-default-initial-1-schedule.sexp`) |
| M6 | iterative | c1/default/listener | 1 | :FOUND/:ADAPTER-CLASS-LATENCY | 0.043147 | 11 | 0/0/990/990/90/90 | 17 | 0 | record (`pass2/results/M6-iterative-c1-default-listener-1-schedule.sexp`) |
| M6 | iterative | c1/default/send | 1 | :FOUND/:ADAPTER-CLASS-LATENCY | 0.044080 | 11 | 0/0/990/990/90/90 | 17 | 0 | record (`pass2/results/M6-iterative-c1-default-send-1-schedule.sexp`) |
| M6 | random | c1/default/initial | 1 | :FOUND/:ADAPTER-CLASS-LATENCY | 0.008032 | 1 | 70/70/0/0/70/70 | 19 | 0 | record (`pass2/results/M6-random-c1-default-initial-1-schedule.sexp`) |
| M6 | random | c1/default/initial | 20261028 | :FOUND/:ADAPTER-CLASS-LATENCY | 0.005928 | 1 | 110/110/0/0/110/110 | 24 | 0 | record (`pass2/results/M6-random-c1-default-initial-20261028-schedule.sexp`) |
| M6 | random | c1/default/initial | 314159265 | :FOUND/:ADAPTER-CLASS-LATENCY | 0.004864 | 1 | 54/54/0/0/54/54 | 13 | 0 | record (`pass2/results/M6-random-c1-default-initial-314159265-schedule.sexp`) |
| ORIGINAL | baseline | c1/default/initial | 1 | :CENSORED/:TRANSITIONS | 0.676644 | 3 | 99995/100005/0/0/0/0 | — | 2 | record (`pass2/results/ORIGINAL-baseline-c1-default-initial-1.sexp`) |
| ORIGINAL | baseline | c1/default/initial | 20261028 | :CENSORED/:TRANSITIONS | 0.620928 | 3 | 99997/100003/0/0/0/0 | — | 2 | record (`pass2/results/ORIGINAL-baseline-c1-default-initial-20261028.sexp`) |
| ORIGINAL | baseline | c1/default/initial | 314159265 | :CENSORED/:TRANSITIONS | 0.678375 | 3 | 99995/100005/0/0/0/0 | — | 2 | record (`pass2/results/ORIGINAL-baseline-c1-default-initial-314159265.sexp`) |
| ORIGINAL | dedup | c1/default/initial | 1 | :CENSORED/:TRANSITIONS | 14.974495 | 5374 | 0/0/100000/100000/0/0 | — | 0 | record (`pass2/results/ORIGINAL-dedup-c1-default-initial-1.sexp`) |
| ORIGINAL | dedup | c2/data/data | 1 | :CENSORED/:TRANSITIONS | 2.468055 | 3 | 0/0/99998/100002/0/0 | — | 0 | record (`pass2/results/ORIGINAL-dedup-c2-data-data-1.sexp`) |
| ORIGINAL | dedup | c2/data/initial | 1 | :CENSORED/:TRANSITIONS | 17.497501 | 5374 | 0/0/100000/100000/0/0 | — | 0 | record (`pass2/results/ORIGINAL-dedup-c2-data-initial-1.sexp`) |
| ORIGINAL | iterative | c1/default/initial | 1 | :CENSORED/:TRANSITIONS | 3.952521 | 5627 | 0/0/100000/100000/0/0 | — | 0 | record (`pass2/results/ORIGINAL-iterative-c1-default-initial-1.sexp`) |
| ORIGINAL | iterative | c1/default/listener | 1 | :CENSORED/:TRANSITIONS | 2.662888 | 1104 | 0/0/99996/100004/0/0 | — | 0 | record (`pass2/results/ORIGINAL-iterative-c1-default-listener-1.sexp`) |
| ORIGINAL | iterative | c1/default/send | 1 | :CENSORED/:TRANSITIONS | 2.821956 | 1106 | 0/0/99998/100002/0/0 | — | 0 | record (`pass2/results/ORIGINAL-iterative-c1-default-send-1.sexp`) |
| ORIGINAL | iterative | c2/data/data | 1 | :CENSORED/:TRANSITIONS | 2.613506 | 3 | 0/0/99998/100002/0/0 | — | 0 | record (`pass2/results/ORIGINAL-iterative-c2-data-data-1.sexp`) |
| ORIGINAL | iterative | c2/data/initial | 1 | :CENSORED/:TRANSITIONS | 4.662559 | 5627 | 0/0/100000/100000/0/0 | — | 0 | record (`pass2/results/ORIGINAL-iterative-c2-data-initial-1.sexp`) |
| ORIGINAL | random | c1/default/initial | 1 | :CENSORED/:TRANSITIONS | 2.145678 | 220 | 100000/100000/0/0/0/0 | — | 0 | record (`pass2/results/ORIGINAL-random-c1-default-initial-1.sexp`) |
| ORIGINAL | random | c1/default/initial | 20261028 | :CENSORED/:TRANSITIONS | 2.450316 | 221 | 99996/100004/0/0/0/0 | — | 0 | record (`pass2/results/ORIGINAL-random-c1-default-initial-20261028.sexp`) |
| ORIGINAL | random | c1/default/initial | 314159265 | :CENSORED/:TRANSITIONS | 2.588588 | 218 | 100000/100000/0/0/0/0 | — | 0 | record (`pass2/results/ORIGINAL-random-c1-default-initial-314159265.sexp`) |
| ORIGINAL | random | c2/data/data | 1 | :CENSORED/:TRANSITIONS | 2.772799 | 1 | 0/0/100000/100000/0/0 | — | 0 | record (`pass2/results/ORIGINAL-random-c2-data-data-1.sexp`) |
| ORIGINAL | random | c2/data/data | 20261028 | :CENSORED/:TRANSITIONS | 2.528416 | 1 | 0/0/100000/100000/0/0 | — | 0 | record (`pass2/results/ORIGINAL-random-c2-data-data-20261028.sexp`) |
| ORIGINAL | random | c2/data/data | 314159265 | :CENSORED/:TRANSITIONS | 2.752441 | 1 | 0/0/100000/100000/0/0 | — | 0 | record (`pass2/results/ORIGINAL-random-c2-data-data-314159265.sexp`) |
| ORIGINAL | random | c2/data/initial | 1 | :CENSORED/:TRANSITIONS | 2.452780 | 11 | 5312/5312/94688/94688/0/0 | — | 0 | record (`pass2/results/ORIGINAL-random-c2-data-initial-1.sexp`) |
| ORIGINAL | random | c2/data/initial | 20261028 | :CENSORED/:TRANSITIONS | 2.357745 | 23 | 10508/10508/89492/89492/0/0 | — | 0 | record (`pass2/results/ORIGINAL-random-c2-data-initial-20261028.sexp`) |
| ORIGINAL | random | c2/data/initial | 314159265 | :CENSORED/:TRANSITIONS | 2.754185 | 23 | 10732/10732/89268/89268/0/0 | — | 0 | record (`pass2/results/ORIGINAL-random-c2-data-initial-314159265.sexp`) |

## Horizon ledger

Depth is suffix length for supplied-prefix rows. Repeated prefixes at successive horizons count again. A partial horizon stops at failure or censoring.

| Mutation | Mode | Profile/declaration/start | Depth | Fully completed | Prefixes attempted | States reached | Exact duplicates |
|---|---|---|---:|---|---:|---:|---:|
| M1 | dedup | c1/default/initial | 0 | yes | 1 | 1 | 0 |
| M1 | dedup | c1/default/initial | 1 | yes | 4 | 4 | 1 |
| M1 | dedup | c1/default/initial | 2 | yes | 12 | 12 | 4 |
| M1 | dedup | c1/default/initial | 3 | yes | 58 | 58 | 15 |
| M1 | dedup | c1/default/initial | 4 | yes | 445 | 445 | 82 |
| M1 | dedup | c1/default/initial | 5 | yes | 4083 | 4083 | 584 |
| M1 | dedup | c1/default/initial | 6 | no | 771 | 770 | 84 |
| M1 | iterative | c1/default/initial | 0 | yes | 1 | 1 | 0 |
| M1 | iterative | c1/default/initial | 1 | yes | 4 | 4 | 0 |
| M1 | iterative | c1/default/initial | 2 | yes | 15 | 15 | 0 |
| M1 | iterative | c1/default/initial | 3 | yes | 85 | 85 | 0 |
| M1 | iterative | c1/default/initial | 4 | yes | 657 | 657 | 0 |
| M1 | iterative | c1/default/initial | 5 | no | 4865 | 4864 | 0 |
| M1 | iterative | c1/default/listener | 0 | no | 1 | 1 | 0 |
| M1 | iterative | c1/default/send | 0 | no | 1 | 1 | 0 |
| M2 | dedup | c1/default/initial | 0 | yes | 1 | 1 | 0 |
| M2 | dedup | c1/default/initial | 1 | yes | 4 | 4 | 1 |
| M2 | dedup | c1/default/initial | 2 | yes | 12 | 12 | 4 |
| M2 | dedup | c1/default/initial | 3 | yes | 58 | 58 | 15 |
| M2 | dedup | c1/default/initial | 4 | yes | 445 | 445 | 82 |
| M2 | dedup | c1/default/initial | 5 | yes | 4083 | 4083 | 584 |
| M2 | dedup | c1/default/initial | 6 | no | 771 | 770 | 84 |
| M2 | dedup | c2/data/data | 0 | yes | 1 | 1 | 0 |
| M2 | dedup | c2/data/data | 1 | no | 2 | 2 | 0 |
| M2 | dedup | c2/data/initial | 0 | yes | 1 | 1 | 0 |
| M2 | dedup | c2/data/initial | 1 | yes | 4 | 4 | 1 |
| M2 | dedup | c2/data/initial | 2 | yes | 12 | 12 | 4 |
| M2 | dedup | c2/data/initial | 3 | yes | 58 | 58 | 15 |
| M2 | dedup | c2/data/initial | 4 | yes | 445 | 445 | 82 |
| M2 | dedup | c2/data/initial | 5 | yes | 4083 | 4083 | 584 |
| M2 | dedup | c2/data/initial | 6 | no | 771 | 770 | 86 |
| M2 | iterative | c1/default/initial | 0 | yes | 1 | 1 | 0 |
| M2 | iterative | c1/default/initial | 1 | yes | 4 | 4 | 0 |
| M2 | iterative | c1/default/initial | 2 | yes | 15 | 15 | 0 |
| M2 | iterative | c1/default/initial | 3 | yes | 85 | 85 | 0 |
| M2 | iterative | c1/default/initial | 4 | yes | 657 | 657 | 0 |
| M2 | iterative | c1/default/initial | 5 | no | 4865 | 4864 | 0 |
| M2 | iterative | c1/default/listener | 0 | yes | 1 | 1 | 0 |
| M2 | iterative | c1/default/listener | 1 | yes | 31 | 31 | 0 |
| M2 | iterative | c1/default/listener | 2 | yes | 679 | 679 | 0 |
| M2 | iterative | c1/default/listener | 3 | no | 393 | 392 | 0 |
| M2 | iterative | c1/default/send | 0 | yes | 1 | 1 | 0 |
| M2 | iterative | c1/default/send | 1 | yes | 31 | 31 | 0 |
| M2 | iterative | c1/default/send | 2 | yes | 819 | 819 | 0 |
| M2 | iterative | c1/default/send | 3 | no | 255 | 254 | 0 |
| M2 | iterative | c2/data/data | 0 | yes | 1 | 1 | 0 |
| M2 | iterative | c2/data/data | 1 | no | 2 | 2 | 0 |
| M2 | iterative | c2/data/initial | 0 | yes | 1 | 1 | 0 |
| M2 | iterative | c2/data/initial | 1 | yes | 4 | 4 | 0 |
| M2 | iterative | c2/data/initial | 2 | yes | 15 | 15 | 0 |
| M2 | iterative | c2/data/initial | 3 | yes | 85 | 85 | 0 |
| M2 | iterative | c2/data/initial | 4 | yes | 657 | 657 | 0 |
| M2 | iterative | c2/data/initial | 5 | no | 4865 | 4864 | 0 |
| M3 | dedup | c1/default/initial | 0 | yes | 1 | 1 | 0 |
| M3 | dedup | c1/default/initial | 1 | yes | 4 | 4 | 1 |
| M3 | dedup | c1/default/initial | 2 | yes | 12 | 12 | 4 |
| M3 | dedup | c1/default/initial | 3 | yes | 58 | 58 | 15 |
| M3 | dedup | c1/default/initial | 4 | no | 99 | 98 | 17 |
| M3 | iterative | c1/default/initial | 0 | yes | 1 | 1 | 0 |
| M3 | iterative | c1/default/initial | 1 | yes | 4 | 4 | 0 |
| M3 | iterative | c1/default/initial | 2 | yes | 15 | 15 | 0 |
| M3 | iterative | c1/default/initial | 3 | yes | 85 | 85 | 0 |
| M3 | iterative | c1/default/initial | 4 | no | 103 | 102 | 0 |
| M3 | iterative | c1/default/listener | 0 | no | 1 | 0 | 0 |
| M3 | iterative | c1/default/send | 0 | no | 1 | 0 | 0 |
| M4 | dedup | c1/default/initial | 0 | yes | 1 | 1 | 0 |
| M4 | dedup | c1/default/initial | 1 | yes | 4 | 4 | 1 |
| M4 | dedup | c1/default/initial | 2 | yes | 12 | 12 | 4 |
| M4 | dedup | c1/default/initial | 3 | yes | 58 | 58 | 15 |
| M4 | dedup | c1/default/initial | 4 | yes | 445 | 445 | 82 |
| M4 | dedup | c1/default/initial | 5 | yes | 4083 | 4083 | 584 |
| M4 | dedup | c1/default/initial | 6 | no | 771 | 770 | 84 |
| M4 | dedup | c2/data/data | 0 | yes | 1 | 1 | 0 |
| M4 | dedup | c2/data/data | 1 | no | 2 | 2 | 0 |
| M4 | dedup | c2/data/initial | 0 | yes | 1 | 1 | 0 |
| M4 | dedup | c2/data/initial | 1 | yes | 4 | 4 | 1 |
| M4 | dedup | c2/data/initial | 2 | yes | 12 | 12 | 4 |
| M4 | dedup | c2/data/initial | 3 | yes | 58 | 58 | 15 |
| M4 | dedup | c2/data/initial | 4 | yes | 445 | 445 | 82 |
| M4 | dedup | c2/data/initial | 5 | yes | 4083 | 4083 | 584 |
| M4 | dedup | c2/data/initial | 6 | no | 771 | 770 | 86 |
| M4 | iterative | c1/default/initial | 0 | yes | 1 | 1 | 0 |
| M4 | iterative | c1/default/initial | 1 | yes | 4 | 4 | 0 |
| M4 | iterative | c1/default/initial | 2 | yes | 15 | 15 | 0 |
| M4 | iterative | c1/default/initial | 3 | yes | 85 | 85 | 0 |
| M4 | iterative | c1/default/initial | 4 | yes | 657 | 657 | 0 |
| M4 | iterative | c1/default/initial | 5 | no | 4865 | 4864 | 0 |
| M4 | iterative | c1/default/listener | 0 | yes | 1 | 1 | 0 |
| M4 | iterative | c1/default/listener | 1 | yes | 31 | 31 | 0 |
| M4 | iterative | c1/default/listener | 2 | yes | 679 | 679 | 0 |
| M4 | iterative | c1/default/listener | 3 | no | 393 | 392 | 0 |
| M4 | iterative | c1/default/send | 0 | yes | 1 | 1 | 0 |
| M4 | iterative | c1/default/send | 1 | yes | 31 | 31 | 0 |
| M4 | iterative | c1/default/send | 2 | yes | 819 | 819 | 0 |
| M4 | iterative | c1/default/send | 3 | no | 255 | 254 | 0 |
| M4 | iterative | c2/data/data | 0 | yes | 1 | 1 | 0 |
| M4 | iterative | c2/data/data | 1 | no | 2 | 2 | 0 |
| M4 | iterative | c2/data/initial | 0 | yes | 1 | 1 | 0 |
| M4 | iterative | c2/data/initial | 1 | yes | 4 | 4 | 0 |
| M4 | iterative | c2/data/initial | 2 | yes | 15 | 15 | 0 |
| M4 | iterative | c2/data/initial | 3 | yes | 85 | 85 | 0 |
| M4 | iterative | c2/data/initial | 4 | yes | 657 | 657 | 0 |
| M4 | iterative | c2/data/initial | 5 | no | 4865 | 4864 | 0 |
| M5 | dedup | c1/default/initial | 0 | yes | 1 | 1 | 0 |
| M5 | dedup | c1/default/initial | 1 | no | 2 | 1 | 0 |
| M5 | iterative | c1/default/initial | 0 | yes | 1 | 1 | 0 |
| M5 | iterative | c1/default/initial | 1 | no | 2 | 1 | 0 |
| M5 | iterative | c1/default/listener | 0 | no | 1 | 0 | 0 |
| M5 | iterative | c1/default/send | 0 | no | 1 | 0 | 0 |
| M6 | dedup | c1/default/initial | 0 | yes | 1 | 1 | 0 |
| M6 | dedup | c1/default/initial | 1 | yes | 4 | 4 | 1 |
| M6 | dedup | c1/default/initial | 2 | yes | 12 | 12 | 4 |
| M6 | dedup | c1/default/initial | 3 | no | 18 | 17 | 2 |
| M6 | iterative | c1/default/initial | 0 | yes | 1 | 1 | 0 |
| M6 | iterative | c1/default/initial | 1 | yes | 4 | 4 | 0 |
| M6 | iterative | c1/default/initial | 2 | yes | 15 | 15 | 0 |
| M6 | iterative | c1/default/initial | 3 | no | 18 | 17 | 0 |
| M6 | iterative | c1/default/listener | 0 | yes | 1 | 1 | 0 |
| M6 | iterative | c1/default/listener | 1 | no | 10 | 9 | 0 |
| M6 | iterative | c1/default/send | 0 | yes | 1 | 1 | 0 |
| M6 | iterative | c1/default/send | 1 | no | 10 | 9 | 0 |
| ORIGINAL | dedup | c1/default/initial | 0 | yes | 1 | 1 | 0 |
| ORIGINAL | dedup | c1/default/initial | 1 | yes | 4 | 4 | 1 |
| ORIGINAL | dedup | c1/default/initial | 2 | yes | 12 | 12 | 4 |
| ORIGINAL | dedup | c1/default/initial | 3 | yes | 58 | 58 | 15 |
| ORIGINAL | dedup | c1/default/initial | 4 | yes | 445 | 445 | 82 |
| ORIGINAL | dedup | c1/default/initial | 5 | yes | 4083 | 4083 | 584 |
| ORIGINAL | dedup | c1/default/initial | 6 | no | 771 | 770 | 84 |
| ORIGINAL | dedup | c2/data/data | 0 | yes | 1 | 1 | 0 |
| ORIGINAL | dedup | c2/data/data | 1 | no | 2 | 2 | 0 |
| ORIGINAL | dedup | c2/data/initial | 0 | yes | 1 | 1 | 0 |
| ORIGINAL | dedup | c2/data/initial | 1 | yes | 4 | 4 | 1 |
| ORIGINAL | dedup | c2/data/initial | 2 | yes | 12 | 12 | 4 |
| ORIGINAL | dedup | c2/data/initial | 3 | yes | 58 | 58 | 15 |
| ORIGINAL | dedup | c2/data/initial | 4 | yes | 445 | 445 | 82 |
| ORIGINAL | dedup | c2/data/initial | 5 | yes | 4083 | 4083 | 584 |
| ORIGINAL | dedup | c2/data/initial | 6 | no | 771 | 770 | 86 |
| ORIGINAL | iterative | c1/default/initial | 0 | yes | 1 | 1 | 0 |
| ORIGINAL | iterative | c1/default/initial | 1 | yes | 4 | 4 | 0 |
| ORIGINAL | iterative | c1/default/initial | 2 | yes | 15 | 15 | 0 |
| ORIGINAL | iterative | c1/default/initial | 3 | yes | 85 | 85 | 0 |
| ORIGINAL | iterative | c1/default/initial | 4 | yes | 657 | 657 | 0 |
| ORIGINAL | iterative | c1/default/initial | 5 | no | 4865 | 4864 | 0 |
| ORIGINAL | iterative | c1/default/listener | 0 | yes | 1 | 1 | 0 |
| ORIGINAL | iterative | c1/default/listener | 1 | yes | 31 | 31 | 0 |
| ORIGINAL | iterative | c1/default/listener | 2 | yes | 679 | 679 | 0 |
| ORIGINAL | iterative | c1/default/listener | 3 | no | 393 | 392 | 0 |
| ORIGINAL | iterative | c1/default/send | 0 | yes | 1 | 1 | 0 |
| ORIGINAL | iterative | c1/default/send | 1 | yes | 31 | 31 | 0 |
| ORIGINAL | iterative | c1/default/send | 2 | yes | 819 | 819 | 0 |
| ORIGINAL | iterative | c1/default/send | 3 | no | 255 | 254 | 0 |
| ORIGINAL | iterative | c2/data/data | 0 | yes | 1 | 1 | 0 |
| ORIGINAL | iterative | c2/data/data | 1 | no | 2 | 2 | 0 |
| ORIGINAL | iterative | c2/data/initial | 0 | yes | 1 | 1 | 0 |
| ORIGINAL | iterative | c2/data/initial | 1 | yes | 4 | 4 | 0 |
| ORIGINAL | iterative | c2/data/initial | 2 | yes | 15 | 15 | 0 |
| ORIGINAL | iterative | c2/data/initial | 3 | yes | 85 | 85 | 0 |
| ORIGINAL | iterative | c2/data/initial | 4 | yes | 657 | 657 | 0 |
| ORIGINAL | iterative | c2/data/initial | 5 | no | 4865 | 4864 | 0 |

## Reachability and G2

Zero positive G2 is unexercised, not passing. States are visited endpoints including repeats, not distinct states. Baseline endpoint counts are not instrumented.

| Mutation | Mode | Profile/declaration/start | Seed | States | Prefixes | G1 | G2 | Positive | Positive with bytes | Refutations | Rejected candidates | Illegal residuals | Unqualified candidates | Cache clears |
|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| M1 | baseline | c1/default/initial | 1 | — | — | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M1 | baseline | c1/default/initial | 20261028 | — | — | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M1 | baseline | c1/default/initial | 314159265 | — | — | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M1 | dedup | c1/default/initial | 1 | 5373 | 5374 | 50000 | 0 | 0 | 0 | 0 | 49050 | 0 | 0 | 69 |
| M1 | iterative | c1/default/initial | 1 | 5626 | 5627 | 50003 | 0 | 0 | 0 | 0 | 82260 | 0 | 0 | 0 |
| M1 | iterative | c1/default/listener | 1 | 1 | 1 | 207 | 1 | 0 | 0 | 1 | 9 | 0 | 0 | 0 |
| M1 | iterative | c1/default/send | 1 | 1 | 1 | 7891 | 61 | 60 | 50 | 1 | 42 | 0 | 0 | 0 |
| M1 | random | c1/default/initial | 1 | 18 | 0 | 6661 | 61 | 60 | 0 | 1 | 132 | 0 | 0 | 0 |
| M1 | random | c1/default/initial | 20261028 | 30 | 0 | 9244 | 61 | 60 | 50 | 1 | 447 | 0 | 0 | 0 |
| M1 | random | c1/default/initial | 314159265 | 156 | 0 | 432 | 1 | 0 | 0 | 1 | 1854 | 0 | 0 | 0 |
| M2 | baseline | c1/default/initial | 1 | — | — | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M2 | baseline | c1/default/initial | 20261028 | — | — | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M2 | baseline | c1/default/initial | 314159265 | — | — | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M2 | dedup | c1/default/initial | 1 | 5373 | 5374 | 50000 | 0 | 0 | 0 | 0 | 49050 | 0 | 0 | 69 |
| M2 | dedup | c2/data/data | 1 | 3 | 3 | 50004 | 244 | 244 | 226 | 0 | 745 | 0 | 0 | 0 |
| M2 | dedup | c2/data/initial | 1 | 5373 | 5374 | 50000 | 0 | 0 | 0 | 0 | 49275 | 0 | 0 | 69 |
| M2 | iterative | c1/default/initial | 1 | 5626 | 5627 | 50003 | 0 | 0 | 0 | 0 | 82260 | 0 | 0 | 0 |
| M2 | iterative | c1/default/listener | 1 | 1103 | 1104 | 50002 | 0 | 0 | 0 | 0 | 65120 | 0 | 0 | 0 |
| M2 | iterative | c1/default/send | 1 | 1105 | 1106 | 50001 | 0 | 0 | 0 | 0 | 118890 | 0 | 0 | 0 |
| M2 | iterative | c2/data/data | 1 | 3 | 3 | 50004 | 244 | 244 | 226 | 0 | 745 | 0 | 0 | 0 |
| M2 | iterative | c2/data/initial | 1 | 5626 | 5627 | 50003 | 0 | 0 | 0 | 0 | 82260 | 0 | 0 | 0 |
| M2 | random | c1/default/initial | 1 | 5633 | 0 | 9670 | 0 | 0 | 0 | 0 | 73305 | 0 | 13 | 0 |
| M2 | random | c1/default/initial | 20261028 | 1795 | 0 | 3015 | 0 | 0 | 0 | 0 | 24965 | 0 | 7 | 0 |
| M2 | random | c1/default/initial | 314159265 | 2444 | 0 | 4372 | 0 | 0 | 0 | 0 | 32685 | 0 | 4 | 0 |
| M2 | random | c2/data/data | 1 | 3 | 0 | 50003 | 245 | 245 | 226 | 0 | 745 | 0 | 0 | 0 |
| M2 | random | c2/data/data | 20261028 | 3 | 0 | 50000 | 241 | 241 | 223 | 0 | 705 | 0 | 0 | 0 |
| M2 | random | c2/data/data | 314159265 | 3 | 0 | 50001 | 245 | 245 | 227 | 0 | 745 | 0 | 0 | 0 |
| M2 | random | c2/data/initial | 1 | 705 | 0 | 1238 | 0 | 0 | 0 | 0 | 13490 | 0 | 1 | 0 |
| M2 | random | c2/data/initial | 20261028 | 2521 | 0 | 48959 | 101 | 101 | 101 | 0 | 37156 | 0 | 8 | 0 |
| M2 | random | c2/data/initial | 314159265 | 147 | 0 | 49868 | 168 | 168 | 138 | 0 | 1977 | 0 | 1 | 0 |
| M3 | baseline | c1/default/initial | 1 | — | — | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M3 | baseline | c1/default/initial | 20261028 | — | — | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M3 | baseline | c1/default/initial | 314159265 | — | — | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M3 | dedup | c1/default/initial | 1 | 173 | 174 | 1326 | 0 | 0 | 0 | 0 | 1935 | 0 | 0 | 1 |
| M3 | iterative | c1/default/initial | 1 | 207 | 208 | 1525 | 0 | 0 | 0 | 0 | 3150 | 0 | 0 | 0 |
| M3 | iterative | c1/default/listener | 1 | 0 | 1 | 10 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M3 | iterative | c1/default/send | 1 | 0 | 1 | 10 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M3 | random | c1/default/initial | 1 | 7 | 0 | 9 | 0 | 0 | 0 | 0 | 45 | 0 | 0 | 0 |
| M3 | random | c1/default/initial | 20261028 | 4 | 0 | 9 | 0 | 0 | 0 | 0 | 45 | 0 | 0 | 0 |
| M3 | random | c1/default/initial | 314159265 | 10 | 0 | 10 | 0 | 0 | 0 | 0 | 45 | 0 | 0 | 0 |
| M4 | baseline | c1/default/initial | 1 | — | — | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M4 | baseline | c1/default/initial | 20261028 | — | — | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M4 | baseline | c1/default/initial | 314159265 | — | — | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M4 | dedup | c1/default/initial | 1 | 5373 | 5374 | 50000 | 0 | 0 | 0 | 0 | 49050 | 0 | 0 | 69 |
| M4 | dedup | c2/data/data | 1 | 3 | 3 | 50004 | 244 | 244 | 226 | 0 | 745 | 0 | 0 | 0 |
| M4 | dedup | c2/data/initial | 1 | 5373 | 5374 | 50000 | 0 | 0 | 0 | 0 | 49275 | 0 | 0 | 69 |
| M4 | iterative | c1/default/initial | 1 | 5626 | 5627 | 50003 | 0 | 0 | 0 | 0 | 82260 | 0 | 0 | 0 |
| M4 | iterative | c1/default/listener | 1 | 1103 | 1104 | 50002 | 0 | 0 | 0 | 0 | 65120 | 0 | 0 | 0 |
| M4 | iterative | c1/default/send | 1 | 1105 | 1106 | 50001 | 0 | 0 | 0 | 0 | 118890 | 0 | 0 | 0 |
| M4 | iterative | c2/data/data | 1 | 3 | 3 | 50004 | 244 | 244 | 226 | 0 | 745 | 0 | 0 | 0 |
| M4 | iterative | c2/data/initial | 1 | 5626 | 5627 | 50003 | 0 | 0 | 0 | 0 | 82260 | 0 | 0 | 0 |
| M4 | random | c1/default/initial | 1 | 13575 | 0 | 23810 | 0 | 0 | 0 | 0 | 176635 | 0 | 9 | 0 |
| M4 | random | c1/default/initial | 20261028 | 2575 | 0 | 4462 | 0 | 0 | 0 | 0 | 35935 | 0 | 1 | 0 |
| M4 | random | c1/default/initial | 314159265 | 4547 | 0 | 8052 | 0 | 0 | 0 | 0 | 61395 | 0 | 1 | 0 |
| M4 | random | c2/data/data | 1 | 3 | 0 | 50003 | 245 | 245 | 226 | 0 | 745 | 0 | 0 | 0 |
| M4 | random | c2/data/data | 20261028 | 3 | 0 | 50000 | 241 | 241 | 223 | 0 | 705 | 0 | 0 | 0 |
| M4 | random | c2/data/data | 314159265 | 3 | 0 | 50000 | 241 | 241 | 223 | 0 | 745 | 0 | 0 | 0 |
| M4 | random | c2/data/initial | 1 | 1391 | 0 | 21009 | 100 | 100 | 70 | 0 | 21870 | 0 | 0 | 0 |
| M4 | random | c2/data/initial | 20261028 | 2913 | 0 | 50001 | 137 | 137 | 137 | 0 | 39840 | 0 | 0 | 0 |
| M4 | random | c2/data/initial | 314159265 | 1942 | 0 | 49841 | 112 | 112 | 100 | 0 | 31052 | 0 | 1 | 0 |
| M5 | baseline | c1/default/initial | 1 | — | — | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M5 | baseline | c1/default/initial | 20261028 | — | — | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M5 | baseline | c1/default/initial | 314159265 | — | — | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M5 | dedup | c1/default/initial | 1 | 2 | 3 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M5 | iterative | c1/default/initial | 1 | 2 | 3 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M5 | iterative | c1/default/listener | 1 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M5 | iterative | c1/default/send | 1 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M5 | random | c1/default/initial | 1 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M5 | random | c1/default/initial | 20261028 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M5 | random | c1/default/initial | 314159265 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M6 | baseline | c1/default/initial | 1 | — | — | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M6 | baseline | c1/default/initial | 20261028 | — | — | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M6 | baseline | c1/default/initial | 314159265 | — | — | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| M6 | dedup | c1/default/initial | 1 | 34 | 35 | 207 | 0 | 0 | 0 | 0 | 315 | 0 | 0 | 0 |
| M6 | iterative | c1/default/initial | 1 | 37 | 38 | 215 | 0 | 0 | 0 | 0 | 360 | 0 | 0 | 0 |
| M6 | iterative | c1/default/listener | 1 | 10 | 11 | 495 | 0 | 0 | 0 | 0 | 1030 | 0 | 0 | 0 |
| M6 | iterative | c1/default/send | 1 | 10 | 11 | 495 | 0 | 0 | 0 | 0 | 1900 | 0 | 0 | 0 |
| M6 | random | c1/default/initial | 1 | 19 | 0 | 35 | 0 | 0 | 0 | 0 | 325 | 0 | 0 | 0 |
| M6 | random | c1/default/initial | 20261028 | 24 | 0 | 55 | 0 | 0 | 0 | 0 | 180 | 0 | 0 | 0 |
| M6 | random | c1/default/initial | 314159265 | 13 | 0 | 27 | 0 | 0 | 0 | 0 | 90 | 0 | 0 | 0 |
| ORIGINAL | baseline | c1/default/initial | 1 | — | — | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| ORIGINAL | baseline | c1/default/initial | 20261028 | — | — | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| ORIGINAL | baseline | c1/default/initial | 314159265 | — | — | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| ORIGINAL | dedup | c1/default/initial | 1 | 5373 | 5374 | 50000 | 0 | 0 | 0 | 0 | 49050 | 0 | 0 | 69 |
| ORIGINAL | dedup | c2/data/data | 1 | 3 | 3 | 50004 | 244 | 244 | 226 | 0 | 745 | 0 | 0 | 0 |
| ORIGINAL | dedup | c2/data/initial | 1 | 5373 | 5374 | 50000 | 0 | 0 | 0 | 0 | 49275 | 0 | 0 | 69 |
| ORIGINAL | iterative | c1/default/initial | 1 | 5626 | 5627 | 50003 | 0 | 0 | 0 | 0 | 82260 | 0 | 0 | 0 |
| ORIGINAL | iterative | c1/default/listener | 1 | 1103 | 1104 | 50002 | 0 | 0 | 0 | 0 | 65120 | 0 | 0 | 0 |
| ORIGINAL | iterative | c1/default/send | 1 | 1105 | 1106 | 50001 | 0 | 0 | 0 | 0 | 118890 | 0 | 0 | 0 |
| ORIGINAL | iterative | c2/data/data | 1 | 3 | 3 | 50004 | 244 | 244 | 226 | 0 | 745 | 0 | 0 | 0 |
| ORIGINAL | iterative | c2/data/initial | 1 | 5626 | 5627 | 50003 | 0 | 0 | 0 | 0 | 82260 | 0 | 0 | 0 |
| ORIGINAL | random | c1/default/initial | 1 | 28366 | 0 | 50000 | 0 | 0 | 0 | 0 | 369650 | 0 | 0 | 0 |
| ORIGINAL | random | c1/default/initial | 20261028 | 28408 | 0 | 50002 | 0 | 0 | 0 | 0 | 378880 | 0 | 0 | 0 |
| ORIGINAL | random | c1/default/initial | 314159265 | 28075 | 0 | 50000 | 0 | 0 | 0 | 0 | 371680 | 0 | 0 | 0 |
| ORIGINAL | random | c2/data/data | 1 | 3 | 0 | 50003 | 245 | 245 | 226 | 0 | 745 | 0 | 0 | 0 |
| ORIGINAL | random | c2/data/data | 20261028 | 3 | 0 | 50000 | 241 | 241 | 223 | 0 | 705 | 0 | 0 | 0 |
| ORIGINAL | random | c2/data/data | 314159265 | 3 | 0 | 50000 | 241 | 241 | 223 | 0 | 745 | 0 | 0 | 0 |
| ORIGINAL | random | c2/data/initial | 1 | 1416 | 0 | 50001 | 156 | 156 | 126 | 0 | 22224 | 0 | 0 | 0 |
| ORIGINAL | random | c2/data/initial | 20261028 | 2913 | 0 | 50000 | 137 | 137 | 137 | 0 | 39885 | 0 | 0 | 0 |
| ORIGINAL | random | c2/data/initial | 314159265 | 2952 | 0 | 50003 | 84 | 84 | 84 | 0 | 44485 | 0 | 0 | 0 |

## ORIGINAL baseline controls, by actual trial seed

Completed known failures do not stop the campaign. A partial control authorizes comparison only through its recorded checked boundary.

| Campaign seed | Actual trial seed | Completed | First failure signature | Last fully checked boundary |
|---:|---:|---|---|---:|
| 1 | 1 | True | [':BASELINE-LIVENESS', 5178] | 5178 |
| 1 | 1015568748 | True | [':BASELINE-LIVENESS', 5171] | 5171 |
| 1 | 1586005467 | False | None | 9 |
| 20261028 | 20261028 | True | [':BASELINE-LIVENESS', 5190] | 5190 |
| 20261028 | 1918327731 | True | [':BASELINE-LIVENESS', 4731] | 4731 |
| 20261028 | 3454201206 | False | None | 444 |
| 314159265 | 314159265 | True | [':BASELINE-LIVENESS', 5152] | 5152 |
| 314159265 | 1811288460 | True | [':BASELINE-LIVENESS', 4875] | 4875 |
| 314159265 | 2039979899 | False | None | 325 |

Records named here are regenerable and git-ignored; `E1-RESULTS.md` ("Raw records") gives the commands.
