# /tank/fn/scratch/qual-c3420013/campaign/pk-run.json

stores 2 (closed and swept: [0, 1])

seed 3; 90 iterations (80 single, 10 concurrent); 206 POSTs in the ledger; 178 final articles present; 92 owner pids, all gone: True

calibration medians (ms from terminator sent): {"tiny": {".allocation-gone": 22.8, ".allocation-seen": 1.8, ".stage-gone": 96.9, ".stage-seen": 48.4, "frontier": 22.8, "reply": 182.1, "stage": 1.8, "stage_cleared": 22.8, "txn": 72.8}, "small": {".allocation-gone": 24.1, ".allocation-seen": 4.6, ".stage-gone": 105.0, ".stage-seen": 57.1, "frontier": 24.1, "reply": 182.3, "stage": 4.6, "stage_cleared": 24.1, "txn": 79.6}, "medium": {".allocation-gone": 43.0, ".allocation-seen": 24.0, ".stage-gone": 151.6, ".stage-seen": 78.7, "frontier": 43.0, "reply": 225.3, "stage": 24.0, "stage_cleared": 43.0, "txn": 109.5}, "large": {".allocation-gone": 83.2, ".allocation-seen": 64.0, ".stage-gone": 189.7, ".stage-seen": 133.8, "frontier": 83.2, "reply": 285.5, "stage": 64.0, "stage_cleared": 83.2, "txn": 164.8}, "over": {"reply": 14.4}}

## Verdicts

- 240-identical: 102
- died-absent: 48
- died-present-identical: 33
- refused: 23
- torn: 0
- lost-240: 0
- reused-number: 0

## Verdicts of the killed POSTs only

| kill kind | verdict | POSTs |
|---|---|---|
| concurrent | 240-identical | 4 |
| concurrent | died-absent | 12 |
| concurrent | died-present-identical | 4 |
| single | 240-identical | 14 |
| single | died-absent | 36 |
| single | died-present-identical | 29 |
| single | refused | 1 |

## Client exit codes by reply

- rc 0: ['240 article received OK']
- rc 1: ['441 posting failed; the article was not received', '441 posting failed; this article is already stored here']
- rc 3: ['<no reply>']

## Kill band against the store state at death

| band | store state at death | kills |
|---|---|---|
| early | frontier-advanced | 7 |
| early | staged,.allocation- | 7 |
| early | staged,.stage- | 3 |
| early | untouched | 4 |
| late | linked(1),.stage- | 2 |
| late | linked(1),no-stage | 13 |
| late | linked(2),.stage- | 1 |
| mid-article | untouched | 8 |
| over-limit | untouched | 6 |
| window | frontier-advanced | 1 |
| window | linked(1),.stage- | 14 |
| window | linked(1),no-stage | 20 |
| window | staged,.stage- | 4 |

## Kill instants against the phase reached

| store state at death | owner log at death | kills | killed at ms (min to max) |
|---|---|---|---|
| untouched | not logged; not logged | 2 | 0.3 to 4.8 |
| untouched | not logged | 16 | 1.9 to 58.9 |
| staged,.allocation- | not logged | 7 | 10.5 to 92.8 |
| frontier-advanced | not logged | 8 | 19.8 to 143.0 |
| staged,.stage- | not logged | 6 | 39.7 to 143.6 |
| linked(1),.stage- | not logged | 15 | 69.9 to 278.8 |
| linked(1),no-stage | not logged | 14 | 102.6 to 402.1 |
| linked(1),no-stage | accepted post logged | 14 | 139.7 to 296.3 |
| staged,.stage- | not logged; not logged | 1 | 142.7 to 142.7 |
| linked(1),no-stage | not logged; accepted post logged | 2 | 175.1 to 207.1 |
| linked(1),no-stage | not logged; not logged | 3 | 196.9 to 249.5 |
| linked(1),.stage- | not logged; accepted post logged | 1 | 277.4 to 277.4 |
| linked(2),.stage- | not logged; accepted post logged | 1 | 351.7 to 351.7 |

## Per kill

| # | store | kind | band | sizes | scheduled ms | killed at ms | replies (rc) | store at death | owner log at death | verdict |
|---|---|---|---|---|---|---|---|---|---|---|
| 0 | 0 | single | late | small | 255.4 | 255.4 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 1 | 0 | single | window | small | 173.5 | 173.5 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 2 | 0 | single | over-limit | over | 26.5 | 26.5 | none (3) | untouched | not logged | died-absent |
| 3 | 0 | single | window | large | 189.2 | 189.2 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 4 | 0 | single | early | tiny | 10.4 | 10.5 | none (3) | staged,.allocation- | not logged | died-absent |
| 5 | 0 | single | late | small | 189.8 | 189.8 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 6 | 0 | single | over-limit | over | 6.8 | 6.8 | none (3) | untouched | not logged | died-absent |
| 7 | 0 | single | early | tiny | 54.0 | 54.0 | none (3) | staged,.stage- | not logged | died-absent |
| 8 | 0 | single | window | tiny | 150.9 | 150.9 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 9 | 0 | single | early | small | 62.2 | 62.2 | none (3) | staged,.stage- | not logged | died-absent |
| 10 | 0 | single | late | medium | 230.2 | 230.2 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 11 | 0 | single | early | small | 62.9 | 62.9 | none (3) | staged,.allocation- | not logged | died-absent |
| 12 | 0 | single | mid-article | medium | 3.7 | 3.7 | none (3) | untouched | not logged | died-absent |
| 13 | 0 | single | window | tiny | 69.8 | 69.9 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 14 | 0 | single | window | large | 228.8 | 228.8 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 15 | 0 | single | window | medium | 170.0 | 170.0 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 16 | 0 | concurrent | early | small,small | 0.3 | 0.3 | none (3) / none (3) | untouched | not logged; not logged | died-absent, died-absent |
| 17 | 0 | single | late | large | 402.1 | 402.1 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 18 | 0 | concurrent | window | large,medium | 221.0 | 221.0 | none (3) / none (3) | linked(1),no-stage | not logged; not logged | died-present-identical, died-absent |
| 19 | 0 | single | window | tiny | 70.8 | 70.8 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 20 | 0 | concurrent | window | large,medium | 207.1 | 207.1 | none (3) / 240 article received OK (0) | linked(1),no-stage | not logged; accepted post logged | died-absent, 240-identical |
| 21 | 0 | single | mid-article | medium | 3.7 | 3.7 | none (3) | untouched | not logged | died-absent |
| 22 | 0 | single | late | medium | 271.3 | 271.3 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 23 | 0 | single | window | tiny | 168.0 | 168.0 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 24 | 0 | single | window | medium | 118.8 | 118.8 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 25 | 0 | single | mid-article | medium | 13.5 | 13.5 | none (3) | untouched | not logged | died-absent |
| 26 | 0 | single | window | medium | 223.7 | 223.7 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 27 | 0 | single | window | tiny | 182.7 | 182.7 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 28 | 0 | single | over-limit | over | 7.6 | 7.6 | none (3) | untouched | not logged | died-absent |
| 29 | 0 | concurrent | window | large,tiny | 277.4 | 277.4 | none (3) / 240 article received OK (0) | linked(1),.stage- | not logged; accepted post logged | died-absent, 240-identical |
| 30 | 0 | single | window | large | 230.2 | 230.2 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 31 | 0 | single | window | small | 73.9 | 73.9 | none (3) | frontier-advanced | not logged | died-absent |
| 32 | 0 | single | window | medium | 139.3 | 139.3 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 33 | 0 | single | window | large | 178.7 | 178.7 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 34 | 0 | concurrent | window | tiny,medium | 175.1 | 175.1 | none (3) / 240 article received OK (0) | linked(1),no-stage | not logged; accepted post logged | died-absent, 240-identical |
| 35 | 0 | single | window | tiny | 78.5 | 78.5 | none (3) | staged,.stage- | not logged | died-absent |
| 36 | 0 | single | window | small | 151.0 | 151.0 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 37 | 0 | single | over-limit | over | 10.1 | 10.1 | none (3) | untouched | not logged | died-absent |
| 38 | 0 | single | window | large | 160.7 | 160.7 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 39 | 0 | single | window | tiny | 102.6 | 102.6 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 40 | 0 | single | late | tiny | 229.3 | 229.3 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 41 | 0 | single | window | large | 201.1 | 201.1 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 42 | 0 | single | late | medium | 284.4 | 284.4 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 43 | 0 | concurrent | window | medium,large | 196.9 | 196.9 | none (3) / none (3) | linked(1),no-stage | not logged; not logged | died-present-identical, died-absent |
| 44 | 0 | concurrent | late | small,tiny | 249.5 | 249.5 | none (3) / none (3) | linked(1),no-stage | not logged; not logged | died-present-identical, died-absent |
| 45 | 0 | single | window | medium | 164.1 | 164.1 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 46 | 0 | concurrent | early | large,small | 4.8 | 4.8 | none (3) / none (3) | untouched | not logged; not logged | died-absent, died-absent |
| 47 | 0 | single | early | small | 42.4 | 42.4 | none (3) | frontier-advanced | not logged | died-absent |
| 48 | 0 | single | early | small | 16.6 | 16.6 | none (3) | staged,.allocation- | not logged | died-absent |
| 49 | 0 | single | early | large | 143.0 | 143.0 | none (3) | frontier-advanced | not logged | died-absent |
| 50 | 0 | single | late | tiny | 257.2 | 257.2 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 51 | 0 | single | over-limit | over | 4.8 | 4.8 | none (3) | untouched | not logged | died-absent |
| 52 | 0 | single | early | large | 109.9 | 109.9 | none (3) | frontier-advanced | not logged | died-absent |
| 53 | 0 | single | late | tiny | 244.2 | 244.2 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 54 | 1 | single | mid-article | small | 4.5 | 4.5 | none (3) | untouched | not logged | died-absent |
| 55 | 1 | single | window | tiny | 114.6 | 114.6 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 56 | 1 | single | early | large | 58.9 | 58.9 | none (3) | untouched | not logged | died-absent |
| 57 | 1 | single | early | tiny | 19.7 | 19.8 | none (3) | frontier-advanced | not logged | died-absent |
| 58 | 1 | single | mid-article | large | 1.9 | 1.9 | none (3) | untouched | not logged | died-absent |
| 59 | 1 | single | window | medium | 153.2 | 153.2 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 60 | 1 | single | early | tiny | 39.7 | 39.7 | none (3) | staged,.stage- | not logged | died-absent |
| 61 | 1 | single | window | large | 238.6 | 238.6 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 62 | 1 | single | window | tiny | 139.7 | 139.7 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 63 | 1 | single | over-limit | over | 21.2 | 21.2 | 441 posting failed; the arti (1) | untouched | not logged | refused |
| 64 | 1 | single | window | tiny | 123.2 | 123.2 | none (3) | staged,.stage- | not logged | died-absent |
| 65 | 1 | single | early | large | 58.6 | 58.6 | none (3) | staged,.allocation- | not logged | died-absent |
| 66 | 1 | single | window | tiny | 179.0 | 179.0 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 67 | 1 | single | early | medium | 46.6 | 46.6 | none (3) | staged,.allocation- | not logged | died-absent |
| 68 | 1 | concurrent | window | small,medium | 142.7 | 142.7 | none (3) / none (3) | staged,.stage- | not logged; not logged | died-absent, died-absent |
| 69 | 1 | single | late | medium | 268.0 | 268.0 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 70 | 1 | single | mid-article | large | 16.3 | 16.3 | none (3) | untouched | not logged | died-absent |
| 71 | 1 | single | mid-article | medium | 5.3 | 5.3 | none (3) | untouched | not logged | died-absent |
| 72 | 1 | single | early | large | 92.8 | 92.8 | none (3) | staged,.allocation- | not logged | died-absent |
| 73 | 1 | single | window | small | 143.6 | 143.6 | none (3) | staged,.stage- | not logged | died-absent |
| 74 | 1 | single | window | tiny | 110.7 | 110.7 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 75 | 1 | single | late | medium | 286.2 | 286.2 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 76 | 1 | single | window | large | 257.5 | 257.5 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 77 | 1 | concurrent | late | large,medium | 351.7 | 351.7 | none (3) / 240 article received OK (0) | linked(2),.stage- | not logged; accepted post logged | died-present-identical, 240-identical |
| 78 | 1 | single | late | medium | 296.3 | 296.3 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 79 | 1 | single | early | small | 26.5 | 26.5 | none (3) | frontier-advanced | not logged | died-absent |
| 80 | 1 | single | early | large | 80.2 | 80.2 | none (3) | frontier-advanced | not logged | died-absent |
| 81 | 1 | single | mid-article | small | 17.1 | 17.1 | none (3) | untouched | not logged | died-absent |
| 82 | 1 | single | late | medium | 278.8 | 278.8 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 83 | 1 | single | window | medium | 187.1 | 187.1 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 84 | 1 | single | late | medium | 282.9 | 282.9 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 85 | 1 | single | early | large | 38.5 | 38.5 | none (3) | untouched | not logged | died-absent |
| 86 | 1 | single | early | small | 13.7 | 13.7 | none (3) | staged,.allocation- | not logged | died-absent |
| 87 | 1 | single | window | medium | 135.5 | 135.5 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 88 | 1 | single | early | large | 105.9 | 105.9 | none (3) | frontier-advanced | not logged | died-absent |
| 89 | 1 | single | window | large | 256.1 | 256.1 | none (3) | linked(1),.stage- | not logged | died-present-identical |

## Failures: 0


judge rc=0
