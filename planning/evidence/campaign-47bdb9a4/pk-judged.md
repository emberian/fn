# /tank/fn/scratch/campaign-47bdb9a4/pk-run.json

stores 2 (closed and swept: [0, 1])

seed 3; 90 iterations (80 single, 10 concurrent); 206 POSTs in the ledger; 178 final articles present; 92 owner pids, all gone: True

calibration medians (ms from terminator sent): {"tiny": {".allocation-gone": 17.3, ".allocation-seen": 1.7, ".stage-gone": 42.5, ".stage-seen": 26.8, "frontier": 17.3, "reply": 67.1, "stage": 1.7, "stage_cleared": 17.3, "txn": 34.0}, "small": {".allocation-gone": 25.3, ".allocation-seen": 6.7, ".stage-gone": 66.9, ".stage-seen": 43.1, "frontier": 25.3, "reply": 83.9, "stage": 6.7, "stage_cleared": 25.3, "txn": 58.6}, "medium": {".allocation-gone": 41.0, ".allocation-seen": 23.0, ".stage-gone": 103.9, ".stage-seen": 70.7, "frontier": 41.0, "reply": 121.3, "stage": 23.0, "stage_cleared": 41.0, "txn": 93.0}, "large": {".allocation-gone": 74.4, ".allocation-seen": 58.4, ".stage-gone": 136.8, ".stage-seen": 107.3, "frontier": 74.4, "reply": 189.4, "stage": 58.4, "stage_cleared": 74.4, "txn": 126.1}, "over": {"reply": 18.1}}

## Verdicts

- 240-identical: 87
- died-absent: 61
- died-present-identical: 35
- refused: 23
- torn: 0
- lost-240: 0
- reused-number: 0

## Verdicts of the killed POSTs only

| kill kind | verdict | POSTs |
|---|---|---|
| concurrent | 240-identical | 2 |
| concurrent | died-absent | 12 |
| concurrent | died-present-identical | 6 |
| single | 240-identical | 1 |
| single | died-absent | 49 |
| single | died-present-identical | 29 |
| single | refused | 1 |

## Client exit codes by reply

- rc 0: ['240 article received OK']
- rc 1: ['441 posting failed; a different article with this Message-ID', '441 posting failed; the article was not received']
- rc 3: ['<no reply>']

## Kill band against the store state at death

| band | store state at death | kills |
|---|---|---|
| early | frontier-advanced | 2 |
| early | linked(1),no-stage | 2 |
| early | staged,.allocation- | 10 |
| early | staged,.stage- | 2 |
| early | untouched | 5 |
| late | frontier-advanced | 1 |
| late | linked(1),no-stage | 14 |
| late | staged,.stage- | 1 |
| mid-article | untouched | 8 |
| over-limit | untouched | 6 |
| window | frontier-advanced | 9 |
| window | linked(1),.stage- | 7 |
| window | linked(1),no-stage | 15 |
| window | staged,.stage- | 8 |

## Kill instants against the phase reached

| store state at death | owner log at death | kills | killed at ms (min to max) |
|---|---|---|---|
| untouched | not logged; not logged | 2 | 0.2 to 3.7 |
| untouched | not logged | 17 | 1.9 to 45.1 |
| staged,.allocation- | not logged | 10 | 4.9 to 71.0 |
| staged,.stage- | not logged | 11 | 25.2 to 164.3 |
| frontier-advanced | not logged | 12 | 32.1 to 174.2 |
| linked(1),.stage- | not logged | 6 | 34.9 to 143.2 |
| linked(1),no-stage | not logged | 23 | 45.8 to 268.5 |
| linked(1),.stage- | not logged; not logged | 1 | 97.5 to 97.5 |
| linked(1),no-stage | not logged; not logged | 5 | 107.7 to 154.4 |
| linked(1),no-stage | accepted post logged | 1 | 120.3 to 120.3 |
| linked(1),no-stage | not logged; accepted post logged | 2 | 186.2 to 234.7 |

## Per kill

| # | store | kind | band | sizes | scheduled ms | killed at ms | replies (rc) | store at death | owner log at death | verdict |
|---|---|---|---|---|---|---|---|---|---|---|
| 0 | 0 | single | late | small | 120.3 | 120.3 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 1 | 0 | single | window | small | 83.4 | 83.4 | none (3) | frontier-advanced | not logged | died-absent |
| 2 | 0 | single | over-limit | over | 26.5 | 26.5 | none (3) | untouched | not logged | died-absent |
| 3 | 0 | single | window | large | 136.5 | 136.5 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 4 | 0 | single | early | tiny | 4.9 | 4.9 | none (3) | staged,.allocation- | not logged | died-absent |
| 5 | 0 | single | late | small | 89.1 | 89.1 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 6 | 0 | single | over-limit | over | 6.8 | 6.8 | none (3) | untouched | not logged | died-absent |
| 7 | 0 | single | early | tiny | 25.2 | 25.2 | none (3) | staged,.stage- | not logged | died-absent |
| 8 | 0 | single | window | tiny | 58.8 | 58.8 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 9 | 0 | single | early | small | 45.8 | 45.8 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 10 | 0 | single | late | medium | 125.4 | 125.4 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 11 | 0 | single | early | small | 46.3 | 46.3 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 12 | 0 | single | mid-article | medium | 3.7 | 3.7 | none (3) | untouched | not logged | died-absent |
| 13 | 0 | single | window | tiny | 32.1 | 32.1 | none (3) | frontier-advanced | not logged | died-absent |
| 14 | 0 | single | window | large | 158.8 | 158.8 | none (3) | staged,.stage- | not logged | died-absent |
| 15 | 0 | single | window | medium | 106.1 | 106.1 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 16 | 0 | concurrent | early | small,small | 0.2 | 0.2 | none (3) / none (3) | untouched | not logged; not logged | died-absent, died-absent |
| 17 | 0 | single | late | large | 268.5 | 268.5 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 18 | 0 | concurrent | window | large,medium | 154.4 | 154.4 | none (3) / none (3) | linked(1),no-stage | not logged; not logged | died-absent, died-present-identical |
| 19 | 0 | single | window | tiny | 32.4 | 32.4 | none (3) | frontier-advanced | not logged | died-absent |
| 20 | 0 | concurrent | window | large,medium | 146.6 | 146.6 | none (3) / none (3) | linked(1),no-stage | not logged; not logged | died-present-identical, died-absent |
| 21 | 0 | single | mid-article | medium | 3.7 | 3.7 | none (3) | untouched | not logged | died-absent |
| 22 | 0 | single | late | medium | 147.9 | 147.9 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 23 | 0 | single | window | tiny | 64.5 | 64.5 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 24 | 0 | single | window | medium | 90.0 | 90.0 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 25 | 0 | single | mid-article | medium | 13.5 | 13.5 | none (3) | untouched | not logged | died-absent |
| 26 | 0 | single | window | medium | 122.9 | 122.9 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 27 | 0 | single | window | tiny | 69.3 | 69.3 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 28 | 0 | single | over-limit | over | 7.6 | 7.6 | none (3) | untouched | not logged | died-absent |
| 29 | 0 | concurrent | window | large,tiny | 186.2 | 186.2 | none (3) / 240 article received OK (0) | linked(1),no-stage | not logged; accepted post logged | died-absent, 240-identical |
| 30 | 0 | single | window | large | 159.6 | 159.6 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 31 | 0 | single | window | small | 53.4 | 53.4 | none (3) | staged,.stage- | not logged | died-absent |
| 32 | 0 | single | window | medium | 96.4 | 96.4 | none (3) | frontier-advanced | not logged | died-absent |
| 33 | 0 | single | window | large | 130.6 | 130.6 | none (3) | staged,.stage- | not logged | died-absent |
| 34 | 0 | concurrent | window | tiny,medium | 107.7 | 107.7 | none (3) / none (3) | linked(1),no-stage | not logged; not logged | died-present-identical, died-absent |
| 35 | 0 | single | window | tiny | 34.9 | 34.9 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 36 | 0 | single | window | small | 76.6 | 76.6 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 37 | 0 | single | over-limit | over | 10.1 | 10.1 | none (3) | untouched | not logged | died-absent |
| 38 | 0 | single | window | large | 120.5 | 120.5 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 39 | 0 | single | window | tiny | 42.9 | 42.9 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 40 | 0 | single | late | tiny | 87.1 | 87.1 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 41 | 0 | single | window | large | 143.2 | 143.2 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 42 | 0 | single | late | medium | 155.1 | 155.1 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 43 | 0 | concurrent | window | medium,large | 140.8 | 140.8 | none (3) / none (3) | linked(1),no-stage | not logged; not logged | died-present-identical, died-absent |
| 44 | 0 | concurrent | late | small,tiny | 117.5 | 117.5 | none (3) / none (3) | linked(1),no-stage | not logged; not logged | died-present-identical, died-absent |
| 45 | 0 | single | window | medium | 104.2 | 104.2 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 46 | 0 | concurrent | early | large,small | 3.7 | 3.7 | none (3) / none (3) | untouched | not logged; not logged | died-absent, died-absent |
| 47 | 0 | single | early | small | 31.2 | 31.2 | none (3) | staged,.allocation- | not logged | died-absent |
| 48 | 0 | single | early | small | 12.2 | 12.2 | none (3) | staged,.allocation- | not logged | died-absent |
| 49 | 0 | single | early | large | 109.4 | 109.4 | none (3) | staged,.stage- | not logged | died-absent |
| 50 | 0 | single | late | tiny | 97.9 | 97.9 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 51 | 0 | single | over-limit | over | 4.8 | 4.8 | none (3) | untouched | not logged | died-absent |
| 52 | 0 | single | early | large | 84.1 | 84.1 | none (3) | frontier-advanced | not logged | died-absent |
| 53 | 0 | single | late | tiny | 92.9 | 92.9 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 54 | 1 | single | mid-article | small | 4.5 | 4.5 | none (3) | untouched | not logged | died-absent |
| 55 | 1 | single | window | tiny | 46.9 | 46.9 | none (3) | frontier-advanced | not logged | died-absent |
| 56 | 1 | single | early | large | 45.1 | 45.1 | none (3) | untouched | not logged | died-absent |
| 57 | 1 | single | early | tiny | 9.2 | 9.2 | none (3) | staged,.allocation- | not logged | died-absent |
| 58 | 1 | single | mid-article | large | 1.9 | 1.9 | none (3) | untouched | not logged | died-absent |
| 59 | 1 | single | window | medium | 100.8 | 100.8 | none (3) | staged,.stage- | not logged | died-absent |
| 60 | 1 | single | early | tiny | 18.6 | 18.6 | none (3) | staged,.allocation- | not logged | died-absent |
| 61 | 1 | single | window | large | 164.3 | 164.3 | none (3) | staged,.stage- | not logged | died-absent |
| 62 | 1 | single | window | tiny | 55.1 | 55.1 | none (3) | staged,.stage- | not logged | died-absent |
| 63 | 1 | single | over-limit | over | 21.2 | 21.2 | 441 posting failed; the arti (1) | untouched | not logged | refused |
| 64 | 1 | single | window | tiny | 49.7 | 49.7 | none (3) | frontier-advanced | not logged | died-absent |
| 65 | 1 | single | early | large | 44.8 | 44.8 | none (3) | untouched | not logged | died-absent |
| 66 | 1 | single | window | tiny | 68.1 | 68.1 | none (3) | frontier-advanced | not logged | died-absent |
| 67 | 1 | single | early | medium | 39.6 | 39.6 | none (3) | staged,.allocation- | not logged | died-absent |
| 68 | 1 | concurrent | window | small,medium | 97.5 | 97.5 | none (3) / none (3) | linked(1),.stage- | not logged; not logged | died-present-identical, died-absent |
| 69 | 1 | single | late | medium | 146.1 | 146.1 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 70 | 1 | single | mid-article | large | 16.3 | 16.3 | none (3) | untouched | not logged | died-absent |
| 71 | 1 | single | mid-article | medium | 5.3 | 5.3 | none (3) | untouched | not logged | died-absent |
| 72 | 1 | single | early | large | 71.0 | 71.0 | none (3) | staged,.allocation- | not logged | died-absent |
| 73 | 1 | single | window | small | 74.4 | 74.4 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 74 | 1 | single | window | tiny | 45.6 | 45.6 | none (3) | staged,.stage- | not logged | died-absent |
| 75 | 1 | single | late | medium | 156.1 | 156.1 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 76 | 1 | single | window | large | 175.0 | 175.0 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 77 | 1 | concurrent | late | large,medium | 234.7 | 234.7 | none (3) / 240 article received OK (0) | linked(1),no-stage | not logged; accepted post logged | died-absent, 240-identical |
| 78 | 1 | single | late | medium | 161.6 | 161.6 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 79 | 1 | single | early | small | 19.5 | 19.5 | none (3) | staged,.allocation- | not logged | died-absent |
| 80 | 1 | single | early | large | 61.4 | 61.4 | none (3) | staged,.allocation- | not logged | died-absent |
| 81 | 1 | single | mid-article | small | 17.1 | 17.1 | none (3) | untouched | not logged | died-absent |
| 82 | 1 | single | late | medium | 152.1 | 152.1 | none (3) | staged,.stage- | not logged | died-absent |
| 83 | 1 | single | window | medium | 111.4 | 111.4 | none (3) | frontier-advanced | not logged | died-absent |
| 84 | 1 | single | late | medium | 154.3 | 154.3 | none (3) | frontier-advanced | not logged | died-absent |
| 85 | 1 | single | early | large | 29.4 | 29.4 | none (3) | untouched | not logged | died-absent |
| 86 | 1 | single | early | small | 10.1 | 10.1 | none (3) | staged,.allocation- | not logged | died-absent |
| 87 | 1 | single | window | medium | 95.3 | 95.3 | none (3) | staged,.stage- | not logged | died-absent |
| 88 | 1 | single | early | large | 81.0 | 81.0 | none (3) | frontier-advanced | not logged | died-absent |
| 89 | 1 | single | window | large | 174.2 | 174.2 | none (3) | frontier-advanced | not logged | died-absent |

## Failures: 0


judge rc=0
