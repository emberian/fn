# ../run2.json

stores 2 (closed and swept: [0, 1])

seed 2; 92 iterations (80 single, 12 concurrent); 224 POSTs in the ledger; 191 final articles present; 94 owner pids, all gone: True

calibration medians (ms from terminator sent): {"tiny": {".allocation-gone": 21.3, ".allocation-seen": 1.7, ".stage-gone": 145.9, ".stage-seen": 40.9, "frontier": 21.3, "reply": 165.4, "stage": 1.7, "stage_cleared": 21.3, "txn": 126.4}, "small": {".allocation-gone": 22.1, ".allocation-seen": 6.8, ".stage-gone": 140.6, ".stage-seen": 46.6, "frontier": 22.1, "reply": 157.6, "stage": 6.8, "stage_cleared": 22.1, "txn": 108.4}, "medium": {".allocation-gone": 62.2, ".allocation-seen": 32.0, ".stage-gone": 125.3, ".stage-seen": 84.7, "frontier": 62.2, "reply": 152.8, "stage": 32.0, "stage_cleared": 62.2, "txn": 103.9}, "large": {".allocation-gone": 95.1, ".allocation-seen": 69.3, ".stage-gone": 170.8, ".stage-seen": 138.9, "frontier": 95.1, "reply": 224.1, "stage": 69.3, "stage_cleared": 95.1, "txn": 156.1}, "over": {"reply": 36.8}}

## Verdicts

- 240-identical: 97
- died-absent: 78
- died-present-identical: 22
- refused: 27
- torn: 0
- lost-240: 0
- reused-number: 0

## Verdicts of the killed POSTs only

| kill kind | verdict | POSTs |
|---|---|---|
| concurrent | died-absent | 17 |
| concurrent | died-present-identical | 7 |
| single | 240-identical | 4 |
| single | died-absent | 61 |
| single | died-present-identical | 15 |

## Client exit codes by reply

- rc 0: ['240 article received OK']
- rc 1: ['441 posting failed; the article was not received', '441 posting failed; the article was refused']
- rc 3: ['<no reply>']

## Kill band against the store state at death

| band | store state at death | kills |
|---|---|---|
| early | frontier-advanced | 3 |
| early | staged,.allocation- | 6 |
| early | staged,.stage- | 2 |
| early | untouched | 11 |
| late | frontier-advanced | 3 |
| late | linked(1),.stage- | 2 |
| late | linked(1),no-stage | 7 |
| late | staged,.allocation- | 2 |
| late | staged,.stage- | 1 |
| late | untouched | 2 |
| mid-article | untouched | 8 |
| over-limit | untouched | 6 |
| window | frontier-advanced | 7 |
| window | linked(1),.stage- | 6 |
| window | linked(1),no-stage | 11 |
| window | staged,.allocation- | 4 |
| window | staged,.stage- | 7 |
| window | untouched | 4 |

## Kill instants against the phase reached

| store state at death | owner log at death | kills | killed at ms (min to max) |
|---|---|---|---|
| untouched | not logged | 29 | 1.9 to 277.7 |
| staged,.allocation- | not logged | 11 | 10.4 to 229.9 |
| untouched | not logged; not logged | 2 | 43.5 to 228.9 |
| frontier-advanced | not logged | 12 | 54.7 to 306.2 |
| staged,.allocation- | not logged; not logged | 1 | 59.8 to 59.8 |
| staged,.stage- | not logged; not logged | 1 | 96.2 to 96.2 |
| staged,.stage- | not logged | 9 | 99.1 to 202.5 |
| linked(1),.stage- | not logged; not logged | 4 | 115.1 to 228.5 |
| linked(1),.stage- | not logged | 4 | 116.8 to 168.7 |
| linked(1),no-stage | not logged; not logged | 3 | 119.3 to 213.6 |
| linked(1),no-stage | not logged | 11 | 128.7 to 222.5 |
| linked(1),no-stage | accepted post logged | 4 | 140.6 to 229.9 |
| frontier-advanced | not logged; not logged | 1 | 154.8 to 154.8 |

## Per kill

| # | store | kind | band | sizes | scheduled ms | killed at ms | replies (rc) | store at death | owner log at death | verdict |
|---|---|---|---|---|---|---|---|---|---|---|
| 0 | 0 | single | window | small | 140.6 | 140.6 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 1 | 0 | single | mid-article | small | 5.1 | 5.1 | none (3) | untouched | not logged | died-absent |
| 2 | 0 | single | mid-article | medium | 12.1 | 12.1 | none (3) | untouched | not logged | died-absent |
| 3 | 0 | single | late | tiny | 229.9 | 229.9 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 4 | 0 | single | early | small | 97.5 | 97.5 | none (3) | frontier-advanced | not logged | died-absent |
| 5 | 0 | single | window | medium | 142.7 | 142.7 | none (3) | frontier-advanced | not logged | died-absent |
| 6 | 0 | single | window | medium | 138.7 | 138.7 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 7 | 0 | single | window | large | 167.5 | 167.5 | none (3) | frontier-advanced | not logged | died-absent |
| 8 | 0 | single | window | medium | 116.1 | 116.1 | none (3) | staged,.allocation- | not logged | died-absent |
| 9 | 0 | concurrent | early | small,large | 59.8 | 59.8 | none (3) / none (3) | staged,.allocation- | not logged; not logged | died-absent, died-absent |
| 10 | 0 | single | window | small | 128.4 | 128.4 | none (3) | staged,.stage- | not logged | died-absent |
| 11 | 0 | single | late | tiny | 187.9 | 187.9 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 12 | 0 | single | early | small | 31.7 | 31.7 | none (3) | staged,.allocation- | not logged | died-absent |
| 13 | 0 | single | early | medium | 84.9 | 84.9 | none (3) | staged,.allocation- | not logged | died-absent |
| 14 | 0 | single | early | large | 125.3 | 125.3 | none (3) | untouched | not logged | died-absent |
| 15 | 0 | single | late | small | 191.4 | 191.4 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 16 | 0 | single | late | small | 170.5 | 170.5 | none (3) | frontier-advanced | not logged | died-absent |
| 17 | 0 | single | window | small | 151.4 | 151.4 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 18 | 0 | single | late | tiny | 222.5 | 222.5 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 19 | 0 | single | window | tiny | 118.3 | 118.3 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 20 | 0 | concurrent | window | tiny,small | 119.3 | 119.3 | none (3) / none (3) | linked(1),no-stage | not logged; not logged | died-present-identical, died-absent |
| 21 | 0 | single | window | large | 167.3 | 167.3 | none (3) | untouched | not logged | died-absent |
| 22 | 0 | concurrent | late | tiny,tiny | 228.5 | 228.5 | none (3) / none (3) | linked(1),.stage- | not logged; not logged | died-absent, died-present-identical |
| 23 | 0 | single | late | medium | 208.7 | 208.7 | none (3) | frontier-advanced | not logged | died-absent |
| 24 | 0 | single | window | tiny | 155.0 | 155.0 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 25 | 0 | single | mid-article | small | 19.7 | 19.7 | none (3) | untouched | not logged | died-absent |
| 26 | 0 | single | window | medium | 141.7 | 141.7 | none (3) | staged,.allocation- | not logged | died-absent |
| 27 | 0 | single | window | tiny | 116.9 | 116.9 | none (3) | staged,.stage- | not logged | died-absent |
| 28 | 0 | single | window | large | 218.4 | 218.4 | none (3) | untouched | not logged | died-absent |
| 29 | 0 | single | window | tiny | 134.1 | 134.1 | none (3) | staged,.allocation- | not logged | died-absent |
| 30 | 0 | concurrent | late | large,medium | 228.9 | 228.9 | none (3) / none (3) | untouched | not logged; not logged | died-absent, died-absent |
| 31 | 0 | single | early | small | 97.1 | 97.1 | none (3) | frontier-advanced | not logged | died-absent |
| 32 | 0 | single | late | large | 277.7 | 277.7 | none (3) | untouched | not logged | died-absent |
| 33 | 0 | single | mid-article | tiny | 17.5 | 17.5 | none (3) | untouched | not logged | died-absent |
| 34 | 0 | concurrent | late | small,tiny | 213.6 | 213.6 | none (3) / none (3) | linked(1),no-stage | not logged; not logged | died-absent, died-present-identical |
| 35 | 0 | single | late | tiny | 194.7 | 194.7 | none (3) | staged,.allocation- | not logged | died-absent |
| 36 | 0 | single | early | large | 112.0 | 112.0 | none (3) | untouched | not logged | died-absent |
| 37 | 0 | single | window | small | 152.8 | 152.8 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 38 | 0 | single | over-limit | over | 28.4 | 28.4 | none (3) | untouched | not logged | died-absent |
| 39 | 0 | single | window | small | 156.9 | 156.9 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 40 | 0 | single | mid-article | large | 2.9 | 2.9 | none (3) | untouched | not logged | died-absent |
| 41 | 0 | single | early | medium | 78.2 | 78.2 | none (3) | untouched | not logged | died-absent |
| 42 | 0 | single | early | medium | 50.9 | 50.9 | none (3) | untouched | not logged | died-absent |
| 43 | 0 | concurrent | window | large,small | 150.2 | 150.2 | none (3) / none (3) | linked(1),no-stage | not logged; not logged | died-absent, died-present-identical |
| 44 | 0 | single | late | small | 208.4 | 208.4 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 45 | 0 | single | window | tiny | 128.7 | 128.7 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 46 | 0 | single | window | large | 154.5 | 154.5 | none (3) | untouched | not logged | died-absent |
| 47 | 0 | single | mid-article | small | 15.6 | 15.6 | none (3) | untouched | not logged | died-absent |
| 48 | 0 | single | early | large | 112.9 | 112.9 | none (3) | untouched | not logged | died-absent |
| 49 | 0 | single | window | tiny | 115.1 | 115.1 | none (3) | staged,.stage- | not logged | died-absent |
| 50 | 0 | single | over-limit | over | 17.7 | 17.7 | none (3) | untouched | not logged | died-absent |
| 51 | 0 | single | early | medium | 93.4 | 93.4 | none (3) | untouched | not logged | died-absent |
| 52 | 1 | single | late | small | 166.7 | 166.7 | none (3) | staged,.stage- | not logged | died-absent |
| 53 | 1 | single | over-limit | over | 29.8 | 29.8 | none (3) | untouched | not logged | died-absent |
| 54 | 1 | single | window | large | 202.5 | 202.5 | none (3) | staged,.stage- | not logged | died-absent |
| 55 | 1 | single | window | medium | 104.2 | 104.2 | none (3) | staged,.stage- | not logged | died-absent |
| 56 | 1 | single | early | tiny | 99.1 | 99.1 | none (3) | staged,.stage- | not logged | died-absent |
| 57 | 1 | single | window | large | 182.7 | 182.7 | none (3) | frontier-advanced | not logged | died-absent |
| 58 | 1 | single | window | small | 149.6 | 149.6 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 59 | 1 | concurrent | window | medium,large | 164.7 | 164.7 | none (3) / none (3) | linked(1),.stage- | not logged; not logged | died-present-identical, died-absent |
| 60 | 1 | single | window | large | 197.2 | 197.2 | none (3) | staged,.allocation- | not logged | died-absent |
| 61 | 1 | single | mid-article | large | 14.0 | 14.0 | none (3) | untouched | not logged | died-absent |
| 62 | 1 | single | over-limit | over | 25.0 | 25.0 | none (3) | untouched | not logged | died-absent |
| 63 | 1 | single | window | small | 128.4 | 128.4 | none (3) | staged,.stage- | not logged | died-absent |
| 64 | 1 | single | over-limit | over | 13.3 | 13.3 | none (3) | untouched | not logged | died-absent |
| 65 | 1 | single | window | large | 170.9 | 170.9 | none (3) | frontier-advanced | not logged | died-absent |
| 66 | 1 | single | mid-article | small | 1.9 | 1.9 | none (3) | untouched | not logged | died-absent |
| 67 | 1 | concurrent | window | tiny,small | 115.7 | 115.7 | none (3) / none (3) | linked(1),.stage- | not logged; not logged | died-present-identical, died-absent |
| 68 | 1 | concurrent | early | large,small | 96.2 | 96.2 | none (3) / none (3) | staged,.stage- | not logged; not logged | died-absent, died-absent |
| 69 | 1 | single | early | small | 59.2 | 59.2 | none (3) | staged,.allocation- | not logged | died-absent |
| 70 | 1 | single | window | medium | 151.7 | 151.7 | none (3) | staged,.stage- | not logged | died-absent |
| 71 | 1 | single | early | tiny | 10.4 | 10.4 | none (3) | staged,.allocation- | not logged | died-absent |
| 72 | 1 | single | early | medium | 43.5 | 43.5 | none (3) | untouched | not logged | died-absent |
| 73 | 1 | single | window | medium | 134.7 | 134.7 | none (3) | frontier-advanced | not logged | died-absent |
| 74 | 1 | single | late | large | 229.9 | 229.9 | none (3) | staged,.allocation- | not logged | died-absent |
| 75 | 1 | single | late | large | 306.2 | 306.2 | none (3) | frontier-advanced | not logged | died-absent |
| 76 | 1 | concurrent | window | tiny,small | 154.8 | 154.8 | none (3) / none (3) | frontier-advanced | not logged; not logged | died-absent, died-absent |
| 77 | 1 | single | early | large | 70.6 | 70.6 | none (3) | untouched | not logged | died-absent |
| 78 | 1 | single | late | tiny | 168.7 | 168.7 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 79 | 1 | concurrent | window | tiny,small | 115.1 | 115.1 | none (3) / none (3) | linked(1),.stage- | not logged; not logged | died-present-identical, died-absent |
| 80 | 1 | single | window | large | 183.9 | 183.9 | none (3) | untouched | not logged | died-absent |
| 81 | 1 | concurrent | early | large,large | 43.5 | 43.5 | none (3) / none (3) | untouched | not logged; not logged | died-absent, died-absent |
| 82 | 1 | single | early | small | 22.5 | 22.5 | none (3) | untouched | not logged | died-absent |
| 83 | 1 | single | early | small | 54.7 | 54.7 | none (3) | frontier-advanced | not logged | died-absent |
| 84 | 1 | single | late | small | 213.5 | 213.5 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 85 | 1 | single | early | medium | 23.5 | 23.5 | none (3) | untouched | not logged | died-absent |
| 86 | 1 | single | window | small | 160.4 | 160.4 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 87 | 1 | single | window | tiny | 116.8 | 116.8 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 88 | 1 | single | window | tiny | 156.6 | 156.6 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 89 | 1 | single | window | tiny | 136.8 | 136.8 | none (3) | frontier-advanced | not logged | died-absent |
| 90 | 1 | single | over-limit | over | 32.0 | 32.0 | none (3) | untouched | not logged | died-absent |
| 91 | 1 | single | early | small | 49.8 | 49.8 | none (3) | staged,.allocation- | not logged | died-absent |

## Failures: 0


