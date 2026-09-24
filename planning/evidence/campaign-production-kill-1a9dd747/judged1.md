# ../run1.json

stores 2 (closed and swept: [0, 1])

seed 1; 92 iterations (80 single, 12 concurrent); 214 POSTs in the ledger; 174 final articles present; 94 owner pids, all gone: True

calibration medians (ms from terminator sent): {"tiny": {".allocation-gone": 24.2, ".allocation-seen": 1.9, ".stage-gone": 125.4, ".stage-seen": 60.3, "frontier": 24.2, "reply": 157.1, "stage": 1.9, "stage_cleared": 24.2, "txn": 91.6}, "small": {".allocation-gone": 28.0, ".allocation-seen": 6.8, ".stage-gone": 128.2, ".stage-seen": 70.6, "frontier": 28.0, "reply": 158.3, "stage": 6.8, "stage_cleared": 28.0, "txn": 94.7}, "medium": {".allocation-gone": 53.0, ".allocation-seen": 27.9, ".stage-gone": 145.8, ".stage-seen": 86.4, "frontier": 53.0, "reply": 180.5, "stage": 27.9, "stage_cleared": 53.0, "txn": 118.3}, "large": {".allocation-gone": 90.4, ".allocation-seen": 70.7, ".stage-gone": 209.3, ".stage-seen": 145.5, "frontier": 90.4, "reply": 253.1, "stage": 70.7, "stage_cleared": 90.4, "txn": 180.4}, "over": {"reply": 37.5}}

## Verdicts

- 240-identical: 87
- died-absent: 69
- died-present-identical: 24
- refused: 34
- torn: 0
- lost-240: 0
- reused-number: 0

## Verdicts of the killed POSTs only

| kill kind | verdict | POSTs |
|---|---|---|
| concurrent | 240-identical | 3 |
| concurrent | died-absent | 18 |
| concurrent | died-present-identical | 3 |
| single | 240-identical | 8 |
| single | died-absent | 51 |
| single | died-present-identical | 21 |

## Client exit codes by reply

- rc 0: ['240 article received OK']
- rc 1: ['441 posting failed; the article was not received', '441 posting failed; the article was refused']
- rc 3: ['<no reply>']

## Kill band against the store state at death

| band | store state at death | kills |
|---|---|---|
| early | frontier-advanced | 5 |
| early | linked(1),no-stage | 1 |
| early | staged,.allocation- | 4 |
| early | staged,.stage- | 2 |
| early | untouched | 10 |
| late | frontier-advanced | 2 |
| late | linked(1),.stage- | 4 |
| late | linked(1),no-stage | 10 |
| late | linked(2),no-stage | 1 |
| mid-article | untouched | 8 |
| over-limit | untouched | 6 |
| window | frontier-advanced | 6 |
| window | linked(1),.allocation- | 1 |
| window | linked(1),.stage- | 9 |
| window | linked(1),no-stage | 8 |
| window | staged,.allocation- | 2 |
| window | staged,.stage- | 5 |
| window | untouched | 8 |

## Kill instants against the phase reached

| store state at death | owner log at death | kills | killed at ms (min to max) |
|---|---|---|---|
| untouched | not logged | 30 | 1.8 to 241.7 |
| staged,.allocation- | not logged | 6 | 21.0 to 201.2 |
| frontier-advanced | not logged | 10 | 48.5 to 222.6 |
| staged,.stage- | not logged; not logged | 2 | 48.9 to 79.9 |
| linked(1),no-stage | accepted post logged | 8 | 57.4 to 212.3 |
| untouched | not logged; not logged | 2 | 81.8 to 107.1 |
| staged,.stage- | not logged | 5 | 96.9 to 197.1 |
| linked(1),.stage- | not logged | 12 | 112.3 to 217.4 |
| linked(1),no-stage | not logged | 9 | 119.8 to 217.5 |
| linked(1),no-stage | not logged; not logged | 2 | 138.5 to 243.6 |
| linked(1),.allocation- | not logged; accepted post logged | 1 | 158.4 to 158.4 |
| frontier-advanced | not logged; not logged | 3 | 177.1 to 240.0 |
| linked(2),no-stage | accepted post logged; accepted post logged | 1 | 228.9 to 228.9 |
| linked(1),.stage- | not logged; not logged | 1 | 258.0 to 258.0 |

## Per kill

| # | store | kind | band | sizes | scheduled ms | killed at ms | replies (rc) | store at death | owner log at death | verdict |
|---|---|---|---|---|---|---|---|---|---|---|
| 0 | 0 | single | window | large | 197.1 | 197.1 | none (3) | staged,.stage- | not logged | died-absent |
| 1 | 0 | single | window | medium | 141.8 | 141.8 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 2 | 0 | single | late | tiny | 189.5 | 189.5 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 3 | 0 | single | window | medium | 179.8 | 179.8 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 4 | 0 | single | window | medium | 115.8 | 115.8 | none (3) | frontier-advanced | not logged | died-absent |
| 5 | 0 | single | over-limit | over | 18.9 | 18.9 | none (3) | untouched | not logged | died-absent |
| 6 | 0 | single | window | small | 108.3 | 108.3 | none (3) | staged,.allocation- | not logged | died-absent |
| 7 | 0 | concurrent | window | tiny,small | 158.4 | 158.4 | none (3) / 240 article received OK (0) | linked(1),.allocation- | not logged; accepted post logged | died-absent, 240-identical |
| 8 | 0 | single | window | medium | 138.4 | 138.4 | none (3) | staged,.stage- | not logged | died-absent |
| 9 | 0 | single | mid-article | tiny | 3.2 | 3.2 | none (3) | untouched | not logged | died-absent |
| 10 | 0 | single | early | tiny | 1.8 | 1.8 | none (3) | untouched | not logged | died-absent |
| 11 | 0 | single | late | tiny | 211.8 | 211.8 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 12 | 0 | single | over-limit | over | 35.0 | 35.0 | none (3) | untouched | not logged | died-absent |
| 13 | 0 | concurrent | window | tiny,large | 181.1 | 181.1 | none (3) / none (3) | frontier-advanced | not logged; not logged | died-absent, died-absent |
| 14 | 0 | single | early | large | 89.7 | 89.7 | none (3) | untouched | not logged | died-absent |
| 15 | 0 | single | late | medium | 202.0 | 202.0 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 16 | 0 | single | early | large | 111.4 | 111.4 | none (3) | untouched | not logged | died-absent |
| 17 | 0 | concurrent | window | large,small | 240.0 | 240.0 | none (3) / none (3) | frontier-advanced | not logged; not logged | died-absent, died-absent |
| 18 | 0 | single | window | tiny | 124.3 | 124.3 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 19 | 0 | single | window | medium | 177.8 | 177.8 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 20 | 0 | single | early | small | 48.5 | 48.5 | none (3) | frontier-advanced | not logged | died-absent |
| 21 | 0 | single | window | large | 201.2 | 201.2 | none (3) | staged,.allocation- | not logged | died-absent |
| 22 | 0 | single | early | tiny | 21.0 | 21.0 | none (3) | staged,.allocation- | not logged | died-absent |
| 23 | 0 | single | late | medium | 217.2 | 217.2 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 24 | 0 | single | late | medium | 222.6 | 222.6 | none (3) | frontier-advanced | not logged | died-absent |
| 25 | 0 | single | mid-article | small | 8.6 | 8.6 | none (3) | untouched | not logged | died-absent |
| 26 | 0 | single | early | large | 105.8 | 105.8 | none (3) | untouched | not logged | died-absent |
| 27 | 0 | single | mid-article | medium | 2.3 | 2.3 | none (3) | untouched | not logged | died-absent |
| 28 | 0 | single | late | small | 183.8 | 183.8 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 29 | 0 | concurrent | window | medium,small | 107.1 | 107.1 | none (3) / none (3) | untouched | not logged; not logged | died-absent, died-absent |
| 30 | 0 | single | window | tiny | 119.8 | 119.8 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 31 | 0 | single | window | medium | 175.4 | 175.4 | none (3) | frontier-advanced | not logged | died-absent |
| 32 | 0 | single | over-limit | over | 17.3 | 17.3 | none (3) | untouched | not logged | died-absent |
| 33 | 0 | single | over-limit | over | 9.0 | 9.0 | none (3) | untouched | not logged | died-absent |
| 34 | 0 | single | early | large | 117.8 | 117.8 | none (3) | untouched | not logged | died-absent |
| 35 | 0 | single | late | medium | 217.4 | 217.4 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 36 | 0 | single | window | large | 223.0 | 223.0 | none (3) | untouched | not logged | died-absent |
| 37 | 0 | single | window | tiny | 119.8 | 119.8 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 38 | 0 | single | late | medium | 185.9 | 185.9 | none (3) | frontier-advanced | not logged | died-absent |
| 39 | 0 | single | late | tiny | 212.3 | 212.3 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 40 | 0 | single | window | small | 116.0 | 116.0 | none (3) | staged,.stage- | not logged | died-absent |
| 41 | 0 | concurrent | window | tiny,medium | 177.1 | 177.1 | none (3) / none (3) | frontier-advanced | not logged; not logged | died-absent, died-absent |
| 42 | 0 | concurrent | late | small,medium | 243.6 | 243.6 | none (3) / none (3) | linked(1),no-stage | not logged; not logged | died-present-identical, died-absent |
| 43 | 0 | concurrent | early | large,medium | 81.8 | 81.8 | none (3) / none (3) | untouched | not logged; not logged | died-absent, died-absent |
| 44 | 0 | single | early | small | 50.4 | 50.4 | none (3) | staged,.allocation- | not logged | died-absent |
| 45 | 0 | single | window | large | 210.0 | 210.0 | none (3) | untouched | not logged | died-absent |
| 46 | 0 | single | early | small | 8.0 | 8.0 | none (3) | untouched | not logged | died-absent |
| 47 | 0 | single | window | large | 241.7 | 241.7 | none (3) | untouched | not logged | died-absent |
| 48 | 0 | single | early | large | 123.5 | 123.5 | none (3) | untouched | not logged | died-absent |
| 49 | 0 | single | window | large | 240.9 | 240.9 | none (3) | untouched | not logged | died-absent |
| 50 | 0 | single | early | large | 70.2 | 70.3 | none (3) | untouched | not logged | died-absent |
| 51 | 0 | single | late | tiny | 165.5 | 165.5 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 52 | 0 | single | window | medium | 160.6 | 160.6 | none (3) | untouched | not logged | died-absent |
| 53 | 0 | single | window | small | 123.4 | 123.4 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 54 | 0 | single | over-limit | over | 38.7 | 38.7 | none (3) | untouched | not logged | died-absent |
| 55 | 0 | single | window | medium | 113.1 | 113.1 | none (3) | untouched | not logged | died-absent |
| 56 | 0 | single | window | small | 117.6 | 117.6 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 57 | 0 | single | window | large | 207.8 | 207.8 | none (3) | untouched | not logged | died-absent |
| 58 | 0 | single | window | tiny | 142.3 | 142.3 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 59 | 0 | single | late | small | 217.5 | 217.5 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 60 | 1 | single | early | small | 65.1 | 65.1 | none (3) | frontier-advanced | not logged | died-absent |
| 61 | 1 | single | early | small | 64.9 | 64.9 | none (3) | frontier-advanced | not logged | died-absent |
| 62 | 1 | single | early | tiny | 57.4 | 57.4 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 63 | 1 | single | mid-article | medium | 8.4 | 8.4 | none (3) | untouched | not logged | died-absent |
| 64 | 1 | concurrent | late | tiny,medium | 228.9 | 228.9 | 240 article received OK (0) / 240 article received OK (0) | linked(2),no-stage | accepted post logged; accepted post logged | 240-identical, 240-identical |
| 65 | 1 | single | window | medium | 150.4 | 150.4 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 66 | 1 | single | window | tiny | 142.9 | 142.9 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 67 | 1 | single | late | small | 204.2 | 204.2 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 68 | 1 | single | window | medium | 157.2 | 157.2 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 69 | 1 | concurrent | early | tiny,small | 48.9 | 48.9 | none (3) / none (3) | staged,.stage- | not logged; not logged | died-absent, died-absent |
| 70 | 1 | concurrent | early | large,small | 79.9 | 79.9 | none (3) / none (3) | staged,.stage- | not logged; not logged | died-absent, died-absent |
| 71 | 1 | single | over-limit | over | 12.3 | 12.3 | none (3) | untouched | not logged | died-absent |
| 72 | 1 | single | mid-article | large | 13.0 | 13.0 | none (3) | untouched | not logged | died-absent |
| 73 | 1 | single | window | tiny | 96.9 | 96.9 | none (3) | staged,.stage- | not logged | died-absent |
| 74 | 1 | concurrent | late | large,medium | 258.0 | 258.0 | none (3) / none (3) | linked(1),.stage- | not logged; not logged | died-present-identical, died-absent |
| 75 | 1 | single | early | tiny | 74.3 | 74.3 | none (3) | staged,.allocation- | not logged | died-absent |
| 76 | 1 | single | early | tiny | 73.7 | 73.7 | none (3) | frontier-advanced | not logged | died-absent |
| 77 | 1 | single | early | medium | 76.8 | 76.8 | none (3) | staged,.allocation- | not logged | died-absent |
| 78 | 1 | single | window | small | 113.1 | 113.1 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 79 | 1 | concurrent | window | medium,small | 138.5 | 138.5 | none (3) / none (3) | linked(1),no-stage | not logged; not logged | died-absent, died-present-identical |
| 80 | 1 | single | late | tiny | 171.0 | 171.0 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 81 | 1 | single | mid-article | small | 5.1 | 5.1 | none (3) | untouched | not logged | died-absent |
| 82 | 1 | single | window | small | 124.7 | 124.7 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 83 | 1 | single | mid-article | tiny | 7.9 | 7.9 | none (3) | untouched | not logged | died-absent |
| 84 | 1 | single | window | small | 156.8 | 156.8 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 85 | 1 | single | early | tiny | 77.5 | 77.5 | none (3) | frontier-advanced | not logged | died-absent |
| 86 | 1 | single | window | tiny | 118.9 | 118.9 | none (3) | staged,.stage- | not logged | died-absent |
| 87 | 1 | single | window | large | 217.6 | 217.6 | none (3) | frontier-advanced | not logged | died-absent |
| 88 | 1 | single | late | small | 197.2 | 197.2 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 89 | 1 | single | window | tiny | 112.3 | 112.3 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 90 | 1 | single | early | medium | 24.6 | 24.6 | none (3) | untouched | not logged | died-absent |
| 91 | 1 | single | mid-article | large | 4.4 | 4.4 | none (3) | untouched | not logged | died-absent |

## Failures: 0


