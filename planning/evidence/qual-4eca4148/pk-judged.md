# /tank/fn/scratch/qual-4eca4148/campaign/pk-run.json

stores 2 (closed and swept: [0, 1])

seed 3; 90 iterations (80 single, 10 concurrent); 206 POSTs in the ledger; 178 final articles present; 92 owner pids, all gone: True

calibration medians (ms from terminator sent): {"tiny": {".allocation-gone": 25.6, ".allocation-seen": 1.2, ".stage-gone": 70.9, ".stage-seen": 40.2, "frontier": 25.6, "reply": 93.5, "stage": 1.2, "stage_cleared": 25.6, "txn": 50.6}, "small": {".allocation-gone": 28.3, ".allocation-seen": 4.5, ".stage-gone": 98.1, ".stage-seen": 58.4, "frontier": 28.3, "reply": 122.2, "stage": 4.5, "stage_cleared": 28.3, "txn": 78.4}, "medium": {".allocation-gone": 44.4, ".allocation-seen": 23.6, ".stage-gone": 111.5, ".stage-seen": 68.0, "frontier": 44.4, "reply": 143.7, "stage": 23.6, "stage_cleared": 44.4, "txn": 86.2}, "large": {".allocation-gone": 70.6, ".allocation-seen": 53.6, ".stage-gone": 170.8, ".stage-seen": 124.8, "frontier": 70.6, "reply": 202.1, "stage": 53.6, "stage_cleared": 70.6, "txn": 145.2}, "over": {"reply": 13.6}}

## Verdicts

- 240-identical: 98
- died-absent: 68
- died-present-identical: 17
- refused: 23
- torn: 0
- lost-240: 0
- reused-number: 0

## Verdicts of the killed POSTs only

| kill kind | verdict | POSTs |
|---|---|---|
| concurrent | 240-identical | 5 |
| concurrent | died-absent | 14 |
| concurrent | died-present-identical | 1 |
| single | 240-identical | 9 |
| single | died-absent | 54 |
| single | died-present-identical | 16 |
| single | refused | 1 |

## Client exit codes by reply

- rc 0: ['240 article received OK']
- rc 1: ['441 posting failed; the article was not received', '441 posting failed; this article is already stored here']
- rc 3: ['<no reply>']

## Kill band against the store state at death

| band | store state at death | kills |
|---|---|---|
| early | frontier-advanced | 3 |
| early | staged,.allocation- | 9 |
| early | staged,.stage- | 3 |
| early | untouched | 6 |
| late | frontier-advanced | 2 |
| late | linked(1),.stage- | 4 |
| late | linked(1),no-stage | 7 |
| late | staged,.stage- | 3 |
| mid-article | untouched | 8 |
| over-limit | untouched | 6 |
| window | frontier-advanced | 9 |
| window | linked(1),.allocation- | 2 |
| window | linked(1),.stage- | 8 |
| window | linked(1),no-stage | 10 |
| window | staged,.allocation- | 5 |
| window | staged,.stage- | 5 |

## Kill instants against the phase reached

| store state at death | owner log at death | kills | killed at ms (min to max) |
|---|---|---|---|
| untouched | not logged; not logged | 1 | 0.3 to 0.3 |
| untouched | not logged | 19 | 1.9 to 93.4 |
| staged,.allocation- | not logged; not logged | 1 | 4.2 to 4.2 |
| staged,.allocation- | not logged | 13 | 7.3 to 124.7 |
| staged,.stage- | not logged | 11 | 37.5 to 190.6 |
| frontier-advanced | not logged | 12 | 41.8 to 188.7 |
| linked(1),.stage- | not logged | 11 | 47.8 to 184.1 |
| linked(1),no-stage | accepted post logged | 9 | 81.9 to 286.1 |
| frontier-advanced | not logged; not logged | 2 | 101.1 to 250.2 |
| linked(1),no-stage | not logged | 5 | 108.8 to 174.2 |
| linked(1),.allocation- | accepted post logged; not logged | 1 | 118.3 to 118.3 |
| linked(1),no-stage | accepted post logged; not logged | 1 | 156.5 to 156.5 |
| linked(1),no-stage | not logged; accepted post logged | 2 | 161.9 to 169.3 |
| linked(1),.stage- | not logged; not logged | 1 | 168.9 to 168.9 |
| linked(1),.allocation- | not logged; accepted post logged | 1 | 199.2 to 199.2 |

## Per kill

| # | store | kind | band | sizes | scheduled ms | killed at ms | replies (rc) | store at death | owner log at death | verdict |
|---|---|---|---|---|---|---|---|---|---|---|
| 0 | 0 | single | late | small | 172.9 | 172.9 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 1 | 0 | single | window | small | 119.6 | 119.6 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 2 | 0 | single | over-limit | over | 26.5 | 26.5 | none (3) | untouched | not logged | died-absent |
| 3 | 0 | single | window | large | 152.4 | 152.4 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 4 | 0 | single | early | tiny | 7.3 | 7.3 | none (3) | staged,.allocation- | not logged | died-absent |
| 5 | 0 | single | late | small | 128.3 | 128.3 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 6 | 0 | single | over-limit | over | 6.8 | 6.8 | none (3) | untouched | not logged | died-absent |
| 7 | 0 | single | early | tiny | 37.5 | 37.5 | none (3) | staged,.stage- | not logged | died-absent |
| 8 | 0 | single | window | tiny | 81.9 | 81.9 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 9 | 0 | single | early | small | 61.3 | 61.3 | none (3) | frontier-advanced | not logged | died-absent |
| 10 | 0 | single | late | medium | 147.9 | 147.9 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 11 | 0 | single | early | small | 62.0 | 62.0 | none (3) | staged,.stage- | not logged | died-absent |
| 12 | 0 | single | mid-article | medium | 3.7 | 3.7 | none (3) | untouched | not logged | died-absent |
| 13 | 0 | single | window | tiny | 47.4 | 47.4 | none (3) | staged,.stage- | not logged | died-absent |
| 14 | 0 | single | window | large | 173.4 | 173.4 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 15 | 0 | single | window | medium | 115.7 | 115.7 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 16 | 0 | concurrent | early | small,small | 0.3 | 0.3 | none (3) / none (3) | untouched | not logged; not logged | died-absent, died-absent |
| 17 | 0 | single | late | large | 286.1 | 286.1 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 18 | 0 | concurrent | window | large,medium | 169.3 | 169.3 | none (3) / 240 article received OK (0) | linked(1),no-stage | not logged; accepted post logged | died-absent, 240-identical |
| 19 | 0 | single | window | tiny | 47.8 | 47.8 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 20 | 0 | concurrent | window | large,medium | 161.9 | 161.9 | none (3) / 240 article received OK (0) | linked(1),no-stage | not logged; accepted post logged | died-absent, 240-identical |
| 21 | 0 | single | mid-article | medium | 3.7 | 3.7 | none (3) | untouched | not logged | died-absent |
| 22 | 0 | single | late | medium | 174.4 | 174.4 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 23 | 0 | single | window | tiny | 89.1 | 89.1 | none (3) | staged,.allocation- | not logged | died-absent |
| 24 | 0 | single | window | medium | 88.4 | 88.4 | none (3) | staged,.allocation- | not logged | died-absent |
| 25 | 0 | single | mid-article | medium | 13.5 | 13.5 | none (3) | untouched | not logged | died-absent |
| 26 | 0 | single | window | medium | 144.3 | 144.3 | none (3) | staged,.stage- | not logged | died-absent |
| 27 | 0 | single | window | tiny | 95.4 | 95.4 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 28 | 0 | single | over-limit | over | 7.6 | 7.6 | none (3) | untouched | not logged | died-absent |
| 29 | 0 | concurrent | window | large,tiny | 199.2 | 199.2 | none (3) / 240 article received OK (0) | linked(1),.allocation- | not logged; accepted post logged | died-absent, 240-identical |
| 30 | 0 | single | window | large | 174.2 | 174.2 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 31 | 0 | single | window | small | 71.7 | 71.7 | none (3) | frontier-advanced | not logged | died-absent |
| 32 | 0 | single | window | medium | 99.3 | 99.3 | none (3) | frontier-advanced | not logged | died-absent |
| 33 | 0 | single | window | large | 146.9 | 146.9 | none (3) | frontier-advanced | not logged | died-absent |
| 34 | 0 | concurrent | window | tiny,medium | 118.3 | 118.3 | 240 article received OK (0) / none (3) | linked(1),.allocation- | accepted post logged; not logged | 240-identical, died-absent |
| 35 | 0 | single | window | tiny | 51.1 | 51.1 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 36 | 0 | single | window | small | 108.8 | 108.8 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 37 | 0 | single | over-limit | over | 10.1 | 10.1 | none (3) | untouched | not logged | died-absent |
| 38 | 0 | single | window | large | 137.3 | 137.3 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 39 | 0 | single | window | tiny | 61.3 | 61.3 | none (3) | frontier-advanced | not logged | died-absent |
| 40 | 0 | single | late | tiny | 119.7 | 119.7 | none (3) | frontier-advanced | not logged | died-absent |
| 41 | 0 | single | window | large | 158.7 | 158.7 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 42 | 0 | single | late | medium | 182.9 | 182.9 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 43 | 0 | concurrent | window | medium,large | 156.5 | 156.5 | 240 article received OK (0) / none (3) | linked(1),no-stage | accepted post logged; not logged | 240-identical, died-absent |
| 44 | 0 | concurrent | late | small,tiny | 168.9 | 168.9 | none (3) / none (3) | linked(1),.stage- | not logged; not logged | died-present-identical, died-absent |
| 45 | 0 | single | window | medium | 112.5 | 112.5 | none (3) | staged,.stage- | not logged | died-absent |
| 46 | 0 | concurrent | early | large,small | 4.2 | 4.2 | none (3) / none (3) | staged,.allocation- | not logged; not logged | died-absent, died-absent |
| 47 | 0 | single | early | small | 41.8 | 41.8 | none (3) | frontier-advanced | not logged | died-absent |
| 48 | 0 | single | early | small | 16.4 | 16.4 | none (3) | staged,.allocation- | not logged | died-absent |
| 49 | 0 | single | early | large | 126.0 | 126.0 | none (3) | staged,.stage- | not logged | died-absent |
| 50 | 0 | single | late | tiny | 134.4 | 134.4 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 51 | 0 | single | over-limit | over | 4.8 | 4.8 | none (3) | untouched | not logged | died-absent |
| 52 | 0 | single | early | large | 96.9 | 96.9 | none (3) | frontier-advanced | not logged | died-absent |
| 53 | 0 | single | late | tiny | 127.5 | 127.5 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 54 | 1 | single | mid-article | small | 4.5 | 4.5 | none (3) | untouched | not logged | died-absent |
| 55 | 1 | single | window | tiny | 66.5 | 66.5 | none (3) | staged,.allocation- | not logged | died-absent |
| 56 | 1 | single | early | large | 51.9 | 51.9 | none (3) | untouched | not logged | died-absent |
| 57 | 1 | single | early | tiny | 13.7 | 13.7 | none (3) | staged,.allocation- | not logged | died-absent |
| 58 | 1 | single | mid-article | large | 1.9 | 1.9 | none (3) | untouched | not logged | died-absent |
| 59 | 1 | single | window | medium | 106.7 | 106.7 | none (3) | frontier-advanced | not logged | died-absent |
| 60 | 1 | single | early | tiny | 27.6 | 27.6 | none (3) | staged,.allocation- | not logged | died-absent |
| 61 | 1 | single | window | large | 178.6 | 178.6 | none (3) | staged,.stage- | not logged | died-absent |
| 62 | 1 | single | window | tiny | 77.1 | 77.1 | none (3) | staged,.stage- | not logged | died-absent |
| 63 | 1 | single | over-limit | over | 21.2 | 21.2 | 441 posting failed; the arti (1) | untouched | not logged | refused |
| 64 | 1 | single | window | tiny | 70.1 | 70.1 | none (3) | staged,.allocation- | not logged | died-absent |
| 65 | 1 | single | early | large | 51.6 | 51.6 | none (3) | untouched | not logged | died-absent |
| 66 | 1 | single | window | tiny | 93.9 | 93.9 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 67 | 1 | single | early | medium | 36.7 | 36.7 | none (3) | staged,.allocation- | not logged | died-absent |
| 68 | 1 | concurrent | window | small,medium | 101.1 | 101.1 | none (3) / none (3) | frontier-advanced | not logged; not logged | died-absent, died-absent |
| 69 | 1 | single | late | medium | 172.4 | 172.4 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 70 | 1 | single | mid-article | large | 16.3 | 16.3 | none (3) | untouched | not logged | died-absent |
| 71 | 1 | single | mid-article | medium | 5.3 | 5.3 | none (3) | untouched | not logged | died-absent |
| 72 | 1 | single | early | large | 81.8 | 81.8 | none (3) | staged,.allocation- | not logged | died-absent |
| 73 | 1 | single | window | small | 105.2 | 105.2 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 74 | 1 | single | window | tiny | 64.8 | 64.8 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 75 | 1 | single | late | medium | 184.1 | 184.1 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 76 | 1 | single | window | large | 188.7 | 188.7 | none (3) | frontier-advanced | not logged | died-absent |
| 77 | 1 | concurrent | late | large,medium | 250.2 | 250.2 | none (3) / none (3) | frontier-advanced | not logged; not logged | died-absent, died-absent |
| 78 | 1 | single | late | medium | 190.6 | 190.6 | none (3) | staged,.stage- | not logged | died-absent |
| 79 | 1 | single | early | small | 26.1 | 26.1 | none (3) | staged,.allocation- | not logged | died-absent |
| 80 | 1 | single | early | large | 70.7 | 70.7 | none (3) | untouched | not logged | died-absent |
| 81 | 1 | single | mid-article | small | 17.1 | 17.1 | none (3) | untouched | not logged | died-absent |
| 82 | 1 | single | late | medium | 179.3 | 179.3 | none (3) | staged,.stage- | not logged | died-absent |
| 83 | 1 | single | window | medium | 124.7 | 124.7 | none (3) | staged,.allocation- | not logged | died-absent |
| 84 | 1 | single | late | medium | 182.0 | 182.0 | none (3) | staged,.stage- | not logged | died-absent |
| 85 | 1 | single | early | large | 33.9 | 33.9 | none (3) | untouched | not logged | died-absent |
| 86 | 1 | single | early | small | 13.5 | 13.5 | none (3) | staged,.allocation- | not logged | died-absent |
| 87 | 1 | single | window | medium | 97.3 | 97.3 | none (3) | frontier-advanced | not logged | died-absent |
| 88 | 1 | single | early | large | 93.3 | 93.4 | none (3) | untouched | not logged | died-absent |
| 89 | 1 | single | window | large | 187.9 | 187.9 | none (3) | frontier-advanced | not logged | died-absent |

## Failures: 0


judge rc=0
