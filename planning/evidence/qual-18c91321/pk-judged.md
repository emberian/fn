# /tank/fn/scratch/qual-18c91321/campaign/pk-run.json

stores 2 (closed and swept: [0, 1])

seed 3; 90 iterations (80 single, 10 concurrent); 206 POSTs in the ledger; 178 final articles present; 92 owner pids, all gone: True

calibration medians (ms from terminator sent): {"tiny": {".allocation-gone": 7.5, ".allocation-seen": 1.4, ".stage-gone": 32.6, ".stage-seen": 16.9, "frontier": 7.5, "reply": 42.4, "stage": 1.4, "stage_cleared": 7.5, "txn": 24.2}, "small": {".allocation-gone": 17.6, ".allocation-seen": 8.0, ".stage-gone": 44.2, ".stage-seen": 31.6, "frontier": 17.6, "reply": 55.9, "stage": 8.0, "stage_cleared": 17.6, "txn": 35.8}, "medium": {".allocation-gone": 36.3, ".allocation-seen": 27.7, ".stage-gone": 85.1, ".stage-seen": 61.1, "frontier": 36.3, "reply": 105.2, "stage": 27.7, "stage_cleared": 36.3, "txn": 68.2}, "large": {".allocation-gone": 75.1, ".allocation-seen": 67.9, ".stage-gone": 125.9, ".stage-seen": 113.1, "frontier": 75.1, "reply": 154.7, "stage": 67.9, "stage_cleared": 75.1, "txn": 119.4}, "over": {"reply": 15.6}}

## Verdicts

- 240-identical: 110
- died-absent: 56
- died-present-identical: 17
- refused: 23
- torn: 0
- lost-240: 0
- reused-number: 0

## Verdicts of the killed POSTs only

| kill kind | verdict | POSTs |
|---|---|---|
| concurrent | 240-identical | 8 |
| concurrent | died-absent | 12 |
| single | 240-identical | 18 |
| single | died-absent | 44 |
| single | died-present-identical | 17 |
| single | refused | 1 |

## Client exit codes by reply

- rc 0: ['240 article received OK']
- rc 1: ['441 posting failed; a different article with this Message-ID', '441 posting failed; the article was not received', '441 posting failed; this article is already stored here']
- rc 3: ['<no reply>']

## Kill band against the store state at death

| band | store state at death | kills |
|---|---|---|
| early | frontier-advanced | 5 |
| early | staged,.allocation- | 9 |
| early | staged,.stage- | 2 |
| early | untouched | 5 |
| late | frontier-advanced | 1 |
| late | linked(1),.stage- | 2 |
| late | linked(1),no-stage | 12 |
| late | staged,.stage- | 1 |
| mid-article | untouched | 8 |
| over-limit | untouched | 6 |
| window | frontier-advanced | 4 |
| window | linked(1),.allocation- | 1 |
| window | linked(1),.stage- | 8 |
| window | linked(1),no-stage | 20 |
| window | staged,.allocation- | 3 |
| window | staged,.stage- | 3 |

## Kill instants against the phase reached

| store state at death | owner log at death | kills | killed at ms (min to max) |
|---|---|---|---|
| untouched | not logged; not logged | 2 | 0.2 to 3.5 |
| untouched | not logged | 17 | 1.9 to 42.7 |
| staged,.allocation- | not logged | 12 | 3.5 to 58.1 |
| frontier-advanced | not logged | 10 | 19.1 to 136.3 |
| staged,.stage- | not logged | 6 | 22.6 to 111.9 |
| linked(1),.stage- | not logged | 9 | 29.1 to 220.1 |
| linked(1),no-stage | not logged | 8 | 33.2 to 146.0 |
| linked(1),no-stage | accepted post logged | 18 | 49.1 to 146.6 |
| linked(1),.allocation- | accepted post logged; not logged | 1 | 77.3 to 77.3 |
| linked(1),.stage- | accepted post logged; not logged | 1 | 79.8 to 79.8 |
| linked(1),no-stage | not logged; accepted post logged | 4 | 89.0 to 153.7 |
| linked(1),no-stage | accepted post logged; not logged | 2 | 124.8 to 192.4 |

## Per kill

| # | store | kind | band | sizes | scheduled ms | killed at ms | replies (rc) | store at death | owner log at death | verdict |
|---|---|---|---|---|---|---|---|---|---|---|
| 0 | 0 | single | late | small | 81.7 | 81.7 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 1 | 0 | single | window | small | 56.1 | 56.1 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 2 | 0 | single | over-limit | over | 26.5 | 26.5 | none (3) | untouched | not logged | died-absent |
| 3 | 0 | single | window | large | 122.1 | 122.1 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 4 | 0 | single | early | tiny | 3.5 | 3.5 | none (3) | staged,.allocation- | not logged | died-absent |
| 5 | 0 | single | late | small | 60.4 | 60.4 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 6 | 0 | single | over-limit | over | 6.8 | 6.8 | none (3) | untouched | not logged | died-absent |
| 7 | 0 | single | early | tiny | 17.9 | 17.9 | none (3) | staged,.allocation- | not logged | died-absent |
| 8 | 0 | single | window | tiny | 38.7 | 38.7 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 9 | 0 | single | early | small | 27.9 | 27.9 | none (3) | frontier-advanced | not logged | died-absent |
| 10 | 0 | single | late | medium | 109.1 | 109.1 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 11 | 0 | single | early | small | 28.3 | 28.3 | none (3) | staged,.stage- | not logged | died-absent |
| 12 | 0 | single | mid-article | medium | 3.7 | 3.7 | none (3) | untouched | not logged | died-absent |
| 13 | 0 | single | window | tiny | 22.6 | 22.6 | none (3) | staged,.stage- | not logged | died-absent |
| 14 | 0 | single | window | large | 136.3 | 136.3 | none (3) | frontier-advanced | not logged | died-absent |
| 15 | 0 | single | window | medium | 87.2 | 87.2 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 16 | 0 | concurrent | early | small,small | 0.2 | 0.2 | none (3) / none (3) | untouched | not logged; not logged | died-absent, died-absent |
| 17 | 0 | single | late | large | 220.1 | 220.1 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 18 | 0 | concurrent | window | large,medium | 133.5 | 133.5 | none (3) / 240 article received OK (0) | linked(1),no-stage | not logged; accepted post logged | died-absent, 240-identical |
| 19 | 0 | single | window | tiny | 22.8 | 22.8 | none (3) | staged,.allocation- | not logged | died-absent |
| 20 | 0 | concurrent | window | large,medium | 128.5 | 128.5 | none (3) / 240 article received OK (0) | linked(1),no-stage | not logged; accepted post logged | died-absent, 240-identical |
| 21 | 0 | single | mid-article | medium | 3.7 | 3.7 | none (3) | untouched | not logged | died-absent |
| 22 | 0 | single | late | medium | 128.8 | 128.8 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 23 | 0 | single | window | tiny | 42.0 | 42.0 | none (3) | frontier-advanced | not logged | died-absent |
| 24 | 0 | single | window | medium | 68.7 | 68.7 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 25 | 0 | single | mid-article | medium | 13.5 | 13.5 | none (3) | untouched | not logged | died-absent |
| 26 | 0 | single | window | medium | 106.6 | 106.6 | none (3) | staged,.stage- | not logged | died-absent |
| 27 | 0 | single | window | tiny | 44.9 | 44.9 | none (3) | staged,.allocation- | not logged | died-absent |
| 28 | 0 | single | over-limit | over | 7.6 | 7.6 | none (3) | untouched | not logged | died-absent |
| 29 | 0 | concurrent | window | large,tiny | 153.7 | 153.7 | none (3) / 240 article received OK (0) | linked(1),no-stage | not logged; accepted post logged | died-absent, 240-identical |
| 30 | 0 | single | window | large | 136.8 | 136.8 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 31 | 0 | single | window | small | 32.7 | 32.7 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 32 | 0 | single | window | medium | 76.1 | 76.1 | none (3) | frontier-advanced | not logged | died-absent |
| 33 | 0 | single | window | large | 118.3 | 118.3 | none (3) | frontier-advanced | not logged | died-absent |
| 34 | 0 | concurrent | window | tiny,medium | 89.0 | 89.0 | none (3) / 240 article received OK (0) | linked(1),no-stage | not logged; accepted post logged | died-absent, 240-identical |
| 35 | 0 | single | window | tiny | 24.3 | 24.3 | none (3) | staged,.allocation- | not logged | died-absent |
| 36 | 0 | single | window | small | 50.8 | 50.8 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 37 | 0 | single | over-limit | over | 10.1 | 10.1 | none (3) | untouched | not logged | died-absent |
| 38 | 0 | single | window | large | 111.9 | 111.9 | none (3) | staged,.stage- | not logged | died-absent |
| 39 | 0 | single | window | tiny | 29.1 | 29.1 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 40 | 0 | single | late | tiny | 56.6 | 56.6 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 41 | 0 | single | window | large | 126.4 | 126.4 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 42 | 0 | single | late | medium | 135.1 | 135.1 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 43 | 0 | concurrent | window | medium,large | 124.8 | 124.8 | 240 article received OK (0) / none (3) | linked(1),no-stage | accepted post logged; not logged | 240-identical, died-absent |
| 44 | 0 | concurrent | late | small,tiny | 79.8 | 79.8 | 240 article received OK (0) / none (3) | linked(1),.stage- | accepted post logged; not logged | 240-identical, died-absent |
| 45 | 0 | single | window | medium | 85.1 | 85.1 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 46 | 0 | concurrent | early | large,small | 3.5 | 3.5 | none (3) / none (3) | untouched | not logged; not logged | died-absent, died-absent |
| 47 | 0 | single | early | small | 19.1 | 19.1 | none (3) | frontier-advanced | not logged | died-absent |
| 48 | 0 | single | early | small | 7.5 | 7.5 | none (3) | staged,.allocation- | not logged | died-absent |
| 49 | 0 | single | early | large | 103.6 | 103.6 | none (3) | staged,.stage- | not logged | died-absent |
| 50 | 0 | single | late | tiny | 63.7 | 63.7 | none (3) | staged,.stage- | not logged | died-absent |
| 51 | 0 | single | over-limit | over | 4.8 | 4.8 | none (3) | untouched | not logged | died-absent |
| 52 | 0 | single | early | large | 79.6 | 79.6 | none (3) | frontier-advanced | not logged | died-absent |
| 53 | 0 | single | late | tiny | 60.4 | 60.4 | none (3) | frontier-advanced | not logged | died-absent |
| 54 | 1 | single | mid-article | small | 4.5 | 4.5 | none (3) | untouched | not logged | died-absent |
| 55 | 1 | single | window | tiny | 31.5 | 31.5 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 56 | 1 | single | early | large | 42.7 | 42.7 | none (3) | untouched | not logged | died-absent |
| 57 | 1 | single | early | tiny | 6.6 | 6.6 | none (3) | staged,.allocation- | not logged | died-absent |
| 58 | 1 | single | mid-article | large | 1.9 | 1.9 | none (3) | untouched | not logged | died-absent |
| 59 | 1 | single | window | medium | 81.1 | 81.1 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 60 | 1 | single | early | tiny | 13.2 | 13.2 | none (3) | staged,.allocation- | not logged | died-absent |
| 61 | 1 | single | window | large | 139.8 | 139.8 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 62 | 1 | single | window | tiny | 36.4 | 36.4 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 63 | 1 | single | over-limit | over | 21.2 | 21.2 | 441 posting failed; the arti (1) | untouched | not logged | refused |
| 64 | 1 | single | window | tiny | 33.2 | 33.2 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 65 | 1 | single | early | large | 42.4 | 42.4 | none (3) | untouched | not logged | died-absent |
| 66 | 1 | single | window | tiny | 44.2 | 44.2 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 67 | 1 | single | early | medium | 29.0 | 29.0 | none (3) | staged,.allocation- | not logged | died-absent |
| 68 | 1 | concurrent | window | small,medium | 77.3 | 77.3 | 240 article received OK (0) / none (3) | linked(1),.allocation- | accepted post logged; not logged | 240-identical, died-absent |
| 69 | 1 | single | late | medium | 127.2 | 127.2 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 70 | 1 | single | mid-article | large | 16.3 | 16.3 | none (3) | untouched | not logged | died-absent |
| 71 | 1 | single | mid-article | medium | 5.3 | 5.3 | none (3) | untouched | not logged | died-absent |
| 72 | 1 | single | early | large | 67.2 | 67.2 | none (3) | frontier-advanced | not logged | died-absent |
| 73 | 1 | single | window | small | 49.1 | 49.1 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 74 | 1 | single | window | tiny | 30.7 | 30.7 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 75 | 1 | single | late | medium | 135.9 | 135.9 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 76 | 1 | single | window | large | 146.6 | 146.6 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 77 | 1 | concurrent | late | large,medium | 192.4 | 192.4 | 240 article received OK (0) / none (3) | linked(1),no-stage | accepted post logged; not logged | 240-identical, died-absent |
| 78 | 1 | single | late | medium | 140.8 | 140.8 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 79 | 1 | single | early | small | 11.9 | 11.9 | none (3) | staged,.allocation- | not logged | died-absent |
| 80 | 1 | single | early | large | 58.1 | 58.1 | none (3) | staged,.allocation- | not logged | died-absent |
| 81 | 1 | single | mid-article | small | 17.1 | 17.1 | none (3) | untouched | not logged | died-absent |
| 82 | 1 | single | late | medium | 132.4 | 132.4 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 83 | 1 | single | window | medium | 93.3 | 93.3 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 84 | 1 | single | late | medium | 134.3 | 134.3 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 85 | 1 | single | early | large | 27.9 | 27.9 | none (3) | untouched | not logged | died-absent |
| 86 | 1 | single | early | small | 6.2 | 6.2 | none (3) | staged,.allocation- | not logged | died-absent |
| 87 | 1 | single | window | medium | 74.8 | 74.8 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 88 | 1 | single | early | large | 76.7 | 76.7 | none (3) | frontier-advanced | not logged | died-absent |
| 89 | 1 | single | window | large | 146.0 | 146.0 | none (3) | linked(1),no-stage | not logged | died-present-identical |

## Failures: 0


judge rc=0
