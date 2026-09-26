# /tank/fn/scratch/qual-69046a76/campaign/pk-run.json

stores 2 (closed and swept: [0, 1])

seed 3; 90 iterations (80 single, 10 concurrent); 206 POSTs in the ledger; 206 final articles present; 92 owner pids, all gone: True

calibration medians (ms from terminator sent): {"tiny": {".allocation-gone": 8.1, ".allocation-seen": 0.3, ".stage-gone": 33.2, ".stage-seen": 16.8, "frontier": 8.1, "reply": 58.7, "stage": 0.3, "stage_cleared": 8.1, "txn": 24.8}, "small": {".allocation-gone": 9.3, ".allocation-seen": 1.3, ".stage-gone": 34.4, ".stage-seen": 18.1, "frontier": 9.3, "reply": 59.9, "stage": 1.3, "stage_cleared": 9.3, "txn": 26.0}, "medium": {".allocation-gone": 12.1, ".allocation-seen": 4.9, ".stage-gone": 43.5, ".stage-seen": 22.2, "frontier": 12.1, "reply": 69.2, "stage": 4.9, "stage_cleared": 12.1, "txn": 36.2}, "large": {".allocation-gone": 19.4, ".allocation-seen": 11.7, ".stage-gone": 49.5, ".stage-seen": 31.4, "frontier": 19.4, "reply": 75.7, "stage": 11.7, "stage_cleared": 19.4, "txn": 41.5}, "over": {".allocation-gone": 25.4, ".allocation-seen": 16.0, ".stage-gone": 77.1, ".stage-seen": 40.0, "frontier": 25.4, "reply": 103.5, "stage": 16.0, "stage_cleared": 25.4, "txn": 68.4}}

## Verdicts

- 240-identical: 120
- died-absent: 53
- died-present-identical: 27
- refused: 0
- torn: 0
- lost-240: 0
- reused-number: 0
- died-absent-resubmit-failed: 6

## Verdicts of the killed POSTs only

| kill kind | verdict | POSTs |
|---|---|---|
| concurrent | 240-identical | 2 |
| concurrent | died-absent | 13 |
| concurrent | died-present-identical | 5 |
| single | 240-identical | 12 |
| single | died-absent | 40 |
| single | died-absent-resubmit-failed | 6 |
| single | died-present-identical | 22 |

## Client exit codes by reply

- rc 0: ['240 article received OK']
- rc 1: ['441 posting failed; this article is already stored here']
- rc 3: ['<no reply>']

## Kill band against the store state at death

| band | store state at death | kills |
|---|---|---|
| early | frontier-advanced | 6 |
| early | staged,.allocation- | 8 |
| early | staged,.stage- | 2 |
| early | untouched | 5 |
| late | linked(1),.stage- | 1 |
| late | linked(1),no-stage | 10 |
| late | linked(2),.stage- | 1 |
| late | staged,.stage- | 4 |
| mid-article | untouched | 8 |
| over-limit | frontier-advanced | 1 |
| over-limit | untouched | 5 |
| window | frontier-advanced | 3 |
| window | linked(1),.stage- | 10 |
| window | linked(1),no-stage | 18 |
| window | staged,.allocation- | 1 |
| window | staged,.stage- | 7 |

## Kill instants against the phase reached

| store state at death | owner log at death | kills | killed at ms (min to max) |
|---|---|---|---|
| untouched | not logged; not logged | 2 | 0.1 to 1.2 |
| untouched | not logged | 16 | 1.9 to 26.5 |
| staged,.allocation- | not logged | 9 | 3.6 to 52.6 |
| frontier-advanced | not logged | 10 | 6.7 to 70.8 |
| staged,.stage- | not logged | 11 | 18.4 to 90.3 |
| linked(1),.stage- | not logged | 9 | 24.1 to 72.8 |
| linked(1),no-stage | not logged | 13 | 34.5 to 85.0 |
| staged,.stage- | not logged; not logged | 2 | 46.1 to 96.2 |
| linked(1),no-stage | not logged; not logged | 2 | 51.6 to 58.8 |
| linked(1),.stage- | not logged; not logged | 2 | 54.7 to 55.9 |
| linked(1),no-stage | accepted post logged | 12 | 58.8 to 110.2 |
| linked(1),no-stage | not logged; accepted post logged | 1 | 75.4 to 75.4 |
| linked(2),.stage- | accepted post logged; not logged | 1 | 85.2 to 85.2 |

## Per kill

| # | store | kind | band | sizes | scheduled ms | killed at ms | replies (rc) | store at death | owner log at death | verdict |
|---|---|---|---|---|---|---|---|---|---|---|
| 0 | 0 | single | late | small | 87.2 | 87.2 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 1 | 0 | single | window | small | 58.8 | 58.8 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 2 | 0 | single | over-limit | over | 26.5 | 26.5 | none (3) | untouched | not logged | died-absent-resubmit-failed |
| 3 | 0 | single | window | large | 49.4 | 49.4 | none (3) | frontier-advanced | not logged | died-absent |
| 4 | 0 | single | early | tiny | 3.6 | 3.6 | none (3) | staged,.allocation- | not logged | died-absent |
| 5 | 0 | single | late | small | 64.5 | 64.5 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 6 | 0 | single | over-limit | over | 6.8 | 6.8 | none (3) | untouched | not logged | died-absent-resubmit-failed |
| 7 | 0 | single | early | tiny | 18.4 | 18.4 | none (3) | staged,.stage- | not logged | died-absent |
| 8 | 0 | single | window | tiny | 50.4 | 50.5 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 9 | 0 | single | early | small | 20.3 | 20.3 | none (3) | frontier-advanced | not logged | died-absent |
| 10 | 0 | single | late | medium | 72.8 | 72.8 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 11 | 0 | single | early | small | 20.6 | 20.6 | none (3) | staged,.stage- | not logged | died-absent |
| 12 | 0 | single | mid-article | medium | 3.7 | 3.7 | none (3) | untouched | not logged | died-absent |
| 13 | 0 | single | window | tiny | 23.8 | 23.8 | none (3) | staged,.stage- | not logged | died-absent |
| 14 | 0 | single | window | large | 61.1 | 61.1 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 15 | 0 | single | window | medium | 54.4 | 54.4 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 16 | 0 | concurrent | early | small,small | 0.1 | 0.1 | none (3) / none (3) | untouched | not logged; not logged | died-absent, died-absent |
| 17 | 0 | single | late | large | 110.2 | 110.2 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 18 | 0 | concurrent | window | large,medium | 58.8 | 58.8 | none (3) / none (3) | linked(1),no-stage | not logged; not logged | died-absent, died-present-identical |
| 19 | 0 | single | window | tiny | 24.1 | 24.1 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 20 | 0 | concurrent | window | large,medium | 54.7 | 54.7 | none (3) / none (3) | linked(1),.stage- | not logged; not logged | died-absent, died-present-identical |
| 21 | 0 | single | mid-article | medium | 3.7 | 3.7 | none (3) | untouched | not logged | died-absent |
| 22 | 0 | single | late | medium | 86.0 | 86.0 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 23 | 0 | single | window | tiny | 56.1 | 56.1 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 24 | 0 | single | window | medium | 38.8 | 38.8 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 25 | 0 | single | mid-article | medium | 13.5 | 13.5 | none (3) | untouched | not logged | died-absent |
| 26 | 0 | single | window | medium | 70.8 | 70.8 | none (3) | frontier-advanced | not logged | died-absent |
| 27 | 0 | single | window | tiny | 60.9 | 60.9 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 28 | 0 | single | over-limit | over | 7.6 | 7.6 | none (3) | untouched | not logged | died-absent-resubmit-failed |
| 29 | 0 | concurrent | window | large,tiny | 75.4 | 75.4 | none (3) / 240 article received OK (0) | linked(1),no-stage | not logged; accepted post logged | died-absent, 240-identical |
| 30 | 0 | single | window | large | 61.5 | 61.5 | none (3) | frontier-advanced | not logged | died-absent |
| 31 | 0 | single | window | small | 24.2 | 24.2 | none (3) | staged,.stage- | not logged | died-absent |
| 32 | 0 | single | window | medium | 45.0 | 45.0 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 33 | 0 | single | window | large | 46.3 | 46.3 | none (3) | staged,.stage- | not logged | died-absent |
| 34 | 0 | concurrent | window | tiny,medium | 55.9 | 55.9 | none (3) / none (3) | linked(1),.stage- | not logged; not logged | died-absent, died-present-identical |
| 35 | 0 | single | window | tiny | 26.6 | 26.6 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 36 | 0 | single | window | small | 51.0 | 51.0 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 37 | 0 | single | over-limit | over | 10.1 | 10.1 | none (3) | untouched | not logged | died-absent-resubmit-failed |
| 38 | 0 | single | window | large | 41.0 | 41.0 | none (3) | staged,.stage- | not logged | died-absent |
| 39 | 0 | single | window | tiny | 34.5 | 34.5 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 40 | 0 | single | late | tiny | 76.7 | 76.7 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 41 | 0 | single | window | large | 52.9 | 52.9 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 42 | 0 | single | late | medium | 90.3 | 90.3 | none (3) | staged,.stage- | not logged | died-absent |
| 43 | 0 | concurrent | window | medium,large | 51.6 | 51.6 | none (3) / none (3) | linked(1),no-stage | not logged; not logged | died-present-identical, died-absent |
| 44 | 0 | concurrent | late | small,tiny | 85.2 | 85.2 | 240 article received OK (0) / none (3) | linked(2),.stage- | accepted post logged; not logged | 240-identical, died-present-identical |
| 45 | 1 | single | window | medium | 52.6 | 52.6 | none (3) | staged,.allocation- | not logged | died-absent |
| 46 | 1 | concurrent | early | large,small | 1.2 | 1.2 | none (3) / none (3) | untouched | not logged; not logged | died-absent, died-absent |
| 47 | 1 | single | early | small | 13.9 | 13.9 | none (3) | frontier-advanced | not logged | died-absent |
| 48 | 1 | single | early | small | 5.4 | 5.4 | none (3) | staged,.allocation- | not logged | died-absent |
| 49 | 1 | single | early | large | 36.0 | 36.0 | none (3) | frontier-advanced | not logged | died-absent |
| 50 | 1 | single | late | tiny | 86.3 | 86.3 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 51 | 1 | single | over-limit | over | 4.8 | 4.8 | none (3) | untouched | not logged | died-absent-resubmit-failed |
| 52 | 1 | single | early | large | 27.7 | 27.7 | none (3) | staged,.allocation- | not logged | died-absent |
| 53 | 1 | single | late | tiny | 81.8 | 81.8 | none (3) | staged,.stage- | not logged | died-absent |
| 54 | 1 | single | mid-article | small | 4.5 | 4.5 | none (3) | untouched | not logged | died-absent |
| 55 | 1 | single | window | tiny | 38.5 | 38.5 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 56 | 1 | single | early | large | 14.8 | 14.8 | none (3) | untouched | not logged | died-absent |
| 57 | 1 | single | early | tiny | 6.7 | 6.7 | none (3) | frontier-advanced | not logged | died-absent |
| 58 | 1 | single | mid-article | large | 1.9 | 1.9 | none (3) | untouched | not logged | died-absent |
| 59 | 1 | single | window | medium | 49.3 | 49.3 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 60 | 1 | single | early | tiny | 13.5 | 13.5 | none (3) | frontier-advanced | not logged | died-absent |
| 61 | 1 | single | window | large | 63.9 | 63.9 | none (3) | staged,.stage- | not logged | died-absent |
| 62 | 1 | single | window | tiny | 46.8 | 46.8 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 63 | 1 | single | over-limit | over | 21.2 | 21.2 | none (3) | frontier-advanced | not logged | died-absent-resubmit-failed |
| 64 | 1 | single | window | tiny | 41.3 | 41.3 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 65 | 1 | single | early | large | 14.7 | 14.7 | none (3) | untouched | not logged | died-absent |
| 66 | 1 | single | window | tiny | 59.7 | 59.7 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 67 | 1 | single | early | medium | 15.4 | 15.4 | none (3) | staged,.allocation- | not logged | died-absent |
| 68 | 1 | concurrent | window | small,medium | 46.1 | 46.1 | none (3) / none (3) | staged,.stage- | not logged; not logged | died-absent, died-absent |
| 69 | 1 | single | late | medium | 85.0 | 85.0 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 70 | 1 | single | mid-article | large | 16.3 | 16.3 | none (3) | untouched | not logged | died-absent |
| 71 | 1 | single | mid-article | medium | 5.3 | 5.3 | none (3) | untouched | not logged | died-absent |
| 72 | 1 | single | early | large | 23.4 | 23.4 | none (3) | staged,.allocation- | not logged | died-absent |
| 73 | 1 | single | window | small | 48.4 | 48.4 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 74 | 1 | single | window | tiny | 37.2 | 37.2 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 75 | 1 | single | late | medium | 90.8 | 90.8 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 76 | 1 | single | window | large | 69.5 | 69.5 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 77 | 1 | concurrent | late | large,medium | 96.2 | 96.2 | none (3) / none (3) | staged,.stage- | not logged; not logged | died-absent, died-absent |
| 78 | 1 | single | late | medium | 94.1 | 94.1 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 79 | 1 | single | early | small | 8.7 | 8.7 | none (3) | staged,.allocation- | not logged | died-absent |
| 80 | 1 | single | early | large | 20.2 | 20.2 | none (3) | staged,.allocation- | not logged | died-absent |
| 81 | 1 | single | mid-article | small | 17.1 | 17.1 | none (3) | untouched | not logged | died-absent |
| 82 | 1 | single | late | medium | 88.5 | 88.5 | none (3) | staged,.stage- | not logged | died-absent |
| 83 | 1 | single | window | medium | 59.6 | 59.6 | none (3) | staged,.stage- | not logged | died-absent |
| 84 | 1 | single | late | medium | 89.8 | 89.8 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 85 | 1 | single | early | large | 9.7 | 9.7 | none (3) | untouched | not logged | died-absent |
| 86 | 1 | single | early | small | 4.5 | 4.5 | none (3) | staged,.allocation- | not logged | died-absent |
| 87 | 1 | single | window | medium | 43.9 | 43.9 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 88 | 1 | single | early | large | 26.7 | 26.7 | none (3) | frontier-advanced | not logged | died-absent |
| 89 | 1 | single | window | large | 69.1 | 69.1 | none (3) | linked(1),no-stage | not logged | died-present-identical |

## Failures: 6

- iteration 2 <pk-3-0021@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 0, 'reply': '240 article received OK\r\n', 'new_transactions': 1}
- iteration 6 <pk-3-0029@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 0, 'reply': '240 article received OK\r\n', 'new_transactions': 1}
- iteration 28 <pk-3-0074@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 0, 'reply': '240 article received OK\r\n', 'new_transactions': 1}
- iteration 37 <pk-3-0096@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 0, 'reply': '240 article received OK\r\n', 'new_transactions': 1}
- iteration 51 <pk-3-0128@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 0, 'reply': '240 article received OK\r\n', 'new_transactions': 1}
- iteration 63 <pk-3-0148@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 0, 'reply': '240 article received OK\r\n', 'new_transactions': 1}

judge rc=1
