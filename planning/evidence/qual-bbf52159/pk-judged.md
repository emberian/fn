# /tank/fn/scratch/qual-bbf52159/campaign/pk-run.json

stores 2 (closed and swept: [0, 1])

seed 3; 90 iterations (80 single, 10 concurrent); 206 POSTs in the ledger; 206 final articles present; 92 owner pids, all gone: True

calibration medians (ms from terminator sent): {"tiny": {".allocation-gone": 22.0, ".allocation-seen": 0.4, ".stage-gone": 88.2, ".stage-seen": 55.2, "frontier": 22.0, "reply": 138.6, "stage": 0.4, "stage_cleared": 22.0, "txn": 72.8}, "small": {".allocation-gone": 20.2, ".allocation-seen": 1.4, ".stage-gone": 79.8, ".stage-seen": 38.4, "frontier": 20.2, "reply": 144.8, "stage": 1.4, "stage_cleared": 20.2, "txn": 53.5}, "medium": {".allocation-gone": 27.9, ".allocation-seen": 4.7, ".stage-gone": 104.7, ".stage-seen": 47.7, "frontier": 27.9, "reply": 172.1, "stage": 4.7, "stage_cleared": 27.9, "txn": 84.4}, "large": {".allocation-gone": 34.3, ".allocation-seen": 13.9, ".stage-gone": 98.3, ".stage-seen": 57.0, "frontier": 34.3, "reply": 231.0, "stage": 13.9, "stage_cleared": 34.3, "txn": 80.7}, "over": {".allocation-gone": 47.1, ".allocation-seen": 17.0, ".stage-gone": 140.4, ".stage-seen": 77.3, "frontier": 47.1, "reply": 198.7, "stage": 17.0, "stage_cleared": 47.1, "txn": 115.1}}

## Verdicts

- 240-identical: 118
- died-absent: 51
- died-present-identical: 31
- refused: 0
- torn: 0
- lost-240: 0
- reused-number: 0
- died-absent-resubmit-failed: 6

## Verdicts of the killed POSTs only

| kill kind | verdict | POSTs |
|---|---|---|
| concurrent | 240-identical | 3 |
| concurrent | died-absent | 11 |
| concurrent | died-present-identical | 6 |
| single | 240-identical | 9 |
| single | died-absent | 40 |
| single | died-absent-resubmit-failed | 6 |
| single | died-present-identical | 25 |

## Client exit codes by reply

- rc 0: ['240 article received OK']
- rc 1: ['441 posting failed; this article is already stored here']
- rc 3: ['<no reply>']

## Kill band against the store state at death

| band | store state at death | kills |
|---|---|---|
| early | frontier-advanced | 6 |
| early | linked(1),.stage- | 1 |
| early | staged,.allocation- | 11 |
| early | staged,.stage- | 2 |
| early | untouched | 1 |
| late | linked(1),.stage- | 3 |
| late | linked(1),no-stage | 11 |
| late | linked(2),no-stage | 1 |
| late | staged,.stage- | 1 |
| mid-article | untouched | 8 |
| over-limit | staged,.allocation- | 1 |
| over-limit | untouched | 5 |
| window | frontier-advanced | 5 |
| window | linked(1),.stage- | 9 |
| window | linked(1),no-stage | 15 |
| window | linked(2),.stage- | 1 |
| window | staged,.stage- | 9 |

## Kill instants against the phase reached

| store state at death | owner log at death | kills | killed at ms (min to max) |
|---|---|---|---|
| untouched | not logged; not logged | 1 | 0.2 to 0.2 |
| untouched | not logged | 13 | 1.9 to 26.5 |
| staged,.allocation- | not logged; not logged | 1 | 2.3 to 2.3 |
| staged,.allocation- | not logged | 11 | 9.2 to 53.9 |
| frontier-advanced | not logged | 11 | 28.6 to 198.3 |
| staged,.stage- | not logged | 11 | 39.7 to 203.9 |
| linked(1),.stage- | not logged | 10 | 53.9 to 176.5 |
| linked(1),no-stage | not logged | 15 | 94.2 to 218.2 |
| linked(1),.stage- | not logged; not logged | 3 | 109.7 to 140.4 |
| linked(1),no-stage | accepted post logged | 9 | 111.2 to 326.3 |
| staged,.stage- | not logged; not logged | 1 | 128.5 to 128.5 |
| linked(1),no-stage | not logged; not logged | 2 | 156.3 to 199.3 |
| linked(2),.stage- | not logged; accepted post logged | 1 | 221.2 to 221.2 |
| linked(2),no-stage | accepted post logged; accepted post logged | 1 | 285.3 to 285.3 |

## Per kill

| # | store | kind | band | sizes | scheduled ms | killed at ms | replies (rc) | store at death | owner log at death | verdict |
|---|---|---|---|---|---|---|---|---|---|---|
| 0 | 0 | single | late | small | 203.9 | 203.9 | none (3) | staged,.stage- | not logged | died-absent |
| 1 | 0 | single | window | small | 137.5 | 137.5 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 2 | 0 | single | over-limit | over | 26.5 | 26.5 | none (3) | untouched | not logged | died-absent-resubmit-failed |
| 3 | 0 | single | window | large | 119.7 | 119.7 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 4 | 0 | single | early | tiny | 10.4 | 10.4 | none (3) | staged,.allocation- | not logged | died-absent |
| 5 | 0 | single | late | small | 151.4 | 151.4 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 6 | 0 | single | over-limit | over | 6.8 | 6.8 | none (3) | untouched | not logged | died-absent-resubmit-failed |
| 7 | 0 | single | early | tiny | 53.9 | 53.9 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 8 | 0 | single | window | tiny | 119.8 | 119.8 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 9 | 0 | single | early | small | 41.8 | 41.8 | none (3) | frontier-advanced | not logged | died-absent |
| 10 | 0 | single | late | medium | 176.5 | 176.5 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 11 | 0 | single | early | small | 42.3 | 42.3 | none (3) | frontier-advanced | not logged | died-absent |
| 12 | 0 | single | mid-article | medium | 3.7 | 3.7 | none (3) | untouched | not logged | died-absent |
| 13 | 0 | single | window | tiny | 68.2 | 68.2 | none (3) | staged,.stage- | not logged | died-absent |
| 14 | 0 | single | window | large | 165.3 | 165.3 | none (3) | staged,.stage- | not logged | died-absent |
| 15 | 0 | single | window | medium | 130.6 | 130.6 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 16 | 0 | concurrent | early | small,small | 0.2 | 0.2 | none (3) / none (3) | untouched | not logged; not logged | died-absent, died-absent |
| 17 | 0 | single | late | large | 326.3 | 326.3 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 18 | 0 | concurrent | window | large,medium | 156.3 | 156.3 | none (3) / none (3) | linked(1),no-stage | not logged; not logged | died-absent, died-present-identical |
| 19 | 0 | single | window | tiny | 68.9 | 68.9 | none (3) | frontier-advanced | not logged | died-absent |
| 20 | 0 | concurrent | window | large,medium | 140.4 | 140.4 | none (3) / none (3) | linked(1),.stage- | not logged; not logged | died-absent, died-present-identical |
| 21 | 0 | single | mid-article | medium | 3.7 | 3.7 | none (3) | untouched | not logged | died-absent |
| 22 | 0 | single | late | medium | 208.1 | 208.1 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 23 | 0 | single | window | tiny | 130.7 | 130.7 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 24 | 0 | single | window | medium | 91.5 | 91.5 | none (3) | staged,.stage- | not logged | died-absent |
| 25 | 0 | single | mid-article | medium | 13.5 | 13.5 | none (3) | untouched | not logged | died-absent |
| 26 | 0 | single | window | medium | 171.6 | 171.6 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 27 | 0 | single | window | tiny | 140.0 | 140.0 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 28 | 0 | single | over-limit | over | 7.6 | 7.6 | none (3) | untouched | not logged | died-absent-resubmit-failed |
| 29 | 0 | concurrent | window | large,tiny | 221.2 | 221.2 | none (3) / 240 article received OK (0) | linked(2),.stage- | not logged; accepted post logged | died-present-identical, 240-identical |
| 30 | 0 | single | window | large | 166.9 | 166.9 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 31 | 0 | single | window | small | 50.2 | 50.2 | none (3) | frontier-advanced | not logged | died-absent |
| 32 | 0 | single | window | medium | 107.1 | 107.1 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 33 | 0 | single | window | large | 107.7 | 107.7 | none (3) | staged,.stage- | not logged | died-absent |
| 34 | 0 | concurrent | window | tiny,medium | 134.4 | 134.4 | none (3) / none (3) | linked(1),.stage- | not logged; not logged | died-present-identical, died-absent |
| 35 | 0 | single | window | tiny | 73.7 | 73.7 | none (3) | staged,.stage- | not logged | died-absent |
| 36 | 0 | single | window | small | 117.8 | 117.8 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 37 | 0 | single | over-limit | over | 10.1 | 10.1 | none (3) | untouched | not logged | died-absent-resubmit-failed |
| 38 | 0 | single | window | large | 86.9 | 86.9 | none (3) | staged,.stage- | not logged | died-absent |
| 39 | 0 | single | window | tiny | 89.1 | 89.1 | none (3) | staged,.stage- | not logged | died-absent |
| 40 | 0 | single | late | tiny | 175.4 | 175.4 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 41 | 0 | single | window | large | 133.4 | 133.4 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 42 | 0 | single | late | medium | 218.2 | 218.2 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 43 | 0 | concurrent | window | medium,large | 128.5 | 128.5 | none (3) / none (3) | staged,.stage- | not logged; not logged | died-absent, died-absent |
| 44 | 0 | concurrent | late | small,tiny | 199.2 | 199.3 | none (3) / none (3) | linked(1),no-stage | not logged; not logged | died-absent, died-present-identical |
| 45 | 1 | single | window | medium | 126.1 | 126.1 | none (3) | staged,.stage- | not logged | died-absent |
| 46 | 1 | concurrent | early | large,small | 2.3 | 2.3 | none (3) / none (3) | staged,.allocation- | not logged; not logged | died-absent, died-absent |
| 47 | 1 | single | early | small | 28.6 | 28.6 | none (3) | frontier-advanced | not logged | died-absent |
| 48 | 1 | single | early | small | 11.2 | 11.2 | none (3) | staged,.allocation- | not logged | died-absent |
| 49 | 1 | single | early | large | 70.1 | 70.1 | none (3) | frontier-advanced | not logged | died-absent |
| 50 | 1 | single | late | tiny | 196.9 | 196.9 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 51 | 1 | single | over-limit | over | 4.8 | 4.8 | none (3) | untouched | not logged | died-absent-resubmit-failed |
| 52 | 1 | single | early | large | 53.9 | 53.9 | none (3) | staged,.allocation- | not logged | died-absent |
| 53 | 1 | single | late | tiny | 186.9 | 186.9 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 54 | 1 | single | mid-article | small | 4.5 | 4.5 | none (3) | untouched | not logged | died-absent |
| 55 | 1 | single | window | tiny | 96.7 | 96.7 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 56 | 1 | single | early | large | 28.9 | 28.9 | none (3) | staged,.allocation- | not logged | died-absent |
| 57 | 1 | single | early | tiny | 19.7 | 19.7 | none (3) | staged,.allocation- | not logged | died-absent |
| 58 | 1 | single | mid-article | large | 1.9 | 1.9 | none (3) | untouched | not logged | died-absent |
| 59 | 1 | single | window | medium | 117.7 | 117.7 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 60 | 1 | single | early | tiny | 39.7 | 39.7 | none (3) | staged,.stage- | not logged | died-absent |
| 61 | 1 | single | window | large | 176.5 | 176.5 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 62 | 1 | single | window | tiny | 112.7 | 112.7 | none (3) | frontier-advanced | not logged | died-absent |
| 63 | 1 | single | over-limit | over | 21.2 | 21.2 | none (3) | staged,.allocation- | not logged | died-absent-resubmit-failed |
| 64 | 1 | single | window | tiny | 102.2 | 102.2 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 65 | 1 | single | early | large | 28.7 | 28.7 | none (3) | staged,.allocation- | not logged | died-absent |
| 66 | 1 | single | window | tiny | 137.7 | 137.7 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 67 | 1 | single | early | medium | 35.9 | 35.9 | none (3) | staged,.allocation- | not logged | died-absent |
| 68 | 1 | concurrent | window | small,medium | 109.7 | 109.7 | none (3) / none (3) | linked(1),.stage- | not logged; not logged | died-present-identical, died-absent |
| 69 | 1 | single | late | medium | 205.6 | 205.6 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 70 | 1 | single | mid-article | large | 16.3 | 16.3 | none (3) | untouched | not logged | died-absent |
| 71 | 1 | single | mid-article | medium | 5.3 | 5.3 | none (3) | untouched | not logged | died-absent |
| 72 | 1 | single | early | large | 45.5 | 45.5 | none (3) | staged,.stage- | not logged | died-absent |
| 73 | 1 | single | window | small | 111.2 | 111.2 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 74 | 1 | single | window | tiny | 94.2 | 94.2 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 75 | 1 | single | late | medium | 219.5 | 219.5 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 76 | 1 | single | window | large | 198.3 | 198.3 | none (3) | frontier-advanced | not logged | died-absent |
| 77 | 1 | concurrent | late | large,medium | 285.3 | 285.3 | 240 article received OK (0) / 240 article received OK (0) | linked(2),no-stage | accepted post logged; accepted post logged | 240-identical, 240-identical |
| 78 | 1 | single | late | medium | 227.3 | 227.3 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 79 | 1 | single | early | small | 17.8 | 17.8 | none (3) | staged,.allocation- | not logged | died-absent |
| 80 | 1 | single | early | large | 39.3 | 39.3 | none (3) | frontier-advanced | not logged | died-absent |
| 81 | 1 | single | mid-article | small | 17.1 | 17.1 | none (3) | untouched | not logged | died-absent |
| 82 | 1 | single | late | medium | 213.9 | 213.9 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 83 | 1 | single | window | medium | 143.6 | 143.6 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 84 | 1 | single | late | medium | 217.0 | 217.0 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 85 | 1 | single | early | large | 18.8 | 18.8 | none (3) | staged,.allocation- | not logged | died-absent |
| 86 | 1 | single | early | small | 9.2 | 9.2 | none (3) | staged,.allocation- | not logged | died-absent |
| 87 | 1 | single | window | medium | 104.2 | 104.2 | none (3) | frontier-advanced | not logged | died-absent |
| 88 | 1 | single | early | large | 51.9 | 51.9 | none (3) | frontier-advanced | not logged | died-absent |
| 89 | 1 | single | window | large | 196.7 | 196.7 | none (3) | linked(1),no-stage | not logged | died-present-identical |

## Failures: 6

- iteration 2 <pk-3-0021@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 0, 'reply': '240 article received OK\r\n', 'new_transactions': 1}
- iteration 6 <pk-3-0029@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 0, 'reply': '240 article received OK\r\n', 'new_transactions': 1}
- iteration 28 <pk-3-0074@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 0, 'reply': '240 article received OK\r\n', 'new_transactions': 1}
- iteration 37 <pk-3-0096@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 0, 'reply': '240 article received OK\r\n', 'new_transactions': 1}
- iteration 51 <pk-3-0128@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 0, 'reply': '240 article received OK\r\n', 'new_transactions': 1}
- iteration 63 <pk-3-0148@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 0, 'reply': '240 article received OK\r\n', 'new_transactions': 1}

judge rc=1
