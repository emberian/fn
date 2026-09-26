# /tank/fn/scratch/qual-b6759850/campaign/pk-run.json

stores 2 (closed and swept: [0, 1])

seed 3; 90 iterations (80 single, 10 concurrent); 206 POSTs in the ledger; 206 final articles present; 92 owner pids, all gone: True

calibration medians (ms from terminator sent): {"tiny": {".allocation-gone": 26.4, ".allocation-seen": 0.5, ".stage-gone": 213.9, ".stage-seen": 135.8, "frontier": 26.4, "reply": 318.5, "stage": 0.5, "stage_cleared": 26.4, "txn": 176.4}, "small": {".allocation-gone": 51.1, ".allocation-seen": 1.5, ".stage-gone": 189.3, ".stage-seen": 105.9, "frontier": 51.1, "reply": 302.1, "stage": 1.5, "stage_cleared": 51.1, "txn": 138.7}, "medium": {".allocation-gone": 47.3, ".allocation-seen": 7.9, ".stage-gone": 164.4, ".stage-seen": 83.1, "frontier": 47.3, "reply": 231.6, "stage": 7.9, "stage_cleared": 47.3, "txn": 143.3}, "large": {".allocation-gone": 37.6, ".allocation-seen": 15.8, ".stage-gone": 118.1, ".stage-seen": 60.0, "frontier": 37.6, "reply": 255.9, "stage": 15.8, "stage_cleared": 37.6, "txn": 88.7}, "over": {".allocation-gone": 84.5, ".allocation-seen": 13.5, ".stage-gone": 243.4, ".stage-seen": 112.7, "frontier": 84.5, "reply": 402.7, "stage": 13.5, "stage_cleared": 84.5, "txn": 164.0}}

## Verdicts

- 240-identical: 135
- died-absent: 37
- died-present-identical: 28
- refused: 0
- torn: 0
- lost-240: 0
- reused-number: 0
- died-absent-resubmit-failed: 6

## Verdicts of the killed POSTs only

| kill kind | verdict | POSTs |
|---|---|---|
| concurrent | 240-identical | 4 |
| concurrent | died-absent | 11 |
| concurrent | died-present-identical | 5 |
| single | 240-identical | 25 |
| single | died-absent | 26 |
| single | died-absent-resubmit-failed | 6 |
| single | died-present-identical | 23 |

## Client exit codes by reply

- rc 0: ['240 article received OK']
- rc 1: ['441 posting failed; this article is already stored here']
- rc 3: ['<no reply>']

## Kill band against the store state at death

| band | store state at death | kills |
|---|---|---|
| early | frontier-advanced | 6 |
| early | linked(1),.stage- | 1 |
| early | linked(1),no-stage | 3 |
| early | staged,.allocation- | 7 |
| early | staged,.stage- | 3 |
| early | untouched | 1 |
| late | linked(1),.stage- | 1 |
| late | linked(1),no-stage | 14 |
| late | linked(2),no-stage | 1 |
| mid-article | untouched | 8 |
| over-limit | staged,.allocation- | 1 |
| over-limit | untouched | 5 |
| window | frontier-advanced | 1 |
| window | linked(1),.allocation- | 1 |
| window | linked(1),.stage- | 10 |
| window | linked(1),no-stage | 23 |
| window | linked(2),no-stage | 1 |
| window | staged,.stage- | 3 |

## Kill instants against the phase reached

| store state at death | owner log at death | kills | killed at ms (min to max) |
|---|---|---|---|
| untouched | not logged; not logged | 1 | 0.6 to 0.6 |
| untouched | not logged | 13 | 1.9 to 26.5 |
| staged,.allocation- | not logged; not logged | 1 | 4.0 to 4.0 |
| staged,.allocation- | not logged | 7 | 20.7 to 43.2 |
| frontier-advanced | not logged | 7 | 23.9 to 128.5 |
| staged,.stage- | not logged | 5 | 46.2 to 184.5 |
| linked(1),no-stage | not logged | 13 | 95.7 to 274.9 |
| linked(1),.stage- | not logged | 10 | 130.8 to 286.5 |
| linked(1),.stage- | not logged; not logged | 2 | 141.9 to 254.7 |
| staged,.stage- | not logged; not logged | 1 | 155.0 to 155.0 |
| linked(1),no-stage | not logged; not logged | 2 | 172.7 to 315.7 |
| linked(1),no-stage | accepted post logged | 25 | 176.4 to 446.1 |
| linked(2),no-stage | accepted post logged; not logged | 1 | 186.2 to 186.2 |
| linked(1),.allocation- | not logged; accepted post logged | 1 | 308.6 to 308.6 |
| linked(2),no-stage | accepted post logged; accepted post logged | 1 | 432.5 to 432.5 |

## Per kill

| # | store | kind | band | sizes | scheduled ms | killed at ms | replies (rc) | store at death | owner log at death | verdict |
|---|---|---|---|---|---|---|---|---|---|---|
| 0 | 0 | single | late | small | 420.1 | 420.1 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 1 | 0 | single | window | small | 286.5 | 286.5 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 2 | 0 | single | over-limit | over | 26.5 | 26.5 | none (3) | untouched | not logged | died-absent-resubmit-failed |
| 3 | 0 | single | window | large | 132.1 | 132.1 | none (3) | staged,.stage- | not logged | died-absent |
| 4 | 0 | single | early | tiny | 25.3 | 25.3 | none (3) | staged,.allocation- | not logged | died-absent |
| 5 | 0 | single | late | small | 312.5 | 312.5 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 6 | 0 | single | over-limit | over | 6.8 | 6.8 | none (3) | untouched | not logged | died-absent-resubmit-failed |
| 7 | 0 | single | early | tiny | 130.8 | 130.8 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 8 | 0 | single | window | tiny | 274.9 | 274.9 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 9 | 0 | single | early | small | 108.4 | 108.4 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 10 | 0 | single | late | medium | 236.5 | 236.5 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 11 | 0 | single | early | small | 109.7 | 109.7 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 12 | 0 | single | mid-article | medium | 3.7 | 3.7 | none (3) | untouched | not logged | died-absent |
| 13 | 0 | single | window | tiny | 164.6 | 164.6 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 14 | 0 | single | window | large | 182.6 | 182.6 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 15 | 0 | single | window | medium | 187.1 | 187.1 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 16 | 0 | concurrent | early | small,small | 0.6 | 0.6 | none (3) / none (3) | untouched | not logged; not logged | died-absent, died-absent |
| 17 | 0 | single | late | large | 361.0 | 361.0 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 18 | 0 | concurrent | window | large,medium | 172.7 | 172.7 | none (3) / none (3) | linked(1),no-stage | not logged; not logged | died-absent, died-present-identical |
| 19 | 0 | single | window | tiny | 166.0 | 166.0 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 20 | 0 | concurrent | window | large,medium | 155.0 | 155.0 | none (3) / none (3) | staged,.stage- | not logged; not logged | died-absent, died-absent |
| 21 | 0 | single | mid-article | medium | 3.7 | 3.7 | none (3) | untouched | not logged | died-absent |
| 22 | 0 | single | late | medium | 278.7 | 278.7 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 23 | 0 | single | window | tiny | 298.1 | 298.1 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 24 | 0 | single | window | medium | 145.4 | 145.4 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 25 | 0 | single | mid-article | medium | 13.5 | 13.5 | none (3) | untouched | not logged | died-absent |
| 26 | 0 | single | window | medium | 230.9 | 230.9 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 27 | 0 | single | window | tiny | 318.2 | 318.2 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 28 | 0 | single | over-limit | over | 7.6 | 7.6 | none (3) | untouched | not logged | died-absent-resubmit-failed |
| 29 | 0 | concurrent | window | large,tiny | 308.6 | 308.6 | none (3) / 240 article received OK (0) | linked(1),.allocation- | not logged; accepted post logged | died-absent, 240-identical |
| 30 | 0 | single | window | large | 184.5 | 184.5 | none (3) | staged,.stage- | not logged | died-absent |
| 31 | 0 | single | window | small | 128.5 | 128.5 | none (3) | frontier-advanced | not logged | died-absent |
| 32 | 0 | single | window | medium | 162.1 | 162.1 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 33 | 0 | single | window | large | 118.7 | 118.7 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 34 | 0 | concurrent | window | tiny,medium | 254.7 | 254.7 | none (3) / none (3) | linked(1),.stage- | not logged; not logged | died-present-identical, died-absent |
| 35 | 0 | single | window | tiny | 176.4 | 176.4 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 36 | 0 | single | window | small | 250.8 | 250.8 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 37 | 0 | single | over-limit | over | 10.1 | 10.1 | none (3) | untouched | not logged | died-absent-resubmit-failed |
| 38 | 0 | single | window | large | 95.7 | 95.7 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 39 | 0 | single | window | tiny | 209.2 | 209.2 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 40 | 0 | single | late | tiny | 397.8 | 397.8 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 41 | 0 | single | window | large | 147.3 | 147.3 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 42 | 0 | single | late | medium | 292.2 | 292.2 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 43 | 0 | concurrent | window | medium,large | 141.9 | 141.9 | none (3) / none (3) | linked(1),.stage- | not logged; not logged | died-present-identical, died-absent |
| 44 | 0 | concurrent | late | small,tiny | 432.5 | 432.5 | 240 article received OK (0) / 240 article received OK (0) | linked(2),no-stage | accepted post logged; accepted post logged | 240-identical, 240-identical |
| 45 | 1 | single | window | medium | 182.3 | 182.3 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 46 | 1 | concurrent | early | large,small | 4.0 | 4.0 | none (3) / none (3) | staged,.allocation- | not logged; not logged | died-absent, died-absent |
| 47 | 1 | single | early | small | 74.0 | 74.0 | none (3) | frontier-advanced | not logged | died-absent |
| 48 | 1 | single | early | small | 29.0 | 29.0 | none (3) | staged,.allocation- | not logged | died-absent |
| 49 | 1 | single | early | large | 77.0 | 77.0 | none (3) | staged,.stage- | not logged | died-absent |
| 50 | 1 | single | late | tiny | 446.1 | 446.1 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 51 | 1 | single | over-limit | over | 4.8 | 4.8 | none (3) | untouched | not logged | died-absent-resubmit-failed |
| 52 | 1 | single | early | large | 59.2 | 59.2 | none (3) | frontier-advanced | not logged | died-absent |
| 53 | 1 | single | late | tiny | 423.5 | 423.5 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 54 | 1 | single | mid-article | small | 4.5 | 4.5 | none (3) | untouched | not logged | died-absent |
| 55 | 1 | single | window | tiny | 225.6 | 225.6 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 56 | 1 | single | early | large | 31.7 | 31.7 | none (3) | staged,.allocation- | not logged | died-absent |
| 57 | 1 | single | early | tiny | 47.8 | 47.8 | none (3) | frontier-advanced | not logged | died-absent |
| 58 | 1 | single | mid-article | large | 1.9 | 1.9 | none (3) | untouched | not logged | died-absent |
| 59 | 1 | single | window | medium | 173.4 | 173.4 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 60 | 1 | single | early | tiny | 96.2 | 96.2 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 61 | 1 | single | window | large | 195.2 | 195.2 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 62 | 1 | single | window | tiny | 259.7 | 259.7 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 63 | 1 | single | over-limit | over | 21.2 | 21.2 | none (3) | staged,.allocation- | not logged | died-absent-resubmit-failed |
| 64 | 1 | single | window | tiny | 237.2 | 237.2 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 65 | 1 | single | early | large | 31.5 | 31.5 | none (3) | staged,.allocation- | not logged | died-absent |
| 66 | 1 | single | window | tiny | 313.2 | 313.2 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 67 | 1 | single | early | medium | 61.0 | 61.0 | none (3) | staged,.stage- | not logged | died-absent |
| 68 | 1 | concurrent | window | small,medium | 186.2 | 186.2 | 240 article received OK (0) / none (3) | linked(2),no-stage | accepted post logged; not logged | 240-identical, died-present-identical |
| 69 | 1 | single | late | medium | 275.4 | 275.4 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 70 | 1 | single | mid-article | large | 16.3 | 16.3 | none (3) | untouched | not logged | died-absent |
| 71 | 1 | single | mid-article | medium | 5.3 | 5.3 | none (3) | untouched | not logged | died-absent |
| 72 | 1 | single | early | large | 50.0 | 50.0 | none (3) | frontier-advanced | not logged | died-absent |
| 73 | 1 | single | window | small | 238.9 | 238.9 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 74 | 1 | single | window | tiny | 220.3 | 220.3 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 75 | 1 | single | late | medium | 294.0 | 294.0 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 76 | 1 | single | window | large | 219.3 | 219.3 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 77 | 1 | concurrent | late | large,medium | 315.7 | 315.7 | none (3) / none (3) | linked(1),no-stage | not logged; not logged | died-absent, died-present-identical |
| 78 | 1 | single | late | medium | 304.4 | 304.4 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 79 | 1 | single | early | small | 46.2 | 46.2 | none (3) | staged,.stage- | not logged | died-absent |
| 80 | 1 | single | early | large | 43.2 | 43.2 | none (3) | staged,.allocation- | not logged | died-absent |
| 81 | 1 | single | mid-article | small | 17.1 | 17.1 | none (3) | untouched | not logged | died-absent |
| 82 | 1 | single | late | medium | 286.5 | 286.5 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 83 | 1 | single | window | medium | 201.0 | 201.0 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 84 | 1 | single | late | medium | 290.7 | 290.7 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 85 | 1 | single | early | large | 20.7 | 20.7 | none (3) | staged,.allocation- | not logged | died-absent |
| 86 | 1 | single | early | small | 23.9 | 23.9 | none (3) | frontier-advanced | not logged | died-absent |
| 87 | 1 | single | window | medium | 159.0 | 159.0 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 88 | 1 | single | early | large | 57.0 | 57.0 | none (3) | frontier-advanced | not logged | died-absent |
| 89 | 1 | single | window | large | 217.5 | 217.5 | none (3) | linked(1),.stage- | not logged | died-present-identical |

## Failures: 6

- iteration 2 <pk-3-0021@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 0, 'reply': '240 article received OK\r\n', 'new_transactions': 1}
- iteration 6 <pk-3-0029@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 0, 'reply': '240 article received OK\r\n', 'new_transactions': 1}
- iteration 28 <pk-3-0074@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 0, 'reply': '240 article received OK\r\n', 'new_transactions': 1}
- iteration 37 <pk-3-0096@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 0, 'reply': '240 article received OK\r\n', 'new_transactions': 1}
- iteration 51 <pk-3-0128@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 0, 'reply': '240 article received OK\r\n', 'new_transactions': 1}
- iteration 63 <pk-3-0148@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 0, 'reply': '240 article received OK\r\n', 'new_transactions': 1}

judge rc=1
