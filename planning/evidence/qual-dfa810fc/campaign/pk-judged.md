# /tank/fn/scratch/qual-dfa810fc/campaign/pk-run.json

stores 2 (closed and swept: [0, 1])

seed 3; 90 iterations (80 single, 10 concurrent); 206 POSTs in the ledger; 206 final articles present; 92 owner pids, all gone: True

calibration medians (ms from terminator sent): {"tiny": {".allocation-gone": 42.0, ".allocation-seen": 0.6, ".stage-gone": 134.0, ".stage-seen": 77.1, "frontier": 42.0, "reply": 217.8, "stage": 0.6, "stage_cleared": 42.0, "txn": 100.6}, "small": {".allocation-gone": 38.9, ".allocation-seen": 1.8, ".stage-gone": 188.7, ".stage-seen": 81.3, "frontier": 38.9, "reply": 322.6, "stage": 1.8, "stage_cleared": 38.9, "txn": 146.9}, "medium": {".allocation-gone": 59.0, ".allocation-seen": 9.8, ".stage-gone": 189.6, ".stage-seen": 103.4, "frontier": 59.0, "reply": 274.1, "stage": 9.8, "stage_cleared": 59.0, "txn": 167.3}, "large": {".allocation-gone": 75.7, ".allocation-seen": 22.3, ".stage-gone": 234.5, ".stage-seen": 116.2, "frontier": 75.7, "reply": 353.4, "stage": 22.3, "stage_cleared": 75.7, "txn": 158.9}, "over": {".allocation-gone": 64.2, ".allocation-seen": 28.6, ".stage-gone": 257.6, ".stage-seen": 110.8, "frontier": 64.2, "reply": 357.1, "stage": 28.6, "stage_cleared": 64.2, "txn": 181.7}}

## Verdicts

- 240-identical: 125
- died-absent: 45
- died-present-identical: 30
- refused: 0
- torn: 0
- lost-240: 0
- reused-number: 0
- died-absent-resubmit-failed: 6

## Verdicts of the killed POSTs only

| kill kind | verdict | POSTs |
|---|---|---|
| concurrent | 240-identical | 3 |
| concurrent | died-absent | 12 |
| concurrent | died-present-identical | 5 |
| single | 240-identical | 16 |
| single | died-absent | 33 |
| single | died-absent-resubmit-failed | 6 |
| single | died-present-identical | 25 |

## Client exit codes by reply

- rc 0: ['240 article received OK']
- rc 1: ['441 posting failed; this article is already stored here']
- rc 3: ['<no reply>']

## Kill band against the store state at death

| band | store state at death | kills |
|---|---|---|
| early | frontier-advanced | 7 |
| early | linked(1),.stage- | 1 |
| early | staged,.allocation- | 6 |
| early | staged,.stage- | 5 |
| early | untouched | 2 |
| late | linked(1),.stage- | 2 |
| late | linked(1),no-stage | 13 |
| late | linked(2),no-stage | 1 |
| mid-article | untouched | 8 |
| over-limit | staged,.allocation- | 1 |
| over-limit | untouched | 5 |
| window | frontier-advanced | 1 |
| window | linked(1),.allocation- | 1 |
| window | linked(1),.stage- | 9 |
| window | linked(1),no-stage | 19 |
| window | linked(2),.stage- | 1 |
| window | staged,.stage- | 8 |

## Kill instants against the phase reached

| store state at death | owner log at death | kills | killed at ms (min to max) |
|---|---|---|---|
| untouched | not logged; not logged | 2 | 0.6 to 4.6 |
| untouched | not logged | 13 | 1.9 to 26.5 |
| staged,.allocation- | not logged | 7 | 14.4 to 56.8 |
| staged,.stage- | not logged | 11 | 48.9 to 267.7 |
| frontier-advanced | not logged | 8 | 54.8 to 170.3 |
| linked(1),.stage- | not logged | 12 | 77.4 to 338.3 |
| linked(1),no-stage | not logged | 13 | 130.9 to 359.4 |
| staged,.stage- | not logged; not logged | 2 | 198.0 to 216.9 |
| linked(1),.allocation- | accepted post logged; not logged | 1 | 225.1 to 225.1 |
| linked(1),no-stage | not logged; not logged | 3 | 232.6 to 438.1 |
| linked(1),no-stage | accepted post logged | 16 | 236.8 to 496.5 |
| linked(2),.stage- | accepted post logged; not logged | 1 | 339.4 to 339.4 |
| linked(2),no-stage | not logged; accepted post logged | 1 | 434.3 to 434.3 |

## Per kill

| # | store | kind | band | sizes | scheduled ms | killed at ms | replies (rc) | store at death | owner log at death | verdict |
|---|---|---|---|---|---|---|---|---|---|---|
| 0 | 0 | single | late | small | 448.4 | 448.4 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 1 | 0 | single | window | small | 305.7 | 305.7 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 2 | 0 | single | over-limit | over | 26.5 | 26.5 | none (3) | untouched | not logged | died-absent-resubmit-failed |
| 3 | 0 | single | window | large | 205.3 | 205.3 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 4 | 0 | single | early | tiny | 14.4 | 14.4 | none (3) | staged,.allocation- | not logged | died-absent |
| 5 | 0 | single | late | small | 333.5 | 333.5 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 6 | 0 | single | over-limit | over | 6.8 | 6.8 | none (3) | untouched | not logged | died-absent-resubmit-failed |
| 7 | 0 | single | early | tiny | 74.6 | 74.6 | none (3) | frontier-advanced | not logged | died-absent |
| 8 | 0 | single | window | tiny | 183.5 | 183.5 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 9 | 0 | single | early | small | 114.8 | 114.8 | none (3) | staged,.stage- | not logged | died-absent |
| 10 | 0 | single | late | medium | 279.3 | 279.3 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 11 | 0 | single | early | small | 116.2 | 116.2 | none (3) | staged,.stage- | not logged | died-absent |
| 12 | 0 | single | mid-article | medium | 3.7 | 3.7 | none (3) | untouched | not logged | died-absent |
| 13 | 0 | single | window | tiny | 95.2 | 95.2 | none (3) | staged,.stage- | not logged | died-absent |
| 14 | 0 | single | window | large | 265.5 | 265.5 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 15 | 0 | single | window | medium | 220.3 | 220.3 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 16 | 0 | concurrent | early | small,small | 0.6 | 0.6 | none (3) / none (3) | untouched | not logged; not logged | died-absent, died-absent |
| 17 | 0 | single | late | large | 496.5 | 496.5 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 18 | 0 | concurrent | window | large,medium | 253.6 | 253.6 | none (3) / none (3) | linked(1),no-stage | not logged; not logged | died-absent, died-present-identical |
| 19 | 0 | single | window | tiny | 96.3 | 96.3 | none (3) | staged,.stage- | not logged | died-absent |
| 20 | 0 | concurrent | window | large,medium | 232.6 | 232.6 | none (3) / none (3) | linked(1),no-stage | not logged; not logged | died-absent, died-present-identical |
| 21 | 0 | single | mid-article | medium | 3.7 | 3.7 | none (3) | untouched | not logged | died-absent |
| 22 | 0 | single | late | medium | 329.1 | 329.1 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 23 | 0 | single | window | tiny | 202.1 | 202.1 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 24 | 0 | single | window | medium | 170.3 | 170.3 | none (3) | frontier-advanced | not logged | died-absent |
| 25 | 0 | single | mid-article | medium | 13.5 | 13.5 | none (3) | untouched | not logged | died-absent |
| 26 | 0 | single | window | medium | 272.6 | 272.6 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 27 | 0 | single | window | tiny | 218.2 | 218.2 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 28 | 0 | single | over-limit | over | 7.6 | 7.6 | none (3) | untouched | not logged | died-absent-resubmit-failed |
| 29 | 0 | concurrent | window | large,tiny | 339.4 | 339.4 | 240 article received OK (0) / none (3) | linked(2),.stage- | accepted post logged; not logged | 240-identical, died-present-identical |
| 30 | 0 | single | window | large | 267.7 | 267.7 | none (3) | staged,.stage- | not logged | died-absent |
| 31 | 0 | single | window | small | 136.1 | 136.1 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 32 | 0 | single | window | medium | 190.3 | 190.3 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 33 | 0 | single | window | large | 189.3 | 189.3 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 34 | 0 | concurrent | window | tiny,medium | 225.1 | 225.1 | 240 article received OK (0) / none (3) | linked(1),.allocation- | accepted post logged; not logged | 240-identical, died-absent |
| 35 | 0 | single | window | tiny | 104.6 | 104.6 | none (3) | staged,.stage- | not logged | died-absent |
| 36 | 0 | single | window | small | 267.3 | 267.3 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 37 | 0 | single | over-limit | over | 10.1 | 10.1 | none (3) | untouched | not logged | died-absent-resubmit-failed |
| 38 | 0 | single | window | large | 161.9 | 161.9 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 39 | 0 | single | window | tiny | 130.9 | 130.9 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 40 | 0 | single | late | tiny | 273.3 | 273.3 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 41 | 0 | single | window | large | 223.4 | 223.4 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 42 | 0 | single | late | medium | 345.0 | 345.0 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 43 | 0 | concurrent | window | medium,large | 216.9 | 216.9 | none (3) / none (3) | staged,.stage- | not logged; not logged | died-absent, died-absent |
| 44 | 0 | concurrent | late | small,tiny | 438.1 | 438.1 | none (3) / none (3) | linked(1),no-stage | not logged; not logged | died-absent, died-present-identical |
| 45 | 1 | single | window | medium | 214.5 | 214.5 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 46 | 1 | concurrent | early | large,small | 4.6 | 4.6 | none (3) / none (3) | untouched | not logged; not logged | died-absent, died-absent |
| 47 | 1 | single | early | small | 78.4 | 78.4 | none (3) | staged,.stage- | not logged | died-absent |
| 48 | 1 | single | early | small | 30.7 | 30.7 | none (3) | staged,.allocation- | not logged | died-absent |
| 49 | 1 | single | early | large | 137.9 | 137.9 | none (3) | staged,.stage- | not logged | died-absent |
| 50 | 1 | single | late | tiny | 306.6 | 306.6 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 51 | 1 | single | over-limit | over | 4.8 | 4.8 | none (3) | untouched | not logged | died-absent-resubmit-failed |
| 52 | 1 | single | early | large | 106.0 | 106.0 | none (3) | frontier-advanced | not logged | died-absent |
| 53 | 1 | single | late | tiny | 291.1 | 291.1 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 54 | 1 | single | mid-article | small | 4.5 | 4.5 | none (3) | untouched | not logged | died-absent |
| 55 | 1 | single | window | tiny | 144.0 | 144.0 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 56 | 1 | single | early | large | 56.8 | 56.8 | none (3) | staged,.allocation- | not logged | died-absent |
| 57 | 1 | single | early | tiny | 27.3 | 27.3 | none (3) | staged,.allocation- | not logged | died-absent |
| 58 | 1 | single | mid-article | large | 1.9 | 1.9 | none (3) | untouched | not logged | died-absent |
| 59 | 1 | single | window | medium | 203.8 | 203.9 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 60 | 1 | single | early | tiny | 54.8 | 54.8 | none (3) | frontier-advanced | not logged | died-absent |
| 61 | 1 | single | window | large | 280.4 | 280.4 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 62 | 1 | single | window | tiny | 171.3 | 171.3 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 63 | 1 | single | over-limit | over | 21.2 | 21.2 | none (3) | staged,.allocation- | not logged | died-absent-resubmit-failed |
| 64 | 1 | single | window | tiny | 153.3 | 153.3 | none (3) | staged,.stage- | not logged | died-absent |
| 65 | 1 | single | early | large | 56.5 | 56.5 | none (3) | frontier-advanced | not logged | died-absent |
| 66 | 1 | single | window | tiny | 214.1 | 214.1 | none (3) | staged,.stage- | not logged | died-absent |
| 67 | 1 | single | early | medium | 71.2 | 71.2 | none (3) | frontier-advanced | not logged | died-absent |
| 68 | 1 | concurrent | window | small,medium | 198.0 | 198.0 | none (3) / none (3) | staged,.stage- | not logged; not logged | died-absent, died-absent |
| 69 | 1 | single | late | medium | 325.2 | 325.2 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 70 | 1 | single | mid-article | large | 16.3 | 16.3 | none (3) | untouched | not logged | died-absent |
| 71 | 1 | single | mid-article | medium | 5.3 | 5.3 | none (3) | untouched | not logged | died-absent |
| 72 | 1 | single | early | large | 89.5 | 89.5 | none (3) | frontier-advanced | not logged | died-absent |
| 73 | 1 | single | window | small | 254.7 | 254.7 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 74 | 1 | single | window | tiny | 139.8 | 139.8 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 75 | 1 | single | late | medium | 347.2 | 347.2 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 76 | 1 | single | window | large | 309.2 | 309.2 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 77 | 1 | concurrent | late | large,medium | 434.3 | 434.3 | none (3) / 240 article received OK (0) | linked(2),no-stage | not logged; accepted post logged | died-present-identical, 240-identical |
| 78 | 1 | single | late | medium | 359.4 | 359.4 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 79 | 1 | single | early | small | 48.9 | 48.9 | none (3) | staged,.stage- | not logged | died-absent |
| 80 | 1 | single | early | large | 77.4 | 77.4 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 81 | 1 | single | mid-article | small | 17.1 | 17.1 | none (3) | untouched | not logged | died-absent |
| 82 | 1 | single | late | medium | 338.3 | 338.3 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 83 | 1 | single | window | medium | 236.8 | 236.8 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 84 | 1 | single | late | medium | 343.2 | 343.2 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 85 | 1 | single | early | large | 37.1 | 37.1 | none (3) | staged,.allocation- | not logged | died-absent |
| 86 | 1 | single | early | small | 25.4 | 25.4 | none (3) | staged,.allocation- | not logged | died-absent |
| 87 | 1 | single | window | medium | 186.6 | 186.6 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 88 | 1 | single | early | large | 102.2 | 102.2 | none (3) | frontier-advanced | not logged | died-absent |
| 89 | 1 | single | window | large | 307.0 | 307.0 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |

## Failures: 6

- iteration 2 <pk-3-0021@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 0, 'reply': '240 article received OK\r\n', 'new_transactions': 1}
- iteration 6 <pk-3-0029@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 0, 'reply': '240 article received OK\r\n', 'new_transactions': 1}
- iteration 28 <pk-3-0074@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 0, 'reply': '240 article received OK\r\n', 'new_transactions': 1}
- iteration 37 <pk-3-0096@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 0, 'reply': '240 article received OK\r\n', 'new_transactions': 1}
- iteration 51 <pk-3-0128@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 0, 'reply': '240 article received OK\r\n', 'new_transactions': 1}
- iteration 63 <pk-3-0148@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 0, 'reply': '240 article received OK\r\n', 'new_transactions': 1}

judge rc=1
