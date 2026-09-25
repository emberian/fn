# /tank/fn/scratch/qual-e747dbcc/campaign/pk-run.json

stores 2 (closed and swept: [0, 1])

seed 3; 90 iterations (80 single, 10 concurrent); 206 POSTs in the ledger; 206 final articles present; 92 owner pids, all gone: True

calibration medians (ms from terminator sent): {"tiny": {".allocation-gone": 14.8, ".allocation-seen": 0.4, ".stage-gone": 76.7, ".stage-seen": 40.3, "frontier": 14.8, "reply": 139.7, "stage": 0.4, "stage_cleared": 14.8, "txn": 52.5}, "small": {".allocation-gone": 17.4, ".allocation-seen": 2.0, ".stage-gone": 84.1, ".stage-seen": 45.8, "frontier": 17.2, "reply": 144.3, "stage": 2.0, "stage_cleared": 17.4, "txn": 65.5}, "medium": {".allocation-gone": 32.7, ".allocation-seen": 8.6, ".stage-gone": 107.8, ".stage-seen": 52.2, "frontier": 32.5, "reply": 162.9, "stage": 8.6, "stage_cleared": 32.7, "txn": 83.2}, "large": {".allocation-gone": 45.8, ".allocation-seen": 21.7, ".stage-gone": 120.9, ".stage-seen": 72.9, "frontier": 45.8, "reply": 176.5, "stage": 21.7, "stage_cleared": 45.8, "txn": 96.2}, "over": {".allocation-gone": 38.1, ".allocation-seen": 22.6, ".stage-gone": 126.5, ".stage-seen": 72.7, "frontier": 38.1, "reply": 181.7, "stage": 22.6, "stage_cleared": 38.1, "txn": 104.9}}

## Verdicts

- 240-identical: 115
- died-absent: 58
- died-present-identical: 27
- refused: 0
- torn: 0
- lost-240: 0
- reused-number: 0
- died-absent-resubmit-failed: 6

## Verdicts of the killed POSTs only

| kill kind | verdict | POSTs |
|---|---|---|
| concurrent | died-absent | 15 |
| concurrent | died-present-identical | 5 |
| single | 240-identical | 9 |
| single | died-absent | 43 |
| single | died-absent-resubmit-failed | 6 |
| single | died-present-identical | 22 |

## Client exit codes by reply

- rc 0: ['240 article received OK']
- rc 1: ['441 posting failed; this article is already stored here']
- rc 3: ['<no reply>']

## Kill band against the store state at death

| band | store state at death | kills |
|---|---|---|
| early | frontier-advanced | 9 |
| early | staged,.allocation- | 7 |
| early | staged,.stage- | 3 |
| early | untouched | 2 |
| late | frontier-advanced | 1 |
| late | linked(1),.stage- | 4 |
| late | linked(1),no-stage | 10 |
| late | staged,.stage- | 1 |
| mid-article | untouched | 8 |
| over-limit | staged,.allocation- | 1 |
| over-limit | untouched | 5 |
| window | frontier-advanced | 7 |
| window | linked(1),.stage- | 11 |
| window | linked(1),no-stage | 11 |
| window | staged,.allocation- | 2 |
| window | staged,.stage- | 8 |

## Kill instants against the phase reached

| store state at death | owner log at death | kills | killed at ms (min to max) |
|---|---|---|---|
| untouched | not logged; not logged | 2 | 0.3 to 2.8 |
| untouched | not logged | 13 | 1.9 to 26.5 |
| staged,.allocation- | not logged | 10 | 7.5 to 162.7 |
| frontier-advanced | not logged | 16 | 28.6 to 176.8 |
| staged,.stage- | not logged | 10 | 38.9 to 129.0 |
| linked(1),no-stage | not logged | 9 | 83.3 to 194.8 |
| linked(1),.stage- | not logged | 13 | 100.8 to 208.0 |
| linked(1),no-stage | not logged; not logged | 3 | 105.8 to 219.0 |
| frontier-advanced | not logged; not logged | 1 | 118.8 to 118.8 |
| linked(1),.stage- | not logged; not logged | 2 | 128.5 to 134.7 |
| linked(1),no-stage | accepted post logged | 9 | 136.9 to 250.5 |
| staged,.stage- | not logged; not logged | 2 | 172.1 to 198.5 |

## Per kill

| # | store | kind | band | sizes | scheduled ms | killed at ms | replies (rc) | store at death | owner log at death | verdict |
|---|---|---|---|---|---|---|---|---|---|---|
| 0 | 0 | single | late | small | 203.2 | 203.2 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 1 | 0 | single | window | small | 138.2 | 138.2 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 2 | 0 | single | over-limit | over | 26.5 | 26.5 | none (3) | untouched | not logged | died-absent-resubmit-failed |
| 3 | 0 | single | window | large | 113.7 | 113.7 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 4 | 0 | single | early | tiny | 7.5 | 7.5 | none (3) | staged,.allocation- | not logged | died-absent |
| 5 | 0 | single | late | small | 150.9 | 150.9 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 6 | 0 | single | over-limit | over | 6.8 | 6.8 | none (3) | untouched | not logged | died-absent-resubmit-failed |
| 7 | 0 | single | early | tiny | 38.9 | 38.9 | none (3) | staged,.stage- | not logged | died-absent |
| 8 | 0 | single | window | tiny | 115.4 | 115.4 | none (3) | frontier-advanced | not logged | died-absent |
| 9 | 0 | single | early | small | 51.2 | 51.2 | none (3) | staged,.stage- | not logged | died-absent |
| 10 | 0 | single | late | medium | 167.2 | 167.2 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 11 | 0 | single | early | small | 51.8 | 51.8 | none (3) | staged,.stage- | not logged | died-absent |
| 12 | 0 | single | mid-article | medium | 3.7 | 3.7 | none (3) | untouched | not logged | died-absent |
| 13 | 0 | single | window | tiny | 50.7 | 50.7 | none (3) | staged,.stage- | not logged | died-absent |
| 14 | 0 | single | window | large | 139.9 | 139.9 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 15 | 0 | single | window | medium | 125.0 | 125.0 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 16 | 0 | concurrent | early | small,small | 0.3 | 0.3 | none (3) / none (3) | untouched | not logged; not logged | died-absent, died-absent |
| 17 | 0 | single | late | large | 250.5 | 250.5 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 18 | 0 | concurrent | window | large,medium | 134.7 | 134.7 | none (3) / none (3) | linked(1),.stage- | not logged; not logged | died-absent, died-present-identical |
| 19 | 0 | single | window | tiny | 51.5 | 51.5 | none (3) | frontier-advanced | not logged | died-absent |
| 20 | 0 | concurrent | window | large,medium | 125.6 | 125.6 | none (3) / none (3) | linked(1),no-stage | not logged; not logged | died-absent, died-present-identical |
| 21 | 0 | single | mid-article | medium | 3.7 | 3.7 | none (3) | untouched | not logged | died-absent |
| 22 | 0 | single | late | medium | 197.2 | 197.2 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 23 | 0 | single | window | tiny | 129.0 | 129.0 | none (3) | staged,.stage- | not logged | died-absent |
| 24 | 0 | single | window | medium | 89.1 | 89.1 | none (3) | staged,.allocation- | not logged | died-absent |
| 25 | 0 | single | mid-article | medium | 13.5 | 13.5 | none (3) | untouched | not logged | died-absent |
| 26 | 0 | single | window | medium | 162.6 | 162.7 | none (3) | staged,.allocation- | not logged | died-absent |
| 27 | 0 | single | window | tiny | 140.8 | 140.8 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 28 | 0 | single | over-limit | over | 7.6 | 7.6 | none (3) | untouched | not logged | died-absent-resubmit-failed |
| 29 | 0 | concurrent | window | large,tiny | 172.1 | 172.1 | none (3) / none (3) | staged,.stage- | not logged; not logged | died-absent, died-absent |
| 30 | 0 | single | window | large | 140.9 | 140.9 | none (3) | frontier-advanced | not logged | died-absent |
| 31 | 0 | single | window | small | 60.7 | 60.7 | none (3) | frontier-advanced | not logged | died-absent |
| 32 | 0 | single | window | medium | 103.4 | 103.4 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 33 | 0 | single | window | large | 106.7 | 106.7 | none (3) | staged,.stage- | not logged | died-absent |
| 34 | 0 | concurrent | window | tiny,medium | 128.5 | 128.5 | none (3) / none (3) | linked(1),.stage- | not logged; not logged | died-present-identical, died-absent |
| 35 | 0 | single | window | tiny | 57.6 | 57.6 | none (3) | staged,.stage- | not logged | died-absent |
| 36 | 0 | single | window | small | 120.7 | 120.7 | none (3) | staged,.stage- | not logged | died-absent |
| 37 | 0 | single | over-limit | over | 10.1 | 10.1 | none (3) | untouched | not logged | died-absent-resubmit-failed |
| 38 | 0 | single | window | large | 94.8 | 94.8 | none (3) | frontier-advanced | not logged | died-absent |
| 39 | 0 | single | window | tiny | 76.8 | 76.8 | none (3) | frontier-advanced | not logged | died-absent |
| 40 | 0 | single | late | tiny | 176.8 | 176.8 | none (3) | frontier-advanced | not logged | died-absent |
| 41 | 0 | single | window | large | 121.6 | 121.6 | none (3) | staged,.stage- | not logged | died-absent |
| 42 | 0 | single | late | medium | 206.8 | 206.8 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 43 | 0 | concurrent | window | medium,large | 118.7 | 118.8 | none (3) / none (3) | frontier-advanced | not logged; not logged | died-absent, died-absent |
| 44 | 0 | concurrent | late | small,tiny | 198.5 | 198.5 | none (3) / none (3) | staged,.stage- | not logged; not logged | died-absent, died-absent |
| 45 | 1 | single | window | medium | 120.9 | 120.9 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 46 | 1 | concurrent | early | large,small | 2.8 | 2.8 | none (3) / none (3) | untouched | not logged; not logged | died-absent, died-absent |
| 47 | 1 | single | early | small | 34.9 | 35.0 | none (3) | frontier-advanced | not logged | died-absent |
| 48 | 1 | single | early | small | 13.7 | 13.8 | none (3) | staged,.allocation- | not logged | died-absent |
| 49 | 1 | single | early | large | 83.4 | 83.4 | none (3) | frontier-advanced | not logged | died-absent |
| 50 | 1 | single | late | tiny | 198.5 | 198.5 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 51 | 1 | single | over-limit | over | 4.8 | 4.8 | none (3) | untouched | not logged | died-absent-resubmit-failed |
| 52 | 1 | single | early | large | 64.2 | 64.2 | none (3) | frontier-advanced | not logged | died-absent |
| 53 | 1 | single | late | tiny | 188.3 | 188.3 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 54 | 1 | single | mid-article | small | 4.5 | 4.5 | none (3) | untouched | not logged | died-absent |
| 55 | 1 | single | window | tiny | 86.4 | 86.4 | none (3) | staged,.stage- | not logged | died-absent |
| 56 | 1 | single | early | large | 34.4 | 34.4 | none (3) | staged,.allocation- | not logged | died-absent |
| 57 | 1 | single | early | tiny | 14.2 | 14.2 | none (3) | staged,.allocation- | not logged | died-absent |
| 58 | 1 | single | mid-article | large | 1.9 | 1.9 | none (3) | untouched | not logged | died-absent |
| 59 | 1 | single | window | medium | 113.2 | 113.2 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 60 | 1 | single | early | tiny | 28.6 | 28.6 | none (3) | frontier-advanced | not logged | died-absent |
| 61 | 1 | single | window | large | 146.4 | 146.4 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 62 | 1 | single | window | tiny | 106.5 | 106.5 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 63 | 1 | single | over-limit | over | 21.2 | 21.2 | none (3) | staged,.allocation- | not logged | died-absent-resubmit-failed |
| 64 | 1 | single | window | tiny | 93.3 | 93.3 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 65 | 1 | single | early | large | 34.2 | 34.2 | none (3) | frontier-advanced | not logged | died-absent |
| 66 | 1 | single | window | tiny | 137.8 | 137.8 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 67 | 1 | single | early | medium | 35.4 | 35.4 | none (3) | frontier-advanced | not logged | died-absent |
| 68 | 1 | concurrent | window | small,medium | 105.8 | 105.8 | none (3) / none (3) | linked(1),no-stage | not logged; not logged | died-present-identical, died-absent |
| 69 | 1 | single | late | medium | 194.8 | 194.8 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 70 | 1 | single | mid-article | large | 16.3 | 16.3 | none (3) | untouched | not logged | died-absent |
| 71 | 1 | single | mid-article | medium | 5.3 | 5.3 | none (3) | untouched | not logged | died-absent |
| 72 | 1 | single | early | large | 54.2 | 54.2 | none (3) | frontier-advanced | not logged | died-absent |
| 73 | 1 | single | window | small | 114.9 | 114.9 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 74 | 1 | single | window | tiny | 83.3 | 83.3 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 75 | 1 | single | late | medium | 208.0 | 208.0 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 76 | 1 | single | window | large | 159.0 | 159.0 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 77 | 1 | concurrent | late | large,medium | 219.0 | 219.0 | none (3) / none (3) | linked(1),no-stage | not logged; not logged | died-present-identical, died-absent |
| 78 | 1 | single | late | medium | 215.4 | 215.4 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 79 | 1 | single | early | small | 21.8 | 21.8 | none (3) | staged,.allocation- | not logged | died-absent |
| 80 | 1 | single | early | large | 46.8 | 46.8 | none (3) | frontier-advanced | not logged | died-absent |
| 81 | 1 | single | mid-article | small | 17.1 | 17.1 | none (3) | untouched | not logged | died-absent |
| 82 | 1 | single | late | medium | 202.7 | 202.7 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 83 | 1 | single | window | medium | 136.9 | 136.9 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 84 | 1 | single | late | medium | 205.7 | 205.7 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 85 | 1 | single | early | large | 22.4 | 22.4 | none (3) | staged,.allocation- | not logged | died-absent |
| 86 | 1 | single | early | small | 11.3 | 11.3 | none (3) | staged,.allocation- | not logged | died-absent |
| 87 | 1 | single | window | medium | 100.8 | 100.8 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 88 | 1 | single | early | large | 61.8 | 61.8 | none (3) | frontier-advanced | not logged | died-absent |
| 89 | 1 | single | window | large | 158.0 | 158.0 | none (3) | linked(1),.stage- | not logged | died-present-identical |

## Failures: 6

- iteration 2 <pk-3-0021@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 0, 'reply': '240 article received OK\r\n', 'new_transactions': 1}
- iteration 6 <pk-3-0029@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 0, 'reply': '240 article received OK\r\n', 'new_transactions': 1}
- iteration 28 <pk-3-0074@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 0, 'reply': '240 article received OK\r\n', 'new_transactions': 1}
- iteration 37 <pk-3-0096@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 0, 'reply': '240 article received OK\r\n', 'new_transactions': 1}
- iteration 51 <pk-3-0128@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 0, 'reply': '240 article received OK\r\n', 'new_transactions': 1}
- iteration 63 <pk-3-0148@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 0, 'reply': '240 article received OK\r\n', 'new_transactions': 1}

judge rc=1
