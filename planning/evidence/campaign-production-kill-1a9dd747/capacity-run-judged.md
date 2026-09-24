# /tank/fn/scratch/campaign-production-kill/run1.json

seed 1; 92 iterations (80 single, 12 concurrent); 214 POSTs in the ledger; 128 final articles present; 93 owner pids, all gone: True

calibration medians (ms from terminator sent): {"tiny": {".allocation-gone": 9.2, ".allocation-seen": 1.9, ".stage-gone": 35.8, ".stage-seen": 20.1, "frontier": 9.2, "reply": 48.9, "stage": 1.9, "stage_cleared": 9.2, "txn": 27.5}, "small": {".allocation-gone": 13.8, ".allocation-seen": 6.5, ".stage-gone": 38.9, ".stage-seen": 24.7, "frontier": 13.8, "reply": 51.4, "stage": 6.5, "stage_cleared": 13.8, "txn": 30.4}, "medium": {".allocation-gone": 38.0, ".allocation-seen": 31.1, ".stage-gone": 80.0, ".stage-seen": 56.4, "frontier": 38.0, "reply": 100.3, "stage": 31.1, "stage_cleared": 38.0, "txn": 70.9}, "large": {".allocation-gone": 78.2, ".allocation-seen": 68.7, ".stage-gone": 127.8, ".stage-seen": 110.4, "frontier": 78.2, "reply": 158.4, "stage": 68.7, "stage_cleared": 78.2, "txn": 120.8}, "over": {"reply": 38.5}}

## Verdicts

- 240-identical: 59
- died-absent: 64
- died-present-identical: 11
- refused: 60
- torn: 0
- lost-240: 0
- reused-number: 0
- died-absent-resubmit-failed: 20

## Client exit codes by reply

- rc 0: ['240 article received OK']
- rc 1: ['441 posting failed; the article was not received', '441 posting failed; the article was refused']
- rc 3: ['<no reply>']

## Kill band against the store state at death

| band | store state at death | kills |
|---|---|---|
| early | staged,.allocation- | 1 |
| early | untouched | 21 |
| late | frontier-advanced | 1 |
| late | linked(1),.stage- | 2 |
| late | linked(1),no-stage | 4 |
| late | staged,.allocation- | 2 |
| late | staged,.stage- | 2 |
| late | untouched | 6 |
| mid-article | untouched | 8 |
| over-limit | untouched | 6 |
| window | frontier-advanced | 5 |
| window | linked(1),.stage- | 2 |
| window | linked(1),no-stage | 4 |
| window | staged,.allocation- | 3 |
| window | staged,.stage- | 4 |
| window | untouched | 21 |

## Kill instants against the phase reached

| store state at death | owner log at death | kills | killed at ms (min to max) |
|---|---|---|---|
| untouched | not logged | 48 | 0.6 to 153.3 |
| untouched | not logged; not logged | 6 | 15.7 to 162.6 |
| staged,.allocation- | not logged | 5 | 17.2 to 122.6 |
| untouched | refused post logged | 8 | 22.3 to 69.2 |
| staged,.stage- | not logged | 6 | 35.6 to 122.4 |
| linked(1),.stage- | not logged | 4 | 37.8 to 125.5 |
| frontier-advanced | not logged | 5 | 45.7 to 128.3 |
| linked(1),no-stage | not logged; not logged | 4 | 53.4 to 129.0 |
| linked(1),no-stage | accepted post logged | 1 | 61.7 to 61.7 |
| linked(1),no-stage | not logged | 3 | 69.1 to 101.4 |
| frontier-advanced | not logged; not logged | 1 | 100.0 to 100.0 |
| staged,.allocation- | not logged; not logged | 1 | 152.4 to 152.4 |

## Per kill

| # | kind | band | sizes | scheduled ms | killed at ms | replies (rc) | store at death | owner log at death | verdict |
|---|---|---|---|---|---|---|---|---|---|
| 0 | single | window | large | 128.3 | 128.3 | none (3) | frontier-advanced | not logged | died-absent |
| 1 | single | window | medium | 81.9 | 81.9 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 2 | single | late | tiny | 61.7 | 61.7 | 240 article received OK (0) | linked(1),no-stage | accepted post logged | 240-identical |
| 3 | single | window | medium | 101.4 | 101.4 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 4 | single | window | medium | 68.6 | 68.6 | none (3) | frontier-advanced | not logged | died-absent |
| 5 | single | over-limit | over | 18.9 | 18.9 | none (3) | untouched | not logged | died-absent |
| 6 | single | window | small | 35.6 | 35.6 | none (3) | staged,.stage- | not logged | died-absent |
| 7 | concurrent | window | tiny,small | 53.4 | 53.4 | none (3) / none (3) | linked(1),no-stage | not logged; not logged | died-absent, died-present-identical |
| 8 | single | window | medium | 80.1 | 80.1 | none (3) | staged,.stage- | not logged | died-absent |
| 9 | single | mid-article | tiny | 3.2 | 3.2 | none (3) | untouched | not logged | died-absent |
| 10 | single | early | tiny | 0.6 | 0.6 | none (3) | untouched | not logged | died-absent |
| 11 | single | late | tiny | 69.1 | 69.1 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 12 | single | over-limit | over | 35.0 | 35.0 | none (3) | untouched | not logged | died-absent |
| 13 | concurrent | window | tiny,large | 119.3 | 119.3 | none (3) / none (3) | linked(1),no-stage | not logged; not logged | died-present-identical, died-absent |
| 14 | single | early | large | 60.1 | 60.1 | none (3) | untouched | not logged | died-absent |
| 15 | single | late | medium | 113.8 | 113.8 | none (3) | staged,.stage- | not logged | died-absent |
| 16 | single | early | large | 74.6 | 74.7 | none (3) | untouched | not logged | died-absent |
| 17 | concurrent | window | large,small | 152.4 | 152.4 | none (3) / none (3) | staged,.allocation- | not logged; not logged | died-absent, died-absent |
| 18 | single | window | tiny | 39.4 | 39.4 | none (3) | staged,.stage- | not logged | died-absent |
| 19 | single | window | medium | 100.4 | 100.4 | none (3) | frontier-advanced | not logged | died-absent |
| 20 | single | early | small | 15.6 | 15.6 | none (3) | untouched | not logged | died-absent |
| 21 | single | window | large | 130.6 | 130.6 | none (3) | untouched | not logged | died-absent |
| 22 | single | early | tiny | 6.3 | 6.3 | none (3) | untouched | not logged | died-absent |
| 23 | single | late | medium | 122.4 | 122.4 | none (3) | staged,.stage- | not logged | died-absent |
| 24 | single | late | medium | 125.5 | 125.5 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 25 | single | mid-article | small | 8.6 | 8.6 | none (3) | untouched | not logged | died-absent |
| 26 | single | early | large | 70.9 | 70.9 | none (3) | untouched | not logged | died-absent |
| 27 | single | mid-article | medium | 2.3 | 2.3 | none (3) | untouched | not logged | died-absent |
| 28 | single | late | small | 62.2 | 62.2 | none (3) | staged,.allocation- | not logged | died-absent |
| 29 | concurrent | window | medium,small | 64.1 | 64.1 | none (3) / none (3) | linked(1),no-stage | not logged; not logged | died-absent, died-present-identical |
| 30 | single | window | tiny | 37.8 | 37.8 | none (3) | staged,.stage- | not logged | died-absent |
| 31 | single | window | medium | 99.1 | 99.1 | none (3) | untouched | not logged | died-absent |
| 32 | single | over-limit | over | 17.3 | 17.3 | none (3) | untouched | not logged | died-absent |
| 33 | single | over-limit | over | 9.0 | 9.0 | none (3) | untouched | not logged | died-absent |
| 34 | single | early | large | 78.9 | 78.9 | none (3) | untouched | not logged | died-absent |
| 35 | single | late | medium | 122.6 | 122.6 | none (3) | staged,.allocation- | not logged | died-absent |
| 36 | single | window | large | 142.8 | 142.8 | none (3) | untouched | not logged | died-absent |
| 37 | single | window | tiny | 37.8 | 37.8 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 38 | single | late | medium | 104.6 | 104.6 | none (3) | untouched | not logged | died-absent |
| 39 | single | late | tiny | 69.3 | 69.3 | none (3) | linked(1),no-stage | not logged | died-present-identical |
| 40 | single | window | small | 38.3 | 38.3 | none (3) | staged,.allocation- | not logged | died-absent |
| 41 | concurrent | window | tiny,medium | 100.0 | 100.0 | none (3) / none (3) | frontier-advanced | not logged; not logged | died-absent, died-absent |
| 42 | concurrent | late | small,medium | 137.4 | 137.4 | none (3) / none (3) | untouched | not logged; not logged | died-absent, died-absent |
| 43 | concurrent | early | large,medium | 54.8 | 54.8 | none (3) / none (3) | untouched | not logged; not logged | died-absent, died-absent |
| 44 | single | early | small | 16.2 | 16.2 | none (3) | untouched | not logged | died-absent |
| 45 | single | window | large | 135.5 | 135.5 | none (3) | untouched | not logged | died-absent |
| 46 | single | early | small | 2.6 | 2.6 | none (3) | untouched | not logged | died-absent |
| 47 | single | window | large | 153.3 | 153.3 | none (3) | untouched | not logged | died-absent |
| 48 | single | early | large | 82.7 | 82.7 | none (3) | untouched | not logged | died-absent |
| 49 | single | window | large | 152.9 | 152.9 | none (3) | untouched | not logged | died-absent |
| 50 | single | early | large | 47.1 | 47.1 | none (3) | untouched | not logged | died-absent |
| 51 | single | late | tiny | 53.7 | 53.7 | none (3) | linked(1),.stage- | not logged | died-present-identical |
| 52 | single | window | medium | 91.6 | 91.6 | none (3) | untouched | not logged | died-absent |
| 53 | single | window | small | 40.9 | 40.9 | none (3) | untouched | not logged | died-absent |
| 54 | single | over-limit | over | 38.7 | 38.7 | none (3) | untouched | not logged | died-absent |
| 55 | single | window | medium | 67.2 | 67.2 | none (3) | untouched | not logged | died-absent |
| 56 | single | window | small | 38.9 | 38.9 | none (3) | untouched | not logged | died-absent |
| 57 | single | window | large | 134.3 | 134.3 | none (3) | untouched | not logged | died-absent |
| 58 | single | window | tiny | 45.7 | 45.7 | none (3) | frontier-advanced | not logged | died-absent |
| 59 | single | late | small | 73.8 | 73.8 | none (3) | frontier-advanced | not logged | died-absent |
| 60 | single | early | small | 20.9 | 20.9 | none (3) | untouched | not logged | died-absent |
| 61 | single | early | small | 20.8 | 20.8 | none (3) | untouched | not logged | died-absent |
| 62 | single | early | tiny | 17.2 | 17.2 | none (3) | staged,.allocation- | not logged | died-absent |
| 63 | single | mid-article | medium | 8.4 | 8.4 | none (3) | untouched | not logged | died-absent |
| 64 | concurrent | late | tiny,medium | 129.0 | 129.0 | none (3) / none (3) | linked(1),no-stage | not logged; not logged | died-present-identical, died-absent |
| 65 | single | window | medium | 86.3 | 86.3 | none (3) | untouched | not logged | died-absent |
| 66 | single | window | tiny | 45.9 | 45.9 | none (3) | staged,.allocation- | not logged | died-absent |
| 67 | single | late | small | 69.2 | 69.2 | 441 posting failed; the arti (1) | untouched | refused post logged | refused |
| 68 | single | window | medium | 89.8 | 89.8 | none (3) | untouched | not logged | died-absent-resubmit-failed |
| 69 | concurrent | early | tiny,small | 15.7 | 15.7 | none (3) / none (3) | untouched | not logged; not logged | died-absent-resubmit-failed, died-absent-resubmit-failed |
| 70 | concurrent | early | large,small | 53.5 | 53.5 | none (3) / none (3) | untouched | not logged; not logged | died-absent-resubmit-failed, died-absent-resubmit-failed |
| 71 | single | over-limit | over | 12.3 | 12.3 | none (3) | untouched | not logged | died-absent |
| 72 | single | mid-article | large | 13.0 | 13.0 | none (3) | untouched | not logged | died-absent-resubmit-failed |
| 73 | single | window | tiny | 29.8 | 29.8 | 441 posting failed; the arti (1) | untouched | refused post logged | refused |
| 74 | concurrent | late | large,medium | 162.6 | 162.6 | none (3) / none (3) | untouched | not logged; not logged | died-absent-resubmit-failed, died-absent-resubmit-failed |
| 75 | single | early | tiny | 22.3 | 22.3 | 441 posting failed; the arti (1) | untouched | refused post logged | refused |
| 76 | single | early | tiny | 22.1 | 22.1 | none (3) | untouched | not logged | died-absent-resubmit-failed |
| 77 | single | early | medium | 46.0 | 46.0 | none (3) | untouched | not logged | died-absent-resubmit-failed |
| 78 | single | window | small | 37.3 | 37.3 | none (3) | untouched | not logged | died-absent-resubmit-failed |
| 79 | concurrent | window | medium,small | 80.2 | 80.2 | none (3) / none (3) | untouched | not logged; not logged | died-absent-resubmit-failed, died-absent-resubmit-failed |
| 80 | single | late | tiny | 55.6 | 55.6 | 441 posting failed; the arti (1) | untouched | refused post logged | refused |
| 81 | single | mid-article | small | 5.1 | 5.1 | none (3) | untouched | not logged | died-absent-resubmit-failed |
| 82 | single | window | small | 41.4 | 41.4 | none (3) | untouched | not logged | died-absent-resubmit-failed |
| 83 | single | mid-article | tiny | 7.9 | 7.9 | none (3) | untouched | not logged | died-absent-resubmit-failed |
| 84 | single | window | small | 52.8 | 52.8 | none (3) | untouched | not logged | died-absent-resubmit-failed |
| 85 | single | early | tiny | 23.2 | 23.2 | 441 posting failed; the arti (1) | untouched | refused post logged | refused |
| 86 | single | window | tiny | 37.5 | 37.5 | 441 posting failed; the arti (1) | untouched | refused post logged | refused |
| 87 | single | window | large | 139.8 | 139.8 | none (3) | untouched | not logged | died-absent-resubmit-failed |
| 88 | single | late | small | 66.8 | 66.8 | 441 posting failed; the arti (1) | untouched | refused post logged | refused |
| 89 | single | window | tiny | 35.2 | 35.2 | 441 posting failed; the arti (1) | untouched | refused post logged | refused |
| 90 | single | early | medium | 14.7 | 14.7 | none (3) | untouched | not logged | died-absent-resubmit-failed |
| 91 | single | mid-article | large | 4.4 | 4.4 | none (3) | untouched | not logged | died-absent-resubmit-failed |

## Failures: 20

- iteration 68 <pk-1-0161@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 1, 'reply': '441 posting failed; the article was refused\r\n', 'new_transactions': 0}
- iteration 69 <pk-1-0162@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 1, 'reply': '441 posting failed; the article was refused\r\n', 'new_transactions': 0}
- iteration 69 <pk-1-0163@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 1, 'reply': '441 posting failed; the article was refused\r\n', 'new_transactions': 0}
- iteration 70 <pk-1-0165@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 1, 'reply': '441 posting failed; the article was refused\r\n', 'new_transactions': 0}
- iteration 70 <pk-1-0166@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 1, 'reply': '441 posting failed; the article was refused\r\n', 'new_transactions': 0}
- iteration 72 <pk-1-0170@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 1, 'reply': '441 posting failed; the article was refused\r\n', 'new_transactions': 0}
- iteration 74 <pk-1-0176@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 1, 'reply': '441 posting failed; the article was refused\r\n', 'new_transactions': 0}
- iteration 74 <pk-1-0177@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 1, 'reply': '441 posting failed; the article was refused\r\n', 'new_transactions': 0}
- iteration 76 <pk-1-0180@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 1, 'reply': '441 posting failed; the article was refused\r\n', 'new_transactions': 0}
- iteration 77 <pk-1-0181@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 1, 'reply': '441 posting failed; the article was refused\r\n', 'new_transactions': 0}
- iteration 78 <pk-1-0182@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 1, 'reply': '441 posting failed; the article was refused\r\n', 'new_transactions': 0}
- iteration 79 <pk-1-0184@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 1, 'reply': '441 posting failed; the article was refused\r\n', 'new_transactions': 0}
- iteration 79 <pk-1-0185@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 1, 'reply': '441 posting failed; the article was refused\r\n', 'new_transactions': 0}
- iteration 81 <pk-1-0189@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 1, 'reply': '441 posting failed; the article was refused\r\n', 'new_transactions': 0}
- iteration 82 <pk-1-0191@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 1, 'reply': '441 posting failed; the article was refused\r\n', 'new_transactions': 0}
- iteration 83 <pk-1-0194@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 1, 'reply': '441 posting failed; the article was refused\r\n', 'new_transactions': 0}
- iteration 84 <pk-1-0195@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 1, 'reply': '441 posting failed; the article was refused\r\n', 'new_transactions': 0}
- iteration 87 <pk-1-0203@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 1, 'reply': '441 posting failed; the article was refused\r\n', 'new_transactions': 0}
- iteration 90 <pk-1-0210@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 1, 'reply': '441 posting failed; the article was refused\r\n', 'new_transactions': 0}
- iteration 91 <pk-1-0213@production-kill.invalid>: died-absent-resubmit-failed; post reply ''; reread {'status': '430 no article with that message-id', 'sha256': None, 'octets': 0, 'identical': None}; resubmit {'rc': 1, 'reply': '441 posting failed; the article was refused\r\n', 'new_transactions': 0}

judge rc=1
