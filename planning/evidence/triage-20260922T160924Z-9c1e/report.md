# Triage triage-20260922T160924Z-9c1e -- persvati

**This is not evidence of certification.** A triage run certifies a tree whose sources were substituted on the box. Its certificates are published nowhere, its manifest is not archived, and nothing in this report is a certification claim about this revision. The certify run ids are left out for that reason; the farm run ids below locate the logs on the box.

Closure: 97 books under 6 roots (books/native-operator, books/native-hybrid-control, tests/acl2/native-operator-tests, tests/acl2/native-admin-tests, tests/acl2/native-control-tests, tests/acl2/native-hybrid-control-tests), per-book budget 800 s, remote root `/home/ember/fn-gates/w32-native-guards-triage`.

Mode: ACL2 provisional certification: a Create wave, one parallel Convert wave that does every book's proofs, and a Complete wave.

## Rounds

- Round 1 (run-20260922T160925Z-cf8c, exit 1): 11 of 97 books failed -- 3 independent, 8 blocked; 721.752 s of certification wall; the tree as committed.

## Independent reds (3)

### books/store-node-resolution -- round 1

Wall 1.653 s; ACL2 exit 0.

```
ACL2 Error [Failure] in (DEFTHM FN-SN-KNOWN-ABORT-IS-EXACT-NODE-ABORT ...): See :DOC failure.
```

Key checkpoint (log line 1450 is the error above):
```
*** Key checkpoint before reverting to proof by induction: ***
Subgoal 8'
(IMPLIES
 (AND
  (FN-SN-STATEP S)
  (EQUAL (FN-SF-PHASE (FN-SN-FILES S))
         :RECORD-STAGED)
  (FN-STORE-RETENTION-EVENT-P (FN-SF-RECORD-CANDIDATE (FN-SN-FILES S)))
  (EQUAL
   (FN-STATE-NEXT-TXID
    (FN-NODE-ACCEPTANCE
       (FN-REPLAY-ADVANCE-TXID
            (FN-SN-NODE S)
            (FN-STORE-EVENT-TXID (FN-SF-RECORD-CANDIDATE (FN-SN-FILES S))))))
   (FN-STORE-EVENT-TXID (FN-SF-RECORD-CANDIDATE (FN-SN-FILES S))))
  (NOT
   (FN-NODE-STAGE
       (FN-REPLAY-ADVANCE-TXID
            (FN-SN-NODE S)
            (FN-STORE-EVENT-TXID (FN-SF-RECORD-CANDIDATE (FN-SN-FILES S))))))
  (NOT
   (MEMBER-EQUAL
      (FN-STORE-EVENT-OBLIGATION-ID (FN-SF-RECORD-CANDIDATE (FN-SN-FILES S)))
      (FN-NODE-BINDING-IDS (FN-NODE-BINDINGS (FN-SN-NODE S)))))
  (EQUAL (FN-STORE-EVENT-KIND (FN-SF-RECORD-CANDIDATE (FN-SN-FILES S)))
... (13 more lines, in the run log on the box)
```

Assuming: nothing; the tree as committed.

### books/store-node-traces -- round 1

Wall 101.799 s; ACL2 exit 0.

```
ACL2 Error [Failure] in (DEFTHM FN-SNT-RECORD-DIRECTORY-PRESERVES-RELATION ...): See :DOC failure.
```

Key checkpoint (log line 61514 is the error above):
```
*** Key checkpoint before reverting to proof by induction: ***
Subgoal 4844.3740.1250'
(IMPLIES
 (AND
  (EQUAL (FN-SF-PHASE (FN-SN-FILES S))
         :RECORD-ATTEMPTED)
  (FN-SN-STATEP
   (FN-SN-MAKE-V2
    (FN-SN-GROUPS S)
    (FN-SN-CAPACITY S)
    (FN-SF-MAKE
     :COMPLETING
     (FN-SF-FRONTIER (FN-SN-FILES S))
     NIL
     (APPEND (FN-SF-RECORDS (FN-SN-FILES S))
             (LIST (FN-SF-RECORD-CANDIDATE (FN-SN-FILES S))))
     NIL
     (CONS (FN-STORE-EVENT-SEQUENCE (FN-SF-RECORD-CANDIDATE (FN-SN-FILES S)))
           (FN-STORE-EVENT-TXID (FN-SF-RECORD-CANDIDATE (FN-SN-FILES S))))
     (FN-SF-SUCCESSES (FN-SN-FILES S))
     (FN-SF-BARRIERS (FN-SN-FILES S)))
    (FN-SN-NODE S)
    (FN-SN-KEYRING S)
    (FN-SN-INDEX S)
    (FN-SN-KEYRING-GENERATION S)
... (54 more lines, in the run log on the box)
```

Assuming: nothing; the tree as committed.

### books/store-observed -- round 1

Wall 1.336 s; ACL2 exit 0.

```
ACL2 Error [Failure] in (DEFTHM FN-SN-OBSERVED-SEED-IS-STATE ...): See :DOC failure.
```

Key checkpoint (log line 941 is the error above):
```
*** Key checkpoint before reverting to proof by induction: ***
Subgoal 6
(IMPLIES
   (AND (FN-STRING-LISTP GROUPS)
        (FN-NO-DUPLICATESP GROUPS)
        (INTEGERP CAPACITY)
        (<= 0 CAPACITY)
        (INTEGERP FRONTIER)
        (<= 0 FRONTIER)
        (<= FRONTIER 4294967295)
        (FN-SF-RECORD-LISTP RECORDS 0 0 FRONTIER))
   (INTEGERP (FN-SN-KEYRING-GENERATION
                  (FN-SN-MAKE GROUPS CAPACITY
                              (FN-SF-MAKE :REPLAYING
                                          FRONTIER NIL RECORDS NIL NIL NIL 0)
                              (FN-NODE-INITIAL-STATE GROUPS CAPACITY)
                              NIL '(NIL NIL NIL)))))
```

Assuming: nothing; the tree as committed.

## Proved, not certified -- every proof in these books succeeded and a book below them has no certificate (8)

### books/native-admin -- round 1

Wall 3.594 s; ACL2 exit 0.

Waiting on: `books/store-node-traces`

Assuming: nothing; the tree as committed.

### books/native-control -- round 1

Wall 1.711 s; ACL2 exit 0.

Waiting on: `books/store-node-traces`

Assuming: nothing; the tree as committed.

### books/native-hybrid-control -- round 1

Wall 1.781 s; ACL2 exit 0.

Waiting on: `books/store-node-traces`

Assuming: nothing; the tree as committed.

### books/native-operator -- round 1

Wall 2.187 s; ACL2 exit 0.

Waiting on: `books/store-node-traces`

Assuming: nothing; the tree as committed.

### tests/acl2/native-admin-tests -- round 1

Wall 1.771 s; ACL2 exit 0.

Waiting on: `books/store-node-traces`

Assuming: nothing; the tree as committed.

### tests/acl2/native-control-tests -- round 1

Wall 1.728 s; ACL2 exit 0.

Waiting on: `books/store-node-traces`

Assuming: nothing; the tree as committed.

### tests/acl2/native-hybrid-control-tests -- round 1

Wall 1.723 s; ACL2 exit 0.

Waiting on: `books/store-node-traces`

Assuming: nothing; the tree as committed.

### tests/acl2/native-operator-tests -- round 1

Wall 2.013 s; ACL2 exit 0.

Waiting on: `books/store-node-traces`

Assuming: nothing; the tree as committed.

