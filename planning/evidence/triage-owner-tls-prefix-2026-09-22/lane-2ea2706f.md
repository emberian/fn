# Triage triage-20260922T175555Z-94f7 -- persvati

**This is not evidence of certification.** A triage run certifies a tree whose sources were substituted on the box. Its certificates are published nowhere, its manifest is not archived, and nothing in this report is a certification claim about this revision. The certify run ids are left out for that reason; the farm run ids below locate the logs on the box.

Closure: 93 books under 1 root (books/owner-tls-prefix), per-book budget 800 s, remote root `/home/ember/fn-gates/t7-owner-tls`.

Mode: ACL2 provisional certification: a Create wave, one parallel Convert wave that does every book's proofs, and a Complete wave.

## Rounds

- Round 1 (run-20260922T175556Z-6fd4, exit 1): 8 of 93 books failed -- 5 independent, 3 blocked; 725.657 s of certification wall; the tree as committed.

## Independent reds (5)

### books/owner-invariants -- round 1

Wall 40.723 s; ACL2 exit 0.

```
ACL2 Error [Failure] in (DEFTHM FN-OWN-READ-OFFERS-AGAINST-THE-LIVE-NODE ...): See :DOC failure.
```

Key checkpoint (log line 30283 is the error above):
```
*** Key checkpoint at the top level: ***
Subgoal 3
(IMPLIES
 (AND
  (FN-PEER-SESSION-PEER (FN-AUTH-SESSION-BASE (FN-OWN-CONN-SESSION CONN)))
  (NOT
    (FN-PEER-SESSION-CFG (FN-AUTH-SESSION-BASE (FN-OWN-CONN-SESSION CONN)))))
 (EQUAL
     (FN-PEER-SESSION-NODE (FN-AUTH-SESSION-BASE (FN-OWN-CONN-SESSION CONN)))
     (FN-SN-NODE (FN-OWN-STORE O))))
```

Assuming: nothing; the tree as committed.

### books/owner-tls-prefix -- round 1

Wall 2.079 s; ACL2 exit 0.

```
ACL2 Error [Failure] in (DEFTHM FN-OCFG-READ-TLS-PREFIX-IS-FULL-READ ...): See :DOC failure.
```

Key checkpoint (log line 744 is the error above):
```
*** Key checkpoint before reverting to proof by induction: ***
Subgoal 13''
(IMPLIES
 (AND
  (NOT (FN-WIRE-STATEP
            (FN-OWN-CONN-WIRE
                 (FN-OWN-FIND-CONN ID (FN-OWN-CONNS (FN-OCFG-OWNER OC))))))
  (FN-OCFG-STATEP OC)
  (FN-OWN-FIND-CONN ID (FN-OWN-CONNS (FN-OCFG-OWNER OC)))
  (NOT
   (FN-OWN-CONN-BOUNDEDP
    (FN-OWN-CONN-MAKE
     (FN-OWN-CONN-ID (FN-OWN-FIND-CONN ID (FN-OWN-CONNS (FN-OCFG-OWNER OC))))
     (FN-OWN-CONN-VERSION
          (FN-OWN-FIND-CONN ID (FN-OWN-CONNS (FN-OCFG-OWNER OC))))
     (FN-OWN-CONN-FRONTIER
          (FN-OWN-FIND-CONN ID (FN-OWN-CONNS (FN-OCFG-OWNER OC))))
     (FN-SERVED-CONN-WIRE
      (FN-SERVED-RESULT-CONN
       (FN-SERVED-COUNTED-RESULT
        (FN-SERVED-STEP-COUNTED-FAST
           (FN-SERVED-MAKE-CONN
                (FN-OWN-CONN-WIRE
                     (FN-OWN-FIND-CONN ID (FN-OWN-CONNS (FN-OCFG-OWNER OC))))
                (FN-OWN-CONN-LIVE-SESSION
... (118 more lines, in the run log on the box)
```

Assuming: nothing; the tree as committed.

### books/store-node-resolution -- round 1

Wall 1.655 s; ACL2 exit 0.

```
ACL2 Error [Failure] in (DEFTHM FN-SN-KNOWN-ABORT-IS-EXACT-NODE-ABORT ...): See :DOC failure.
```

Key checkpoint (log line 1449 is the error above):
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

Wall 117.321 s; ACL2 exit 0.

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

Wall 1.343 s; ACL2 exit 0.

```
ACL2 Error [Failure] in (DEFTHM FN-SN-OBSERVED-SEED-IS-STATE ...): See :DOC failure.
```

Key checkpoint (log line 940 is the error above):
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

## Proved, not certified -- every proof in these books succeeded and a book below them has no certificate (3)

### books/owner -- round 1

Wall 2.207 s; ACL2 exit 0.

Waiting on: `books/store-node-traces`

Assuming: nothing; the tree as committed.

### books/owner-config -- round 1

Wall 3.109 s; ACL2 exit 0.

Waiting on: `books/store-node-traces`

Assuming: nothing; the tree as committed.

### books/owner-fault -- round 1

Wall 1.889 s; ACL2 exit 0.

Waiting on: `books/store-node-traces`

Assuming: nothing; the tree as committed.

