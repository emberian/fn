; Witnesses and teeth for the configuration record keystones.
;
; Two reachable, non-degenerate witnesses:
;
;   * a three-generation history -- create two groups and set capacity, create
;     a third group, retire one -- whose three intermediate configurations
;     differ from each other and from the final one, so a fold that dropped a
;     record or applied a delta list out of order would be separated;
;   * a creation that is refused because the resulting served table would not
;     render inside the RFC 3977 section 3.1 initial line.
;
; And one tooth per hypothesis of each keystone, as a concrete violating
; value rather than a general negated `must-fail'.

(in-package "ACL2")
(include-book "../../books/config-invariants")
(include-book "../../books/store-config")

(local (in-theory (enable fn-cfg-vocabulary fn-cfg-invariants-vocabulary)))

; -----------------------------------------------------------------------------
; The default record is exactly today's compiled-in table.
;
; `*fn-store-groups*' survives until packet R4 deletes it.  Until then this is
; the equality that says the configuration record replaces it rather than
; competing with it.

(assert-event
 (equal (fn-cfg-group-names
         (fn-cfg-value (fn-config-replay 0 510 (list *fn-cfg-default-record*)))
         1)
        *fn-store-groups*))

(assert-event (fn-cfg-recordp *fn-cfg-default-record*))
(assert-event (equal (fn-cfg-record-generation *fn-cfg-default-record*) 1))

; -----------------------------------------------------------------------------
; A three-generation history with a retirement

(defconst *cfg-t-stamp* (fn-clock-observation 7 1000 5 t))

(defconst *cfg-t-r1*
  (fn-cfg-record-make
   0 10 1
   (list (fn-cfg-create-group "fn.letters" "policy-a")
         (fn-cfg-create-group "fn.test" "policy-a")
         (fn-cfg-set-capacity 4096))
   *cfg-t-stamp*))

(defconst *cfg-t-r2*
  (fn-cfg-record-make
   1 11 2
   (list (fn-cfg-create-group "fn.dtn" "policy-b")
         (fn-cfg-set-limit "max-payload" 32768))
   *cfg-t-stamp*))

(defconst *cfg-t-r3*
  (fn-cfg-record-make
   2 12 3
   (list (fn-cfg-remove-group "fn.test")
         (fn-cfg-set-peers (list (fn-cfg-row-make "dtn://peer" "tcpcl" "plan"
                                                  0))))
   *cfg-t-stamp*))

(defconst *cfg-t-history* (list *cfg-t-r1* *cfg-t-r2* *cfg-t-r3*))

(assert-event (fn-cfg-recordp *cfg-t-r1*))
(assert-event (fn-cfg-recordp *cfg-t-r2*))
(assert-event (fn-cfg-recordp *cfg-t-r3*))

(defconst *cfg-t-g1* (fn-config-replay 0 510 (list *cfg-t-r1*)))
(defconst *cfg-t-g2* (fn-config-replay 0 510 (list *cfg-t-r1* *cfg-t-r2*)))
(defconst *cfg-t-g3* (fn-config-replay 0 510 *cfg-t-history*))

(assert-event (fn-cfgp *cfg-t-g3*))
(assert-event (equal (fn-cfg-generation *cfg-t-g1*) 1))
(assert-event (equal (fn-cfg-generation *cfg-t-g2*) 2))
(assert-event (equal (fn-cfg-generation *cfg-t-g3*) 3))

; Non-degenerate: the three served tables are three different tables, and the
; capacity is not zero, so a fold that ignored a record would be caught.
(assert-event
 (equal (fn-cfg-group-names (fn-cfg-value *cfg-t-g1*) 1)
        '("fn.letters" "fn.test")))
(assert-event
 (equal (fn-cfg-group-names (fn-cfg-value *cfg-t-g2*) 2)
        '("fn.letters" "fn.test" "fn.dtn")))
(assert-event
 (equal (fn-cfg-group-names (fn-cfg-value *cfg-t-g3*) 3)
        '("fn.letters" "fn.dtn")))
(assert-event (equal (fn-cfg-capacity (fn-cfg-value *cfg-t-g3*)) 4096))

; Retirement never deletes: the retired entry, its creation stamp and its
; local-number watermark are all still there at generation 3, and the group is
; still live AT generation 2, which is what keeps an article accepted then
; bound to a group that existed then.
(assert-event
 (consp (fn-cfg-group-find (fn-cfg-groups (fn-cfg-value *cfg-t-g3*))
                           "fn.test")))
(assert-event
 (equal (fn-cfg-group-created-stamp
         (fn-cfg-group-find (fn-cfg-groups (fn-cfg-value *cfg-t-g3*))
                            "fn.test"))
        *cfg-t-stamp*))
(assert-event
 (equal (fn-cfg-group-created-gen
         (fn-cfg-group-find (fn-cfg-groups (fn-cfg-value *cfg-t-g3*))
                            "fn.test"))
        1))
(assert-event
 (equal (fn-cfg-group-retired-gen
         (fn-cfg-group-find (fn-cfg-groups (fn-cfg-value *cfg-t-g3*))
                            "fn.test"))
        3))
(assert-event (fn-cfg-group-livep (fn-cfg-value *cfg-t-g3*) 2 "fn.test"))
(assert-event
 (not (fn-cfg-group-livep (fn-cfg-value *cfg-t-g3*) 3 "fn.test")))

; Re-creating the retired name resumes its numbering rather than appending a
; second entry for the same name.
(defconst *cfg-t-g4*
  (fn-config-replay
   0 510
   (append *cfg-t-history*
           (list (fn-cfg-record-make
                  3 13 4 (list (fn-cfg-create-group "fn.test" "policy-c"))
                  *cfg-t-stamp*)))))
(assert-event
 (equal (len (fn-cfg-groups (fn-cfg-value *cfg-t-g4*)))
        (len (fn-cfg-groups (fn-cfg-value *cfg-t-g3*)))))
(assert-event (fn-cfg-group-livep (fn-cfg-value *cfg-t-g4*) 4 "fn.test"))

; The codec round trip on the non-degenerate record, and its canonicality:
; a different record does not encode to the same octets.
(assert-event
 (equal (fn-cfg-decode-exact (fn-cfg-encode *cfg-t-r3*))
        (fn-record-parse-ok *cfg-t-r3* nil)))
(assert-event
 (not (equal (fn-cfg-encode *cfg-t-r3*) (fn-cfg-encode *cfg-t-r2*))))

; -----------------------------------------------------------------------------
; Teeth: one concrete violating value per hypothesis.

; `fn-cfg-record-acceptablep' hypothesis 1: the record's generation must be
; the successor of the replayed one.  A record claiming generation 7 over an
; empty configuration is refused, and the whole replay faults rather than
; applying part of it.
(defconst *cfg-t-wrong-gen*
  (fn-cfg-record-make 0 10 7
                      (list (fn-cfg-create-group "fn.letters" "policy-a"))
                      *cfg-t-stamp*))
(assert-event (fn-cfg-recordp *cfg-t-wrong-gen*))
(assert-event (equal (fn-config-replay 0 510 (list *cfg-t-wrong-gen*))
                     :fault))

; Hypothesis 2 (`fn-cfg-recordp'): a record whose generation is not a uint32.
(defconst *cfg-t-bad-record*
  (fn-cfg-record-make 0 10 :one
                      (list (fn-cfg-create-group "fn.letters" "policy-a"))
                      *cfg-t-stamp*))
(assert-event (not (fn-cfg-recordp *cfg-t-bad-record*)))
(assert-event (equal (fn-config-replay 0 510 (list *cfg-t-bad-record*))
                     :fault))

; A record with an empty delta list is not a record: a generation bump that
; changes nothing is not a reconfiguration.
(assert-event
 (not (fn-cfg-recordp (fn-cfg-record-make 0 10 1 nil *cfg-t-stamp*))))

; Hypothesis 3 (admissibility), capacity: a capacity below the reservation
; total is refused, and the refusal changes nothing.
(assert-event
 (equal (fn-cfg-admissible-reason (fn-cfg-value *cfg-t-g3*) 4 *cfg-t-stamp*
                                  100 510 (list (fn-cfg-set-capacity 99)))
        :capacity-below-reserved))
(assert-event
 (null (fn-cfg-admissible-reason (fn-cfg-value *cfg-t-g3*) 4 *cfg-t-stamp*
                                 99 510 (list (fn-cfg-set-capacity 99)))))
(assert-event
 (equal (fn-config-replay-loop
         *cfg-t-g3* 100 510
         (list (fn-cfg-record-make 3 13 4 (list (fn-cfg-set-capacity 99))
                                   *cfg-t-stamp*)))
        :fault))

; Hypothesis 3, duplicate creation: creating a live group again is refused,
; while creating it after a retirement in the SAME record is admissible.
(assert-event
 (equal (fn-cfg-admissible-reason
         (fn-cfg-value *cfg-t-g3*) 4 *cfg-t-stamp* 0 510
         (list (fn-cfg-create-group "fn.letters" "policy-a")))
        :duplicate-group))
(assert-event
 (null (fn-cfg-admissible-reason
        (fn-cfg-value *cfg-t-g3*) 4 *cfg-t-stamp* 0 510
        (list (fn-cfg-remove-group "fn.letters")
              (fn-cfg-create-group "fn.letters" "policy-d")))))

; Hypothesis 3, removal: retiring a group that is not live is refused.
(assert-event
 (equal (fn-cfg-admissible-reason
         (fn-cfg-value *cfg-t-g3*) 4 *cfg-t-stamp* 0 510
         (list (fn-cfg-remove-group "fn.test")))
        :no-such-group))

; -----------------------------------------------------------------------------
; The overflowing creation.
;
; A creation whose resulting served table would not render inside the RFC 3977
; section 3.1 initial line is refused: one reconfiguration must not be able to
; deny service to every future connection.  The ceiling is an argument, so
; `books/nntp-syntax' stays its only owner.

(defconst *cfg-t-long-name*
  "fn.a-very-long-group-name-used-only-to-overflow-the-initial-line-0001")

(defconst *cfg-t-wide*
  (fn-config-replay
   0 4096
   (list (fn-cfg-record-make
          0 10 1
          (list (fn-cfg-create-group *cfg-t-long-name* "policy-a")
                (fn-cfg-create-group "fn.letters" "policy-a")
                (fn-cfg-create-group "fn.test" "policy-a"))
          *cfg-t-stamp*))))

(assert-event (fn-cfgp *cfg-t-wide*))

; Under a 64-octet ceiling the same creation is inadmissible, with the named
; reason, and under a wide ceiling it is admissible: the tooth separates on
; the ceiling alone.
(assert-event
 (equal (fn-cfg-admissible-reason
         (fn-cfg-value *cfg-t-wide*) 2 *cfg-t-stamp* 0 64
         (list (fn-cfg-create-group "fn.dtn" "policy-b")))
        :group-table-unprojectable))
(assert-event
 (null (fn-cfg-admissible-reason
        (fn-cfg-value *cfg-t-wide*) 2 *cfg-t-stamp* 0 510
        (list (fn-cfg-create-group "fn.dtn" "policy-b")))))
(assert-event
 (equal (fn-config-replay-loop
         *cfg-t-wide* 0 64
         (list (fn-cfg-record-make
                1 11 2 (list (fn-cfg-create-group "fn.dtn" "policy-b"))
                *cfg-t-stamp*)))
        :fault))

; A limit above its format ceiling is refused, so no configuration can name a
; bound the codec cannot represent.
(assert-event
 (equal (fn-cfg-admissible-reason
         (fn-cfg-value *cfg-t-g3*) 4 *cfg-t-stamp* 0 510
         (list (fn-cfg-set-limit "max-payload" 32769)))
        :limit-above-ceiling))

; -----------------------------------------------------------------------------
; Replay is a fold, on this history rather than in the abstract.

(assert-event
 (equal (fn-config-replay-loop *cfg-t-g2* 0 510 (list *cfg-t-r3*))
        *cfg-t-g3*))

; A crash image that lost the last record recovers generation 2, not 3:
; `<=', never `='.
(assert-event
 (equal (fn-cfg-generation
         (fn-config-replay 0 510 (fn-cfg-take 2 *cfg-t-history*)))
        2))
(assert-event
 (< (fn-cfg-generation (fn-config-replay 0 510 (fn-cfg-take 2
                                                            *cfg-t-history*)))
    (fn-cfg-generation (fn-config-replay 0 510 *cfg-t-history*))))
