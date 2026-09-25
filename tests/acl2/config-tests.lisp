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
(include-book "../../books/config-records")
(include-book "../../books/node-config")
(include-book "../../books/store-config")
(include-book "../../books/codec-attach")

(local (in-theory (enable fn-cfg-vocabulary fn-cfg-invariants-vocabulary
                          fn-cnode-vocabulary)))

; -----------------------------------------------------------------------------
; The default record is exactly the former compiled-in table.
;
; `*fn-store-groups*' is gone (packet R4); the two names below are what it
; said, and the configured node built on the default record has exactly the
; acceptance state `fn-initial-state' built from them (the keystone
; `fn-cnode-initial-of-the-default-record-is-fn-initial-state-of-its-groups').

(assert-event
 (equal (fn-cfg-group-names
         (fn-cfg-value (fn-config-replay 0 (fn-cnode-line-ceiling)
                                         (list *fn-cfg-default-record*)))
         1)
        '("fn.letters" "fn.test")))
(assert-event (equal (fn-cnode-line-ceiling) 510))

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
; bound the codec cannot represent.  The ceiling is the record codec's payload
; width (D27), no longer the pre-D27 32 768.
(assert-event
 (equal (fn-cfg-admissible-reason
         (fn-cfg-value *cfg-t-g3*) 4 *cfg-t-stamp* 0 510
         (list (fn-cfg-set-limit "max-payload" (1+ *fn-record-max-payload*))))
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

; -----------------------------------------------------------------------------
; Teeth for the hypotheses added on 2026-09-19 when the invariants book first
; certified: each is a concrete value on which the conclusion fails.

; `fn-cfg-groups-create-keeps-the-names-or-adds-one' needs a group list: on
; (nil) with name nil, `fn-cfg-group-find' answers nil yet creation replaces.
(assert-event (not (fn-cfg-group-listp '(nil))))
(assert-event (not (consp (fn-cfg-group-find '(nil) nil))))
(assert-event
 (not (equal (fn-cfg-group-all-names
              (fn-cfg-groups-create '(nil) 1 *cfg-t-stamp* nil "p"))
             (append (fn-cfg-group-all-names '(nil)) (list nil)))))

; `fn-cfg-groups-retire-preserves-group-listp' needs the entry live at `gen':
; retiring at generation 0 an entry created at generation 1 leaves an entry
; retired before it was created.
(defconst *cfg-t-late-entry*
  (list (fn-cfg-group-make "fn.late" 1 *cfg-t-stamp* nil "policy-a" 0)))
(assert-event (fn-cfg-group-listp *cfg-t-late-entry*))
(assert-event (not (fn-cfg-entry-livep (fn-cfg-group-find *cfg-t-late-entry*
                                                          "fn.late")
                                       0)))
(assert-event
 (not (fn-cfg-group-listp (fn-cfg-groups-retire *cfg-t-late-entry* 0
                                                "fn.late"))))

; `fn-config-replay-loop-generation-counts-records' needs a numeric starting
; generation: on the empty history the loop returns its argument unchanged.
(assert-event
 (with-guard-checking
  :none
  (not (equal (fn-cfg-generation
               (fn-config-replay-loop (fn-cfg-make "x" (fn-cfg-empty-value))
                                      0 510 nil))
              (+ (fn-cfg-generation (fn-cfg-make "x" (fn-cfg-empty-value)))
                 0)))))

; `fn-config-aware-loop-is-fn-config-replay-on-config-only-histories' needs
; the configuration replay not to fault: on a refused record (generation 5 on
; the initial configuration) the aware loop keeps the last good configuration
; beside its fault while `fn-config-replay-loop' is `:fault'.
(defconst *cfg-t-refused-js*
  (list (fn-jrec-make :config 0
                      (fn-cfg-record-make 0 10 5 (list (fn-cfg-set-capacity 1))
                                          *cfg-t-stamp*))))
(defconst *cfg-t-node* (fn-node-initial-state '("fn.letters" "fn.test") 1048576))
(assert-event (fn-node-statep *cfg-t-node*))
(assert-event (and (fn-jrec-listp *cfg-t-refused-js*)
                   (fn-jrec-config-onlyp *cfg-t-refused-js*)
                   (fn-jrec-sequences-from *cfg-t-refused-js* 0)))
(assert-event
 (equal (fn-config-replay-loop (fn-cfg-initial) 0 510
                               (fn-jrec-bodies *cfg-t-refused-js*))
        :fault))
(assert-event
 (not (equal (fn-config-aware-config
              (fn-config-aware-loop *cfg-t-node* (fn-cfg-initial) 0 510
                                    *cfg-t-refused-js* 0))
             (fn-config-replay-loop (fn-cfg-initial) 0 510
                                    (fn-jrec-bodies *cfg-t-refused-js*)))))

; =============================================================================
; The configured node (books/node-config): witnesses and teeth

(defconst *cn-t-cfg1*
  (fn-config-replay 0 (fn-cnode-line-ceiling) (list *fn-cfg-default-record*)))
(defconst *cn-t-cn1* (fn-cnode-initial *cn-t-cfg1*))
(assert-event (fn-cnode-statep *cn-t-cn1*))
(assert-event (equal (fn-cnode-served *cn-t-cn1*) '("fn.letters" "fn.test")))
(assert-event (equal (fn-cnode-domain *cn-t-cn1*) '("fn.letters" "fn.test")))

; Two articles into fn.test at generation 1, through the lifted transitions:
; the served check passes at the pinned generation 1 and fails at any other.
(defconst *cn-t-payload* '(72 105))
(defun cn-t-post (cn msgid txid)
  (declare (xargs :mode :program))
  (fn-cnode-complete
   (fn-cnode-prepare cn 1 1 msgid *cn-t-payload* '("fn.test")
                     (concatenate 'string "ob-" msgid) "subject" "ev" 1 841000000)
   txid 1 :durable))
(defconst *cn-t-cn1b* (cn-t-post (cn-t-post *cn-t-cn1* "<a@t>" 0) "<b@t>" 1))
(assert-event (fn-cnode-statep *cn-t-cn1b*))
(assert-event (equal (len (fn-state-articles (fn-node-acceptance (fn-cnode-node *cn-t-cn1b*)))) 2))
(assert-event (equal (fn-next-number "fn.test" (fn-state-nexts (fn-node-acceptance (fn-cnode-node *cn-t-cn1b*)))) 3))

; --- fn-cnode-prepare-stages-only-served-groups -----------------------------
; Witness: a staged prepare carries exactly the offered, served groups.
(defconst *cn-t-staged*
  (fn-cnode-prepare *cn-t-cn1b* 1 1 "<c@t>" *cn-t-payload* '("fn.letters" "fn.test")
                    "ob-c" "subject" "ev" 1 841000000))
(assert-event (not (equal *cn-t-staged* *cn-t-cn1b*)))
(assert-event (equal (fn-pending-groups (fn-state-pending (fn-node-acceptance (fn-cnode-node *cn-t-staged*))))
                     '("fn.letters" "fn.test")))
; Tooth (the one hypothesis, "prepare staged"): a stale pin (generation 0) is
; refused, and then the pin is NOT the node's generation.
(assert-event (equal (fn-cnode-prepare *cn-t-cn1b* 0 1 "<c@t>" *cn-t-payload* '("fn.test")
                                       "ob-c" "subject" "ev" 1 841000000)
                     *cn-t-cn1b*))
(assert-event (not (equal 0 (fn-cfg-generation (fn-cnode-config *cn-t-cn1b*)))))

; --- retirement: generation 2 retires fn.test -------------------------------
(defconst *cn-t-retire*
  (fn-cfg-record-make 1 2 2 (list (fn-cfg-remove-group "fn.test")) *cfg-t-stamp*))
(assert-event (fn-cnode-record-acceptablep *cn-t-cn1b* *cn-t-retire* (fn-cnode-line-ceiling)))
(defconst *cn-t-cn2* (fn-cnode-apply-config *cn-t-cn1b* *cn-t-retire* (fn-cnode-line-ceiling)))
(assert-event (fn-cnode-statep *cn-t-cn2*))
(assert-event (equal (fn-cfg-generation (fn-cnode-config *cn-t-cn2*)) 2))
; SEPARATING WITNESS for fn-cnode-apply-config-keeps-watermarks-and-articles:
; the served table lost fn.test, the domain and the watermark did not, and
; both articles are still bound.
(assert-event (equal (fn-cnode-served *cn-t-cn2*) '("fn.letters")))
(assert-event (equal (fn-cnode-domain *cn-t-cn2*) '("fn.letters" "fn.test")))
(assert-event (equal (fn-next-number "fn.test" (fn-state-nexts (fn-node-acceptance (fn-cnode-node *cn-t-cn2*)))) 3))
(assert-event (equal (fn-state-articles (fn-node-acceptance (fn-cnode-node *cn-t-cn2*)))
                     (fn-state-articles (fn-node-acceptance (fn-cnode-node *cn-t-cn1b*)))))
; The separation that makes the served table load-bearing: at generation 2 a
; post into fn.test is refused by the configured node while the plain node,
; whose list is the domain, would still stage it.
(assert-event (equal (fn-cnode-prepare *cn-t-cn2* 2 1 "<d@t>" *cn-t-payload* '("fn.test")
                                       "ob-d" "subject" "ev" 1 841000000)
                     *cn-t-cn2*))
(assert-event (not (equal (fn-node-prepare (fn-cnode-node *cn-t-cn2*) 1 "<d@t>" *cn-t-payload*
                                           '("fn.test") "ob-d" "subject" "ev" 1 841000000)
                          (fn-cnode-node *cn-t-cn2*))))
; Revival at generation 3 resumes the numbering: the next article in fn.test
; takes local number 3, not 1.
(defconst *cn-t-revive*
  (fn-cfg-record-make 2 2 3 (list (fn-cfg-create-group "fn.test" "policy-b")) *cfg-t-stamp*))
(defconst *cn-t-cn3* (fn-cnode-apply-config *cn-t-cn2* *cn-t-revive* (fn-cnode-line-ceiling)))
(assert-event (fn-cnode-statep *cn-t-cn3*))
(assert-event (equal (fn-cnode-served *cn-t-cn3*) '("fn.letters" "fn.test")))
(defconst *cn-t-cn3b*
  (fn-cnode-complete
   (fn-cnode-prepare *cn-t-cn3* 3 1 "<e@t>" *cn-t-payload* '("fn.test") "ob-<e@t>" "subject" "ev" 1 841000000)
   2 1 :durable))
(assert-event (equal (fn-article-memberships
                      (car (fn-state-articles (fn-node-acceptance (fn-cnode-node *cn-t-cn3b*)))))
                     '(("fn.test" . 3))))
; Refusals change nothing: a retire of a name that is not served, and a
; reconfiguration while a transaction is staged (:group-staged).
(assert-event (equal (fn-cnode-apply-config *cn-t-cn2* *cn-t-retire* (fn-cnode-line-ceiling)) *cn-t-cn2*))
(assert-event (equal (fn-cnode-apply-config *cn-t-staged* *cn-t-retire* (fn-cnode-line-ceiling)) *cn-t-staged*))
(assert-event (not (fn-cnode-record-acceptablep *cn-t-staged* *cn-t-retire* (fn-cnode-line-ceiling))))
; A capacity decrease below the live reservation is refused at the node's real
; reservation total (two admitted charges of 1).
(assert-event (equal (fn-retain-reserved (fn-node-retention (fn-cnode-node *cn-t-cn1b*))) 2))
(assert-event (not (fn-cnode-record-acceptablep
                    *cn-t-cn1b* (fn-cfg-record-make 1 2 2 (list (fn-cfg-set-capacity 1)) *cfg-t-stamp*)
                    (fn-cnode-line-ceiling))))
(assert-event (fn-cnode-record-acceptablep
               *cn-t-cn1b* (fn-cfg-record-make 1 2 2 (list (fn-cfg-set-capacity 2)) *cfg-t-stamp*)
               (fn-cnode-line-ceiling)))

; --- the two-kind replay ------------------------------------------------------
(defun cn-t-article (seq txid msgid)
  (declare (xargs :mode :program))
  (fn-jrec-make :article seq
                (fn-record-make seq txid 1 msgid *cn-t-payload* '("fn.test")
                                (concatenate 'string "ob-" msgid) "subject" "ev" 1 841000000)))
(defconst *cn-t-js*
  (list (fn-jrec-make :config 0 *fn-cfg-default-record*)
        (cn-t-article 1 0 "<a@t>")
        (cn-t-article 2 1 "<b@t>")
        (fn-jrec-make :config 3 (fn-cfg-record-make 3 2 2 (list (fn-cfg-remove-group "fn.test")) *cfg-t-stamp*))
        (fn-jrec-make :config 4 (fn-cfg-record-make 4 2 3 (list (fn-cfg-create-group "fn.test" "policy-b")) *cfg-t-stamp*))
        (cn-t-article 5 2 "<e@t>")))
(defconst *cn-t-replayed* (fn-cnode-replay *cn-t-js*))
(assert-event (equal (fn-replay-result-kind *cn-t-replayed*) :ok))
(assert-event (equal (fn-cfg-generation (fn-cnode-config (fn-replay-result-node *cn-t-replayed*))) 3))
(assert-event (equal (fn-replay-result-node *cn-t-replayed*) *cn-t-cn3b*))
; Witness for fn-cnode-replay-loop-splits-at-any-prefix: every split of the
; six-record history resumes to the same result.
(defun cn-t-split-ok (n)
  (declare (xargs :mode :program))
  (let ((mid (fn-cnode-replay-loop (fn-cnode-initial (fn-cfg-initial)) (fn-cnode-line-ceiling)
                                   (take n *cn-t-js*) 0)))
    (equal (fn-cnode-replay-loop (fn-replay-result-node mid) (fn-cnode-line-ceiling)
                                 (nthcdr n *cn-t-js*) (fn-replay-result-sequence mid))
           *cn-t-replayed*)))
(assert-event (and (cn-t-split-ok 0) (cn-t-split-ok 1) (cn-t-split-ok 3) (cn-t-split-ok 5) (cn-t-split-ok 6)))
; Tooth (true-listp a): an improper prefix faults where the appended history
; does not.
(assert-event (equal (fn-replay-result-reason
                      (fn-cnode-replay-loop (fn-cnode-initial (fn-cfg-initial)) (fn-cnode-line-ceiling)
                                            (cons (car *cn-t-js*) 17) 0))
                     :improper-record-list))
(assert-event (equal (fn-replay-result-kind (fn-cnode-replay (append (list (car *cn-t-js*)) nil))) :ok))
; Witness for fn-cnode-recovered-generation-is-at-most-the-live-generation:
; the prefix that lost the last two records recovers generation 3, the prefix
; that lost the last three recovers 2, both at most the live 3.  A record
; posting into fn.test at generation 2 (retired) is a :node-refusal fault,
; and the plain replay would have accepted it.
(assert-event (equal (fn-cfg-generation (fn-cnode-config (fn-replay-result-node
                      (fn-cnode-replay (take 4 *cn-t-js*))))) 2))
(defconst *cn-t-into-retired*
  (list (car *cn-t-js*) (cadr *cn-t-js*) (caddr *cn-t-js*) (cadddr *cn-t-js*)
        (cn-t-article 4 2 "<z@t>")))
(assert-event (equal (fn-replay-result-reason (fn-cnode-replay *cn-t-into-retired*)) :node-refusal))
; The same three posts as a plain (transaction-only, sequences from 0) history
; are accepted by fn-replay, whose node admits over the domain and knows no
; retirement; the served check is what refused the third one above.
(assert-event (fn-replay-okp (fn-replay '("fn.letters" "fn.test") 1048576
                                        (fn-jrec-bodies (list (cn-t-article 0 0 "<a@t>")
                                                              (cn-t-article 1 1 "<b@t>")
                                                              (cn-t-article 2 2 "<z@t>"))))))

; --- books/store-config over a table parameter ------------------------------
; The name/code inversion holds over the configured domain and needs the
; no-NIL-name hypothesis: a NIL name's code comes back as "unknown".
(assert-event (equal (fn-store-groups-from-codes
                      (fn-store-codes-from-groups '("fn.test" "fn.letters") '("fn.letters" "fn.test"))
                      '("fn.letters" "fn.test"))
                     '("fn.test" "fn.letters")))
(assert-event (equal (fn-store-codes-from-groups '(nil) '(nil)) '(0)))
(assert-event (equal (fn-store-groups-from-codes '(0) '(nil)) :bad))

; -----------------------------------------------------------------------------
; Teeth for fn-cfg-labelp-of-record-group-name.  Tight witness: a group name
; at the record's ceiling (256 octets) is a label at the label's width.
; Without the hypothesis the conclusion fails: a 257-octet ASCII string is
; not a label.
(defconst *cfgt-name-256*
  (coerce (make-list *fn-record-max-group-name* :initial-element #\a) 'string))
(assert-event (and (fn-record-group-namep *cfgt-name-256*)
                   (fn-cfg-labelp *cfgt-name-256*)
                   (equal (length *cfgt-name-256*) *fn-cfg-max-label*)))
(assert-event (not (fn-cfg-labelp
                    (coerce (make-list 257 :initial-element #\a) 'string))))
