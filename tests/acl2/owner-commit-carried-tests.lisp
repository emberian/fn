; Teeth for books/owner-commit-carried.lisp.
(in-package "ACL2")
(include-book "../../books/owner-commit-carried")
(include-book "std/testing/must-fail" :dir :system)
(include-book "owner-served-invariants-tests")

; Reachable witness: owner-served-invariants-tests' *osi-completing*,
; connection 4's injected article staged and at :completing, reached by
; fn-own-run from owner-tests.  Its history has three records and the
; completion is the third, so the seek skips two records unexamined.
(defconst *ccar-t-o* *osi-completing*)
(defconst *ccar-t-cfg* *osi-cfg*)
(defconst *ccar-t-files* (fn-sn-files (fn-own-store *ccar-t-o*)))
(assert-event (fn-own-relation *ccar-t-o*))
(assert-event (fn-sn-statep (fn-own-store *ccar-t-o*)))
(assert-event (equal (len (fn-sf-records *ccar-t-files*)) 3))
(assert-event (equal (car (fn-sf-completion *ccar-t-files*)) 2))
; The keystone on the witness, and it is not vacuous: the commit is the
; durable one, the record found is the article record, and the owner moves.
(assert-event (equal (fn-ccar-own-finish *ccar-t-o* *ccar-t-cfg*)
                     (fn-own-finish *ccar-t-o* *ccar-t-cfg*)))
(assert-event (equal (car (fn-ccar-own-finish *ccar-t-o* *ccar-t-cfg*)) :durable))
(assert-event (fn-record-p (fn-ccar-completion-record (fn-own-store *ccar-t-o*))))
(assert-event (equal (fn-ccar-completion-record (fn-own-store *ccar-t-o*))
                     (car (last (fn-sf-records *ccar-t-files*)))))
(assert-event (not (equal (cdr (fn-ccar-own-finish *ccar-t-o* *ccar-t-cfg*))
                          *ccar-t-o*)))
; Preservation on the witness: the relation and the premise hold after.
(assert-event (fn-own-relation (cdr (fn-ccar-own-finish *ccar-t-o* *ccar-t-cfg*))))
(assert-event (fn-sn-statep
               (fn-own-store (cdr (fn-ccar-own-finish *ccar-t-o* *ccar-t-cfg*)))))
; The mismatch witness (another record completed for the submission) is
; still :fault through the carried commit.
(assert-event (equal (fn-ccar-own-finish *osi-mismatch-completing* *ccar-t-cfg*)
                     (fn-own-finish *osi-mismatch-completing* *ccar-t-cfg*)))
(assert-event (equal (car (fn-ccar-own-finish *osi-mismatch-completing* *ccar-t-cfg*))
                     :fault))

; The host's call runs compiled code: every carried function is guard-verified.
(assert-event
 (and (eq (symbol-class 'fn-ccar-own-finish (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-ccar-own-complete (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-ccar-sn-finish (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-ccar-completion-enabledp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-ccar-completion-core-enabledp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-ccar-completion-names-submission-p (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-ccar-seek (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-ccar-sn-finish-enabled (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-ccar-own-complete-enabled (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-ccar-cpe-projection-step (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-ccar-th-prefix-step (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-ccar-sn-record-bindsp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-ccar-ocfg-complete (w state)) :common-lisp-compliant)))

; The premise.  The same owner with the first record of its history dropped
; (test-only surgery; a store whose records do not start at sequence 0, as
; an unrenumbered compaction would leave).  Only the record-list conjunct of
; fn-sn-statep fails: the node, the phase and the frontier are the
; witness's.  The whole-history search still finds the completion record;
; the seek looks at position 2, runs off the end and finds nothing.
(defconst *ccar-t-bad-files*
  (update-nth 4 (cdr (fn-sf-records *ccar-t-files*)) *ccar-t-files*))
(defconst *ccar-t-bad-store*
  (update-nth 2 *ccar-t-bad-files* (fn-own-store *ccar-t-o*)))
(defconst *ccar-t-bad-o*
  (let ((o *ccar-t-o*))
    (fn-own-make *ccar-t-bad-store*
                 (fn-own-view o) (fn-own-conns o) (fn-own-next-id o)
                 (fn-own-max-conns o) (fn-own-pending o) (fn-own-ledger o)
                 (fn-own-clock o) (fn-own-facts o) (fn-own-config o)
                 (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o))))
(assert-event (equal (fn-sn-files (fn-own-store *ccar-t-bad-o*)) *ccar-t-bad-files*))
(assert-event (not (fn-sn-statep *ccar-t-bad-store*)))
(assert-event (not (fn-sf-record-listp (fn-sf-records *ccar-t-bad-files*) 0 0
                                       (fn-sf-frontier *ccar-t-bad-files*))))
(assert-event (fn-node-statep (fn-sn-node *ccar-t-bad-store*)))
(assert-event (equal (fn-sf-phase *ccar-t-bad-files*) :completing))
(assert-event (not (fn-own-relation *ccar-t-bad-o*)))
(assert-event (equal (fn-sn-completion-record *ccar-t-bad-store*)
                     (fn-sn-completion-record (fn-own-store *ccar-t-o*))))
(assert-event (with-guard-checking :none
               (null (fn-ccar-completion-record *ccar-t-bad-store*))))

; fn-ccar-seek-is-find-record without fn-sf-record-listp.
(must-fail
 (defthm fn-ccar-t-seek-without-record-listp
   (equal (fn-ccar-seek (fn-sf-completion *ccar-t-bad-files*)
                        (fn-sf-records *ccar-t-bad-files*) 0)
          (fn-sn-find-record (fn-sf-completion *ccar-t-bad-files*)
                             (fn-sf-records *ccar-t-bad-files*)))))
; fn-ccar-completion-record-is-completion-record without fn-sn-statep.
(must-fail
 (defthm fn-ccar-t-completion-record-without-statep
   (equal (fn-ccar-completion-record *ccar-t-bad-store*)
          (fn-sn-completion-record *ccar-t-bad-store*))))
; fn-ccar-completion-names-submission-p-is-reference without fn-sn-statep:
; the reference finds connection 4's record, the seek finds none.
(assert-event
 (with-guard-checking :none
  (fn-own-completion-names-submission-p *ccar-t-bad-o* *ccar-t-cfg*)))
(must-fail
 (defthm fn-ccar-t-names-submission-without-statep
   (equal (fn-ccar-completion-names-submission-p *ccar-t-bad-o* *ccar-t-cfg*)
          (fn-own-completion-names-submission-p *ccar-t-bad-o* *ccar-t-cfg*))))
; fn-ccar-own-finish-is-own-finish has no hypothesis, and holds here too:
; in the logic both gates conjoin fn-sn-statep and refuse.  The premise
; separates the executed code, which drops that conjunct: the reference's
; raw gate would find the record by the whole-history search and complete,
; the carried one finds nothing (the two lookups above).  Guard verification
; equates each raw function with its logic only where fn-sn-statep holds.
(assert-event
 (with-guard-checking :none
  (and (equal (fn-ccar-own-finish *ccar-t-bad-o* *ccar-t-cfg*)
              (fn-own-finish *ccar-t-bad-o* *ccar-t-cfg*))
       (equal (fn-ccar-own-finish *ccar-t-bad-o* *ccar-t-cfg*)
              (cons :fault *ccar-t-bad-o*)))))
(assert-event (equal (guard 'fn-ccar-own-finish nil (w state))
                     (guard 'fn-own-finish nil (w state))))
; The preservation theorems without their hypotheses: the bad owner is left
; as it was, so neither the premise nor the relation holds after.
(must-fail
 (defthm fn-ccar-t-preserves-statep-without-statep
   (fn-sn-statep (fn-own-store (cdr (fn-ccar-own-finish *ccar-t-bad-o* *ccar-t-cfg*))))))
(must-fail
 (defthm fn-ccar-t-preserves-relation-without-relation
   (fn-own-relation (cdr (fn-ccar-own-finish *ccar-t-bad-o* *ccar-t-cfg*)))))
