; Teeth for books/owner-prepare-carried.lisp.
(in-package "ACL2")
(include-book "../../books/owner-prepare-carried")
(include-book "std/testing/must-fail" :dir :system)
(include-book "owner-served-invariants-tests")

; Reachable witness: owner-tests' *own-taken* (connection 4's submission in
; flight) after the four frontier events of its POST, so the store is
; :reserved with the durable history before the article, and the record is
; that submission's own (owner-served-invariants-tests osi-sub-record).
(defconst *pcar-t-record* (osi-sub-record 2 2 *osi-sub*))
(defconst *pcar-t-o*
  (fn-own-run *own-taken* (fn-own-take 4 (own-post-events *pcar-t-record*))))
(defconst *pcar-t-oc* (fn-ocfg-make *pcar-t-o* *osi-cfg* nil nil))
(defconst *pcar-t-files* (fn-sn-files (fn-own-store *pcar-t-o*)))
(assert-event (fn-own-relation *pcar-t-o*))
(assert-event (equal (fn-sf-phase *pcar-t-files*) :reserved))
(assert-event (equal (len (fn-sf-records *pcar-t-files*)) 2))

; The fold keystone on the witness history, and what it computes: 1 + the
; txid of the last record, not the record count.
(assert-event (equal (fn-pcar-next-lower (fn-sf-records *pcar-t-files*))
                     (fn-sf-next-lower (fn-sf-records *pcar-t-files*) 0)))
(assert-event (equal (fn-pcar-next-lower (fn-sf-records *pcar-t-files*))
                     (1+ (fn-store-event-txid
                          (car (last (fn-sf-records *pcar-t-files*)))))))
; No invariant is used: the equation holds on a list whose txids decrease
; (records swapped), which fn-sf-record-listp refuses.
(defconst *pcar-t-swapped*
  (list (cadr (fn-sf-records *pcar-t-files*)) (car (fn-sf-records *pcar-t-files*))))
(assert-event (not (fn-sf-record-listp *pcar-t-swapped* 0 0
                                       (fn-sf-frontier *pcar-t-files*))))
(assert-event (equal (fn-pcar-next-lower *pcar-t-swapped*)
                     (fn-sf-next-lower *pcar-t-swapped* 0)))
; The initial 0 is load-bearing: on the empty history the fold returns its
; accumulator, and the carried value is 0.
(must-fail
 (defthm fn-pcar-t-next-lower-with-another-start
   (equal (fn-pcar-next-lower nil) (fn-sf-next-lower nil 1))))

; The host's keystone on the witness, and it is not vacuous: below the
; budget the carried prepare stages the record; at the budget it is the
; identity.
(defconst *pcar-t-prepared* (fn-pcar-sbud-prepare *pcar-t-oc* *pcar-t-record* 100))
(assert-event (equal *pcar-t-prepared*
                     (fn-sbud-prepare *pcar-t-oc* *pcar-t-record* 100)))
(assert-event (equal (fn-sf-phase (fn-sn-files (fn-own-store (fn-ocfg-owner *pcar-t-prepared*))))
                     :record-staged))
(assert-event (fn-pcar-candidatep *pcar-t-record* (fn-sf-records *pcar-t-files*)
                                  (fn-sf-frontier *pcar-t-files*)))
(assert-event (equal (fn-pcar-sbud-prepare *pcar-t-oc* *pcar-t-record* 2) *pcar-t-oc*))
(assert-event (equal (fn-pcar-sbud-prepare *pcar-t-oc* *pcar-t-record* 2)
                     (fn-sbud-prepare *pcar-t-oc* *pcar-t-record* 2)))
; A record at the wrong transaction id is refused by both.
(defconst *pcar-t-late-record* (osi-sub-record 2 3 *osi-sub*))
(assert-event (not (fn-pcar-candidatep *pcar-t-late-record* (fn-sf-records *pcar-t-files*)
                                       (fn-sf-frontier *pcar-t-files*))))
(assert-event (equal (fn-pcar-sbud-prepare *pcar-t-oc* *pcar-t-late-record* 100)
                     (fn-sbud-prepare *pcar-t-oc* *pcar-t-late-record* 100)))
(assert-event (equal (fn-pcar-sbud-prepare *pcar-t-oc* *pcar-t-late-record* 100)
                     *pcar-t-oc*))
; Preservation on the witness.
(assert-event (fn-own-relation (fn-ocfg-owner *pcar-t-prepared*)))

; The host's call runs compiled code: every carried function is guard-verified,
; under the reference's own guard.
(assert-event
 (and (eq (symbol-class 'fn-pcar-next-lower (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-pcar-candidatep (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-pcar-stage-record (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-pcar-spc-prepare (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-pcar-opc-owner-prepare (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-pcar-opc-prepare (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-pcar-sbud-prepare (w state)) :common-lisp-compliant)))
(assert-event (equal (guard 'fn-pcar-sbud-prepare nil (w state))
                     (guard 'fn-sbud-prepare nil (w state))))
(assert-event (equal (guard 'fn-pcar-candidatep nil (w state))
                     (guard 'fn-sf-candidatep nil (w state))))

; fn-pcar-sbud-prepare-preserves-owner-relation without its hypothesis: the
; same owner with its first record dropped (the relation fails; the store
; is still :reserved), prepared, does not satisfy the relation.
(defconst *pcar-t-bad-o*
  (let* ((o *pcar-t-o*)
         (files (update-nth 4 (cdr (fn-sf-records *pcar-t-files*)) *pcar-t-files*)))
    (fn-own-make (update-nth 2 files (fn-own-store o))
                 (fn-own-view o) (fn-own-conns o) (fn-own-next-id o)
                 (fn-own-max-conns o) (fn-own-pending o) (fn-own-ledger o)
                 (fn-own-clock o) (fn-own-facts o) (fn-own-config o)
                 (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o))))
(defconst *pcar-t-bad-oc* (fn-ocfg-make *pcar-t-bad-o* *osi-cfg* nil nil))
(assert-event (not (fn-own-relation *pcar-t-bad-o*)))
(must-fail
 (defthm fn-pcar-t-preserves-relation-without-relation
   (fn-own-relation
    (fn-ocfg-owner (fn-pcar-sbud-prepare *pcar-t-bad-oc* *pcar-t-record* 100)))))
