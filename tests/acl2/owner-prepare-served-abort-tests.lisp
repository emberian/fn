; Owner-level reachable teeth for the deferred known abort (lane
; host-decisions item 2, PRF-299): books/store-node-resolution fn-sn-known-abort
; aborts every non-held staged event, and books/owner-prepare-served-ocl
; fn-psrv-known-abort-preserves-invariant covers every candidate.  The host's
; entry is host/owner-host.lisp fn-owner-known-abort: (:store (:known-abort))
; through fn-owner-step, answering :aborted exactly when the Store left a
; record phase for :ready.  The staged owners are
; owner-prepare-served-events-tests' topic, consumer and keyring events and
; owner-identity-served-tests' interned composite row, each staged by the
; host's own prepare over ACL2's own proposal.
(in-package "ACL2")
(include-book "owner-identity-served-tests")

(defun psa-abort (oc fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (fn-ocfg-step oc (list :store (list :known-abort)) fn-arena))
(bpr-lift psa-abort 1)
(defun psa-txid (oc)
  (fn-state-next-txid (fn-node-acceptance (fn-sn-node (lgt-store oc)))))
(defun psa-frontier (oc) (fn-sf-frontier (fn-sn-files (lgt-store oc))))
(defun psa-records (oc) (fn-sf-records (fn-sn-files (lgt-store oc))))

; The host's word (fn-owner-known-abort) for BEFORE and AFTER.
(defun psa-word (before after)
  (if (and (member-equal (lgt-phase before) '(:record-staged :record-data-durable))
           (not (equal (lgt-store after) (lgt-store before)))
           (equal (lgt-phase after) :ready))
      :aborted
    :fault))

; A second prepare after the abort: the topic install ACL2 proposes at the
; aborted owner's coordinates, reserved and prepared by the host's entries.
(defun psa-second (oc)
  (let* ((r (fn-olr-ocfg-reserve oc))
         (p (fn-th-local-propose :install (fn-sn-topic (lgt-store r)) (psa-txid r) 0 1000
                                 (make-list 32 :initial-element 6) 0)))
    (if (equal (car p) :ok) (fn-psrv-prepare-topic r (cadr p)) :no-proposal)))

(defmacro psa-witness (name staged)
  `(progn
     (make-event (list 'defconst ',name (list 'quote (in-arena-psa-abort *sr-arena* ,staged))))
     (assert-event (fn-lgoc-invariantp ,staged))
     (assert-event (equal (lgt-phase ,staged) :record-staged))
     (assert-event (not (fn-held-p (pse-candidate ,staged))))
     (assert-event (equal (psa-word ,staged ,name) :aborted))
     (assert-event (equal (lgt-phase ,name) :ready))
     ; the node advanced over the reserved txid to the frontier
     (assert-event (equal (psa-txid ,staged) (1- (psa-frontier ,staged))))
     (assert-event (equal (psa-txid ,name) (psa-frontier ,staged)))
     (assert-event (equal (psa-frontier ,name) (psa-frontier ,staged)))
     ; nothing published
     (assert-event (equal (psa-records ,name) (psa-records ,staged)))
     (assert-event (fn-lgoc-invariantp ,name))
     ; not fenced: a second prepare is admitted and carries the invariant
     (assert-event (equal (lgt-phase (psa-second ,name)) :record-staged))
     (assert-event (fn-lgoc-invariantp (psa-second ,name)))))

; REACHABLE witnesses, one per deferred kind.
(psa-witness *psa-topic-aborted* *pse-topic-staged*)
(psa-witness *psa-consumer-aborted* *pse-consumer-staged*)
(psa-witness *psa-keyring-aborted* *pse-identity-staged*)
(psa-witness *psa-composite-aborted* *ois-staged*)
; The composite row is a retained composite (fn-hstxa-p), not a held row.
(assert-event (fn-hstxa-p (pse-candidate *ois-staged*)))
