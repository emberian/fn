; Teeth for books/owner-fault.lisp: the seven fn-own-fault theorems that
; planning/proof-events.json registers under PRF-040.
;
; For each theorem: a reachable witness at which every hypothesis and the
; conclusion hold; then, per hypothesis, a value at which the other
; hypotheses hold and that one fails, asserted first, then the false
; conclusion asserted, then a must-fail on the conclusion.  A hypothesis no
; value can violate gets a theorem instead, proving the conclusion without
; it.  The fixture is tests/acl2/owner-tests.lisp's served POST scenario:
; *own-taken* has connection 4's submission in flight, connection 4 holding
; the pending transaction and reader 3 open.
;
; The two PRF-040 events over the configured wrapper
; (fn-ocfg-fault-keeps-every-other-connection, fn-ocfg-open-at-the-bound-refuses)
; have their teeth in tests/acl2/owner-served-invariants-tests.lisp.

(in-package "ACL2")
(include-book "owner-tests")
(include-book "std/testing/must-fail" :dir :system)

(defconst *oft-o* *own-taken*)
(assert-event (fn-own-relation *oft-o*))
(assert-event (fn-own-find-conn 3 (fn-own-conns *oft-o*)))
(assert-event (fn-own-find-conn 4 (fn-own-conns *oft-o*)))
(assert-event (equal (fn-own-sub-id (fn-own-inflight *oft-o*)) 4))
(assert-event (equal (fn-own-pending *oft-o*) 4))

; -----------------------------------------------------------------------------
; fn-own-fault-closes-the-faulted-connection (no hypothesis).  Witness:
; connection 4 was open, and after its fault it is not found.
(assert-event (fn-own-find-conn 4 (fn-own-conns *oft-o*)))
(assert-event (not (fn-own-find-conn 4 (fn-own-conns (cdr (fn-own-fault *oft-o* 4))))))

; -----------------------------------------------------------------------------
; fn-own-fault-keeps-every-other-connection.  Hypothesis: other /= id.
(defun oft-keeps-other-p (o id other)
  (equal (fn-own-find-conn other (fn-own-conns (cdr (fn-own-fault o id))))
         (fn-own-find-conn other (fn-own-conns o))))
; Witness: connection 4 faults, reader 3 (open) is the same record.
(assert-event (not (equal 3 4)))
(assert-event (oft-keeps-other-p *oft-o* 4 3))
; Tooth: other = id = 4.
(assert-event (equal 4 4))
(assert-event (not (oft-keeps-other-p *oft-o* 4 4)))
(must-fail (assert-event (oft-keeps-other-p *oft-o* 4 4)))

; -----------------------------------------------------------------------------
; fn-own-fault-clears-the-faulted-submission.  Hypotheses: (fn-own-inflight o)
; and (equal (fn-own-sub-id (fn-own-inflight o)) id).
(defun oft-clears-p (o id)
  (not (fn-own-inflight (cdr (fn-own-fault o id)))))
; Witness: connection 4's submission is in flight; its fault clears it.
(assert-event (fn-own-inflight *oft-o*))
(assert-event (oft-clears-p *oft-o* 4))
; Tooth (the submission is the faulted connection's): faulting reader 3,
; with connection 4's submission in flight, leaves it in flight.
(assert-event (fn-own-inflight *oft-o*))
(assert-event (not (equal (fn-own-sub-id (fn-own-inflight *oft-o*)) 3)))
(assert-event (not (oft-clears-p *oft-o* 3)))
(must-fail (assert-event (oft-clears-p *oft-o* 3)))
; (fn-own-inflight o) has no tooth: nothing in flight stays nothing in
; flight, so the conclusion holds without it.  The hypothesis is redundant.
(defthm oft-clears-the-faulted-submission-needs-only-the-id
  (implies (equal (fn-own-sub-id (fn-own-inflight o)) id)
           (not (fn-own-inflight (cdr (fn-own-fault o id)))))
  :hints (("Goal" :in-theory (enable fn-own-fault fn-own-close))))

; -----------------------------------------------------------------------------
; fn-own-fault-keeps-another-connections-submission.  Hypotheses:
; (fn-own-inflight o) and (not (equal (fn-own-sub-id (fn-own-inflight o)) id)).
(defun oft-keeps-another-p (o id)
  (equal (fn-own-inflight (cdr (fn-own-fault o id))) (fn-own-inflight o)))
; Witness: reader 3 faults; connection 4's submission stays in flight.
(assert-event (fn-own-inflight *oft-o*))
(assert-event (not (equal (fn-own-sub-id (fn-own-inflight *oft-o*)) 3)))
(assert-event (oft-keeps-another-p *oft-o* 3))
; Tooth (the submission is another connection's): connection 4 faults.
(assert-event (fn-own-inflight *oft-o*))
(assert-event (equal (fn-own-sub-id (fn-own-inflight *oft-o*)) 4))
(assert-event (not (oft-keeps-another-p *oft-o* 4)))
(must-fail (assert-event (oft-keeps-another-p *oft-o* 4)))
; (fn-own-inflight o) has no tooth: with nothing in flight the slot stays
; empty, which is what it was.  The hypothesis is redundant.
(defthm oft-keeps-another-connections-submission-needs-only-the-id
  (implies (not (equal (fn-own-sub-id (fn-own-inflight o)) id))
           (equal (fn-own-inflight (cdr (fn-own-fault o id)))
                  (fn-own-inflight o)))
  :hints (("Goal" :in-theory (enable fn-own-fault fn-own-close))))

; -----------------------------------------------------------------------------
; fn-own-fault-releases-the-faulted-transaction.  Hypothesis:
; (equal (fn-own-pending o) id).
(defun oft-releases-p (o id)
  (not (fn-own-pending (cdr (fn-own-fault o id)))))
; Witness: connection 4 holds the transaction; its fault releases it.
(assert-event (equal (fn-own-pending *oft-o*) 4))
(assert-event (oft-releases-p *oft-o* 4))
; Tooth: reader 3 faults while connection 4 holds the transaction, which
; stays held.  (The review of 2026-09-24 found no violating value; this is
; one, and it is reachable.)
(assert-event (not (equal (fn-own-pending *oft-o*) 3)))
(assert-event (not (oft-releases-p *oft-o* 3)))
(must-fail (assert-event (oft-releases-p *oft-o* 3)))

; -----------------------------------------------------------------------------
; fn-own-fault-is-not-a-store-event (no hypothesis).  Witness, not
; degenerate: the store holds two durable records and a transaction in
; progress, the ledger two completions, and the fault of the connection
; that owns the transaction leaves all three, and the view, unchanged.
(defconst *oft-faulted* (cdr (fn-own-fault *oft-o* 4)))
(assert-event (equal (len (fn-sf-records (fn-sn-files (fn-own-store *oft-o*)))) 2))
(assert-event (equal (len (fn-own-ledger *oft-o*)) 2))
(assert-event (equal (fn-own-store *oft-faulted*) (fn-own-store *oft-o*)))
(assert-event (equal (fn-own-view *oft-faulted*) (fn-own-view *oft-o*)))
(assert-event (equal (fn-own-ledger *oft-faulted*) (fn-own-ledger *oft-o*)))
; The owner state itself did change: the connection, the submission and
; the transaction went.
(assert-event (not (equal *oft-faulted* *oft-o*)))

; -----------------------------------------------------------------------------
; fn-own-fault-reply-is-not-a-post-outcome (no hypothesis).  Witness at
; the nearest outcome: the malformed posting session, whose reply is
; books/nntp-post.lisp's own 403, for each completion word.
(defun oft-fault-reply-differs-p (ps completion)
  (not (equal (fn-served-reply-octets (fn-own-fault-effects))
              (fn-served-reply-octets
               (fn-post-result-effects (fn-nntp-post-outcome ps completion))))))
(assert-event (equal (take 4 (fn-served-reply-octets
                              (fn-post-result-effects (fn-nntp-post-outcome nil :durable))))
                     (fn-nntp-string-octets "403 ")))
(assert-event (equal (take 4 (fn-served-reply-octets (fn-own-fault-effects)))
                     (fn-nntp-string-octets "403 ")))
(assert-event (oft-fault-reply-differs-p nil :durable))
(assert-event (oft-fault-reply-differs-p nil :refused))
(assert-event (oft-fault-reply-differs-p nil :uncertain))
