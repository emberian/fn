; Teeth for the port keystones of books/owner-feed-live-carried.lisp
; (rp-feed-defer-drop, rp-feed-dropped-holds-capacity, rp-feed-reply-msgid),
; over the host-called subject `fn-own-feed-port-peer-carried' and the
; capacity verdict `fn-own-feed-target-capacityp'.  The tables are the ones
; tests/acl2/owner-feed-tests.lisp builds: nodeB with <1@a.fn.test> offered
; by CHECK on connection 3.
(in-package "ACL2")
(include-book "../../books/owner-feed-live-carried")
(include-book "owner-feed-tests")

(defconst *oflc-tbl* (car *oft-ticked*))
(assert-event (fn-own-feed-tablep *oflc-tbl*))
(assert-event (fn-ofct-table-relationp *oflc-tbl*))
(assert-event (fn-feed-inflightp *oft-msgid* (fn-own-feed-find "nodeB" *oflc-tbl*)))

; -----------------------------------------------------------------------------
; `fn-own-feed-port-deferral-keeps-every-entry'

(defconst *oflc-431* (fn-feed-response 431 *oft-msgid*))
(defconst *oflc-deferred*
  (fn-own-feed-port-peer-carried "nodeB" *oflc-tbl* (list :reply *oflc-431* nil *oft-obs*)))
; Positive: the complete antecedent and conclusion.
(assert-event
 (and (fn-own-feed-tablep *oflc-tbl*)
      (fn-own-feed-entry-of "nodeB" *oflc-tbl*)
      (member-equal (fn-feed-response-code *oflc-431*) '(431 436))
      (fn-feed-inflightp (fn-feed-response-msgid *oflc-431*)
                         (fn-own-feed-find "nodeB" *oflc-tbl*))
      (fn-feed-presentp *oft-msgid* (fn-own-feed-find "nodeB" *oflc-tbl*))
      (equal (fn-own-feed-port-status *oflc-deferred*) :accepted)
      (fn-feed-presentp *oft-msgid*
                        (fn-own-feed-find "nodeB" (fn-own-feed-port-table *oflc-deferred*)))
      (equal (fn-feed-undelivered
              (fn-own-feed-find "nodeB" (fn-own-feed-port-table *oflc-deferred*)))
             (fn-feed-undelivered (fn-own-feed-find "nodeB" *oflc-tbl*)))
      (not (fn-feed-has-leave-recordp (oft-o "nodeB") *oft-msgid*
                                      (fn-own-feed-port-records *oflc-deferred*)))))
; The record is the :feed-retry alone.
(assert-event (equal (len (fn-own-feed-port-records *oflc-deferred*)) 1))
(assert-event (equal (fn-feed-journal-kind (car (fn-own-feed-port-records *oflc-deferred*)))
                     :feed-retry))
; Hypothesis removal: the code.  A 437 for the same entry retires it with an
; outcome record, a leave record.  Every other hypothesis holds.
(defconst *oflc-437*
  (fn-own-feed-port-peer-carried "nodeB" *oflc-tbl*
                                 (list :reply (fn-feed-response 437 *oft-msgid*) nil *oft-obs*)))
(assert-event
 (and (not (fn-feed-presentp *oft-msgid*
                             (fn-own-feed-find "nodeB" (fn-own-feed-port-table *oflc-437*))))
      (fn-feed-has-leave-recordp (oft-o "nodeB") *oft-msgid*
                                 (fn-own-feed-port-records *oflc-437*))))
; Hypothesis removal: the entry in flight (tests/acl2/peer-feed-tests.lisp
; carries the separating feed, a retry bound of one, where a 436 naming a
; queued entry is a loss that gives up the one in flight).

; -----------------------------------------------------------------------------
; `fn-own-feed-port-holds-only-owed-entries'

(defun oflc-owed-after (event)
  (let ((g (fn-own-feed-find "nodeB"
                             (fn-own-feed-port-table
                              (fn-own-feed-port-peer-carried "nodeB" *oflc-tbl* event)))))
    (equal (fn-feed-undelivered g) (fn-feed-owed-count (fn-feed-queue g)))))
; Positive, over a deferral, a final answer, a loss and a stray reply.
(assert-event (oflc-owed-after (list :reply *oflc-431* nil *oft-obs*)))
(assert-event (oflc-owed-after (list :reply (fn-feed-response 239 *oft-msgid*) nil *oft-obs*)))
(assert-event (oflc-owed-after (list :lost *oft-obs*)))
(assert-event (oflc-owed-after (list :reply (fn-feed-response 239 (oft-o "<x@y>")) nil *oft-obs*)))
; Mutation (labelled; no fn-feedp feed holds it now): the pre-2026-10-04
; given-up entry, `(:dropped :retry-bound)', is not owed, so a queue of one
; such entry has length 1 and owed count 0 -- the slot it held for good.
(assert-event (equal (fn-feed-owed-count
                      (list (fn-feed-entry *oft-msgid* '(:dropped :retry-bound) 3 0 3)))
                     0))
(assert-event (not (fn-feed-entryp (fn-feed-entry *oft-msgid* '(:dropped :retry-bound) 3 0 3))))

; -----------------------------------------------------------------------------
; `fn-own-feed-capacity-refusal-is-owed-work'

; nodeB with room for one, holding <1@a.fn.test> owed.
(defconst *oflc-full*
  (fn-own-feed-put "nodeB" (fn-own-feed-record-of "nodeB" *oft-accepted*)
                   (fn-feed-enqueue
                    (fn-feed-open (oft-o "nodeB") (fn-feed-limits 1 1000 3 t)
                                  (fn-feed-contact (fn-own-feed-find "nodeB" *oft-accepted*))
                                  3)
                    *oft-msgid* 1)
                   *oft-accepted*))
(assert-event (fn-own-feed-tablep *oflc-full*))
(defconst *oflc-new* (oft-o "<2@a.fn.test>"))
; Positive: refused, and the target that refuses owes a full queue.
(assert-event
 (and (fn-own-feed-tablep *oflc-full*)
      (not (fn-own-feed-target-capacityp '("nodeB") *oflc-full* *oflc-new*))
      (fn-own-feed-some-target-fullp '("nodeB") *oflc-full* *oflc-new*)))
; The same table after the one entry is given up at the bound has room
; again (before 2026-10-04 the given-up entry kept the slot and this read
; refused for good).
(defconst *oflc-gave-up*
  (fn-own-feed-put "nodeB" (fn-own-feed-record-of "nodeB" *oft-accepted*)
                   (fn-feed-give-up (fn-own-feed-find "nodeB" *oflc-full*)
                                    *oft-msgid* :retry-bound)
                   *oflc-full*))
(assert-event (fn-own-feed-tablep *oflc-gave-up*))
(assert-event (fn-own-feed-target-capacityp '("nodeB") *oflc-gave-up* *oflc-new*))
(assert-event (not (fn-own-feed-some-target-fullp '("nodeB") *oflc-gave-up* *oflc-new*)))

; -----------------------------------------------------------------------------
; `fn-own-feed-port-stray-reply-is-a-loss' over the carried subject (the
; reference port's witness is in tests/acl2/owner-feed-tests.lisp).
(defconst *oflc-stray*
  (fn-own-feed-port-peer-carried "nodeB" *oflc-tbl* (list :reply *oft-stray* nil *oft-obs*)))
(assert-event
 (and (not (equal (fn-feed-response-msgid *oft-stray*)
                  (fn-own-feed-inflight-msgid
                   (fn-feed-queue (fn-own-feed-find "nodeB" *oflc-tbl*)))))
      (equal (fn-own-feed-find "nodeB" (fn-own-feed-port-table *oflc-stray*))
             (fn-feed-lost (fn-own-feed-find "nodeB" *oflc-tbl*) *oft-obs*))
      (equal (fn-own-feed-reply-word *oflc-tbl* "nodeB" *oft-stray*
                                     (fn-own-feed-port-effects *oflc-stray*))
             :lost)))
