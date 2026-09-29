; fn: witnesses and teeth for books/owner-reclaim-ready.lisp (Q16 (a), lane
; online-reclaim-5): the swapped owner takes a POST after the open's
; recovery barriers, and never without them.
(in-package "ACL2")
(include-book "../../books/owner-reclaim-ready")
(include-book "must-fail-checked")

; The rebuild of owner-reclaim-conns-tests (two retention events, two
; configuration records).  The LIVE owner is reachable: that rebuild's owner
; after the open's three barriers (what a restart serves), one connection
; opened on it, and one submission queued through the control port.
(defconst *orrd-t-events*
  (list (fn-store-retention-event-make :undertake 0 0 0 "forward-orcp" "subject" "evidence" 10)
        (fn-store-retention-event-make :release 1 1 1 "forward-orcp" "subject" "evidence" 0)))
(defconst *orrd-t-configs*
  (list *fn-cfg-default-record*
        (fn-cfg-record-make 1 7 2 (list (fn-cfg-set-capacity 1)) *fn-cfg-default-stamp*)))
(defconst *orrd-t-rebuilt-oc* (cadr (fn-orcp-rebuild *orrd-t-events* *orrd-t-configs* 8 4)))
(defconst *orrd-t-opened*
  (cdr (fn-ocfg-open (fn-orrd-barriers *orrd-t-rebuilt-oc* *fn-sf-recovery-barrier-count*) nil)))
(defconst *orrd-t-msgid* (fn-nntp-string-octets "<orrd@example.invalid>"))
(defconst *orrd-t-groups* (list (fn-nntp-string-octets "fn.letters")))
(defconst *orrd-t-source*
  (append (fn-nntp-string-octets "From: cli@example.invalid") '(13 10)
          (fn-nntp-string-octets "Subject: after the swap") '(13 10)
          (fn-nntp-string-octets "Newsgroups: fn.letters") '(13 10)
          (fn-nntp-string-octets "Message-ID: <orrd@example.invalid>") '(13 10)
          '(13 10)
          (fn-nntp-string-octets "Posted after the reclaim.") '(13 10)))
(defconst *orrd-t-live*
  (fn-ocfg-with-owner *orrd-t-opened*
                      (fn-own-control-submit (fn-ocfg-owner *orrd-t-opened*)
                                             *orrd-t-msgid* *orrd-t-groups* *orrd-t-source*)))
(assert-event (equal (fn-own-control-submit-result (fn-ocfg-owner *orrd-t-opened*)
                                                   *orrd-t-msgid* *orrd-t-groups* *orrd-t-source*)
                     :submitted))

; -----------------------------------------------------------------------------
; KEYSTONE fn-orrd-a-post-after-the-swap-is-taken-as-before, positive witness
; (reachable: the live owner is a restart's owner with a connection open and a
; submission queued).  Antecedent: the decision is :swap.  Conclusion, per
; literal: the served owner is :ready; it keeps the live queue; it takes
; exactly when the live pipeline does; the take takes the live queue's head.
(defun orrd-t-take (oc fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (fn-ocfg-owner (fn-ocfg-step oc '(:take) fn-arena)))
(defconst *orrd-t-ready* (fn-orrd-ready-ocfg *orrd-t-live* *orrd-t-rebuilt-oc*))
(defconst *orrd-t-next* (fn-orcp-swapped-ocfg *orrd-t-live* *orrd-t-rebuilt-oc*))
(assert-event (equal (fn-sf-phase (fn-sn-files (fn-own-store (fn-ocfg-owner *orrd-t-live*))))
                     :ready))
(assert-event (equal (len (fn-own-conns (fn-ocfg-owner *orrd-t-live*))) 1))
(assert-event (equal (len (fn-own-queue (fn-ocfg-owner *orrd-t-live*))) 1))
(assert-event (equal (fn-orcp-swap-decision :swap *orrd-t-live* *orrd-t-rebuilt-oc*) :swap))
(assert-event (fn-orrd-pipeline-takesp *orrd-t-live*))
(assert-event (equal (fn-sf-phase (fn-sn-files (fn-own-store (fn-ocfg-owner *orrd-t-ready*))))
                     :ready))
(assert-event (equal (fn-own-queue (fn-ocfg-owner *orrd-t-ready*))
                     (fn-own-queue (fn-ocfg-owner *orrd-t-live*))))
(assert-event (fn-orrd-takesp *orrd-t-ready*))
(assert-event (equal (fn-own-pending (orrd-t-take *orrd-t-ready* fn-arena))
                     (fn-own-sub-id (car (fn-own-queue (fn-ocfg-owner *orrd-t-live*))))))
(assert-event (equal (fn-own-queue (orrd-t-take *orrd-t-ready* fn-arena)) nil))
; ... as the live owner's own take does.
(assert-event (equal (fn-own-pending (orrd-t-take *orrd-t-live* fn-arena))
                     (fn-own-pending (orrd-t-take *orrd-t-ready* fn-arena))))

; fn-orrd-the-swap-without-the-barriers-never-takes, positive witness (the
; defect native-orp4 found): served without the barriers the swapped owner is
; :recovering and its take is the identity; the submission stays queued.
(assert-event (equal (fn-sf-phase (fn-sn-files (fn-own-store (fn-ocfg-owner *orrd-t-next*))))
                     :recovering))
(assert-event (not (fn-orrd-takesp *orrd-t-next*)))
(assert-event (equal (orrd-t-take *orrd-t-next* fn-arena) (fn-ocfg-owner *orrd-t-next*)))
(assert-event (equal (len (fn-own-queue (orrd-t-take *orrd-t-next* fn-arena))) 1))
(must-fail-checked
 (assert-event (fn-orrd-takesp *orrd-t-next*)))

; Hypothesis removal (the only hypothesis, decision = :swap): a rebuild that
; faulted (max-conns -1).  No retained hypothesis; the omitted one fails (the
; decision is :unbound); the conclusion fails (the served owner is not :ready).
(defconst *orrd-t-fault* (cadr (fn-orcp-rebuild *orrd-t-events* *orrd-t-configs* 8 -1)))
(assert-event (equal *orrd-t-fault* :fault))
(assert-event (equal (fn-orcp-swap-decision :swap *orrd-t-live* *orrd-t-fault*) :unbound))
;; (The served owner over a :fault rebuild violates the barrier's guard when
;; run; its phase is decided by the prover's ground evaluation.)
(defthm orrd-t-fault-rebuild-is-not-ready
  (not (equal (fn-sf-phase (fn-sn-files (fn-own-store (fn-ocfg-owner
                                                       (fn-orrd-ready-ocfg *orrd-t-live*
                                                                           *orrd-t-fault*)))))
              :ready))
  :rule-classes nil)
(must-fail-checked
 (defthm orrd-t-fault-rebuild-is-ready
   (equal (fn-sf-phase (fn-sn-files (fn-own-store (fn-ocfg-owner
                                                   (fn-orrd-ready-ocfg *orrd-t-live*
                                                                       *orrd-t-fault*)))))
          :ready)
   :rule-classes nil))
