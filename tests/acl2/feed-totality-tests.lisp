; Reachable teeth for the bounded FNFD port profile.
(in-package "ACL2")
(include-book "../../books/feed-totality")
(include-book "std/testing/must-fail" :dir :system)

(defconst *fn-feed-ft-peer* '(105 110 110))
(defconst *fn-feed-ft-msgid* '(60 116 64 102 110 62))
(defconst *fn-feed-ft-contact* (fn-sched-contact "inn" 0 1000000))
(defconst *fn-feed-ft-open*
  (fn-feed-open *fn-feed-ft-peer* (fn-feed-limits 4 1000 5 t)
                *fn-feed-ft-contact* 7))
(defconst *fn-feed-ft-queued*
  (fn-feed-enqueue *fn-feed-ft-open* *fn-feed-ft-msgid* 1))
(defconst *fn-feed-ft-offered*
  (fn-feed-live-next *fn-feed-ft-queued*
                     (list :tick (fn-clock-observation 10 0 0 nil))))

; This is a live open -> enqueue -> offer -> retry path.  The abstract state
; accepts the natural timestamp, while FNFD cannot spell it in eight octets.
; The port refuses before the retry transition, so the outstanding offer and
; all queued work remain intact.
(defconst *fn-feed-ft-overflow-obs*
  (fn-clock-observation (+ 1 *fn-frame-max-nat*) 0 0 nil))
(defconst *fn-feed-ft-overflow-event*
  (list :reply (fn-feed-response 431 *fn-feed-ft-msgid*) nil
        *fn-feed-ft-overflow-obs*))
(defconst *fn-feed-ft-overflow-records*
  (fn-feed-live-records *fn-feed-ft-offered* *fn-feed-ft-overflow-event*))
(assert-event (fn-feedp *fn-feed-ft-offered*))
(assert-event (not (fn-feed-records-portp *fn-feed-ft-overflow-records*)))
(assert-event (equal (fn-feed-port-step-status
                      (fn-feed-live-port-step *fn-feed-ft-offered*
                                              *fn-feed-ft-overflow-event*))
                     :refused))
(assert-event (equal (fn-feed-port-step-feed
                      (fn-feed-live-port-step *fn-feed-ft-offered*
                                              *fn-feed-ft-overflow-event*))
                     *fn-feed-ft-offered*))
(assert-event (equal (fn-feed-port-step-records
                      (fn-feed-live-port-step *fn-feed-ft-offered*
                                              *fn-feed-ft-overflow-event*)) nil))
(assert-event (equal (fn-feed-port-step-effects
                      (fn-feed-live-port-step *fn-feed-ft-offered*
                                              *fn-feed-ft-overflow-event*)) nil))
(must-fail
 (assert-event (fn-feed-drivenp *fn-feed-ft-offered* *fn-feed-ft-overflow-records*)))

; A valid pair of maximum-length text fields is another reachable enqueue,
; but its exact field encoding exceeds FNFD's 1024-octet payload ceiling.
; It is refused without silently shortening peer or Message-ID text.
(defun fn-feed-ft-scalar-repeat (n)
  (declare (xargs :guard (natp n)))
  (if (zp n) nil
    (append '(240 144 128 128) (fn-feed-ft-scalar-repeat (1- n)))))

(defconst *fn-feed-ft-long-text* (fn-feed-ft-scalar-repeat 128))
(defconst *fn-feed-ft-payload-open*
  (fn-feed-open *fn-feed-ft-long-text* (fn-feed-limits 4 1000 5 t)
                *fn-feed-ft-contact* 7))
(defconst *fn-feed-ft-payload-event*
  (list :enqueue *fn-feed-ft-long-text* 1))
(defconst *fn-feed-ft-payload-records*
  (fn-feed-live-records *fn-feed-ft-payload-open* *fn-feed-ft-payload-event*))
(assert-event (fn-feedp *fn-feed-ft-payload-open*))
(assert-event (fn-feed-journalp *fn-feed-ft-payload-records*))
(assert-event (not (fn-feed-records-portp *fn-feed-ft-payload-records*)))
(assert-event (equal (fn-feed-port-step-status
                      (fn-feed-live-port-step *fn-feed-ft-payload-open*
                                              *fn-feed-ft-payload-event*))
                     :refused))
(assert-event (equal (fn-feed-port-step-feed
                      (fn-feed-live-port-step *fn-feed-ft-payload-open*
                                              *fn-feed-ft-payload-event*))
                     *fn-feed-ft-payload-open*))
(must-fail
 (assert-event (not (equal (fn-feed-encode :feed-enqueue
                                            (fn-feed-journal-values
                                             (car *fn-feed-ft-payload-records*))
                                            *fn-feed-port-digest*)
                           :bad))))

; A normal selected offer is accepted and exposes the exact record/effect
; subjects.  Removing feed validity is a separate refusal hypothesis tooth.
(defconst *fn-feed-ft-tick-event*
  (list :tick (fn-clock-observation 10 0 0 nil)))
(assert-event (equal (fn-feed-port-step-status
                      (fn-feed-live-port-step *fn-feed-ft-queued*
                                              *fn-feed-ft-tick-event*))
                     :accepted))
(assert-event (equal (fn-feed-port-step-records
                      (fn-feed-live-port-step *fn-feed-ft-queued*
                                              *fn-feed-ft-tick-event*))
                     (fn-feed-live-records *fn-feed-ft-queued*
                                           *fn-feed-ft-tick-event*)))
(must-fail
 (assert-event (equal (fn-feed-port-step-status
                       (fn-feed-live-port-step nil *fn-feed-ft-tick-event*))
                      :accepted)))
