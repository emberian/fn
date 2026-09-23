(in-package "ACL2")
(include-book "../../books/feed-port-replay")
(include-book "std/testing/must-fail" :dir :system)

(defconst *fpr-peer* '(105 110 110))
(defconst *fpr-a* '(60 97 64 102 110 62))
(defconst *fpr-b* '(60 98 64 102 110 62))
(defconst *fpr-c* '(60 99 64 102 110 62))
(defconst *fpr-d* '(60 100 64 102 110 62))
(defconst *fpr-e* '(60 101 64 102 110 62))
(defconst *fpr-obs* (fn-clock-observation 10 0 0 nil))
(defconst *fpr-open*
  (fn-feed-open *fpr-peer* (fn-feed-limits 5 1000 3 t)
                (fn-sched-contact "inn" 0 1000000) 7))

; Five durable queue entries, two completed deliveries, and a crash after
; the third :feed-sent record but before its outcome. The next two queued
; articles make the witness distinct from an empty or singleton feed.
(defconst *fpr-events*
  (list (list :enqueue *fpr-a* 1)
        (list :enqueue *fpr-b* 2)
        (list :enqueue *fpr-c* 3)
        (list :enqueue *fpr-d* 4)
        (list :enqueue *fpr-e* 5)
        (list :tick *fpr-obs*)
        (list :reply (fn-feed-response 238 *fpr-a*) '(65 13 10) *fpr-obs*)
        (list :reply (fn-feed-response 239 *fpr-a*) nil *fpr-obs*)
        (list :tick *fpr-obs*)
        (list :reply (fn-feed-response 238 *fpr-b*) '(66 13 10) *fpr-obs*)
        (list :reply (fn-feed-response 239 *fpr-b*) nil *fpr-obs*)
        (list :tick *fpr-obs*)
        (list :reply (fn-feed-response 238 *fpr-c*) '(67 13 10) *fpr-obs*)))
(defconst *fpr-live* (fn-feed-port-run *fpr-open* *fpr-events*))
(defconst *fpr-records* (fn-feed-port-history *fpr-open* *fpr-events*))
(defconst *fpr-replayed* (fn-feed-replay *fpr-open* *fpr-records*))

(assert-event (equal (len (fn-feed-queue *fpr-live*)) 5))
(assert-event (equal (len *fpr-records*) 13))
(assert-event (equal (fn-feed-state-of *fpr-a* (fn-feed-queue *fpr-live*)) :done))
(assert-event (equal (fn-feed-state-of *fpr-b* (fn-feed-queue *fpr-live*)) :done))
(assert-event (fn-feed-sentp (fn-feed-state-of *fpr-c* (fn-feed-queue *fpr-live*))))
(assert-event (equal (fn-feed-state-of *fpr-d* (fn-feed-queue *fpr-live*)) :queued))
(assert-event (equal (fn-feed-state-of *fpr-e* (fn-feed-queue *fpr-live*)) :queued))
(assert-event (equal (fn-feed-restart *fpr-replayed*) (fn-feed-restart *fpr-live*)))
(assert-event (equal (fn-feed-next-attempt *fpr-replayed*) 4))
(assert-event (equal (fn-feed-state-of *fpr-c*
                 (fn-feed-queue (fn-feed-restart *fpr-replayed*))) :queued))
(assert-event (equal (fn-feed-port-step-effects
                      (fn-feed-live-port-step
                       (fn-feed-with-conn (fn-feed-restart *fpr-replayed*) 8)
                       (list :tick *fpr-obs*)))
                     (list (list :command 8 (fn-feed-check-line *fpr-c*)))))

; Drop the crash-image premise by fabricating a durable 239 for the third
; attempt. It changes that entry to :done while the live run remains :sent.
(defconst *fpr-false-image*
  (append *fpr-records*
          (list (fn-feed-journal-entry :feed-outcome
                  (list *fpr-peer* *fpr-c* 3 239)))))
(must-fail (assert-event
  (equal (fn-feed-restart (fn-feed-replay *fpr-open* *fpr-false-image*))
         (fn-feed-restart *fpr-live*))))
