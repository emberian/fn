; Actual owner-table boundary witnesses for bounded FNFD port admission.
(in-package "ACL2")
(include-book "../../books/owner-feed")
(include-book "std/testing/must-fail" :dir :system)

(defconst *fn-ofp-peer* "peer")
(defconst *fn-ofp-record*
  (fn-cfg-peer-make "peer" "peer.fn.test" '(:nntp "127.0.0.1" 1120)
                    '("fn.*" 32768 16) '("fn.*" t 256 1000)
                    '(:source-address "127.0.0.2")))
(assert-event (fn-cfg-peerp *fn-ofp-record*))
(defconst *fn-ofp-base-table*
  (fn-own-feed-reconfigure nil (list *fn-ofp-record*)))
(assert-event (fn-own-feed-tablep *fn-ofp-base-table*))

(defconst *fn-ofp-msgid* '(60 112 64 102 110 62))
(defconst *fn-ofp-open*
  (fn-feed-with-conn
   (fn-own-feed-find *fn-ofp-peer* *fn-ofp-base-table*) 7))
(defconst *fn-ofp-queued*
  (fn-feed-enqueue *fn-ofp-open* *fn-ofp-msgid* 1))
(defconst *fn-ofp-table*
  (fn-own-feed-put *fn-ofp-peer* *fn-ofp-record* *fn-ofp-queued*
                   *fn-ofp-base-table*))
(assert-event (fn-own-feed-tablep *fn-ofp-table*))
(defconst *fn-ofp-obs* (fn-clock-observation 10 0 0 nil))
(defconst *fn-ofp-tick*
  (fn-own-feed-port-tick-peer *fn-ofp-peer* *fn-ofp-table* *fn-ofp-obs*))

(assert-event (equal (fn-own-feed-port-status *fn-ofp-tick*) :accepted))
(assert-event (consp (fn-own-feed-port-records *fn-ofp-tick*)))
(assert-event (consp (fn-own-feed-port-effects *fn-ofp-tick*)))
(assert-event (equal (fn-own-feed-find *fn-ofp-peer*
                                        (fn-own-feed-port-table *fn-ofp-tick*))
                     (mv-nth 0 (fn-feed-tick-step *fn-ofp-queued* *fn-ofp-obs*))))

; This is the owner-called tick shape at an unrepresentable monotonic value.
; The port refuses before returning the offer command or changing the table.
(defconst *fn-ofp-overflow-obs*
  (fn-clock-observation (+ 1 *fn-frame-max-nat*) 0 0 nil))
(defconst *fn-ofp-overflow*
  (fn-own-feed-port-tick-peer *fn-ofp-peer* *fn-ofp-table*
                              *fn-ofp-overflow-obs*))
(assert-event (equal (fn-own-feed-port-status *fn-ofp-overflow*) :refused))
(assert-event (equal (fn-own-feed-port-table *fn-ofp-overflow*) *fn-ofp-table*))
(assert-event (equal (fn-own-feed-port-records *fn-ofp-overflow*) nil))
(assert-event (equal (fn-own-feed-port-effects *fn-ofp-overflow*) nil))
(must-fail (assert-event
 (equal (fn-own-feed-port-table *fn-ofp-overflow*)
        (car (fn-own-feed-tick-peer *fn-ofp-peer* *fn-ofp-table*
                                    *fn-ofp-overflow-obs*)))))

; Reply, loss and restart take the same owner/table boundary and return their
; generated records only when their exact FNFD encoding is admissible.
(defconst *fn-ofp-offered-table* (fn-own-feed-port-table *fn-ofp-tick*))
(defconst *fn-ofp-reply*
  (fn-own-feed-port-observe-peer *fn-ofp-peer* *fn-ofp-offered-table*
    (fn-feed-response 431 *fn-ofp-msgid*) nil *fn-ofp-obs*))
(assert-event (equal (fn-own-feed-port-status *fn-ofp-reply*) :accepted))
(assert-event (consp (fn-own-feed-port-records *fn-ofp-reply*)))
(defconst *fn-ofp-lost*
  (fn-own-feed-port-lost-peer *fn-ofp-peer*
                              (fn-own-feed-port-table *fn-ofp-reply*)
                              *fn-ofp-obs*))
(assert-event (equal (fn-own-feed-port-status *fn-ofp-lost*) :accepted))
(assert-event (consp (fn-own-feed-port-records *fn-ofp-lost*)))
(defconst *fn-ofp-restart*
  (fn-own-feed-port-restart-peer *fn-ofp-peer*
                                 (fn-own-feed-port-table *fn-ofp-lost*)))
(assert-event (equal (fn-own-feed-port-status *fn-ofp-restart*) :accepted))
(assert-event (consp (fn-own-feed-port-records *fn-ofp-restart*)))
