; Actual owner-table boundary witnesses for bounded FNFD port admission.
(in-package "ACL2")
(include-book "../../books/owner-feed-port")
(include-book "std/testing/must-fail" :dir :system)

(defconst *fn-ofp-peer* "nodeB")
(defconst *fn-ofp-record*
  (fn-cfg-peer-make "nodeB" "b.fn.test" '(:nntp "127.0.0.1" 1120)
                    '("fn.*" 32768 16) '("fn.*" t 256 1000)
                    '(:source-address "127.0.0.2")))
(assert-event (fn-cfg-peerp *fn-ofp-record*))
(defconst *fn-ofp-change*
  (append *fn-cfg-default-change*
          (list (fn-cfg-set-peer-delta *fn-ofp-record*))))
(defconst *fn-ofp-config*
  (fn-config-replay 0 510
                    (list (fn-cfg-record-make 0 0 1 *fn-ofp-change*
                                              *fn-cfg-default-stamp*))))
(assert-event (fn-cfgp *fn-ofp-config*))
(defconst *fn-ofp-peers* (fn-cfg-peers (fn-cfg-value *fn-ofp-config*)))
(assert-event (equal (fn-cfg-peer-find *fn-ofp-peer* *fn-ofp-peers*)
                     *fn-ofp-record*))
(defconst *fn-ofp-base-table*
  (fn-own-feed-reconfigure nil *fn-ofp-peers*))
(assert-event (fn-own-feed-tablep *fn-ofp-base-table*))

(defconst *fn-ofp-msgid*
  (fn-record-string-octets "<1@a.fn.test>"))
(defconst *fn-ofp-open*
  (fn-feed-with-conn
   (fn-own-feed-find *fn-ofp-peer* *fn-ofp-base-table*) 7))
(assert-event (fn-feedp *fn-ofp-open*))
(defconst *fn-ofp-queued*
  (fn-feed-enqueue *fn-ofp-open* *fn-ofp-msgid* 1))
(assert-event (fn-feedp *fn-ofp-queued*))
(defconst *fn-ofp-table*
  (fn-own-feed-put *fn-ofp-peer* *fn-ofp-record* *fn-ofp-queued*
                   *fn-ofp-base-table*))
(assert-event (fn-own-feed-tablep *fn-ofp-table*))
(defconst *fn-ofp-obs* (fn-clock-observation 10 0 0 nil))
(defconst *fn-ofp-tick*
  (fn-own-feed-port-tick-peer *fn-ofp-peer* *fn-ofp-table* *fn-ofp-obs*))
(defconst *fn-ofp-tick-next*
  (mv-let (next effects)
    (fn-feed-tick-step *fn-ofp-queued* *fn-ofp-obs*)
    (declare (ignore effects))
    next))

(assert-event (equal (fn-own-feed-port-status *fn-ofp-tick*) :accepted))
(assert-event (consp (fn-own-feed-port-records *fn-ofp-tick*)))
(assert-event (consp (fn-own-feed-port-effects *fn-ofp-tick*)))
(assert-event (equal (fn-own-feed-find *fn-ofp-peer*
                                        (fn-own-feed-port-table *fn-ofp-tick*))
                     *fn-ofp-tick-next*))

; Loss records carry their monotonic observation.  This is the owner-called
; loss shape at an unrepresentable value: refusal preserves the queued work
; before it can publish the :feed-lost record or mutate the backoff.
(defconst *fn-ofp-overflow-obs*
  (fn-clock-observation (+ 1 *fn-frame-max-nat*) 0 0 nil))
(defconst *fn-ofp-overflow*
  (fn-own-feed-port-lost-peer *fn-ofp-peer* *fn-ofp-table*
                              *fn-ofp-overflow-obs*))
(assert-event (equal (fn-own-feed-port-status *fn-ofp-overflow*) :refused))
(assert-event (equal (fn-own-feed-port-table *fn-ofp-overflow*) *fn-ofp-table*))
(assert-event (equal (fn-own-feed-port-records *fn-ofp-overflow*) nil))
(assert-event (equal (fn-own-feed-port-effects *fn-ofp-overflow*) nil))
(must-fail (assert-event
 (equal (fn-own-feed-port-table *fn-ofp-overflow*)
        (fn-own-feed-lost-one *fn-ofp-peer* *fn-ofp-table*
                               *fn-ofp-overflow-obs*))))

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

; Restart composition is one logical all-or-nothing owner transition.  Two
; configured peers are both restarted and contribute their exact port records.
(defconst *fn-ofp-record-2*
  (fn-cfg-peer-make "peer2" "peer2.fn.test" '(:nntp "127.0.0.1" 1121)
                    '("fn.*" 32768 16) '("fn.*" t 256 1000)
                    '(:source-address "127.0.0.3")))
(defconst *fn-ofp-two-base-table*
  (fn-own-feed-reconfigure nil (list *fn-ofp-record* *fn-ofp-record-2*)))
(defconst *fn-ofp-restart-source*
  (fn-own-feed-find *fn-ofp-peer* (fn-own-feed-port-table *fn-ofp-lost*)))
(assert-event (fn-feedp *fn-ofp-restart-source*))
(defconst *fn-ofp-two-table*
  (fn-own-feed-put
   "peer2" *fn-ofp-record-2* *fn-ofp-restart-source*
   (fn-own-feed-put *fn-ofp-peer* *fn-ofp-record* *fn-ofp-restart-source*
                    *fn-ofp-two-base-table*)))
(defconst *fn-ofp-restart-fold*
  (fn-own-feed-port-restart-fold
   (fn-own-feed-names *fn-ofp-two-table*)
   *fn-ofp-two-table* *fn-ofp-two-table*))
(assert-event (equal (fn-own-feed-port-status *fn-ofp-restart-fold*) :accepted))
(assert-event (equal (len (fn-own-feed-port-records *fn-ofp-restart-fold*)) 2))
(assert-event (equal (fn-own-feed-port-effects *fn-ofp-restart-fold*) nil))

; A stale/missing peer name refuses the whole fold and exposes neither the
; earlier table nor a partial restart-record batch.
(defconst *fn-ofp-restart-refusal*
  (fn-own-feed-port-restart-fold
   (list *fn-ofp-peer* "missing") *fn-ofp-two-table* *fn-ofp-two-table*))
(assert-event (equal (fn-own-feed-port-status *fn-ofp-restart-refusal*) :refused))
(assert-event (equal (fn-own-feed-port-table *fn-ofp-restart-refusal*)
                     *fn-ofp-two-table*))
(assert-event (equal (fn-own-feed-port-records *fn-ofp-restart-refusal*) nil))
(assert-event (equal (fn-own-feed-port-effects *fn-ofp-restart-refusal*) nil))
(must-fail
 (assert-event
  (equal (fn-own-feed-port-status *fn-ofp-restart-refusal*) :accepted)))
