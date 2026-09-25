; Teeth for books/store-open-node-bridge.lisp.  The witness is the host's
; open (fn-cpo-open-observed, host/store-node-host.lisp:180) of a crash image
; of the K5 fixture's second publication under a fresh store's one initial
; configuration record (txid 0), the image store-open-bridge-tests uses.  The
; separating history for fn-sonb-configured-before-eventsp is the one
; config-observed-tests keeps: an undertaking, its release, then a capacity
; reduction at txid 7 that the configured replay admits at its historical
; reservation total and the final table cannot replay.
(in-package "ACL2")
(include-book "../../books/store-open-node-bridge")
(include-book "byte-store-stable-prefix-tests")
(include-book "std/testing/must-fail" :dir :system)

(defconst *sonbt-configs* (list *fn-cfg-default-record*))
; Both at txid 0, both at sequence 0: the second replays to :config-sequence.
(defconst *sonbt-fault-configs* (list *fn-cfg-default-record* *fn-cfg-default-record*))

(defun sonbt-image ()
  (let ((pair (bsk5-linked-2)))
    (fn-bs-crash (car pair)
                 (fn-bs-view-choices (fn-bs-pending (car pair)) (fn-bs-unit (car pair))))))
(defun sonbt-f () (fn-bs-scan-frontier (fn-bs-scan-store (sonbt-image))))
(defun sonbt-r () (fn-bs-scan-records (fn-bs-scan-store (sonbt-image))))
(defun sonbt-host (configs) (fn-cpo-open-observed configs (sonbt-f) (sonbt-r)))
(defun sonbt-st (configs) (fn-sn-open-state (sonbt-host configs)))

; The conclusion of fn-sonb-configured-replay-is-fixed-table-replay.
(defun sonbt-agreesp (configs events)
  (let* ((cn (fn-replay-result-node (fn-cpr-replay configs events)))
         (answer (fn-replay (fn-cnode-domain-of (fn-cnode-config cn))
                            (fn-cfg-capacity (fn-cfg-value (fn-cnode-config cn)))
                            events)))
    (and (fn-replay-okp answer)
         (equal (fn-replay-result-node answer) (fn-cnode-node cn)))))

; The separating history (config-observed-tests).
(defconst *sonbt-events*
  (list (fn-store-retention-event-make :undertake 0 0 0
                                        "forward-cpo" "subject" "evidence" 10)
        (fn-store-retention-event-make :release 1 1 1
                                        "forward-cpo" "subject" "evidence" 0)))
(defconst *sonbt-reconfigured*
  (list *fn-cfg-default-record*
        (fn-cfg-record-make 1 7 2 (list (fn-cfg-set-capacity 1))
                            *fn-cfg-default-stamp*)))
(defconst *sonbt-reconfigured-open*
  (fn-cpo-open-observed *sonbt-reconfigured* 8 *sonbt-events*))

; ---------------------------------------------------------------------------
; Witness: a non-empty journal (two records, frontier 2) under the fresh
; store's configuration; every hypothesis and every conclusion holds.
(assert-event (and (equal (len (sonbt-r)) 2) (equal (sonbt-f) 2)))
(assert-event
 (and (fn-sonb-configured-before-eventsp *sonbt-configs*)
      (equal (fn-replay-result-kind (fn-cpr-replay *sonbt-configs* (sonbt-r))) :ok)
      (sonbt-agreesp *sonbt-configs* (sonbt-r))
      (fn-sn-open-okp (sonbt-host *sonbt-configs*))
      (equal (fn-sn-node (sonbt-st *sonbt-configs*))
             (fn-cst-replay-node *sonbt-configs* (sonbt-r) (sonbt-f)))
      (equal (fn-sn-node (sonbt-st *sonbt-configs*))
             (fn-sf-replay-node (fn-sn-groups (sonbt-st *sonbt-configs*))
                                (fn-sn-capacity (sonbt-st *sonbt-configs*))
                                (sonbt-r) (sonbt-f)))
      (fn-snt-relation (sonbt-st *sonbt-configs*))))
; Non-degenerate: the node is not the initial node; two events moved it.
(assert-event
 (not (equal (fn-sn-node (sonbt-st *sonbt-configs*))
             (fn-node-initial-state (fn-sn-groups (sonbt-st *sonbt-configs*))
                                    (fn-sn-capacity (sonbt-st *sonbt-configs*))))))

; ---------------------------------------------------------------------------
; Drop fn-sonb-configured-before-eventsp.  The configured replay succeeds and
; the host opens, but the fixed-table replay under the final capacity 1
; refuses the undertaking of 10, so the correspondence, the node conjunct and
; fn-snt-relation all fail.
(assert-event
 (and (not (fn-sonb-configured-before-eventsp *sonbt-reconfigured*))
      (equal (fn-replay-result-kind (fn-cpr-replay *sonbt-reconfigured* *sonbt-events*)) :ok)
      (fn-sn-open-okp *sonbt-reconfigured-open*)
      (equal (fn-sn-node (fn-sn-open-state *sonbt-reconfigured-open*))
             (fn-cst-replay-node *sonbt-reconfigured* *sonbt-events* 8))))
(must-fail (assert-event (sonbt-agreesp *sonbt-reconfigured* *sonbt-events*)))
(must-fail
 (assert-event
  (equal (fn-sn-node (fn-sn-open-state *sonbt-reconfigured-open*))
         (fn-sf-replay-node (fn-sn-groups (fn-sn-open-state *sonbt-reconfigured-open*))
                            (fn-sn-capacity (fn-sn-open-state *sonbt-reconfigured-open*))
                            *sonbt-events* 8))))
(must-fail
 (assert-event (fn-snt-relation (fn-sn-open-state *sonbt-reconfigured-open*))))

; Drop the configured replay's success (the correspondence) or the host
; open's success (the host statements): two records at txid 0 whose second
; repeats sequence 0.  The fault keeps the node after the first record,
; which is the initial node, while the fixed-table replay runs both events.
(assert-event
 (and (fn-sonb-configured-before-eventsp *sonbt-fault-configs*)
      (equal (fn-replay-result-kind (fn-cpr-replay *sonbt-fault-configs* (sonbt-r))) :fault)
      (not (fn-sn-open-okp (sonbt-host *sonbt-fault-configs*)))))
(must-fail (assert-event (sonbt-agreesp *sonbt-fault-configs* (sonbt-r))))
(must-fail (assert-event (fn-snt-relation (sonbt-st *sonbt-fault-configs*))))

; fn-sn-open-observed-success-configured-node-of-host-open without the
; host's success: an empty configuration journal is refused (:history), and
; a refused open's state is its reason, whose node is nil, while the
; configured replay of the empty journals is the initial node.
(assert-event
 (and (not (fn-sn-open-okp (fn-cpo-open-observed nil 0 nil)))
      (consp (fn-cst-replay-node nil nil 0))))
(must-fail
 (assert-event
  (equal (fn-sn-node (fn-sn-open-state (fn-cpo-open-observed nil 0 nil)))
         (fn-cst-replay-node nil nil 0))))

; fn-sn-open-observed-success-exact-history-node-of-host-open has no
; separating instance for its host-success hypothesis: a refused open's
; state is its reason, whose node, groups and capacity are all nil, and the
; fixed-table replay under a nil capacity is nil.  The hypothesis is kept
; because the statement is about the opened state; its other hypothesis is
; separated above.
(assert-event
 (and (not (fn-sn-open-okp (sonbt-host *sonbt-fault-configs*)))
      (equal (fn-sn-node (sonbt-st *sonbt-fault-configs*)) nil)
      (equal (fn-sf-replay-node (fn-sn-groups (sonbt-st *sonbt-fault-configs*))
                                (fn-sn-capacity (sonbt-st *sonbt-fault-configs*))
                                (sonbt-r) (sonbt-f))
             nil)))
