; Teeth for books/store-open-bridge.lisp.  The witness is the host's open
; (fn-cpo-open-observed, host/store-node-host.lisp:159) of a crash image of
; the K5 fixture's second publication: the linked cut, kept, so the scanned
; journal holds two acknowledged-shape records at frontier 2.
(in-package "ACL2")
(include-book "../../books/store-open-bridge")
(include-book "byte-store-stable-prefix-tests")
(include-book "std/testing/must-fail" :dir :system)

(defconst *sobt-configs* (list *fn-cfg-default-record*))
; Two configuration records, both at sequence 0: the second replays to
; (:fault ... :config-sequence).  A non-empty journal, so the open reaches
; the replay rather than its (null configs) refusal.
(defconst *sobt-fault-configs* (list *fn-cfg-default-record* *fn-cfg-default-record*))

(defun sobt-image ()
  (let ((pair (bsk5-linked-2)))
    (fn-bs-crash (car pair)
                 (fn-bs-view-choices (fn-bs-pending (car pair)) (fn-bs-unit (car pair))))))
(defun sobt-f () (fn-bs-scan-frontier (fn-bs-scan-store (sobt-image))))
(defun sobt-r () (fn-bs-scan-records (fn-bs-scan-store (sobt-image))))
(defun sobt-host (configs) (fn-cpo-open-observed configs (sobt-f) (sobt-r)))
(defun sobt-model (groups capacity)
  (fn-sn-open-observed groups capacity (sobt-f) (sobt-r)))
(defun sobt-files (opened) (fn-sn-files (fn-sn-open-state opened)))

; The image is non-trivial: two records, frontier 2.
(assert-event (and (equal (len (sobt-r)) 2) (equal (sobt-f) 2)))

; Witness for fn-cpo-open-observed-is-sn-open-observed-on-the-kernel: both
; hypotheses hold, the host opens, and the kernels agree.
(assert-event
 (and (fn-sn-open-okp (sobt-model *bsk5-groups* *bsk5-capacity*))
      (fn-sob-configured-openp *sobt-configs* (sobt-f) (sobt-r))
      (fn-sn-open-okp (sobt-host *sobt-configs*))
      (equal (sobt-files (sobt-host *sobt-configs*))
             (sobt-files (sobt-model *bsk5-groups* *bsk5-capacity*)))
      (equal (sobt-files (sobt-host *sobt-configs*))
             (fn-bs-recovered-kernel (sobt-f) (sobt-r) 0))))

; Witness for fn-cpo-open-observed-succeeds-exactly: every conjunct.
(assert-event
 (and (fn-sn-observed-historyp (sobt-f) (sobt-r))
      (fn-sn-observed-identity-okp (sobt-r))
      (fn-sn-observed-consumer-okp (sobt-r))
      (fn-sn-observed-topic-okp (sobt-r))
      (fn-sob-identity-typedp (sobt-r))))

; The corollaries' conclusions at the witness.
(assert-event
 (let ((st (fn-sn-open-state (sobt-host *sobt-configs*))))
   (and (equal (fn-sf-records (fn-sn-files st)) (sobt-r))
        (equal (fn-sf-phase (fn-sn-files (fn-sn-observed-rebarrier st 4))) :recovering)
        (equal (fn-sf-phase (fn-sn-files (fn-sn-observed-rebarrier st 5))) :ready)
        (fn-cpo-history-relation st))))

; Drop fn-sob-configured-openp: a configuration journal that replays :fault.
; The store-only open still succeeds on the same image; the host's refuses.
(assert-event
 (and (equal (fn-replay-result-kind (fn-cpr-replay *sobt-fault-configs* (sobt-r))) :fault)
      (not (fn-sob-configured-openp *sobt-fault-configs* (sobt-f) (sobt-r)))
      (fn-sn-open-okp (sobt-model *bsk5-groups* *bsk5-capacity*))))
(must-fail
 (assert-event (fn-sn-open-okp (sobt-host *sobt-fault-configs*))))

; Drop the store-only open's success: with no groups the fixed-table replay
; refuses the journal.  The host still opens, but the kernels differ, so the
; second conclusion needs the first hypothesis.
(assert-event
 (and (not (fn-sn-open-okp (sobt-model nil *bsk5-capacity*)))
      (fn-sn-open-okp (sobt-host *sobt-configs*))))
(must-fail
 (assert-event
  (equal (sobt-files (sobt-host *sobt-configs*))
         (sobt-files (sobt-model nil *bsk5-capacity*)))))

; Observed, not proved: with one configuration record the host's opened
; state is the store-only one opened under that configuration's own table
; and capacity, with the configuration history installed.  A theorem of this
; form needs a node correspondence between fn-cpr-replay and fn-replay; it
; would carry fn-snt-relation, and so the two theorems that do not transfer.
(assert-event
 (let* ((cn (fn-replay-result-node (fn-cpr-replay *sobt-configs* (sobt-r))))
        (m (sobt-model (fn-cnode-domain-of (fn-cnode-config cn))
                       (fn-cfg-capacity (fn-cfg-value (fn-cnode-config cn))))))
   (and (fn-sn-open-okp m)
        (equal (fn-cpo-install (fn-sn-open-state m) cn *sobt-configs*)
               (fn-sn-open-state (sobt-host *sobt-configs*)))
        (fn-snt-relation (fn-sn-open-state (sobt-host *sobt-configs*))))))
