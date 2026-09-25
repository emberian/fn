; host/spike-storage-fast-host.lisp -- spike/storage (D28): replay without
; per-event whole-state revalidation.  ld'ed by host/native/build.lisp before
; host/store-node-host.lisp, whose open wrappers call these.
;
; Measured (hbox, N=300, logs/sprof-full300.txt): 76% of a full-replay open
; is fn-node-statep, called four times per replayed event by fn-cpr-loop and
; fn-cpr-apply-event (books/config-physical-replay.lisp), and fn-node-statep
; is itself quadratic (binding/article subset checks by member).  So the open
; is Theta(N^3).  AGENTS.md: "carry the invariant in state and prove it
; preserved".
;
;; SPIKE: defers, for dev to prove (book above config-physical-replay):
;;  1. fn-replay-apply-record-preserves-node-statep: (fn-node-statep n) and
;;     (consp (fn-replay-apply-record n e)) imply the result is fn-node-statep
;;     (node-config.lisp has it for fn-cnode-apply-record).
;;  2. fn-spk-cpr-fold-equals-cpr-loop: under (fn-cnode-statep cn),
;;     (fn-spk-cpr-fold cn configs events cs es nil) = (fn-cpr-loop ...), and
;;     with PAUSE = t it equals fn-sco-cpr-prefix.  By induction with 1 and
;;     fn-cnode-apply-config's preservation.
;;  3. The once-per-open recognizers dropped here (fn-cnode-statep at the
;;     finish, fn-sn-statep of the opened state) are implied by 2 and the
;;     existing open theorems; the spike does not run them.

(in-package "ACL2")
; The books host/store-node-host.lisp includes (P3 adds the checkpoint ones).
(include-book "../books/store-observed")
(include-book "../books/poster-bytes")
(include-book "../books/native-config-observation")
(include-book "../books/store-sweep")
(include-book "../books/store-node-resolution")
(include-book "../books/store-prepare-correspondence")
(include-book "../books/store-budget")
(include-book "../books/node-config")
(include-book "../books/native-admin")
(include-book "../books/store-checkpoint-open")
(include-book "../books/store-checkpoint-codec")
(include-book "../books/byte-store-state-checkpoint-program")
(include-book "../books/peer-config")
(include-book "../books/provenance-codec")

(defun fn-spk-apply-event (cn event)
  (declare (xargs :mode :program))
  (if (and (fn-store-event-p event) (fn-cpr-event-servedp cn event))
      (let ((next (fn-replay-apply-record (fn-cnode-node cn) event)))
        (if (consp next) (fn-cnode-make next (fn-cnode-config cn)) nil))
    nil))

; The fold of fn-cpr-loop (PAUSE nil) or fn-sco-cpr-prefix (PAUSE t), with
; the whole-state recognizer run on configuration steps only (rare), never
; per event.  The caller establishes (fn-cnode-statep cn) once.
(defun fn-spk-cpr-fold (cn configs events config-sequence event-sequence pause)
  (declare (xargs :mode :program))
  (if (and pause (not (consp events)))
      (fn-sco-paused cn config-sequence event-sequence)
    (let ((position (+ (nfix config-sequence) (nfix event-sequence))))
      (if (fn-cpr-config-firstp configs events)
          (let* ((record (car configs))
                 (txid (fn-cfg-record-txid record))
                 (node (fn-cnode-node cn)))
            (cond ((not (fn-cfg-recordp record))
                   (fn-replay-fault cn position :invalid-config-record))
                  ((not (equal (fn-cfg-record-sequence record) config-sequence))
                   (fn-replay-fault cn position :config-sequence))
                  ((not (fn-replay-advance-okp node txid))
                   (fn-replay-fault cn position :config-txid))
                  (t (let ((at (fn-cnode-make
                                (fn-replay-advance-txid node txid)
                                (fn-cnode-config cn))))
                       (if (not (fn-cnode-record-acceptablep
                                 at record (fn-cnode-line-ceiling)))
                           (fn-replay-fault cn position :config-refusal)
                         (fn-spk-cpr-fold
                          (fn-cnode-apply-config at record (fn-cnode-line-ceiling))
                          (cdr configs) events
                          (+ 1 (nfix config-sequence)) event-sequence pause))))))
        (if (consp events)
            (let ((event (car events)))
              (cond ((not (fn-store-event-p event))
                     (fn-replay-fault cn position :invalid-event))
                    ((not (equal (fn-store-event-sequence event) event-sequence))
                     (fn-replay-fault cn position :event-sequence))
                    (t (let ((next (fn-spk-apply-event cn event)))
                         (if (not (consp next))
                             (fn-replay-fault cn position :event-refusal)
                           (fn-spk-cpr-fold next configs (cdr events)
                                            config-sequence
                                            (+ 1 (nfix event-sequence)) pause))))))
          (if (and (null configs) (null events))
              (fn-replay-ok cn position)
            (fn-replay-fault cn position :improper-history)))))))

(defun fn-spk-cpr-start (cn configs events cs es pause)
  (declare (xargs :mode :program))
  (if (not (fn-cnode-statep cn))
      (fn-replay-fault cn (+ (nfix cs) (nfix es)) :invalid-node)
    (fn-spk-cpr-fold cn configs events cs es pause)))

(defun fn-spk-cpr-replay (configs events)
  (declare (xargs :mode :program))
  (fn-spk-cpr-start (fn-cnode-initial (fn-cfg-initial)) configs events 0 0 nil))

; fn-cpo-open-observed with the fast fold and without the closing recognizers.
(defun fn-spk-open-tail (configs frontier events cn identity consumer topic event-index)
  (declare (xargs :mode :program))
  (let ((node (fn-cnode-node cn)))
    (if (not (fn-replay-advance-okp node frontier))
        (fn-sn-open-error :frontier)
      (let* ((advanced (fn-replay-advance-txid node frontier))
             (config (fn-cnode-config cn))
             (files (fn-sf-make :recovering frontier nil events nil nil nil 0))
             (seed (fn-sn-observed-seed (fn-cnode-domain-of config)
                                        (fn-cfg-capacity (fn-cfg-value config))
                                        frontier events))
             (opened (fn-sn-with-event-index
                      (fn-sn-with-topic
                       (fn-sn-with-consumer
                        (fn-cpo-install
                         (fn-sn-update-replayed
                          seed files advanced
                          (fn-stx-index-of-store (fn-stx-store advanced) nil)
                          identity)
                         (fn-cnode-make advanced config) configs)
                        (fn-cp-nth 1 consumer))
                       topic)
                      event-index)))
        (if (and (equal (fn-stxk-context-kind identity) :ok)
                 (consp consumer) (eq (car consumer) :ok)
                 (eq (fn-th-at 0 topic) :ok))
            (fn-sn-open-ok opened)
          (fn-sn-open-error :identity))))))

(defun fn-spk-cpo-open-observed (configs frontier events)
  (declare (xargs :mode :program))
  (if (or (null configs) (not (fn-sn-observed-historyp frontier events)))
      (fn-sn-open-error :history)
    (let ((replayed (fn-spk-cpr-replay configs events)))
      (if (not (equal (fn-replay-result-kind replayed) :ok))
          (fn-sn-open-error :replay)
        (fn-spk-open-tail configs frontier events
                          (fn-replay-result-node replayed)
                          (fn-replay-identity events)
                          (fn-cpe-projection-replay nil events 0)
                          (fn-th-prefix-project events)
                          (fn-cei-build events))))))

; P3's checkpoint folds over the fast fold.
(defun fn-spk-sco-capture (configs records)
  (declare (xargs :mode :program))
  (let ((records (true-list-fix records)))
    (fn-sco-make records
                 (fn-spk-cpr-start (fn-cnode-initial (fn-cfg-initial))
                                   configs records 0 0 t)
                 (fn-replay-identity-loop records (fn-stxk-initial-context 0))
                 (fn-cpe-projection-replay nil records 0)
                 (fn-th-prefix-loop (fn-th-prefix-state :ok 0 nil nil nil nil nil)
                                    records)
                 (fn-cei-build-aux records 0 nil))))

(defun fn-spk-sco-cpr-resume (r configs events)
  (declare (xargs :mode :program))
  (if (fn-sco-pausedp r)
      (let ((cs (fn-sco-at 2 r)))
        (fn-spk-cpr-start (fn-sco-at 1 r) (fn-sco-nthcdr (nfix cs) configs) events
                          cs (fn-sco-at 3 r) t))
    r))

(defun fn-spk-sco-cpr-finish (r configs)
  (declare (xargs :mode :program))
  (if (fn-sco-pausedp r)
      (let ((cs (fn-sco-at 2 r)))
        (fn-spk-cpr-fold (fn-sco-at 1 r) (fn-sco-nthcdr (nfix cs) configs) nil
                         cs (fn-sco-at 3 r) nil))
    r))

(defun fn-spk-sco-extend (c configs suffix)
  (declare (xargs :mode :program))
  (let ((records (true-list-fix (fn-sco-records c))))
    (fn-sco-make (append records suffix)
                 (fn-spk-sco-cpr-resume (fn-sco-cpr c) configs suffix)
                 (fn-replay-identity-loop suffix (fn-sco-identity c))
                 (fn-sco-consumer-resume (fn-sco-consumer c) suffix (len records))
                 (fn-th-prefix-loop (fn-sco-topic c) suffix)
                 (fn-cei-build-aux suffix (len records) (fn-sco-event-index c)))))

(defun fn-spk-sco-finalize (c configs frontier)
  (declare (xargs :mode :program))
  (let ((events (fn-sco-records c)))
    (if (or (null configs) (not (fn-sn-observed-historyp frontier events)))
        (fn-sn-open-error :history)
      (let ((replayed (fn-spk-sco-cpr-finish (fn-sco-cpr c) configs)))
        (if (not (equal (fn-replay-result-kind replayed) :ok))
            (fn-sn-open-error :replay)
          (fn-spk-open-tail configs frontier events
                            (fn-replay-result-node replayed)
                            (fn-sco-identity c) (fn-sco-consumer c)
                            (fn-sco-topic c) (fn-sco-event-index c)))))))

(defun fn-spk-sco-open (c configs frontier suffix)
  (declare (xargs :mode :program))
  (fn-spk-sco-finalize (fn-spk-sco-extend c configs suffix) configs frontier))

(defun fn-spk-sco-replay-result (c configs suffix)
  (declare (xargs :mode :program))
  (fn-spk-sco-cpr-finish (fn-spk-sco-cpr-resume (fn-sco-cpr c) configs suffix)
                         configs))

; The open result's kind without fn-sn-open-okp's fn-sn-statep.
(defun fn-spk-open-okp (opened)
  (declare (xargs :mode :program))
  (and (fn-sn-open-shapep opened) (equal (fn-sn-open-kind opened) :ok)))
