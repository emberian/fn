; PRF-1077/HST-040: resume the checkpoint's PAUSED configured fold by
; exactly one configuration or event tick.  No full-history restarts and no
; nthcdr walk back to a configuration counter.  The continuation retains
; the unconsumed lists by pointer.  This is one preparer component; summary
; folds, canonical rows and page commit must also become funded/resumable.
(in-package "ACL2")
(include-book "store-checkpoint-open")
(defun fn-osp-cpr-tick (cn configs events config-sequence event-sequence)
  (declare (xargs :guard (fn-cnode-statep cn) :verify-guards nil
                  ))
  (if (not (consp events))
      (list :done (fn-sco-paused cn config-sequence event-sequence))
    (let ((position (+ (nfix config-sequence) (nfix event-sequence))))
      (if (mbe :logic (not (fn-cnode-statep cn)) :exec nil)
          (list :done (fn-replay-fault cn position :invalid-node))
        (if (fn-cpr-config-firstp configs events)
            (let* ((record (car configs))
                   (txid (fn-cfg-record-txid record))
                   (node (fn-cnode-node cn)))
              (cond ((not (fn-cfg-recordp record))
                     (list :done (fn-replay-fault cn position :invalid-config-record)))
                    ((not (equal (fn-cfg-record-sequence record) config-sequence))
                     (list :done (fn-replay-fault cn position :config-sequence)))
                    ((not (fn-replay-advance-okp node txid))
                     (list :done (fn-replay-fault cn position :config-txid)))
                    (t (let ((at (fn-cnode-make
                                  (fn-replay-advance-txid node txid)
                                  (fn-cnode-config cn))))
                         (if (mbe :logic (not (fn-cnode-statep at)) :exec nil)
                             (list :done (fn-replay-fault cn position :invalid-node))
                           (if (not (mbe :logic (fn-cnode-record-acceptablep
                                              at record (fn-cnode-line-ceiling))
                                         :exec (fn-cnode-carried-acceptablep
                                                at record (fn-cnode-line-ceiling))))
                               (list :done (fn-replay-fault cn position :config-refusal))
                             (list :continue
                              (fn-cnode-apply-config
                               at record (fn-cnode-line-ceiling))
                              (cdr configs) events
                              (+ 1 (nfix config-sequence)) event-sequence)))))))
          (let ((event (car events)))
            (cond ((not (fn-store-event-p event))
                   (list :done (fn-replay-fault cn position :invalid-event)))
                  ((not (equal (fn-store-event-sequence event) event-sequence))
                   (list :done (fn-replay-fault cn position :event-sequence)))
                  (t (let ((next (fn-cpr-apply-event cn event)))
                       (if (mbe :logic (not (fn-cnode-statep next))
                                :exec (not (consp next)))
                           (list :done (fn-replay-fault cn position :event-refusal))
                         (list :continue next configs (cdr events)
                                            config-sequence
                                            (+ 1 (nfix event-sequence)))))))))))))

(defun fn-osp-cpr-after (tick)
  (declare (xargs :guard t :verify-guards nil))
  (if (equal (car tick) :continue)
      (fn-sco-cpr-prefix (nth 1 tick) (nth 2 tick) (nth 3 tick)
                         (nth 4 tick) (nth 5 tick))
    (nth 1 tick)))

; Named refinement: the host-called tick retains the original paused
; prefix fold's value, including every refusal and its position.
(defthm fn-osp-cpr-tick-refines-the-paused-fold
  (equal (fn-osp-cpr-after
          (fn-osp-cpr-tick cn configs events config-sequence event-sequence))
         (fn-sco-cpr-prefix cn configs events config-sequence event-sequence))
  :hints (("Goal" :do-not-induct t
           :expand ((fn-sco-cpr-prefix cn configs events config-sequence event-sequence))
           :in-theory (e/d (fn-osp-cpr-after fn-osp-cpr-tick)
                            (fn-cnode-statep fn-cpr-apply-event
                             fn-cnode-apply-config fn-sco-cpr-prefix
                             fn-cpr-config-firstp fn-cfg-recordp
                             fn-replay-advance-okp fn-cnode-carried-acceptablep
                             fn-cnode-record-acceptablep fn-store-event-p
                             fn-replay-fault fn-sco-paused)))))

(defthm fn-osp-cpr-continue-consumes-exactly-one-input
  (let ((tick (fn-osp-cpr-tick cn configs events cs es)))
    (implies (equal (car tick) :continue)
             (and (consp events)
                  (or (and (consp configs)
                           (equal (nth 2 tick) (cdr configs))
                           (equal (nth 3 tick) events))
                      (and (equal (nth 2 tick) configs)
                           (equal (nth 3 tick) (cdr events))))
                  (equal (+ (len (nth 2 tick)) (len (nth 3 tick)))
                         (- (+ (len configs) (len events)) 1)))))
  :hints (("Goal" :in-theory (e/d (fn-osp-cpr-tick)
                                  (fn-cnode-statep fn-cpr-apply-event
                                   fn-cnode-apply-config fn-replay-fault
                                   fn-sco-paused)))))

(defthm fn-osp-cpr-continue-preserves-configured-state
  (implies (equal (car (fn-osp-cpr-tick cn configs events cs es)) :continue)
           (fn-cnode-statep (nth 1 (fn-osp-cpr-tick cn configs events cs es))))
  :hints (("Goal" :in-theory (e/d (fn-osp-cpr-tick)
                                  (fn-cnode-statep fn-cnode-apply-config
                                   fn-cpr-apply-event fn-cnode-record-acceptablep
                                   fn-cnode-carried-acceptablep)))))
(local
 (defthm fn-osp-cnode-statep-has-node-statep
   (implies (fn-cnode-statep cn) (fn-node-statep (fn-cnode-node cn)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-cnode-statep)))))
(verify-guards fn-osp-cpr-tick
  :hints (("Goal"
           :use ((:instance fn-cpr-config-firstp-has-config)
                 (:instance fn-cpr-apply-event-statep-iff-consp
                            (event (car events)))
                 (:instance fn-cnode-advanced-node-is-configured
                            (txid (fn-cfg-record-txid (car configs))))
                 (:instance fn-cnode-record-acceptablep-is-the-carried-check
                            (cn (fn-cnode-make
                                 (fn-replay-advance-txid
                                  (fn-cnode-node cn)
                                  (fn-cfg-record-txid (car configs)))
                                 (fn-cnode-config cn)))
                            (record (car configs))
                            (ceiling (fn-cnode-line-ceiling))))
           :in-theory (e/d (fn-cnode-apply-config-preserves-state)
                           (fn-cnode-statep fn-cpr-config-firstp fn-cpr-apply-event
                            fn-cnode-apply-config fn-cnode-record-acceptablep
                            fn-cfg-recordp fn-store-event-p)))))
(defun fn-osp-cpr-begin (configs records)
  (declare (xargs :guard t))
  (list (fn-cnode-initial (fn-cfg-initial)) configs records 0 0))
