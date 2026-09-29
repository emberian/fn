; PRF-1077/HST-040: resume the checkpoint's PAUSED configured fold by
; exactly one configuration or event tick.  No full-history restarts and no
; nthcdr walk back to a configuration counter.  The continuation retains
; the unconsumed lists by pointer.  This is one preparer component; summary
; folds, canonical rows and page commit must also become funded/resumable.
(in-package "ACL2")
(include-book "store-checkpoint-open")
(include-book "store-checkpoint-arena")
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

; Remaining four summaries: one event per tick, carrying each fold's state
; independently.  No repeated append of the accumulated record prefix.
(defun fn-osp-fold-begin (records)
  (declare (xargs :guard t))
  (list records (fn-stxk-initial-context 0) (list :ok nil)
        (fn-th-prefix-state :ok 0 nil nil nil nil nil) nil 0))
(defun fn-osp-fold-tick (cursor)
  (declare (xargs :guard (natp (fn-sco-at 5 cursor))))
  (let ((records (fn-sco-at 0 cursor))
        (identity (fn-sco-at 1 cursor))
        (consumer (fn-sco-at 2 cursor))
        (topic (fn-sco-at 3 cursor))
        (index (fn-sco-at 4 cursor))
        (count (fn-sco-at 5 cursor)))
    (cond ((not (consp records))
           (if (null records)
               (list :done (list identity consumer topic index))
             (list :refused :improper-records)))
          (t
           (let ((event (car records)))
             (list :continue
                   (list (cdr records)
                         (fn-replay-identity-step identity event)
                         (if (equal (fn-sco-at 0 consumer) :ok)
                             (fn-cpe-projection-step (fn-sco-at 1 consumer) event count)
                           consumer)
                         (fn-th-prefix-step topic event)
                         (fn-cei-put count event index)
                         (+ 1 count))))))))
(defun fn-osp-fold-value (cursor)
  (declare (xargs :guard t :verify-guards nil))
  (let ((records (fn-sco-at 0 cursor)))
    (list (fn-replay-identity-loop records (fn-sco-at 1 cursor))
          (fn-sco-consumer-resume (fn-sco-at 2 cursor) records (fn-sco-at 5 cursor))
          (fn-th-prefix-loop (fn-sco-at 3 cursor) records)
          (fn-cei-build-aux records (fn-sco-at 5 cursor) (fn-sco-at 4 cursor)))))
(local
 (defthm fn-osp-consumer-step-ok-has-natural-counter
   (implies (equal (car (fn-cpe-projection-step s event expected)) :ok)
            (natp expected))
   :hints (("Goal" :in-theory (e/d (fn-cpe-projection-step fn-cp-uintp)
                                  (fn-cpe-projection-decision fn-cpe-projection-advance
                                   fn-cpe-operation fn-cp-initial fn-cp-state fn-cp-apply))))))
(defthm fn-osp-fold-tick-retains-the-four-summary-values
  (implies (and (fn-sco-store-eventsp (fn-sco-at 0 cursor))
                (implies (equal (fn-sco-at 0 (fn-sco-at 2 cursor)) :ok)
                         (equal (fn-sco-at 2 cursor)
                                (list :ok (fn-sco-at 1 (fn-sco-at 2 cursor))))))
           (let ((tick (fn-osp-fold-tick cursor)))
             (equal (fn-osp-fold-value cursor)
                    (if (equal (car tick) :continue)
                        (fn-osp-fold-value (nth 1 tick))
                      (nth 1 tick)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-osp-consumer-step-ok-has-natural-counter
                            (s (fn-sco-at 1 (fn-sco-at 2 cursor)))
                            (event (car (fn-sco-at 0 cursor)))
                            (expected (fn-sco-at 5 cursor))))
           :in-theory (e/d (fn-osp-fold-tick fn-osp-fold-value fn-sco-consumer-resume
                            fn-replay-identity-loop fn-cpe-projection-replay
                            fn-th-prefix-loop fn-cei-build-aux fn-sco-at
                            fn-sco-store-eventsp)
                           (fn-replay-identity-step fn-cpe-projection-step
                            fn-th-prefix-step fn-cei-put)))))
(defthm fn-osp-fold-continue-is-exactly-one-record
  (let ((tick (fn-osp-fold-tick cursor)))
    (implies (equal (car tick) :continue)
             (and (consp (fn-sco-at 0 cursor))
                  (equal (fn-sco-at 0 (nth 1 tick))
                         (cdr (fn-sco-at 0 cursor)))
                  (equal (fn-sco-at 5 (nth 1 tick))
                         (+ 1 (fn-sco-at 5 cursor))))))
  :hints (("Goal" :in-theory (e/d (fn-osp-fold-tick fn-sco-at)
                                  (fn-replay-identity-step fn-cpe-projection-step
                                   fn-th-prefix-step fn-cei-put)))))
(defthm fn-osp-fold-natural-counter-is-preserved
  (implies (and (natp (fn-sco-at 5 cursor))
                (equal (car (fn-osp-fold-tick cursor)) :continue))
           (natp (fn-sco-at 5 (nth 1 (fn-osp-fold-tick cursor)))))
  :hints (("Goal" :in-theory (e/d (fn-osp-fold-tick fn-sco-at)
                                  (fn-replay-identity-step fn-cpe-projection-step
                                   fn-th-prefix-step fn-cei-put)))))

; Canonical row preparation and its final reversal are separate resumable
; phases.  One tick canonicalizes one row or reverses one list cell; no
; terminal reverse of the whole captured prefix on a scheduling tick.
(defun fn-osp-canon-begin (records)
  (declare (xargs :guard t))
  (list :canon records 0 nil nil))
(defun fn-osp-canon-tick (cursor fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (natp (fn-sco-at 2 cursor))))
  (let ((phase (fn-sco-at 0 cursor))
        (remaining (fn-sco-at 1 cursor))
        (h (fn-sco-at 2 cursor))
        (rev (fn-sco-at 3 cursor))
        (out (fn-sco-at 4 cursor)))
    (cond
     ((equal phase :canon)
      (if (consp remaining)
          (let* ((w (fn-row-wire-of (car remaining) fn-arena))
                 (row (fn-scka-intern-one w h)))
            (if (equal row :bad) (list :done :bad)
              (list :continue
                    (list :canon (cdr remaining)
                          (if (fn-scka-sealsp w) (+ 1 h) h)
                          (cons row rev) out))))
        (if (null remaining)
            (list :continue (list :reverse rev h nil nil))
          (list :refused :improper-records))))
     ((equal phase :reverse)
      (if (consp remaining)
          (list :continue (list :reverse (cdr remaining) h nil
                                (cons (car remaining) out)))
        (if (null remaining) (list :done out)
          (list :refused :improper-reverse))))
     (t (list :refused :phase)))))
(defun fn-osp-canon-value (cursor fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (if (equal (fn-sco-at 0 cursor) :canon)
      (let ((r (fn-scka-canon-rows (fn-sco-at 1 cursor) fn-arena
                                  (fn-sco-at 2 cursor))))
        (if (equal r :bad) :bad (revappend (fn-sco-at 3 cursor) r)))
    (revappend (fn-sco-at 1 cursor) (fn-sco-at 4 cursor))))
(local
 (defthm fn-osp-canon-rows-one-step-by-definition
   (equal (fn-scka-canon-rows rows fn-arena h)
          (if (atom rows) nil
            (let* ((w (fn-row-wire-of (car rows) fn-arena))
                   (row (fn-scka-intern-one w h)))
              (if (equal row :bad) :bad
                (let ((rest (fn-scka-canon-rows
                             (cdr rows) fn-arena
                             (if (fn-scka-sealsp w) (+ 1 h) h))))
                  (if (equal rest :bad) :bad (cons row rest)))))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :expand ((fn-scka-canon-rows rows fn-arena h))
            :in-theory (disable fn-scka-canon-rows
                         fn-scka-canon-rows-is-intern-at-of-alpha
                         fn-scka-intern-one fn-scka-sealsp fn-row-wire-of)))))
(defthm fn-osp-canon-tick-is-the-canonical-rows-continuation
  (implies (and (member-equal (fn-sco-at 0 cursor) '(:canon :reverse))
                (true-listp (fn-sco-at 1 cursor)))
           (let ((tick (fn-osp-canon-tick cursor fn-arena)))
             (equal (fn-osp-canon-value cursor fn-arena)
                    (if (equal (car tick) :continue)
                        (fn-osp-canon-value (nth 1 tick) fn-arena)
                      (nth 1 tick)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-osp-canon-rows-one-step-by-definition
                            (rows (fn-sco-at 1 cursor))
                            (h (fn-sco-at 2 cursor))))
           :in-theory (e/d (fn-osp-canon-tick fn-osp-canon-value fn-sco-at revappend)
                            (fn-scka-canon-rows fn-scka-intern-one
                             fn-scka-canon-rows-is-intern-at-of-alpha
                             fn-scka-intern-at fn-rows-wire-of revappend-removal
                             fn-scka-sealsp fn-row-wire-of)))))

(defthm fn-osp-canon-continue-is-one-row-or-one-reverse-cell
  (let ((tick (fn-osp-canon-tick cursor fn-arena)))
    (implies (equal (car tick) :continue)
             (or (and (equal (fn-sco-at 0 cursor) :canon)
                      (consp (fn-sco-at 1 cursor))
                      (equal (fn-sco-at 0 (nth 1 tick)) :canon)
                      (equal (fn-sco-at 1 (nth 1 tick)) (cdr (fn-sco-at 1 cursor))))
                 (and (equal (fn-sco-at 0 cursor) :canon)
                      (null (fn-sco-at 1 cursor))
                      (equal (nth 1 tick)
                             (list :reverse (fn-sco-at 3 cursor)
                                   (fn-sco-at 2 cursor) nil nil)))
                 (and (equal (fn-sco-at 0 cursor) :reverse)
                      (consp (fn-sco-at 1 cursor))
                      (equal (fn-sco-at 0 (nth 1 tick)) :reverse)
                      (equal (fn-sco-at 1 (nth 1 tick)) (cdr (fn-sco-at 1 cursor)))
                      (equal (fn-sco-at 4 (nth 1 tick))
                             (cons (car (fn-sco-at 1 cursor))
                                   (fn-sco-at 4 cursor)))))))
  :hints (("Goal" :in-theory (e/d (fn-osp-canon-tick fn-sco-at)
                                  (fn-scka-intern-one fn-row-wire-of fn-scka-sealsp)))))
(defthm fn-osp-canon-continue-keeps-the-executable-cursor
  (implies (and (natp (fn-sco-at 2 cursor))
                (true-listp (fn-sco-at 1 cursor))
                (true-listp (fn-sco-at 3 cursor))
                (true-listp (fn-sco-at 4 cursor))
                (equal (car (fn-osp-canon-tick cursor fn-arena)) :continue))
           (let ((next (nth 1 (fn-osp-canon-tick cursor fn-arena))))
             (and (natp (fn-sco-at 2 next))
                  (true-listp (fn-sco-at 1 next))
                  (true-listp (fn-sco-at 3 next))
                  (true-listp (fn-sco-at 4 next)))))
  :hints (("Goal" :in-theory (e/d (fn-osp-canon-tick fn-sco-at)
                                  (fn-scka-intern-one fn-row-wire-of fn-scka-sealsp)))))
