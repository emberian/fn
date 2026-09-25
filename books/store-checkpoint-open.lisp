; fn: open a Store from an exact-state checkpoint (P3, design
; planning/design-2026-09-25-bounds.md section 3.1).
;
; The host's open is `fn-cpo-open-observed' (config-observed.lisp), called
; by `fn-store-sn-recover' (host/store-node-host.lisp).  It makes six passes
; over the whole record list: the history recognizer, the configuration and
; node fold `fn-cpr-loop', the identity fold, the consumer projection, the
; topic prefix and the event index.  Each of the five folds is a
; left fold with an accumulator, so the state after a prefix P is a value
; and the folds resume from it over any suffix Q.
;
; A checkpoint (`fn-sco-capture') is that value: the record list itself and
; each fold's accumulator after it.  It holds the exact state; it removes no
; record, so it is packing plus a cache and D13 is not a precondition.
; `fn-sco-open' resumes every fold over the suffix and finishes as
; `fn-cpo-open-observed' does.  The keystone
; `fn-sn-recover-from-checkpoint-equals-full-recover' says the two opens are
; equal for every configuration history, frontier, prefix and suffix.  It is
; built from one append lemma per fold.
;
; The history recognizer is not resumed: it runs over the whole record
; list, which the checkpoint carries.  It is one linear pass with no replay,
; at open only.
(in-package "ACL2")
(include-book "config-observed")
(local (in-theory (disable fn-sn-make-v6)))

; A total nth: the checkpoint is decoded from bytes, so its accessors take
; any value.
(local
 (defthm fn-sco-cp-nth-is-nth
   (equal (fn-cp-nth n x) (nth n x))
   :hints (("Goal" :in-theory (enable fn-cp-nth)))))

(defun fn-sco-at (n x)
  (declare (xargs :guard (natp n)))
  (mbe :logic (nth n x) :exec (fn-cp-nth n x)))

(defun fn-sco-drop (n x)
  (declare (xargs :guard (natp n)))
  (if (zp n) x (fn-sco-drop (1- n) (if (consp x) (cdr x) nil))))

(local
 (defthm fn-sco-drop-is-nthcdr
   (equal (fn-sco-drop n x) (nthcdr n x))))

(defun fn-sco-nthcdr (n x)
  (declare (xargs :guard (natp n)))
  (mbe :logic (nthcdr n x) :exec (fn-sco-drop n x)))

; -----------------------------------------------------------------------------
; The configuration fold, stopped where the record prefix ends.
;
; It is `fn-cpr-loop' with one change: when the events run out it pauses
; instead of draining the remaining configurations.  A paused result records
; the node and the two sequence counters; the configurations still to come
; are the ones the counter has not consumed.

(defun fn-sco-paused (cn config-sequence event-sequence)
  (declare (xargs :guard t))
  (list :paused cn config-sequence event-sequence))

(defun fn-sco-pausedp (x)
  (declare (xargs :guard t))
  (and (consp x) (eq (car x) :paused)))

(defun fn-sco-cpr-prefix (cn configs events config-sequence event-sequence)
  (declare (xargs :guard t :verify-guards nil
                  :measure (+ (len configs) (len events))))
  (if (not (consp events))
      (fn-sco-paused cn config-sequence event-sequence)
    (let ((position (+ (nfix config-sequence) (nfix event-sequence))))
      (if (not (fn-cnode-statep cn))
          (fn-replay-fault cn position :invalid-node)
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
                         (if (not (fn-cnode-statep at))
                             (fn-replay-fault cn position :invalid-node)
                           (if (not (fn-cnode-record-acceptablep
                                     at record (fn-cnode-line-ceiling)))
                               (fn-replay-fault cn position :config-refusal)
                             (fn-sco-cpr-prefix
                              (fn-cnode-apply-config
                               at record (fn-cnode-line-ceiling))
                              (cdr configs) events
                              (+ 1 (nfix config-sequence)) event-sequence)))))))
          (let ((event (car events)))
            (cond ((not (fn-store-event-p event))
                   (fn-replay-fault cn position :invalid-event))
                  ((not (equal (fn-store-event-sequence event) event-sequence))
                   (fn-replay-fault cn position :event-sequence))
                  (t (let ((next (fn-cpr-apply-event cn event)))
                       (if (not (fn-cnode-statep next))
                           (fn-replay-fault cn position :event-refusal)
                         (fn-sco-cpr-prefix next configs (cdr events)
                                            config-sequence
                                            (+ 1 (nfix event-sequence)))))))))))))

(defun fn-sco-cpr-resume (r configs events)
  ; Resume a stored configuration fold over more events.  The configurations
  ; not yet consumed are the tail after the stored configuration counter.
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-sco-pausedp r)
      (let ((cs (fn-sco-at 2 r)))
        (fn-sco-cpr-prefix (fn-sco-at 1 r) (fn-sco-nthcdr (nfix cs) configs) events
                           cs (fn-sco-at 3 r)))
    r))

(defun fn-sco-cpr-finish (r configs)
  ; Drain the remaining configurations, exactly as fn-cpr-loop does once the
  ; events are exhausted.
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-sco-pausedp r)
      (let ((cs (fn-sco-at 2 r)))
        (fn-cpr-loop (fn-sco-at 1 r) (fn-sco-nthcdr (nfix cs) configs) nil cs (fn-sco-at 3 r)))
    r))

; -----------------------------------------------------------------------------
; The checkpoint value

(defun fn-sco-make (records cpr identity consumer topic event-index)
  (declare (xargs :guard t))
  (list :fn-store-checkpoint records cpr identity consumer topic event-index))

(defun fn-sco-records (c) (declare (xargs :guard t)) (fn-sco-at 1 c))
(defun fn-sco-cpr (c) (declare (xargs :guard t)) (fn-sco-at 2 c))
(defun fn-sco-identity (c) (declare (xargs :guard t)) (fn-sco-at 3 c))
(defun fn-sco-consumer (c) (declare (xargs :guard t)) (fn-sco-at 4 c))
(defun fn-sco-topic (c) (declare (xargs :guard t)) (fn-sco-at 5 c))
(defun fn-sco-event-index (c) (declare (xargs :guard t)) (fn-sco-at 6 c))

(defun fn-sco-sequence (c)
  ; S: the number of records the checkpoint covers.
  (declare (xargs :guard t))
  (len (fn-sco-records c)))

(defun fn-sco-shapep (c)
  (declare (xargs :guard t))
  (and (true-listp c)
       (equal (len c) 7)
       (eq (car c) :fn-store-checkpoint)
       (true-listp (fn-sco-records c))))

(defun fn-sco-consumer-resume (consumer events expected)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (consp consumer) (eq (car consumer) :ok))
      (fn-cpe-projection-replay (fn-cp-nth 1 consumer) events expected)
    consumer))

; The capture of a record prefix.  The record list is normalized to a true
; list; `append' does the same to its first argument, so the capture of any
; prefix extends to the full history.
(defun fn-sco-capture (configs records)
  (declare (xargs :guard t :verify-guards nil))
  (let ((records (true-list-fix records)))
    (fn-sco-make records
                 (fn-sco-cpr-prefix (fn-cnode-initial (fn-cfg-initial))
                                    configs records 0 0)
                 (fn-replay-identity-loop records (fn-stxk-initial-context 0))
                 (fn-cpe-projection-replay nil records 0)
                 (fn-th-prefix-loop (fn-th-prefix-state :ok 0 nil nil nil nil nil)
                                    records)
                 (fn-cei-build-aux records 0 nil))))

; Resume every fold over a suffix.  This is also how the owner publishes the
; next checkpoint: the value after open is the capture of the whole history.
(defun fn-sco-extend (c configs suffix)
  (declare (xargs :guard t :verify-guards nil))
  (let ((records (true-list-fix (fn-sco-records c))))
    (fn-sco-make (append records suffix)
                 (fn-sco-cpr-resume (fn-sco-cpr c) configs suffix)
                 (fn-replay-identity-loop suffix (fn-sco-identity c))
                 (fn-sco-consumer-resume (fn-sco-consumer c) suffix
                                         (len records))
                 (fn-th-prefix-loop (fn-sco-topic c) suffix)
                 (fn-cei-build-aux suffix (len records)
                                   (fn-sco-event-index c)))))

; The body of fn-cpo-open-observed, with each fold's result taken from the
; checkpoint instead of recomputed.
(defun fn-sco-finalize (c configs frontier)
  (declare (xargs :guard t :verify-guards nil))
  (let ((events (fn-sco-records c)))
    (if (or (null configs)
            (not (fn-sn-observed-historyp frontier events)))
        (fn-sn-open-error :history)
      (let ((replayed (fn-sco-cpr-finish (fn-sco-cpr c) configs)))
        (if (not (equal (fn-replay-result-kind replayed) :ok))
            (fn-sn-open-error :replay)
          (let* ((cn (fn-replay-result-node replayed))
                 (node (fn-cnode-node cn)))
            (if (not (and (fn-cnode-statep cn)
                          (fn-replay-advance-okp node frontier)))
                (fn-sn-open-error :frontier)
              (let* ((advanced (fn-replay-advance-txid node frontier))
                     (config (fn-cnode-config cn))
                     (identity (fn-sco-identity c))
                     (consumer (fn-sco-consumer c))
                     (topic (fn-sco-topic c))
                     (files (fn-sf-make :recovering frontier nil events
                                        nil nil nil 0))
                     (seed (fn-sn-observed-seed
                            (fn-cnode-domain-of config)
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
                              (fn-sco-event-index c))))
                (if (and (equal (fn-stxk-context-kind identity) :ok)
                         (consp consumer) (eq (car consumer) :ok)
                         (eq (fn-th-at 0 topic) :ok)
                         (fn-sn-statep opened))
                    (fn-sn-open-ok opened)
                  (fn-sn-open-error :identity))))))))))

; The function the host calls at open when a checkpoint verified
; (fn-store-sn-recover-from-checkpoint, host/store-node-host.lisp).
(defun fn-sco-open (c configs frontier suffix)
  (declare (xargs :guard t :verify-guards nil))
  (fn-sco-finalize (fn-sco-extend c configs suffix) configs frontier))

; The configuration the opened Store serves, for the host's fn-store-cfg.
(defun fn-sco-replay-result (c configs suffix)
  (declare (xargs :guard t :verify-guards nil))
  (fn-sco-cpr-finish (fn-sco-cpr-resume (fn-sco-cpr c) configs suffix) configs))

; -----------------------------------------------------------------------------
; One append lemma per fold

(defthm fn-sco-cpr-prefix-paused-counter
  (implies (and (natp config-sequence)
                (fn-sco-pausedp
                 (fn-sco-cpr-prefix cn configs events config-sequence
                                    event-sequence)))
           (and (integerp (nth 2 (fn-sco-cpr-prefix cn configs events
                                                    config-sequence event-sequence)))
                (<= config-sequence
                    (nth 2 (fn-sco-cpr-prefix cn configs events
                                              config-sequence event-sequence)))))
  :rule-classes ((:rewrite :corollary
                  (implies (and (natp config-sequence)
                                (fn-sco-pausedp
                                 (fn-sco-cpr-prefix cn configs events config-sequence
                                                    event-sequence)))
                           (integerp (nth 2 (fn-sco-cpr-prefix cn configs events
                                                               config-sequence
                                                               event-sequence)))))
                 (:linear :corollary
                  (implies (and (natp config-sequence)
                                (fn-sco-pausedp
                                 (fn-sco-cpr-prefix cn configs events config-sequence
                                                    event-sequence)))
                           (<= config-sequence
                               (nth 2 (fn-sco-cpr-prefix cn configs events
                                                         config-sequence
                                                         event-sequence))))))
  :hints (("Goal" :induct (fn-sco-cpr-prefix cn configs events config-sequence
                                             event-sequence)
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(fn-sco-cpr-prefix fn-replay-fault
                                        fn-sco-paused fn-sco-pausedp
                                        nfix natp fix car-cons cdr-cons nth zp
                                        (:executable-counterpart equal))))))

(local
 (defthm fn-sco-nthcdr-of-cdr-step
   (implies (and (natp a) (natp b) (< a b))
            (equal (nthcdr (- b (+ 1 a)) (cdr x))
                   (nthcdr (- b a) x)))
   :hints (("Goal" :expand ((nthcdr (- b a) x))))))

(local
 (defthm fn-sco-config-firstp-of-append
   (implies (consp prefix)
            (equal (fn-cpr-config-firstp configs (append prefix suffix))
                   (fn-cpr-config-firstp configs prefix)))
   :hints (("Goal" :in-theory (enable fn-cpr-config-firstp)))))

(local
 (defthm fn-sco-nthcdr-zero-diff
   (equal (nthcdr (- n n) x) x)))

(local
 (defthm fn-sco-append-shape
   (and (implies (consp p)
                 (and (consp (append p s))
                      (equal (car (append p s)) (car p))
                      (equal (cdr (append p s)) (append (cdr p) s))))
        (implies (not (consp p))
                 (equal (append p s) s)))))

; The configuration and node fold (keystone part 1): a fold over P ++ Q is
; the fold over P, paused, then resumed over Q from the configurations the
; pause has not consumed.  fn-cpr-loop is the host's pass; the prefix is its
; exact copy up to the pause.
(defthm fn-cpr-loop-append
  (implies (and (natp config-sequence) (natp event-sequence))
           (equal (fn-cpr-loop cn configs (append prefix suffix)
                               config-sequence event-sequence)
                  (let ((r (fn-sco-cpr-prefix cn configs prefix
                                              config-sequence event-sequence)))
                    (if (fn-sco-pausedp r)
                        (fn-cpr-loop (nth 1 r)
                                     (nthcdr (- (nth 2 r) config-sequence) configs)
                                     suffix (nth 2 r) (nth 3 r))
                      r))))
  :hints (("Goal" :induct (fn-sco-cpr-prefix cn configs prefix config-sequence
                                             event-sequence)
           :expand ((:free (ev cs es) (fn-cpr-loop cn configs ev cs es)))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(fn-sco-cpr-prefix fn-sco-paused fn-sco-pausedp
                                        nfix natp fix car-cons cdr-cons nth zp
                                        nthcdr fn-sco-append-shape
                                        fn-sco-config-firstp-of-append
                                        fn-sco-nthcdr-of-cdr-step
                                        fn-sco-nthcdr-zero-diff
                                        fn-sco-cpr-prefix-paused-counter
                                        (:executable-counterpart equal)
                                        fn-replay-fault)))))

; The same split for the paused fold itself: resuming is the fold over the
; concatenation.  This is what lets one checkpoint extend to the next.
(defthm fn-sco-cpr-prefix-append
  (implies (and (natp config-sequence) (natp event-sequence))
           (equal (fn-sco-cpr-prefix cn configs (append prefix suffix)
                                     config-sequence event-sequence)
                  (let ((r (fn-sco-cpr-prefix cn configs prefix
                                              config-sequence event-sequence)))
                    (if (fn-sco-pausedp r)
                        (fn-sco-cpr-prefix (nth 1 r)
                                           (nthcdr (- (nth 2 r) config-sequence)
                                                   configs)
                                           suffix (nth 2 r) (nth 3 r))
                      r))))
  :hints (("Goal" :induct (fn-sco-cpr-prefix cn configs prefix config-sequence
                                             event-sequence)
           :expand ((:free (ev cs es) (fn-sco-cpr-prefix cn configs ev cs es)))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(fn-sco-cpr-prefix fn-sco-paused fn-sco-pausedp
                                        nfix natp fix car-cons cdr-cons nth zp
                                        nthcdr fn-sco-append-shape
                                        fn-sco-config-firstp-of-append
                                        fn-sco-nthcdr-of-cdr-step
                                        fn-sco-nthcdr-zero-diff
                                        fn-sco-cpr-prefix-paused-counter
                                        (:executable-counterpart equal)
                                        fn-replay-fault)))))

; A list of Store events, as the history recognizer admits.
(defun fn-sco-store-eventsp (records)
  (declare (xargs :guard t))
  (if (consp records)
      (and (fn-store-event-p (car records))
           (fn-sco-store-eventsp (cdr records)))
    (null records)))

(defthm fn-replay-identity-append
  (implies (fn-sco-store-eventsp prefix)
           (equal (fn-replay-identity-loop (append prefix suffix) ctx)
                  (fn-replay-identity-loop suffix
                                           (fn-replay-identity-loop prefix ctx))))
  :hints (("Goal" :induct (fn-replay-identity-loop prefix ctx)
           :in-theory (e/d (fn-replay-identity-loop)
                           (fn-replay-identity-step fn-store-event-p)))))

(defthm fn-cpe-projection-replay-append
  (implies (and (natp expected) (true-listp prefix))
           (equal (fn-cpe-projection-replay s (append prefix suffix) expected)
                  (let ((r (fn-cpe-projection-replay s prefix expected)))
                    (if (and (consp r) (eq (car r) :ok))
                        (fn-cpe-projection-replay (fn-cp-nth 1 r) suffix
                                                  (+ expected (len prefix)))
                      r))))
  :hints (("Goal" :induct (fn-cpe-projection-replay s prefix expected)
           :in-theory (e/d (fn-cpe-projection-replay fn-cp-nth)
                           (fn-cpe-projection-step)))))

(defthm fn-th-prefix-project-append
  (implies (true-listp prefix)
           (equal (fn-th-prefix-loop projection (append prefix suffix))
                  (fn-th-prefix-loop (fn-th-prefix-loop projection prefix)
                                     suffix)))
  :hints (("Goal" :induct (fn-th-prefix-loop projection prefix)
           :in-theory (e/d (fn-th-prefix-loop) (fn-th-prefix-step)))))

(defthm fn-cei-build-append
  (implies (natp sequence)
           (equal (fn-cei-build-aux (append prefix suffix) sequence index)
                  (fn-cei-build-aux suffix (+ sequence (len prefix))
                                    (fn-cei-build-aux prefix sequence index))))
  :hints (("Goal" :induct (fn-cei-build-aux prefix sequence index)
           :in-theory (e/d (fn-cei-build-aux) (fn-cei-put)))))

; The history recognizer over P ++ Q admits only a true list of Store events.
(defthm fn-sco-record-listp-shape
  (implies (fn-sf-record-listp records sequence lower frontier)
           (and (true-listp records)
                (fn-sco-store-eventsp records)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (e/d (fn-sf-record-listp) (fn-store-event-p)))))

(local
 (defthm fn-sco-store-eventsp-of-append
   (implies (fn-sco-store-eventsp (append p s))
            (fn-sco-store-eventsp (true-list-fix p)))
   :hints (("Goal" :in-theory (disable fn-store-event-p)))))

(local
 (defthm fn-sco-true-listp-of-append
   (equal (true-listp (append p s)) (true-listp s))))

(local
 (defthm fn-sco-append-true-list-fix
   (equal (append (true-list-fix p) s) (append p s))))

(local
 (defthm fn-sco-true-list-fix-when-true-listp
   (implies (true-listp x) (equal (true-list-fix x) x))))

(local
 (defthm fn-sco-len-true-list-fix
   (equal (len (true-list-fix x)) (len x))))

(local
 (defthm fn-sco-cpe-replay-shape
   (let ((r (fn-cpe-projection-replay s records expected)))
     (and (consp r) (true-listp r)))
   :hints (("Goal" :in-theory (enable fn-cpe-projection-replay
                                      fn-cpe-projection-step)))))

; -----------------------------------------------------------------------------
; The keystone

; Extending the capture of P over Q is the capture of P ++ Q: the checkpoint
; the owner publishes after an open is the capture of the whole history.
(defthm fn-sco-extend-of-capture
  (implies (and (fn-sco-store-eventsp (true-list-fix prefix))
                (true-listp suffix))
           (equal (fn-sco-extend (fn-sco-capture configs prefix) configs suffix)
                  (fn-sco-capture configs (append prefix suffix))))
  :hints (("Goal"
           :use ((:instance fn-sco-cpr-prefix-append
                            (cn (fn-cnode-initial (fn-cfg-initial)))
                            (prefix (true-list-fix prefix))
                            (config-sequence 0) (event-sequence 0))
                 (:instance fn-replay-identity-append
                            (prefix (true-list-fix prefix))
                            (ctx (fn-stxk-initial-context 0)))
                 (:instance fn-cpe-projection-replay-append
                            (s nil) (prefix (true-list-fix prefix)) (expected 0))
                 (:instance fn-th-prefix-project-append
                            (projection (fn-th-prefix-state :ok 0 nil nil nil nil nil))
                            (prefix (true-list-fix prefix)))
                 (:instance fn-cei-build-append
                            (prefix (true-list-fix prefix)) (sequence 0) (index nil)))
           :in-theory (e/d (fn-sco-extend fn-sco-capture fn-sco-make
                            fn-sco-records fn-sco-cpr fn-sco-identity
                            fn-sco-consumer fn-sco-topic fn-sco-event-index
                            fn-sco-at fn-sco-nthcdr fn-sco-cpr-resume fn-sco-consumer-resume
                            fn-cp-nth)
                           (fn-sco-cpr-prefix-append fn-replay-identity-append
                            fn-cpe-projection-replay-append
                            fn-th-prefix-project-append fn-cei-build-append
                            fn-sco-cpr-prefix fn-replay-identity-loop
                            fn-cpe-projection-replay fn-th-prefix-loop
                            fn-cei-build-aux fn-sco-store-eventsp
                            fn-cnode-initial fn-cfg-initial
                            fn-stxk-initial-context fn-th-prefix-state)))))

; Finishing the capture of a whole history is the host's open of it.
(defthm fn-sco-finalize-of-capture
  (implies (true-listp records)
           (equal (fn-sco-finalize (fn-sco-capture configs records) configs frontier)
                  (fn-cpo-open-observed configs frontier records)))
  :hints (("Goal"
           :use ((:instance fn-cpr-loop-append
                            (cn (fn-cnode-initial (fn-cfg-initial)))
                            (prefix records) (suffix nil)
                            (config-sequence 0) (event-sequence 0)))
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(fn-sco-finalize fn-sco-capture fn-sco-make
                         fn-sco-records fn-sco-cpr fn-sco-identity
                         fn-sco-consumer fn-sco-topic fn-sco-event-index
                         fn-sco-at fn-sco-nthcdr fn-sco-cpr-finish fn-cpo-open-observed
                         fn-cpr-replay fn-replay-identity fn-th-prefix-project
                         fn-cei-build nth car-cons cdr-cons nfix natp fix zp
                         fn-sco-true-list-fix-when-true-listp
                         fn-sco-cpr-prefix-paused-counter fn-sco-cpe-replay-shape
                         append-to-nil unicity-of-0 commutativity-of-+
                         (:executable-counterpart unary--)
                         (:executable-counterpart equal)
                         (:executable-counterpart natp)
                         (:executable-counterpart zp)
                         (:executable-counterpart nfix))))))

(local
 (defthm fn-sco-open-when-history
   (implies (fn-sn-observed-historyp frontier (append prefix suffix))
            (equal (fn-sco-open (fn-sco-capture configs prefix) configs frontier suffix)
                   (fn-cpo-open-observed configs frontier (append prefix suffix))))
   :hints (("Goal"
            :use ((:instance fn-sco-extend-of-capture)
                  (:instance fn-sco-finalize-of-capture
                             (records (append prefix suffix)))
                  (:instance fn-sco-record-listp-shape
                             (records (append prefix suffix))
                             (sequence 0) (lower 0))
                  (:instance fn-sco-store-eventsp-of-append (p prefix) (s suffix)))
            :in-theory (union-theories
                        (theory 'minimal-theory)
                        '(fn-sco-open fn-sn-observed-historyp
                          fn-sco-true-listp-of-append))))))

(local
 (defthm fn-sco-true-listp-true-list-fix
   (true-listp (true-list-fix x))))

(local
 (defthm fn-sco-open-when-no-history
   (implies (not (fn-sn-observed-historyp frontier (append prefix suffix)))
            (equal (fn-sco-open (fn-sco-capture configs prefix) configs frontier suffix)
                   (fn-cpo-open-observed configs frontier (append prefix suffix))))
   :hints (("Goal"
            :in-theory (union-theories
                        (theory 'minimal-theory)
                        '(fn-sco-open fn-sco-finalize fn-cpo-open-observed
                          fn-sco-extend fn-sco-capture fn-sco-make
                          fn-sco-records fn-sco-at nth car-cons cdr-cons
                          fn-sco-append-true-list-fix
                          fn-sco-true-list-fix-when-true-listp
                          fn-sco-true-listp-true-list-fix
                          (:executable-counterpart equal)
                          (:executable-counterpart zp)))))))

; The keystone.  The host calls fn-sco-open at open when a checkpoint
; verified (fn-store-sn-recover-from-checkpoint, host/store-node-host.lisp)
; and fn-cpo-open-observed on a full replay (fn-store-sn-recover).  For every
; configuration history, frontier, record prefix P and suffix Q, opening the
; capture of P over Q is the full open of P ++ Q.  No hypothesis: a history
; the recognizer refuses is refused by both.
(defthm fn-sn-recover-from-checkpoint-equals-full-recover
  (equal (fn-sco-open (fn-sco-capture configs prefix) configs frontier suffix)
         (fn-cpo-open-observed configs frontier (append prefix suffix)))
  :hints (("Goal" :cases ((fn-sn-observed-historyp frontier (append prefix suffix)))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(fn-sco-open-when-history
                                        fn-sco-open-when-no-history)))))

; A checkpoint captured under one configuration history opens under a longer
; one.  Configuration and Store records share one transaction-ID frontier,
; so a configuration published after the checkpoint has a txid above every
; record the checkpoint covers; under that condition the capture does not
; see it, and the keystone applies with the configuration history read at
; open.
(defun fn-sco-txids-belowp (events bound)
  (declare (xargs :guard (natp bound)))
  (if (consp events)
      (and (< (nfix (fn-store-event-txid (car events))) bound)
           (fn-sco-txids-belowp (cdr events) bound))
    t))

(defun fn-sco-later-configsp (later events)
  (declare (xargs :guard t))
  (or (not (consp later))
      (fn-sco-txids-belowp events (nfix (fn-cfg-record-txid (car later))))))

(local
 (defthm fn-sco-config-firstp-of-later
   (implies (and (consp events) (fn-sco-later-configsp later events))
            (equal (fn-cpr-config-firstp (append configs later) events)
                   (fn-cpr-config-firstp configs events)))
   :hints (("Goal" :in-theory (enable fn-cpr-config-firstp)))))

(local
 (defthm fn-sco-config-firstp-later-alone
   (implies (and (consp events) (fn-sco-later-configsp later events))
            (not (fn-cpr-config-firstp later events)))
   :hints (("Goal" :in-theory (enable fn-cpr-config-firstp)))))

(local
 (defthm fn-sco-later-configsp-of-cdr
   (implies (fn-sco-later-configsp later events)
            (fn-sco-later-configsp later (cdr events)))))

(defthm fn-sco-cpr-prefix-of-later-configs
  (implies (fn-sco-later-configsp later events)
           (equal (fn-sco-cpr-prefix cn (append configs later) events
                                     config-sequence event-sequence)
                  (fn-sco-cpr-prefix cn configs events
                                     config-sequence event-sequence)))
  :hints (("Goal" :induct (fn-sco-cpr-prefix cn configs events
                                             config-sequence event-sequence)
           :expand ((:free (cf cs es) (fn-sco-cpr-prefix cn cf events cs es)))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(fn-sco-paused fn-sco-pausedp fn-replay-fault
                                        car-cons cdr-cons nfix fn-sco-append-shape
                                        fn-sco-config-firstp-of-later
                                        fn-sco-config-firstp-later-alone
                                        fn-cpr-config-firstp-has-config
                                        fn-sco-later-configsp-of-cdr
                                        (:induction fn-sco-cpr-prefix)
                                        (:executable-counterpart equal))))
          (and stable-under-simplificationp
               '(:cases ((consp configs))))))

(defthm fn-sco-capture-of-later-configs
  (implies (fn-sco-later-configsp later (true-list-fix records))
           (equal (fn-sco-capture (append configs later) records)
                  (fn-sco-capture configs records)))
  :hints (("Goal" :in-theory (e/d (fn-sco-capture)
                                  (fn-sco-cpr-prefix fn-sco-later-configsp)))))

; Which open runs.  The checkpoint serves only when its digest chain verified,
; it covers no more records than the store has committed, and the suffix it
; leaves is within K, the profile's max-open-suffix.  Otherwise the open is a
; full replay, reported with its reason; it is slower, never wrong, because the
; checkpoint is derived and replay stays authoritative (storage.md:227).
(defun fn-sco-select (status sequence count k)
  (declare (xargs :guard t))
  (cond ((eq status :absent) (list :full-replay :absent))
        ((not (eq status :ok)) (list :full-replay :corrupt))
        ((not (and (natp sequence) (natp count) (<= sequence count)))
         (list :full-replay :ahead-of-history))
        ((not (and (natp k) (<= (- count sequence) k)))
         (list :full-replay :suffix-exceeds-k))
        (t (list :checkpoint sequence))))

(defthm fn-sco-select-bounds-the-suffix
  (implies (equal (car (fn-sco-select status sequence count k)) :checkpoint)
           (and (equal status :ok)
                (natp sequence) (natp count)
                (<= sequence count)
                (<= (- count sequence) k)))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; Guards: the host runs these compiled.

(verify-guards fn-sco-cpr-prefix
  :hints (("Goal" :in-theory (e/d (fn-cnode-statep)
                                  (fn-cpr-config-firstp fn-cpr-apply-event
                                   fn-cfg-recordp fn-store-event-p)))))
(verify-guards fn-sco-cpr-resume)
(verify-guards fn-sco-cpr-finish)
(verify-guards fn-sco-consumer-resume)
(verify-guards fn-sco-capture)
(verify-guards fn-sco-extend)
(verify-guards fn-sco-finalize
  :hints (("Goal"
           :in-theory (e/d (fn-cnode-statep)
                           (fn-cpr-replay fn-cpr-loop fn-sn-statep
                            fn-sco-cpr-finish fn-sco-cpr-prefix)))))
(verify-guards fn-sco-open)
(verify-guards fn-sco-replay-result)
