; The record log's completion-driven commit driver and the POST
; transaction's durability (Builder L, landing 1: P4, AckEligible =>
; DurableCommitEvidence).
;
; The driver fn-ptd is the log half of the POST transaction machine (A's
; books/post-transaction.lisp delegates its log phases to it): it takes one
; record at the kernel's next txid, submits the segment's extension when the
; record's entry does not fit, the record's chained entry at the kernel's
; frontier, and the barrier, and answers :posted only on the barrier's :ok
; completion -- the commit point (RUNTIME-MODEL section 5).  Its completions
; are the host operations of books/store-log-durable.lisp (fn-lgu-host-step),
; so the cut theorem there discharges durability.
;
; Cut model: the cuts of fn-lgu-host-run over the driver's operations (every
; intermediate store of each: the seal's extension written, extension
; fenced, record written; the fence; the acknowledgement), and every
; admissible crash image of each cut (fn-bs-crash-imagep).  The environment
; chooses each action's outcome at issue (the byte model's), so a crash while
; an action is in flight is a crash image of the cut its completion with that
; outcome produces; the keystone quantifies over every continuation E2, which
; includes the completions of whatever is in flight.  Input contract: a
; completion names the one outstanding action (the POST machine's buffer
; handle and generation).  Scope: one segment, no rotation, a batch of one,
; one transaction in flight.
;
; The theorems (each from the open: KS0 R-related to the store BS and
; fn-ptd-open-kernelp, which the open's kernel is, fn-ptd-open-kernelp-of-the-open):
;   P4-1 fn-ptd-posted-only-at-the-barrier-completion: a step answers :posted
;        iff the driver is :syncing and the input is the barrier's :ok; its
;        operations are then the fence and one acknowledgement.
;   P4-2 fn-ptd-run-is-the-host-run: the driver's kernel is the host run's,
;        and its extent and sealed extent are the store's, so its actions are
;        fn-lgu-host-step's syscalls.
;   P4-3 fn-ptd-posted-are-the-acknowledged: the records answered :posted, in
;        order, are the kernel's newly acknowledged ones.
;   KEYSTONE fn-ptd-posted-records-are-recovered-at-every-later-cut.
; Teeth: tests/acl2/post-transaction-durable-tests.lisp.

(in-package "ACL2")
(include-book "store-log-durable")

(defun fn-ptd-mk (ph ks rec ext nxt)
  (declare (xargs :guard t))
  (list ph ks rec (nfix ext) (nfix nxt)))
(defun fn-ptd-ph (st) (declare (xargs :guard t)) (car (true-list-fix st)))
(defun fn-ptd-ks (st) (declare (xargs :guard t)) (nth 1 (true-list-fix st)))
(defun fn-ptd-rec (st) (declare (xargs :guard t)) (nth 2 (true-list-fix st)))
(defun fn-ptd-ext (st) (declare (xargs :guard t)) (nfix (nth 3 (true-list-fix st))))
(defun fn-ptd-nxt (st) (declare (xargs :guard t)) (nfix (nth 4 (true-list-fix st))))

; The driver after the open: the open's kernel, the segment's extent.
(defun fn-ptd-init (ks ext) (declare (xargs :guard t)) (fn-ptd-mk :ready ks nil ext ext))

; The take the driver asks for: a batch of one, at the kernel's next txid.
(defun fn-ptd-take-op (ks r unit)
  (declare (xargs :guard t :verify-guards nil))
  (list :take r (fn-lgk-next-txid ks) 0 0 0 0 unit))

; The record's write: the kernel's chained entry at its frontier.
(defun fn-ptd-record-write (ks ino unit)
  (declare (xargs :guard t :verify-guards nil))
  (list :pwrite ino (fn-lgk-frontier ks) (fn-lgk-append-octets ks unit)))

(defun fn-ptd-begin (st r ino unit max)
  (declare (xargs :guard t :verify-guards nil))
  (let ((ks (fn-ptd-ks st)) (ext (fn-ptd-ext st)))
    (if (not (equal (fn-ptd-ph st) :ready))
        (mv st nil (list (cons (if (equal (fn-ptd-ph st) :fenced) :refused :busy) r)) nil)
      (let* ((tk (fn-ptd-take-op ks r unit))
             (ks1 (fn-lgk-host-step ks tk))
             (nxt (fn-lgk-sealed-extent ks1 ext unit)))
        (if (not (and (equal (fn-lgu-take-verdict r max) :admissible)
                      (not (consp (fn-lgk-batch ks)))
                      (not (consp (fn-lgk-inflight ks)))
                      (consp (fn-lgk-batch ks1))
                      (fn-lg-append-admitsp ks1 unit nxt)))
            (mv st nil (list (cons :refused r)) nil)
          (if (equal nxt ext)
              (mv (fn-ptd-mk :writing ks1 r ext nxt)
                  (list (fn-ptd-record-write ks1 ino unit)) nil (list tk))
            (mv (fn-ptd-mk :extending ks1 r ext nxt)
                (list (list :pwrite ino ext (fn-bs-zeros (- nxt ext)))) nil (list tk))))))))

; The seal's kernel effect (fn-lgu-host-step :seal): the append, faulted
; unless every outcome was :ok.
(defun fn-ptd-sealed (ks unit nxt ok)
  (declare (xargs :guard t :verify-guards nil))
  (let ((ks1 (fn-lgk-append ks unit nxt))) (if ok ks1 (fn-lgk-fence-failed ks1))))

(defun fn-ptd-complete (st ev ino unit)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((ph (fn-ptd-ph st)) (ks (fn-ptd-ks st)) (r (fn-ptd-rec st))
         (ext (fn-ptd-ext st)) (nxt (fn-ptd-nxt st))
         (kind (car ev)) (o (cdr ev)))
    (cond
     ((and (equal ph :extending) (equal kind :pwrite))
      (if (equal o :ok)
          (mv (fn-ptd-mk :extsyncing ks r ext nxt) (list (list :fsync ino)) nil nil)
        (mv (fn-ptd-mk :fenced (fn-ptd-sealed ks unit nxt nil) nil ext nxt)
            nil (list (cons :refused r)) (list (list :seal o :ok :ok)))))
     ((and (equal ph :extsyncing) (equal kind :fsync))
      (if (equal o :ok)
          (mv (fn-ptd-mk :writing ks r ext nxt) (list (fn-ptd-record-write ks ino unit)) nil nil)
        (mv (fn-ptd-mk :fenced (fn-ptd-sealed ks unit nxt nil) nil ext nxt)
            nil (list (cons :refused r)) (list (list :seal :ok o :ok)))))
     ((and (equal ph :writing) (equal kind :pwrite))
      (if (equal o :ok)
          (mv (fn-ptd-mk :syncing (fn-ptd-sealed ks unit nxt t) r ext nxt)
              (list (list :fsync ino)) nil (list (list :seal :ok :ok o)))
        (mv (fn-ptd-mk :fenced (fn-ptd-sealed ks unit nxt nil) nil ext nxt)
            nil (list (cons :uncertain r)) (list (list :seal :ok :ok o)))))
     ((and (equal ph :syncing) (equal kind :fsync))
      (if (equal o :ok)
          ;; THE COMMIT POINT: the barrier's completion.
          (mv (fn-ptd-mk :ready (fn-lgk-finish-one (fn-lgk-fence ks unit)) nil nxt nxt)
              nil (list (cons :posted r)) (list (list :fence o) (list :finish-one)))
        (mv (fn-ptd-mk :fenced (fn-lgk-fence-failed ks) nil ext nxt)
            nil (list (cons :uncertain r)) (list (list :fence o)))))
     (t (mv st nil nil nil)))))

(defun fn-ptd-step (st in ino unit max)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (consp in) (equal (car in) :begin))
      (fn-ptd-begin st (cadr in) ino unit max)
    (fn-ptd-complete st in ino unit)))

; A run over inputs: (mv ST ACTIONS ANSWERS OPS), each list in order.
(defun fn-ptd-run (st ins ino unit max)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom ins)
      (mv st nil nil nil)
    (mv-let (st1 a1 w1 o1) (fn-ptd-step st (car ins) ino unit max)
      (mv-let (st2 a2 w2 o2) (fn-ptd-run st1 (cdr ins) ino unit max)
        (mv st2 (append a1 a2) (append w1 w2) (append o1 o2))))))

; The records answered :posted, in order.
(defun fn-ptd-posted (answers)
  (declare (xargs :guard t))
  (cond ((atom answers) nil)
        ((and (consp (car answers)) (equal (car (car answers)) :posted))
         (cons (cdr (car answers)) (fn-ptd-posted (cdr answers))))
        (t (fn-ptd-posted (cdr answers)))))
(defthm fn-ptd-posted-only-at-the-barrier-completion
  (mv-let (st1 acts ans ops) (fn-ptd-step st in ino unit max)
    (declare (ignore st1 acts))
    (and (iff (consp (fn-ptd-posted ans))
              (and (equal (fn-ptd-ph st) :syncing) (equal in '(:fsync . :ok))))
         (implies (consp (fn-ptd-posted ans))
                  (and (equal ans (list (cons :posted (fn-ptd-rec st))))
                       (equal ops '((:fence :ok) (:finish-one)))))))
  :hints (("Goal" :in-theory (disable fn-lgk-host-step fn-lgk-sealed-extent fn-lgk-append-octets
                                      fn-lg-append-admitsp fn-lgu-take-verdict fn-lgk-finish-one
                                      fn-lgk-fence fn-lgk-fence-failed fn-ptd-sealed fn-bs-zeros
                                      fn-lgk-frontier fn-lgk-batch fn-lgk-inflight fn-lgk-next-txid))))

; -----------------------------------------------------------------------------
; The invariant: the driver against the host run of its operations.

(defun fn-ptd-invp (st bs ks ino genesis max)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((unit (fn-bs-unit bs)) (ext (fn-ptd-ext st)) (nxt (fn-ptd-nxt st))
         (c (fn-bs-durable-content bs ino)))
    (and (equal (fn-ptd-ks st) ks)
         (case (fn-ptd-ph st)
           (:ready (and (fn-lgk-relp bs ks ino genesis max)
                        (not (consp (fn-lgk-batch ks))) (not (consp (fn-lgk-inflight ks)))
                        (equal (fn-lgk-acked ks) (len (fn-lgk-committed ks)))
                        (equal ext (len c))))
           ((:extending :extsyncing :writing)
            (and (fn-lgk-relp bs ks ino genesis max)
                 (not (consp (fn-lgk-inflight ks)))
                 (equal (fn-lgk-batch ks) (list (fn-ptd-rec st)))
                 (equal (fn-lgk-acked ks) (len (fn-lgk-committed ks)))
                 (equal ext (len c))
                 (or (equal (fn-ptd-ph st) :writing) (not (equal nxt ext)))
                 (equal nxt (fn-lgk-sealed-extent ks ext unit))
                 (fn-lg-append-admitsp ks unit nxt)))
           (:syncing (and (fn-lgk-relp bs ks ino genesis max)
                          (equal (fn-lgk-phase ks) :appended)
                          (equal (fn-lgk-inflight ks) (list (fn-ptd-rec st)))
                          (not (consp (fn-lgk-batch ks)))
                          (equal (fn-lgk-acked ks) (len (fn-lgk-committed ks)))
                          (equal nxt (len c))))
           (otherwise (<= (fn-lgk-acked ks) (len (fn-lgk-committed ks))))))))

(defthm fn-ptd-unit-of-write
  (equal (fn-bs-unit (mv-nth 1 (fn-bs-write s ino offset octets outcome))) (fn-bs-unit s))
  :hints (("Goal" :in-theory (enable fn-bs-write))))
(defthm fn-ptd-unit-of-fsync
  (equal (fn-bs-unit (mv-nth 1 (fn-bs-fsync-file s ino outcome))) (fn-bs-unit s))
  :hints (("Goal" :in-theory (enable fn-bs-fsync-file fn-bs-fence-file))))
(defthm fn-ptd-unit-of-host-step
  (equal (fn-bs-unit (mv-nth 1 (fn-lgu-host-step bs ks op ino max))) (fn-bs-unit bs))
  :hints (("Goal" :in-theory (e/d (fn-lgu-host-step fn-lgu-extend)
                                  (fn-bs-write fn-bs-fsync-file fn-lgk-host-step fn-lgk-append
                                   fn-lgk-sealed-extent fn-lg-append-admitsp fn-lgk-append-octets)))))
(defthm fn-ptd-unit-of-host-final
  (equal (fn-bs-unit (car (fn-lgu-host-final bs ks ops ino max))) (fn-bs-unit bs))
  :hints (("Goal" :induct (fn-lgu-host-final bs ks ops ino max)
           :in-theory (disable fn-lgu-host-step))))

(defthm fn-ptd-host-final-of-nil
  (equal (fn-lgu-host-final bs ks nil ino max) (cons bs ks)))

(defthm fn-ptd-host-final-of-one
  (equal (fn-lgu-host-final bs ks (list op) ino max)
         (cons (mv-nth 1 (fn-lgu-host-step bs ks op ino max))
               (mv-nth 2 (fn-lgu-host-step bs ks op ino max))))
  :hints (("Goal" :expand ((fn-lgu-host-final bs ks (list op) ino max))
           :in-theory (disable fn-lgu-host-step))))

(defthm fn-ptd-host-final-of-two
  (equal (fn-lgu-host-final bs ks (list op1 op2) ino max)
         (let ((bs1 (mv-nth 1 (fn-lgu-host-step bs ks op1 ino max)))
               (ks1 (mv-nth 2 (fn-lgu-host-step bs ks op1 ino max))))
           (cons (mv-nth 1 (fn-lgu-host-step bs1 ks1 op2 ino max))
                 (mv-nth 2 (fn-lgu-host-step bs1 ks1 op2 ino max)))))
  :hints (("Goal" :expand ((fn-lgu-host-final bs ks (list op1 op2) ino max)
                           (:free (b k) (fn-lgu-host-final b k (list op2) ino max)))
           :in-theory (disable fn-lgu-host-step))))

; The take of one record into an empty batch.
(defthm fn-ptd-take-fields
  (let ((ks1 (fn-lgk-host-step ks (fn-ptd-take-op ks r unit))))
    (and (equal (fn-lgk-committed ks1) (fn-lgk-committed ks))
         (equal (fn-lgk-acked ks1) (fn-lgk-acked ks))
         (equal (fn-lgk-inflight ks1) (fn-lgk-inflight ks))
         (implies (not (consp (fn-lgk-batch ks)))
                  (iff (consp (fn-lgk-batch ks1)) (not (equal (fn-lgk-phase ks) :fault))))
         (implies (and (not (consp (fn-lgk-batch ks))) (consp (fn-lgk-batch ks1)))
                  (equal (fn-lgk-batch ks1) (list r)))))
  :hints (("Goal" :in-theory (enable fn-lgk-host-step fn-olr-take fn-lgk-prepare fn-ptd-take-op))))

(defthm fn-ptd-fields-of-mk
  (and (equal (fn-ptd-ph (fn-ptd-mk ph ks rec ext nxt)) ph)
       (equal (fn-ptd-ks (fn-ptd-mk ph ks rec ext nxt)) ks)
       (equal (fn-ptd-rec (fn-ptd-mk ph ks rec ext nxt)) rec)
       (equal (fn-ptd-ext (fn-ptd-mk ph ks rec ext nxt)) (nfix ext))
       (equal (fn-ptd-nxt (fn-ptd-mk ph ks rec ext nxt)) (nfix nxt))))

(defthm fn-ptd-invp-of-in-flight
  (implies (and (member-equal ph '(:extending :extsyncing :writing))
                (fn-lgk-relp bs ks ino genesis max)
                (not (consp (fn-lgk-inflight ks)))
                (equal (fn-lgk-batch ks) (list rec))
                (equal (fn-lgk-acked ks) (len (fn-lgk-committed ks)))
                (equal ext (len (fn-bs-durable-content bs ino)))
                (or (equal ph :writing) (not (equal nxt ext)))
                (equal nxt (fn-lgk-sealed-extent ks ext (fn-bs-unit bs)))
                (natp nxt)
                (fn-lg-append-admitsp ks (fn-bs-unit bs) nxt))
           (fn-ptd-invp (fn-ptd-mk ph ks rec ext nxt) bs ks ino genesis max))
  :hints (("Goal" :in-theory (disable fn-lgk-relp fn-lgk-sealed-extent fn-lg-append-admitsp fn-ptd-mk))))

(defthm fn-ptd-invp-at-ready
  (implies (and (fn-ptd-invp st bs ks ino genesis max) (equal (fn-ptd-ph st) :ready))
           (and (equal (fn-ptd-ks st) ks)
                (fn-lgk-relp bs ks ino genesis max)
                (not (consp (fn-lgk-batch ks))) (not (consp (fn-lgk-inflight ks)))
                (equal (fn-lgk-acked ks) (len (fn-lgk-committed ks)))
                (equal (fn-ptd-ext st) (len (fn-bs-durable-content bs ino)))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (disable fn-lgk-relp))))

(defthm fn-ptd-invp-of-same
  (implies (fn-ptd-invp st bs ks ino genesis max)
           (equal (fn-ptd-ks st) ks))
  :rule-classes :forward-chaining)

(defthm fn-ptd-take-op-shape
  (and (fn-lgu-kernel-op-p (fn-ptd-take-op ks r unit))
       (equal (car (fn-ptd-take-op ks r unit)) :take)
       (equal (nth 1 (fn-ptd-take-op ks r unit)) r)))

(defthm fn-ptd-begin-keeps-the-invariant
  (implies (and (fn-ptd-invp st bs ks ino genesis max)
                (equal unit (fn-bs-unit bs)))
           (mv-let (st1 acts ans ops) (fn-ptd-begin st r ino unit max)
             (declare (ignore acts ans))
             (let ((f (fn-lgu-host-final bs ks ops ino max)))
               (fn-ptd-invp st1 (car f) (cdr f) ino genesis max))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-ptd-begin)
                           (fn-lgk-host-step fn-lgk-sealed-extent fn-lg-append-admitsp fn-lgu-take-verdict
                            fn-lgk-relp fn-bs-zeros fn-lgk-append-octets fn-lgu-host-step fn-ptd-take-op
                            fn-lgk-committed fn-lgk-acked fn-lgk-inflight fn-lgk-batch fn-lgk-phase
                            fn-ptd-invp fn-ptd-mk fn-ptd-ph fn-ptd-ks fn-ptd-ext fn-ptd-nxt fn-ptd-rec
                            fn-ptd-record-write fn-bs-durable-content))
           :cases ((equal (fn-ptd-ph st) :ready))
           :use ((:instance fn-lgu-host-step-of-a-kernel-op-export
                            (op (fn-ptd-take-op ks r unit)))
                 (:instance fn-lgu-kernel-op-keeps-the-relation-export
                            (op (fn-ptd-take-op ks r unit)))
                 (:instance fn-lgu-take-verdict-admits-exactly-log-records (record r))
                 (:instance fn-lgu-relp-content-shape)
                 (:instance fn-ptd-take-fields)
                 (:instance fn-lgu-sealed-extent-facts
                            (ks (fn-lgk-host-step ks (fn-ptd-take-op ks r unit)))
                            (extent (fn-ptd-ext st)))))))

(defthm fn-lgu-extend-unit
  (equal (fn-bs-unit (mv-nth 1 (fn-lgu-extend bs k ino extent next eo1 eo2))) (fn-bs-unit bs))
  :hints (("Goal" :in-theory (e/d (fn-lgu-extend) (fn-bs-write fn-bs-fsync-file fn-bs-zeros)))))
(defthm fn-lg-append-admitsp-means-fits
  (implies (fn-lg-append-admitsp ks unit extent)
           (and (fn-lgk-fitsp ks unit extent)
                (not (consp (fn-lgk-inflight ks)))
                (not (equal (fn-lgk-phase ks) :fault))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-lg-append-admitsp))))

(defthm fn-ptd-extend-ok
  (equal (mv-nth 2 (fn-lgu-extend bs k ino extent next eo1 eo2))
         (or (equal next extent) (and (equal eo1 :ok) (equal eo2 :ok))))
  :hints (("Goal" :in-theory (e/d (fn-lgu-extend) (fn-bs-write fn-bs-fsync-file fn-bs-zeros)))))
(defthm fn-ptd-extend-of-no-extension
  (equal (mv-nth 1 (fn-lgu-extend bs k ino extent extent eo1 eo2)) bs)
  :hints (("Goal" :in-theory (e/d (fn-lgu-extend) (fn-bs-write fn-bs-fsync-file fn-bs-zeros)))))

(defthm fn-ptd-durable-of-write
  (equal (fn-bs-durable-content (mv-nth 1 (fn-bs-write s ino2 offset octets outcome)) ino)
         (fn-bs-durable-content s ino))
  :hints (("Goal" :in-theory (enable fn-bs-write fn-bs-durable-content))))

; The seal from an in-flight state: its kernel is the driver's, and when
; every outcome is :ok the store is related to the append and its durable
; length is the sealed extent.
(defthm fn-ptd-seal-step
  (let* ((unit (fn-bs-unit bs))
         (ext (len (fn-bs-durable-content bs ino)))
         (nxt (fn-lgk-sealed-extent ks ext unit))
         (r (fn-lgu-host-step bs ks (list :seal eo1 eo2 o) ino max))
         (ok (and (or (equal nxt ext) (and (equal eo1 :ok) (equal eo2 :ok))) (equal o :ok))))
    (implies (and (fn-lgk-relp bs ks ino genesis max)
                  (not (consp (fn-lgk-inflight ks)))
                  (fn-lg-append-admitsp ks unit nxt))
             (and (equal (mv-nth 2 r) (fn-ptd-sealed ks unit nxt ok))
                  (implies ok
                           (and (fn-lgk-relp (mv-nth 1 r) (fn-lgk-append ks unit nxt) ino genesis max)
                                (equal (len (fn-bs-durable-content (mv-nth 1 r) ino)) nxt))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lgu-host-step fn-ptd-sealed)
                           (fn-lgk-relp fn-lgu-extend fn-bs-write fn-bs-fsync-file
                            fn-lgk-append fn-lgk-fence-failed fn-lgk-sealed-extent fn-lgk-append-octets
                            fn-lgk-fitsp fn-bs-durable-content fn-lgk-frontier fn-lgk-inflight
                            fn-lgk-phase mod fn-lg-append-admitsp
                            fn-lgk-append-preserves-relation fn-lgu-extend-keeps-the-relation))
           :use ((:instance fn-lgu-relp-content-shape)
                 (:instance fn-lgu-sealed-extent-facts
                            (unit (fn-bs-unit bs)) (extent (len (fn-bs-durable-content bs ino))))
                 (:instance fn-lgu-extend-keeps-the-relation
                            (k (fn-lgk-append ks (fn-bs-unit bs)
                                              (fn-lgk-sealed-extent ks (len (fn-bs-durable-content bs ino))
                                                                    (fn-bs-unit bs))))
                            (extent (len (fn-bs-durable-content bs ino)))
                            (next (fn-lgk-sealed-extent ks (len (fn-bs-durable-content bs ino))
                                                        (fn-bs-unit bs))))
                 (:instance fn-lgk-append-preserves-relation
                            (bs (mv-nth 1 (fn-lgu-extend bs
                                                         (fn-lgk-append ks (fn-bs-unit bs)
                                                                        (fn-lgk-sealed-extent ks (len (fn-bs-durable-content bs ino))
                                                                                              (fn-bs-unit bs)))
                                                         ino (len (fn-bs-durable-content bs ino))
                                                         (fn-lgk-sealed-extent ks (len (fn-bs-durable-content bs ino))
                                                                               (fn-bs-unit bs))
                                                         eo1 eo2))))
                 (:instance fn-lgu-extend-unit
                            (k (fn-lgk-append ks (fn-bs-unit bs)
                                              (fn-lgk-sealed-extent ks (len (fn-bs-durable-content bs ino))
                                                                    (fn-bs-unit bs))))
                            (extent (len (fn-bs-durable-content bs ino)))
                            (next (fn-lgk-sealed-extent ks (len (fn-bs-durable-content bs ino))
                                                        (fn-bs-unit bs))))
                 (:instance fn-lg-append-admitsp-means-fits
                            (unit (fn-bs-unit bs))
                            (extent (fn-lgk-sealed-extent ks (len (fn-bs-durable-content bs ino))
                                                          (fn-bs-unit bs))))))))

(defthm fn-ptd-relp-pending-shape
  (implies (fn-lgk-relp bs ks ino genesis max)
           (and ino
                (true-listp (fn-bs-durable-content bs ino))
                (equal (fn-bs-pending bs)
                       (if (consp (fn-lgk-inflight ks))
                           (list (list :write ino (fn-lgk-frontier ks)
                                       (fn-lg-log (fn-lgk-inflight ks) (fn-lgk-last ks) (fn-bs-unit bs))))
                         nil))
                (<= (+ (fn-lgk-frontier ks)
                       (len (fn-lg-log (fn-lgk-inflight ks) (fn-lgk-last ks) (fn-bs-unit bs))))
                    (len (fn-bs-durable-content bs ino)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-lgk-relp fn-lgk-content-okp)
                                  (fn-lg-scan fn-lg-scan-last fn-lg-log fn-bs-take fn-lg-zerosp
                                   fn-lg-recordsp fn-frame-digestp fn-bs-durable-content
                                   fn-lgk-frontier fn-lgk-inflight fn-lgk-last)))))

(defthm fn-ptd-apply-one-write
  (implies (and ino (equal p (list (list :write ino f w))))
           (equal (cdr (assoc-equal ino (car (fn-bs-apply-ops inodes dirs (fn-bs-ops-for-ino p ino)))))
                  (fn-bs-splice (cdr (assoc-equal ino inodes)) f w)))
  :hints (("Goal" :in-theory (e/d (fn-bs-apply-op fn-bs-apply-ops fn-bs-ops-for-ino) (fn-bs-splice)))))

(defthm fn-ptd-fence-file-of-one-write
  (implies (and ino (equal (fn-bs-pending s) (list (list :write ino f w))))
           (equal (fn-bs-durable-content (fn-bs-fence-file s ino) ino)
                  (fn-bs-splice (fn-bs-durable-content s ino) f w)))
  :hints (("Goal" :in-theory (e/d (fn-bs-fence-file fn-bs-durable-content) (fn-bs-splice fn-bs-apply-ops))
           :use ((:instance fn-ptd-apply-one-write (p (fn-bs-pending s))
                            (inodes (fn-bs-inodes s)) (dirs (fn-bs-dirs s)))))))

(defthm fn-ptd-fence-file-of-nothing
  (implies (not (consp (fn-bs-pending s)))
           (equal (fn-bs-durable-content (fn-bs-fence-file s ino) ino)
                  (fn-bs-durable-content s ino)))
  :hints (("Goal" :in-theory (enable fn-bs-fence-file fn-bs-durable-content))))

(defthm fn-ptd-fsync-keeps-the-durable-length
  (implies (fn-lgk-relp bs ks ino genesis max)
           (equal (len (fn-bs-durable-content (mv-nth 1 (fn-bs-fsync-file bs ino :ok)) ino))
                  (len (fn-bs-durable-content bs ino))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bs-fsync-file)
                           (fn-lgk-relp fn-bs-fence-file fn-lg-log fn-bs-splice fn-bs-durable-content))
           :use ((:instance fn-ptd-relp-pending-shape)
                 (:instance fn-ptd-fence-file-of-one-write
                            (s bs) (f (fn-lgk-frontier ks))
                            (w (fn-lg-log (fn-lgk-inflight ks) (fn-lgk-last ks) (fn-bs-unit bs))))
                 (:instance fn-ptd-fence-file-of-nothing (s bs))))))

(defthm fn-ptd-fence-step
  (implies (and (fn-lgk-relp bs ks ino genesis max)
                (equal (fn-lgk-phase ks) :appended))
           (let ((r (fn-lgu-host-step bs ks (list :fence o) ino max)))
             (and (equal (mv-nth 2 r) (if (equal o :ok) (fn-lgk-fence ks (fn-bs-unit bs))
                                        (fn-lgk-fence-failed ks)))
                  (implies (equal o :ok)
                           (and (fn-lgk-relp (mv-nth 1 r) (fn-lgk-fence ks (fn-bs-unit bs)) ino genesis max)
                                (equal (len (fn-bs-durable-content (mv-nth 1 r) ino))
                                       (len (fn-bs-durable-content bs ino)))
                                (equal (fn-bs-unit (mv-nth 1 r)) (fn-bs-unit bs)))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lgu-host-step)
                           (fn-lgk-relp fn-bs-fsync-file fn-lgk-fence fn-lgk-fence-failed
                            fn-bs-durable-content fn-lgk-phase))
           :use ((:instance fn-lgk-fence-preserves-relation)
                 (:instance fn-ptd-fsync-keeps-the-durable-length)))))

(defthm fn-ptd-fence-fields
  (let ((k2 (fn-lgk-fence ks unit)))
    (and (equal (fn-lgk-committed k2) (append (true-list-fix (fn-lgk-committed ks))
                                              (true-list-fix (fn-lgk-inflight ks))))
         (equal (fn-lgk-acked k2) (fn-lgk-acked ks))
         (equal (fn-lgk-batch k2) (fn-lgk-batch ks))
         (equal (fn-lgk-inflight k2) nil)))
  :hints (("Goal" :in-theory (enable fn-lgk-fence))))

(defthm fn-ptd-finish-one-fields
  (let ((k2 (fn-lgk-finish-one ks)))
    (and (equal (fn-lgk-committed k2) (fn-lgk-committed ks))
         (equal (fn-lgk-acked k2) (if (< (fn-lgk-acked ks) (len (fn-lgk-committed ks)))
                                      (+ 1 (fn-lgk-acked ks)) (fn-lgk-acked ks)))
         (equal (fn-lgk-batch k2) (fn-lgk-batch ks))
         (equal (fn-lgk-inflight k2) (fn-lgk-inflight ks))))
  :hints (("Goal" :in-theory (enable fn-lgk-finish-one))))

(defthm fn-ptd-append-fields
  (implies (fn-lg-append-admitsp ks unit extent)
           (let ((k2 (fn-lgk-append ks unit extent)))
             (and (equal (fn-lgk-committed k2) (fn-lgk-committed ks))
                  (equal (fn-lgk-acked k2) (fn-lgk-acked ks))
                  (equal (fn-lgk-batch k2) nil)
                  (equal (fn-lgk-inflight k2) (true-list-fix (fn-lgk-batch ks)))
                  (equal (fn-lgk-phase k2) :appended))))
  :hints (("Goal" :in-theory (enable fn-lgk-append fn-lg-append-admitsp))))

(defthm fn-ptd-invp-in-flight-facts
  (implies (and (fn-ptd-invp st bs ks ino genesis max)
                (member-equal (fn-ptd-ph st) '(:extending :extsyncing :writing)))
           (and (fn-lgk-relp bs ks ino genesis max)
                (not (consp (fn-lgk-inflight ks)))
                (equal (fn-lgk-batch ks) (list (fn-ptd-rec st)))
                (equal (fn-lgk-acked ks) (len (fn-lgk-committed ks)))
                (equal (fn-ptd-ext st) (len (fn-bs-durable-content bs ino)))
                (or (equal (fn-ptd-ph st) :writing) (not (equal (fn-ptd-nxt st) (fn-ptd-ext st))))
                (equal (fn-ptd-nxt st) (fn-lgk-sealed-extent ks (fn-ptd-ext st) (fn-bs-unit bs)))
                (fn-lg-append-admitsp ks (fn-bs-unit bs) (fn-ptd-nxt st))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-lgk-relp fn-lgk-sealed-extent fn-lg-append-admitsp))))

(defthm fn-ptd-invp-syncing-facts
  (implies (and (fn-ptd-invp st bs ks ino genesis max) (equal (fn-ptd-ph st) :syncing))
           (and (fn-lgk-relp bs ks ino genesis max)
                (equal (fn-lgk-phase ks) :appended)
                (equal (fn-lgk-inflight ks) (list (fn-ptd-rec st)))
                (not (consp (fn-lgk-batch ks)))
                (equal (fn-lgk-acked ks) (len (fn-lgk-committed ks)))
                (equal (fn-ptd-nxt st) (len (fn-bs-durable-content bs ino)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-lgk-relp))))

(defthm fn-ptd-invp-when-fenced
  (implies (and (equal (fn-ptd-ph st) :fenced) (equal (fn-ptd-ks st) ks)
                (<= (fn-lgk-acked ks) (len (fn-lgk-committed ks))))
           (fn-ptd-invp st bs ks ino genesis max)))

(defthm fn-ptd-invp-of-ready
  (implies (and (fn-lgk-relp bs ks ino genesis max)
                (not (consp (fn-lgk-batch ks))) (not (consp (fn-lgk-inflight ks)))
                (equal (fn-lgk-acked ks) (len (fn-lgk-committed ks)))
                (equal ext (len (fn-bs-durable-content bs ino))))
           (fn-ptd-invp (fn-ptd-mk :ready ks rec ext nxt) bs ks ino genesis max))
  :hints (("Goal" :in-theory (disable fn-lgk-relp))))

(defthm fn-ptd-invp-of-syncing
  (implies (and (fn-lgk-relp bs ks ino genesis max)
                (equal (fn-lgk-phase ks) :appended)
                (equal (fn-lgk-inflight ks) (list rec))
                (not (consp (fn-lgk-batch ks)))
                (equal (fn-lgk-acked ks) (len (fn-lgk-committed ks)))
                (equal nxt (len (fn-bs-durable-content bs ino))))
           (fn-ptd-invp (fn-ptd-mk :syncing ks rec ext nxt) bs ks ino genesis max))
  :hints (("Goal" :in-theory (disable fn-lgk-relp))))

(defthm fn-ptd-fence-failed-fields
  (let ((k2 (fn-lgk-fence-failed ks)))
    (and (equal (fn-lgk-committed k2) (fn-lgk-committed ks))
         (equal (fn-lgk-acked k2) (fn-lgk-acked ks))))
  :hints (("Goal" :in-theory (enable fn-lgk-fence-failed))))

(defmacro fn-ptd-complete-goal ()
  '(implies (and (fn-ptd-invp st bs ks ino genesis max)
                 (equal unit (fn-bs-unit bs)))
            (mv-let (st1 acts ans ops) (fn-ptd-complete st ev ino unit)
              (declare (ignore acts ans))
              (let ((f (fn-lgu-host-final bs ks ops ino max)))
                (fn-ptd-invp st1 (car f) (cdr f) ino genesis max)))))

(deftheory fn-ptd-closed
  '(fn-lgk-relp fn-lgk-sealed-extent fn-lg-append-admitsp fn-lgk-append fn-lgk-fence fn-lgk-fence-failed
    fn-lgk-finish-one fn-lgu-host-step fn-ptd-invp fn-ptd-mk fn-ptd-ph fn-ptd-ks fn-ptd-ext fn-ptd-nxt
    fn-ptd-rec fn-ptd-record-write fn-bs-durable-content fn-lgk-committed fn-lgk-acked fn-lgk-inflight
    fn-lgk-batch fn-lgk-phase fn-bs-zeros))

(defthm fn-ptd-complete-in-flight-keeps-the-invariant
  (implies (member-equal (fn-ptd-ph st) '(:extending :extsyncing :writing))
           (fn-ptd-complete-goal))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-ptd-complete fn-ptd-sealed) (set-difference-theories (current-theory :here) (theory 'fn-ptd-closed)))
           :use ((:instance fn-ptd-invp-in-flight-facts)
                 (:instance fn-ptd-seal-step (eo1 (if (equal (fn-ptd-ph st) :extending) (cdr ev) :ok))
                            (eo2 (if (equal (fn-ptd-ph st) :extsyncing) (cdr ev) :ok))
                            (o (if (equal (fn-ptd-ph st) :writing) (cdr ev) :ok)))
                 (:instance fn-ptd-append-fields (unit (fn-bs-unit bs)) (extent (fn-ptd-nxt st)))
                 (:instance fn-ptd-invp-of-in-flight (ph :extsyncing) (rec (fn-ptd-rec st))
                            (ext (fn-ptd-ext st)) (nxt (fn-ptd-nxt st)))
                 (:instance fn-ptd-invp-of-in-flight (ph :writing) (rec (fn-ptd-rec st))
                            (ext (fn-ptd-ext st)) (nxt (fn-ptd-nxt st)))
                 (:instance fn-ptd-invp-of-syncing
                            (bs (mv-nth 1 (fn-lgu-host-step bs ks (list :seal :ok :ok (cdr ev)) ino max)))
                            (ks (fn-lgk-append ks (fn-bs-unit bs) (fn-ptd-nxt st)))
                            (rec (fn-ptd-rec st)) (ext (fn-ptd-ext st)) (nxt (fn-ptd-nxt st)))))))

(defthm fn-lgk-relp-committed-true-listp
  (implies (fn-lgk-relp bs ks ino genesis max)
           (true-listp (fn-lgk-committed ks)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-lgk-relp fn-lgk-content-okp)
                                  (fn-lg-scan fn-lg-scan-last fn-lg-log fn-bs-take fn-lg-zerosp
                                   fn-lg-recordsp fn-frame-digestp fn-bs-durable-content)))))

(defthm fn-ptd-finish-one-is-a-kernel-op
  (and (fn-lgu-kernel-op-p '(:finish-one))
       (equal (fn-lgk-host-step ks '(:finish-one)) (fn-lgk-finish-one ks)))
  :hints (("Goal" :in-theory (enable fn-lgk-host-step))))

(defthm fn-ptd-complete-syncing-keeps-the-invariant
  (implies (equal (fn-ptd-ph st) :syncing)
           (fn-ptd-complete-goal))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-ptd-complete) (set-difference-theories (current-theory :here) (theory 'fn-ptd-closed)))
           :use ((:instance fn-ptd-invp-syncing-facts)
                 (:instance fn-ptd-fence-step (o (cdr ev)))
                 (:instance fn-ptd-fence-fields (unit (fn-bs-unit bs)))
                 (:instance fn-ptd-finish-one-fields (ks (fn-lgk-fence ks (fn-bs-unit bs))))
                 (:instance fn-lgu-host-step-of-a-kernel-op-export
                            (op '(:finish-one))
                            (bs (mv-nth 1 (fn-lgu-host-step bs ks '(:fence :ok) ino max)))
                            (ks (fn-lgk-fence ks (fn-bs-unit bs))))
                 (:instance fn-lgu-kernel-op-keeps-the-relation-export
                            (op '(:finish-one))
                            (bs (mv-nth 1 (fn-lgu-host-step bs ks '(:fence :ok) ino max)))
                            (ks (fn-lgk-fence ks (fn-bs-unit bs))))
                 (:instance fn-ptd-invp-of-ready
                            (bs (mv-nth 1 (fn-lgu-host-step bs ks '(:fence :ok) ino max)))
                            (ks (fn-lgk-finish-one (fn-lgk-fence ks (fn-bs-unit bs))))
                            (rec nil) (ext (fn-ptd-nxt st)) (nxt (fn-ptd-nxt st)))
                 (:instance fn-lgk-relp-committed-true-listp)))))

(defthm fn-ptd-complete-at-rest-keeps-the-invariant
  (implies (not (member-equal (fn-ptd-ph st) '(:extending :extsyncing :writing :syncing)))
           (fn-ptd-complete-goal))
  :hints (("Goal" :do-not-induct t :in-theory (union-theories '(fn-ptd-complete) (set-difference-theories (current-theory :here) (theory 'fn-ptd-closed))))))

(defthm fn-ptd-step-keeps-the-invariant
  (implies (and (fn-ptd-invp st bs ks ino genesis max)
                (equal unit (fn-bs-unit bs)))
           (mv-let (st1 acts ans ops) (fn-ptd-step st in ino unit max)
             (declare (ignore acts ans))
             (let ((f (fn-lgu-host-final bs ks ops ino max)))
               (fn-ptd-invp st1 (car f) (cdr f) ino genesis max))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-ptd-step member-equal) (theory 'minimal-theory))
           :use ((:instance fn-ptd-begin-keeps-the-invariant (r (cadr in)))
                 (:instance fn-ptd-complete-in-flight-keeps-the-invariant (ev in))
                 (:instance fn-ptd-complete-syncing-keeps-the-invariant (ev in))
                 (:instance fn-ptd-complete-at-rest-keeps-the-invariant (ev in))))))

(defun fn-ptd-run-ind (st bs ks ins ino unit max)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom ins) (list st bs ks)
    (mv-let (st1 a w ops) (fn-ptd-step st (car ins) ino unit max)
      (declare (ignore a w))
      (let ((f (fn-lgu-host-final bs ks ops ino max)))
        (fn-ptd-run-ind st1 (car f) (cdr f) (cdr ins) ino unit max)))))

(defthm fn-ptd-run-keeps-the-invariant
  (implies (and (fn-ptd-invp st bs ks ino genesis max)
                (equal unit (fn-bs-unit bs)))
           (mv-let (st1 acts ans ops) (fn-ptd-run st ins ino unit max)
             (declare (ignore acts ans))
             (let ((f (fn-lgu-host-final bs ks ops ino max)))
               (fn-ptd-invp st1 (car f) (cdr f) ino genesis max))))
  :hints (("Goal" :induct (fn-ptd-run-ind st bs ks ins ino unit max)
           :in-theory (disable fn-ptd-step fn-ptd-invp fn-lgu-host-final fn-ptd-invp-of-same fn-ptd-invp-at-ready fn-ptd-ks))
          ("Subgoal *1/2" :use ((:instance fn-ptd-step-keeps-the-invariant (in (car ins)))
                                (:instance fn-lgu-host-final-of-append-export
                                           (x (mv-nth 3 (fn-ptd-step st (car ins) ino unit max)))
                                           (y (mv-nth 3 (fn-ptd-run (mv-nth 0 (fn-ptd-step st (car ins) ino unit max))
                                                                    (cdr ins) ino unit max))))
                                (:instance fn-ptd-unit-of-host-final
                                           (ops (mv-nth 3 (fn-ptd-step st (car ins) ino unit max))))))))

; The kernel the open leaves: no batch, nothing in flight, every committed
; record acknowledged.  The open's kernel is one (fn-lgk-recover sets ACKED to
; the count it scanned): fn-ptd-open-kernelp-of-the-open.
(defun fn-ptd-open-kernelp (ks)
  (declare (xargs :guard t :verify-guards nil))
  (and (not (consp (fn-lgk-batch ks)))
       (not (consp (fn-lgk-inflight ks)))
       (equal (fn-lgk-acked ks) (len (fn-lgk-committed ks)))))

(local
 (defthm fn-ptd-open-kernelp-facts
  (implies (fn-ptd-open-kernelp ks)
           (and (not (consp (fn-lgk-batch ks)))
                (not (consp (fn-lgk-inflight ks)))
                (equal (fn-lgk-acked ks) (len (fn-lgk-committed ks)))))
  :rule-classes nil))

(defthm fn-ptd-open-kernelp-of-the-open
  (fn-ptd-open-kernelp (fn-lgt-recover c genesis unit max floor))
  :hints (("Goal" :in-theory (e/d (fn-lgt-recover fn-lgk-recover) (fn-lg-scan fn-lg-scan-last fn-lgt-next-after)))))

(defthm fn-ptd-init-invp
  (implies (and (fn-lgk-relp bs ks0 ino genesis max)
                (fn-ptd-open-kernelp ks0))
           (fn-ptd-invp (fn-ptd-init ks0 (len (fn-bs-durable-content bs ino))) bs ks0 ino genesis max))
  :hints (("Goal" :in-theory (disable fn-lgk-relp))))

(defthm fn-ptd-invp-gives-the-host-run
  (implies (fn-ptd-invp st bs ks ino genesis max)
           (and (equal (fn-ptd-ks st) ks)
                (implies (member-equal (fn-ptd-ph st) '(:ready :extending :extsyncing :writing))
                         (equal (fn-ptd-ext st) (len (fn-bs-durable-content bs ino))))
                (implies (member-equal (fn-ptd-ph st) '(:extending :extsyncing :writing))
                         (equal (fn-ptd-nxt st)
                                (fn-lgk-sealed-extent (fn-ptd-ks st) (fn-ptd-ext st) (fn-bs-unit bs))))
                (implies (equal (fn-ptd-ph st) :syncing)
                         (equal (fn-ptd-nxt st) (len (fn-bs-durable-content bs ino))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-lgk-relp fn-lgk-sealed-extent fn-lg-append-admitsp))))

(defthm fn-ptd-run-is-the-host-run
  (let* ((st0 (fn-ptd-init ks0 (len (fn-bs-durable-content bs ino)))))
    (implies (and (fn-lgk-relp bs ks0 ino genesis max) (fn-ptd-open-kernelp ks0))
             (mv-let (st acts ans ops) (fn-ptd-run st0 ins ino (fn-bs-unit bs) max)
               (declare (ignore acts ans))
               (let ((f (fn-lgu-host-final bs ks0 ops ino max)))
                 (and (equal (fn-ptd-ks st) (cdr f))
                      (implies (member-equal (fn-ptd-ph st) '(:ready :extending :extsyncing :writing))
                               (equal (fn-ptd-ext st) (len (fn-bs-durable-content (car f) ino))))
                      (implies (member-equal (fn-ptd-ph st) '(:extending :extsyncing :writing))
                               (equal (fn-ptd-nxt st)
                                      (fn-lgk-sealed-extent (fn-ptd-ks st) (fn-ptd-ext st)
                                                            (fn-bs-unit bs))))
                      (implies (equal (fn-ptd-ph st) :syncing)
                               (equal (fn-ptd-nxt st) (len (fn-bs-durable-content (car f) ino)))))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'minimal-theory)
           :use ((:instance fn-ptd-invp-gives-the-host-run
                            (st (mv-nth 0 (fn-ptd-run (fn-ptd-init ks0
                                                                   (len (fn-bs-durable-content bs ino)))
                                                      ins ino (fn-bs-unit bs) max)))
                            (bs (car (fn-lgu-host-final bs ks0
                                                        (mv-nth 3 (fn-ptd-run (fn-ptd-init ks0
                                                                                           (len (fn-bs-durable-content bs ino)))
                                                                              ins ino (fn-bs-unit bs) max))
                                                        ino max)))
                            (ks (cdr (fn-lgu-host-final bs ks0
                                                        (mv-nth 3 (fn-ptd-run (fn-ptd-init ks0
                                                                                           (len (fn-bs-durable-content bs ino)))
                                                                              ins ino (fn-bs-unit bs) max))
                                                        ino max))))
                 (:instance fn-ptd-unit-of-host-final
                            (ks ks0)
                            (ops (mv-nth 3 (fn-ptd-run (fn-ptd-init ks0
                                                                    (len (fn-bs-durable-content bs ino)))
                                                       ins ino (fn-bs-unit bs) max))))
                 (:instance fn-ptd-init-invp)
                 (:instance fn-ptd-run-keeps-the-invariant
                            (st (fn-ptd-init ks0
                                             (len (fn-bs-durable-content bs ino))))
                            (ks ks0)
                            (unit (fn-bs-unit bs)))))))

; -----------------------------------------------------------------------------
; The acknowledgements: each step answers :posted for exactly the records it acknowledges.

(defthm fn-ptd-host-step-of-finish-one
  (and (equal (mv-nth 2 (fn-lgu-host-step bs ks '(:finish-one) ino max)) (fn-lgk-finish-one ks))
       (equal (mv-nth 1 (fn-lgu-host-step bs ks '(:finish-one) ino max)) bs))
  :hints (("Goal" :in-theory (e/d (fn-lgu-host-step fn-lgu-kernel-op-p fn-lgk-host-step)
                                  (fn-lgk-finish-one)))))

(local
 (defthm fn-ptd-take-past-a-list-of-one
  (implies (and (true-listp c) (equal a (len c)))
           (and (equal (take (+ 1 a) (append c (list x))) (append c (list x)))
                (equal (nthcdr a (append c (list x))) (list x))
                (equal (take a (append c (list x))) c)))))

(local
 (defthm fn-ptd-take-of-append-at-len
  (implies (and (true-listp c) (equal a (len c)))
           (and (equal (take a (append c y)) c)
                (equal (nthcdr a (append c y)) y)))))

(local
 (defthm fn-ptd-take-of-len
  (implies (and (true-listp c) (equal a (len c)))
           (equal (take a c) c))))

(local
 (defthm fn-ptd-nthcdr-of-len
  (implies (and (true-listp c) (equal a (len c)))
           (equal (nthcdr a c) nil))))

(local
 (defthm fn-ptd-take-past-a-singleton
  (implies (and (true-listp c) (equal a (len c)) (consp y) (not (cdr y)))
           (equal (take (+ 1 a) (append c y)) (append c y)))))

(defmacro fn-ptd-ack-goal (form)
  `(implies (and (fn-ptd-invp st bs ks ino genesis max)
                 (equal unit (fn-bs-unit bs)))
            (mv-let (st1 acts ans ops) ,form
              (declare (ignore st1 acts))
              (let ((ks1 (cdr (fn-lgu-host-final bs ks ops ino max))))
                (and (equal (fn-ptd-posted ans)
                            (nthcdr (fn-lgk-acked ks) (take (fn-lgk-acked ks1) (fn-lgk-committed ks1))))
                     (<= (fn-lgk-acked ks) (fn-lgk-acked ks1))
                     (equal (take (fn-lgk-acked ks) (fn-lgk-committed ks1))
                            (take (fn-lgk-acked ks) (fn-lgk-committed ks))))))))

(local
 (defthm fn-ptd-nthcdr-of-take-same
  (implies (natp n) (equal (nthcdr n (take n x)) nil))))

(defthm fn-ptd-begin-acknowledges
  (fn-ptd-ack-goal (fn-ptd-begin st r ino unit max))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-ptd-begin)
                           (fn-lgk-host-step fn-lgk-sealed-extent fn-lg-append-admitsp fn-lgu-take-verdict
                            fn-lgk-relp fn-bs-zeros fn-lgk-append-octets fn-lgu-host-step fn-ptd-take-op
                            fn-lgk-committed fn-lgk-acked fn-lgk-inflight fn-lgk-batch fn-lgk-phase
                            fn-ptd-invp fn-ptd-mk fn-ptd-ph fn-ptd-ks fn-ptd-ext fn-ptd-nxt fn-ptd-rec
                            fn-ptd-record-write fn-bs-durable-content))
           :use ((:instance fn-lgu-host-step-of-a-kernel-op-export
                            (op (fn-ptd-take-op ks r unit)))
                 (:instance fn-ptd-take-fields)))))

(defthm fn-ptd-complete-in-flight-acknowledges
  (implies (member-equal (fn-ptd-ph st) '(:extending :extsyncing :writing))
           (fn-ptd-ack-goal (fn-ptd-complete st ev ino unit)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-ptd-complete fn-ptd-sealed) (set-difference-theories (current-theory :here) (theory 'fn-ptd-closed)))
           :use ((:instance fn-ptd-invp-in-flight-facts)
                 (:instance fn-ptd-seal-step (eo1 (if (equal (fn-ptd-ph st) :extending) (cdr ev) :ok))
                            (eo2 (if (equal (fn-ptd-ph st) :extsyncing) (cdr ev) :ok))
                            (o (if (equal (fn-ptd-ph st) :writing) (cdr ev) :ok)))
                 (:instance fn-ptd-append-fields (unit (fn-bs-unit bs)) (extent (fn-ptd-nxt st)))))))

(defthm fn-ptd-complete-syncing-acknowledges
  (implies (equal (fn-ptd-ph st) :syncing)
           (fn-ptd-ack-goal (fn-ptd-complete st ev ino unit)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-ptd-complete) (set-difference-theories (current-theory :here) (union-theories '(take nthcdr) (theory 'fn-ptd-closed))))
           :use ((:instance fn-ptd-invp-syncing-facts)
                 (:instance fn-ptd-fence-step (o (cdr ev)))
                 (:instance fn-ptd-fence-fields (unit (fn-bs-unit bs)))
                 (:instance fn-ptd-finish-one-fields (ks (fn-lgk-fence ks (fn-bs-unit bs))))
                 (:instance fn-lgu-host-step-of-a-kernel-op-export
                            (op '(:finish-one))
                            (bs (mv-nth 1 (fn-lgu-host-step bs ks '(:fence :ok) ino max)))
                            (ks (fn-lgk-fence ks (fn-bs-unit bs))))
                 (:instance fn-lgk-relp-committed-true-listp)))))

(defthm fn-ptd-complete-at-rest-acknowledges
  (implies (not (member-equal (fn-ptd-ph st) '(:extending :extsyncing :writing :syncing)))
           (fn-ptd-ack-goal (fn-ptd-complete st ev ino unit)))
  :hints (("Goal" :do-not-induct t :in-theory (union-theories '(fn-ptd-complete) (set-difference-theories (current-theory :here) (theory 'fn-ptd-closed))))))

(defthm fn-ptd-posted-of-append
  (equal (fn-ptd-posted (append a b)) (append (fn-ptd-posted a) (fn-ptd-posted b))))

(local
 (defthm fn-ptd-take-of-take
  (implies (and (natp a) (natp b) (<= a b))
           (equal (take a (take b x)) (take a x)))))

(defun fn-ptd-split-ind (a b c x)
  (declare (xargs :measure (nfix c)))
  (if (or (zp c) (zp b)) (list a x)
    (fn-ptd-split-ind (if (zp a) 0 (1- a)) (1- b) (1- c) (cdr x))))

(local
 (defthm fn-ptd-nthcdr-take-split
  (implies (and (natp a) (natp b) (natp c) (<= a b) (<= b c))
           (equal (append (nthcdr a (take b x)) (nthcdr b (take c x)))
                  (nthcdr a (take c x))))
  :hints (("Goal" :induct (fn-ptd-split-ind a b c x)))))

(defthm fn-ptd-step-acknowledges
  (fn-ptd-ack-goal (fn-ptd-step st in ino unit max))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-ptd-step member-equal) (theory 'minimal-theory))
           :use ((:instance fn-ptd-begin-acknowledges (r (cadr in)))
                 (:instance fn-ptd-complete-in-flight-acknowledges (ev in))
                 (:instance fn-ptd-complete-syncing-acknowledges (ev in))
                 (:instance fn-ptd-complete-at-rest-acknowledges (ev in))))))

(defthm fn-ptd-acked-natp
  (natp (fn-lgk-acked ks))
  :rule-classes :type-prescription)

(local
 (defthm fn-ptd-host-final-of-append
   (equal (fn-lgu-host-final bs ks (append x y) ino max)
          (let ((f (fn-lgu-host-final bs ks x ino max)))
            (fn-lgu-host-final (car f) (cdr f) y ino max)))
   :hints (("Goal" :use fn-lgu-host-final-of-append-export))))

(defthm fn-ptd-nthcdr-of-take-prefix
  (implies (and (natp n) (natp m) (<= n m) (equal (take m x) (take m y)))
           (equal (take n x) (take n y)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-ptd-take-of-take)
           :use ((:instance fn-ptd-take-of-take (a n) (b m) (x x))
                 (:instance fn-ptd-take-of-take (a n) (b m) (x y))))))

(defthm fn-ptd-acknowledged-slices-compose
  (implies (and (natp a) (natp a1) (natp a2)
                (<= a a1) (equal (take a c1) (take a c0))
                (<= a1 a2) (equal (take a1 c2) (take a1 c1)))
           (and (equal (append (nthcdr a (take a1 c1)) (nthcdr a1 (take a2 c2)))
                       (nthcdr a (take a2 c2)))
                (<= a a2)
                (equal (take a c2) (take a c0))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-ptd-take-of-take fn-ptd-nthcdr-take-split take nthcdr)
           :use ((:instance fn-ptd-take-of-take (b a1) (x c2))
                 (:instance fn-ptd-take-of-take (b a1) (x c1))
                 (:instance fn-ptd-nthcdr-take-split (b a1) (c a2) (x c2))
                 (:instance fn-ptd-nthcdr-of-take-prefix (n a) (m a1) (x c2) (y c1))))))

(defthm fn-ptd-run-acknowledges
  (fn-ptd-ack-goal (fn-ptd-run st ins ino unit max))
  :hints (("Goal" :induct (fn-ptd-run-ind st bs ks ins ino unit max)
           :in-theory (disable fn-ptd-step fn-ptd-invp fn-lgu-host-final fn-ptd-invp-of-same
                               fn-ptd-invp-at-ready fn-ptd-ks fn-lgk-acked fn-lgk-committed take nthcdr))
          ("Subgoal *1/2" :use ((:instance fn-ptd-step-acknowledges (in (car ins)))
                                (:instance fn-ptd-step-keeps-the-invariant (in (car ins)))
                                (:instance fn-ptd-unit-of-host-final
                                           (ops (mv-nth 3 (fn-ptd-step st (car ins) ino unit max))))
                                (:instance fn-ptd-acknowledged-slices-compose
                                           (a (fn-lgk-acked ks)) (c0 (fn-lgk-committed ks))
                                           (a1 (fn-lgk-acked (cdr (fn-lgu-host-final bs ks (mv-nth 3 (fn-ptd-step st (car ins) ino unit max)) ino max))))
                                           (c1 (fn-lgk-committed (cdr (fn-lgu-host-final bs ks (mv-nth 3 (fn-ptd-step st (car ins) ino unit max)) ino max))))
                                           (a2 (fn-lgk-acked (cdr (fn-lgu-host-final bs ks (append (mv-nth 3 (fn-ptd-step st (car ins) ino unit max))
                                                                                                  (mv-nth 3 (fn-ptd-run (mv-nth 0 (fn-ptd-step st (car ins) ino unit max)) (cdr ins) ino unit max)))
                                                                                         ino max))))
                                           (c2 (fn-lgk-committed (cdr (fn-lgu-host-final bs ks (append (mv-nth 3 (fn-ptd-step st (car ins) ino unit max))
                                                                                                      (mv-nth 3 (fn-ptd-run (mv-nth 0 (fn-ptd-step st (car ins) ino unit max)) (cdr ins) ino unit max)))
                                                                                             ino max))))))))
  :otf-flg t)

; -----------------------------------------------------------------------------
; No host operation loses an acknowledgement, at any cut.

; Monotonicity: no host operation of the run loses an acknowledgement.
(defun fn-ptd-keeps-acked-p (ks ks2)
  (declare (xargs :guard t :verify-guards nil))
  (and (<= (fn-lgk-acked ks) (fn-lgk-acked ks2))
       (equal (take (fn-lgk-acked ks) (fn-lgk-committed ks2))
              (take (fn-lgk-acked ks) (fn-lgk-committed ks)))
       (<= (fn-lgk-acked ks2) (len (fn-lgk-committed ks2)))))

(defthm fn-ptd-keeps-acked-p-transitive
  (implies (and (fn-ptd-keeps-acked-p k1 k2) (fn-ptd-keeps-acked-p k2 k3))
           (fn-ptd-keeps-acked-p k1 k3))
  :hints (("Goal" :in-theory (disable take)
           :use ((:instance fn-ptd-nthcdr-of-take-prefix
                            (n (fn-lgk-acked k1)) (m (fn-lgk-acked k2))
                            (x (fn-lgk-committed k3)) (y (fn-lgk-committed k2)))))))

(local
 (defthm fn-ptd-keeps-acked-p-reflexive
  (implies (<= (fn-lgk-acked ks) (len (fn-lgk-committed ks)))
           (fn-ptd-keeps-acked-p ks ks))))

(local
 (defthm fn-ptd-take-of-append-within
  (implies (<= (nfix a) (len c))
           (equal (take a (append (true-list-fix c) x)) (take a c)))))

(local
 (defthm fn-ptd-take-of-append-within-plain
  (implies (<= (nfix a) (len c))
           (equal (take a (append c x)) (take a c)))))

(defthm fn-ptd-kernel-ops-keep-acked
  (implies (<= (fn-lgk-acked ks) (len (fn-lgk-committed ks)))
           (and (fn-ptd-keeps-acked-p ks (fn-lgk-append ks unit extent))
                (fn-ptd-keeps-acked-p ks (fn-lgk-fence ks unit))
                (fn-ptd-keeps-acked-p ks (fn-lgk-fence-failed ks))
                (implies (fn-lgu-kernel-op-p op)
                         (fn-ptd-keeps-acked-p ks (fn-lgk-host-step ks op)))))
  :hints (("Goal" :in-theory (e/d (fn-lgk-host-step fn-lgu-kernel-op-p fn-lgt-prepare fn-lgk-prepare
                                   fn-olr-take fn-olr-consume-to fn-lgk-finish-one fn-lgk-fence-failed
                                   fn-lgk-append fn-lgk-fence)
                                  (take fn-lg-log fn-lgk-fitsp fn-lgt-txid fn-olr-entry-octets
                                   fn-lg-last-trailer)))))

(defun fn-ptd-all-keep (ks pairs)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom pairs) t
    (and (fn-ptd-keeps-acked-p ks (cdr (car pairs)))
         (fn-ptd-all-keep ks (cdr pairs)))))

(defthm fn-ptd-all-keep-of-append
  (equal (fn-ptd-all-keep ks (append a b))
         (and (fn-ptd-all-keep ks a) (fn-ptd-all-keep ks b))))

(defthm fn-ptd-extend-pairs-keep
  (implies (fn-ptd-keeps-acked-p ks k)
           (fn-ptd-all-keep ks (mv-nth 0 (fn-lgu-extend bs k ino extent next eo1 eo2))))
  :hints (("Goal" :in-theory (e/d (fn-lgu-extend) (fn-bs-write fn-bs-fsync-file fn-bs-zeros fn-ptd-keeps-acked-p)))))

(defthm fn-ptd-fence-failed-append-keeps-acked
  (implies (<= (fn-lgk-acked ks) (len (fn-lgk-committed ks)))
           (fn-ptd-keeps-acked-p ks (fn-lgk-fence-failed (fn-lgk-append ks unit extent))))
  :hints (("Goal" :in-theory (e/d (fn-lgk-fence-failed fn-lgk-append) (take fn-lgk-fitsp fn-lg-log)))))

(defthm fn-ptd-host-step-keeps-acked
  (implies (<= (fn-lgk-acked ks) (len (fn-lgk-committed ks)))
           (mv-let (pairs bs1 ks1) (fn-lgu-host-step bs ks op ino max)
             (declare (ignore bs1))
             (and (fn-ptd-all-keep ks pairs)
                  (fn-ptd-keeps-acked-p ks ks1))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lgu-host-step)
                           (fn-ptd-keeps-acked-p fn-lgu-extend fn-bs-write fn-bs-fsync-file fn-lgk-append
                            fn-lgk-fence fn-lgk-fence-failed fn-lgk-host-step fn-lgk-sealed-extent
                            fn-lg-append-admitsp fn-lgk-append-octets fn-lgu-take-verdict fn-lgu-kernel-op-p
                            fn-bs-durable-content fn-lgk-frontier fn-lgk-phase fn-bs-zeros))
           :use ((:instance fn-ptd-kernel-ops-keep-acked (unit (fn-bs-unit bs))
                            (extent (fn-lgk-sealed-extent ks (len (fn-bs-durable-content bs ino)) (fn-bs-unit bs))))
                 (:instance fn-ptd-kernel-ops-keep-acked
                            (ks (fn-lgk-append ks (fn-bs-unit bs)
                                               (fn-lgk-sealed-extent ks (len (fn-bs-durable-content bs ino)) (fn-bs-unit bs)))))
                 (:instance fn-ptd-keeps-acked-p-transitive
                            (k1 ks)
                            (k2 (fn-lgk-append ks (fn-bs-unit bs)
                                               (fn-lgk-sealed-extent ks (len (fn-bs-durable-content bs ino)) (fn-bs-unit bs))))
                            (k3 (fn-lgk-fence-failed
                                 (fn-lgk-append ks (fn-bs-unit bs)
                                                (fn-lgk-sealed-extent ks (len (fn-bs-durable-content bs ino)) (fn-bs-unit bs))))))
                 (:instance fn-ptd-keeps-acked-p-reflexive)
                 (:instance fn-ptd-extend-pairs-keep
                            (k (fn-lgk-append ks (fn-bs-unit bs)
                                              (fn-lgk-sealed-extent ks (len (fn-bs-durable-content bs ino)) (fn-bs-unit bs))))
                            (extent (len (fn-bs-durable-content bs ino)))
                            (next (fn-lgk-sealed-extent ks (len (fn-bs-durable-content bs ino)) (fn-bs-unit bs)))
                            (eo1 (nth 1 op)) (eo2 (nth 2 op)))))))

(defthm fn-ptd-keeps-acked-bounds
  (implies (fn-ptd-keeps-acked-p ks ks2)
           (<= (fn-lgk-acked ks2) (len (fn-lgk-committed ks2))))
  :rule-classes :forward-chaining)

(defthm fn-ptd-all-keep-transitive
  (implies (and (fn-ptd-keeps-acked-p k1 k2) (fn-ptd-all-keep k2 pairs))
           (fn-ptd-all-keep k1 pairs))
  :hints (("Goal" :induct (fn-ptd-all-keep k2 pairs) :in-theory (disable fn-ptd-keeps-acked-p))))

(defthm fn-ptd-host-step-keeps-acked-split
  (implies (<= (fn-lgk-acked ks) (len (fn-lgk-committed ks)))
           (and (fn-ptd-all-keep ks (mv-nth 0 (fn-lgu-host-step bs ks op ino max)))
                (fn-ptd-keeps-acked-p ks (mv-nth 2 (fn-lgu-host-step bs ks op ino max)))
                (<= (fn-lgk-acked (mv-nth 2 (fn-lgu-host-step bs ks op ino max)))
                    (len (fn-lgk-committed (mv-nth 2 (fn-lgu-host-step bs ks op ino max)))))))
  :rule-classes nil
  :hints (("Goal" :use fn-ptd-host-step-keeps-acked :in-theory (disable fn-lgu-host-step))))

(defthm fn-ptd-host-run-keeps-acked
  (implies (<= (fn-lgk-acked ks) (len (fn-lgk-committed ks)))
           (fn-ptd-all-keep ks (fn-lgu-host-run bs ks ops ino max)))
  :hints (("Goal" :induct (fn-lgu-host-run bs ks ops ino max)
           :in-theory (disable fn-lgu-host-step fn-ptd-keeps-acked-p fn-lgk-acked fn-lgk-committed))
          ("Subgoal *1/2" :use ((:instance fn-ptd-host-step-keeps-acked-split (op (car ops)))
                                (:instance fn-ptd-keeps-acked-p-reflexive)
                                (:instance fn-ptd-all-keep-transitive
                                           (k1 ks) (k2 (mv-nth 2 (fn-lgu-host-step bs ks (car ops) ino max)))
                                           (pairs (fn-lgu-host-run (mv-nth 1 (fn-lgu-host-step bs ks (car ops) ino max))
                                                                   (mv-nth 2 (fn-lgu-host-step bs ks (car ops) ino max))
                                                                   (cdr ops) ino max)))))))

; -----------------------------------------------------------------------------
; P4-3 and the keystone.

(local
 (defthm fn-ptd-len-nthcdr
  (equal (len (nthcdr n x)) (nfix (- (len x) (nfix n))))))

(local
 (defthm fn-ptd-member-of-append
  (iff (member-equal p (append a b)) (or (member-equal p a) (member-equal p b)))))

(local
 (defthm fn-ptd-len-take
  (equal (len (take n x)) (nfix n))))

(local
 (defthm fn-ptd-len-nthcdr-take
  (implies (and (natp a) (natp b) (<= a b))
           (equal (len (nthcdr a (take b x))) (- b a)))))

(defun fn-ptd-two-ind (a b y)
  (declare (xargs :measure (nfix a)))
  (if (zp a) (list b y) (fn-ptd-two-ind (1- a) (1- b) (cdr y))))

(local
 (defthm fn-ptd-take-nthcdr-is-nthcdr-take
  (implies (and (natp a) (natp b) (<= a b))
           (equal (take (- b a) (nthcdr a y)) (nthcdr a (take b y))))
  :hints (("Goal" :induct (fn-ptd-two-ind a b y)))))

(defthm fn-ptd-recovered-slice
  (implies (and (natp a0) (natp a1) (natp ap)
                (<= a0 a1) (<= a1 ap) (<= ap (len rec))
                (equal (take ap rec) (take ap cp))
                (equal (take a1 cp) (take a1 c1))
                (equal (take a0 c1) (take a0 c0)))
           (let ((p (nthcdr a0 (take a1 c1))))
             (and (<= (+ a0 (len p)) (len rec))
                  (equal (take a0 rec) (take a0 c0))
                  (equal (take (len p) (nthcdr a0 rec)) p))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable take nthcdr fn-ptd-take-of-take fn-ptd-take-nthcdr-is-nthcdr-take)
           :use ((:instance fn-ptd-take-of-take (a a0) (b ap) (x rec))
                 (:instance fn-ptd-take-of-take (a a0) (b ap) (x cp))
                 (:instance fn-ptd-take-of-take (a a1) (b ap) (x rec))
                 (:instance fn-ptd-take-of-take (a a1) (b ap) (x cp))
                 (:instance fn-ptd-take-of-take (a a0) (b a1) (x cp))
                 (:instance fn-ptd-take-of-take (a a0) (b a1) (x c1))
                 (:instance fn-ptd-take-nthcdr-is-nthcdr-take (a a0) (b a1) (y rec))))))

(defthm fn-ptd-all-keep-member
  (implies (and (fn-ptd-all-keep k pairs) (member-equal p pairs))
           (fn-ptd-keeps-acked-p k (cdr p)))
  :hints (("Goal" :in-theory (disable fn-ptd-keeps-acked-p))))

(defun fn-ptd-final-ind (bs ks x ino max)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom x) (list bs ks)
    (mv-let (pairs bs1 ks1) (fn-lgu-host-step bs ks (car x) ino max)
      (declare (ignore pairs))
      (fn-ptd-final-ind bs1 ks1 (cdr x) ino max))))

(defthm fn-ptd-later-cuts-are-cuts
  (implies (member-equal p (fn-lgu-host-run (car (fn-lgu-host-final bs ks x ino max))
                                            (cdr (fn-lgu-host-final bs ks x ino max)) y ino max))
           (member-equal p (fn-lgu-host-run bs ks (append x y) ino max)))
  :hints (("Goal" :induct (fn-ptd-final-ind bs ks x ino max)
           :in-theory (disable fn-lgu-host-step))))

(defun fn-ptd-all-unit (u pairs)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom pairs) t
    (and (equal (fn-bs-unit (car (car pairs))) u) (fn-ptd-all-unit u (cdr pairs)))))

(defthm fn-ptd-all-unit-of-append
  (equal (fn-ptd-all-unit u (append a b)) (and (fn-ptd-all-unit u a) (fn-ptd-all-unit u b))))

(defthm fn-ptd-all-unit-member
  (implies (and (fn-ptd-all-unit u pairs) (member-equal p pairs))
           (equal (fn-bs-unit (car p)) u)))

(defthm fn-ptd-extend-pairs-unit-car
  (fn-ptd-all-unit (fn-bs-unit bs) (car (fn-lgu-extend bs k ino extent next eo1 eo2)))
  :hints (("Goal" :in-theory (e/d (fn-lgu-extend) (fn-bs-write fn-bs-fsync-file fn-bs-zeros)))))

(defthm fn-ptd-host-step-pairs-unit
  (fn-ptd-all-unit (fn-bs-unit bs) (mv-nth 0 (fn-lgu-host-step bs ks op ino max)))
  :hints (("Goal" :in-theory (e/d (fn-lgu-host-step)
                                  (fn-lgu-extend fn-bs-write fn-bs-fsync-file fn-lgk-append fn-lgk-fence
                                   fn-lgk-fence-failed fn-lgk-host-step fn-lgk-sealed-extent
                                   fn-lg-append-admitsp fn-lgk-append-octets fn-lgu-take-verdict
                                   fn-lgu-kernel-op-p fn-bs-durable-content fn-lgk-frontier fn-lgk-phase
                                   fn-bs-zeros)))))

(defthm fn-ptd-host-step-pairs-unit-car
  (fn-ptd-all-unit (fn-bs-unit bs) (car (fn-lgu-host-step bs ks op ino max)))
  :hints (("Goal" :use fn-ptd-host-step-pairs-unit :in-theory (e/d (mv-nth) (fn-ptd-host-step-pairs-unit fn-lgu-host-step)))))

(defthm fn-ptd-host-run-pairs-unit
  (fn-ptd-all-unit (fn-bs-unit bs) (fn-lgu-host-run bs ks ops ino max))
  :hints (("Goal" :induct (fn-lgu-host-run bs ks ops ino max)
           :in-theory (disable fn-lgu-host-step))))

(defthm fn-ptd-posted-are-the-acknowledged
  (let* ((st0 (fn-ptd-init ks0 (len (fn-bs-durable-content bs ino)))))
    (implies (and (fn-lgk-relp bs ks0 ino genesis max) (fn-ptd-open-kernelp ks0))
             (mv-let (st acts ans ops) (fn-ptd-run st0 ins ino (fn-bs-unit bs) max)
               (declare (ignore acts ops))
               (let ((ks (fn-ptd-ks st)))
                 (equal (fn-ptd-posted ans)
                        (nthcdr (fn-lgk-acked ks0)
                                (take (fn-lgk-acked ks) (fn-lgk-committed ks))))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'minimal-theory)
           :use ((:instance fn-ptd-init-invp)
                 (:instance fn-ptd-run-acknowledges
                            (st (fn-ptd-init ks0
                                             (len (fn-bs-durable-content bs ino))))
                            (ks ks0)
                            (unit (fn-bs-unit bs)))
                 (:instance fn-ptd-run-is-the-host-run)))))

(local
 (defthm fn-ptd-posted-records-are-recovered-at-every-later-cut-nested
  (let* ((unit (fn-bs-unit bs))
         (st0 (fn-ptd-init ks0 (len (fn-bs-durable-content bs ino)))))
    (implies (and (fn-lgk-relp bs ks0 ino genesis max) (fn-ptd-open-kernelp ks0))
             (mv-let (st1 acts1 ans1 ops1) (fn-ptd-run st0 e1 ino unit max)
               (declare (ignore acts1))
               (mv-let (st2 acts2 ans2 ops2) (fn-ptd-run st1 e2 ino unit max)
                 (declare (ignore st2 acts2 ans2))
                 (let* ((f1 (fn-lgu-host-final bs ks0 ops1 ino max))
                        (p (fn-ptd-posted ans1))
                        (a0 (fn-lgk-acked ks0)))
                   (implies (and (member-equal pair (fn-lgu-host-run (car f1) (cdr f1) ops2 ino max))
                                 (fn-bs-crash-imagep (car pair) image))
                            (let ((recovered (fn-lgk-committed
                                              (fn-lgk-recover (fn-bs-durable-content image ino)
                                                              genesis unit max next-txid))))
                              (and (<= (+ a0 (len p)) (len recovered))
                                   (equal (take a0 recovered) (take a0 (fn-lgk-committed ks0)))
                                   (equal (take (len p) (nthcdr a0 recovered)) p)))))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-ptd-keeps-acked-p fn-ptd-acked-natp natp)
                                      (theory 'minimal-theory))
           :use ((:instance fn-ptd-init-invp)
                 (:instance fn-ptd-run-acknowledges
                            (st (fn-ptd-init ks0
                                             (len (fn-bs-durable-content bs ino))))
                            (ks ks0)
                            (ins e1) (unit (fn-bs-unit bs)))
                 (:instance fn-ptd-open-kernelp-facts (ks ks0))
                 (:instance fn-ptd-host-run-keeps-acked
                            (ks ks0)
                            (ops (mv-nth 3 (fn-ptd-run (fn-ptd-init ks0
                                                                    (len (fn-bs-durable-content bs ino)))
                                                       e1 ino (fn-bs-unit bs) max))))
                 (:instance fn-lgu-host-final-is-a-cut-export
                            (ks ks0)
                            (ops (mv-nth 3 (fn-ptd-run (fn-ptd-init ks0
                                                                    (len (fn-bs-durable-content bs ino)))
                                                       e1 ino (fn-bs-unit bs) max))))
                 (:instance fn-ptd-all-keep-member
                            (k ks0)
                            (pairs (fn-lgu-host-run bs ks0
                                                    (mv-nth 3 (fn-ptd-run (fn-ptd-init ks0
                                                                                       (len (fn-bs-durable-content bs ino)))
                                                                          e1 ino (fn-bs-unit bs) max))
                                                    ino max))
                            (p (fn-lgu-host-final bs ks0
                                                  (mv-nth 3 (fn-ptd-run (fn-ptd-init ks0
                                                                                     (len (fn-bs-durable-content bs ino)))
                                                                        e1 ino (fn-bs-unit bs) max))
                                                  ino max)))
                 (:instance fn-ptd-host-run-keeps-acked
                            (bs (car (fn-lgu-host-final bs ks0 (mv-nth 3 (fn-ptd-run (fn-ptd-init ks0 (len (fn-bs-durable-content bs ino))) e1 ino (fn-bs-unit bs) max)) ino max)))
                            (ks (cdr (fn-lgu-host-final bs ks0 (mv-nth 3 (fn-ptd-run (fn-ptd-init ks0 (len (fn-bs-durable-content bs ino))) e1 ino (fn-bs-unit bs) max)) ino max)))
                            (ops (mv-nth 3 (fn-ptd-run (mv-nth 0 (fn-ptd-run (fn-ptd-init ks0 (len (fn-bs-durable-content bs ino))) e1 ino (fn-bs-unit bs) max)) e2 ino (fn-bs-unit bs) max))))
                 (:instance fn-ptd-all-keep-member
                            (k (cdr (fn-lgu-host-final bs ks0 (mv-nth 3 (fn-ptd-run (fn-ptd-init ks0 (len (fn-bs-durable-content bs ino))) e1 ino (fn-bs-unit bs) max)) ino max)))
                            (pairs (fn-lgu-host-run (car (fn-lgu-host-final bs ks0 (mv-nth 3 (fn-ptd-run (fn-ptd-init ks0 (len (fn-bs-durable-content bs ino))) e1 ino (fn-bs-unit bs) max)) ino max)) (cdr (fn-lgu-host-final bs ks0 (mv-nth 3 (fn-ptd-run (fn-ptd-init ks0 (len (fn-bs-durable-content bs ino))) e1 ino (fn-bs-unit bs) max)) ino max)) (mv-nth 3 (fn-ptd-run (mv-nth 0 (fn-ptd-run (fn-ptd-init ks0 (len (fn-bs-durable-content bs ino))) e1 ino (fn-bs-unit bs) max)) e2 ino (fn-bs-unit bs) max)) ino max))
                            (p pair))
                 (:instance fn-ptd-later-cuts-are-cuts
                            (p pair)
                            (ks ks0)
                            (x (mv-nth 3 (fn-ptd-run (fn-ptd-init ks0 (len (fn-bs-durable-content bs ino))) e1 ino (fn-bs-unit bs) max))) (y (mv-nth 3 (fn-ptd-run (mv-nth 0 (fn-ptd-run (fn-ptd-init ks0 (len (fn-bs-durable-content bs ino))) e1 ino (fn-bs-unit bs) max)) e2 ino (fn-bs-unit bs) max))))
                 (:instance fn-ptd-host-run-pairs-unit
                            (bs (car (fn-lgu-host-final bs ks0 (mv-nth 3 (fn-ptd-run (fn-ptd-init ks0 (len (fn-bs-durable-content bs ino))) e1 ino (fn-bs-unit bs) max)) ino max))) (ks (cdr (fn-lgu-host-final bs ks0 (mv-nth 3 (fn-ptd-run (fn-ptd-init ks0 (len (fn-bs-durable-content bs ino))) e1 ino (fn-bs-unit bs) max)) ino max))) (ops (mv-nth 3 (fn-ptd-run (mv-nth 0 (fn-ptd-run (fn-ptd-init ks0 (len (fn-bs-durable-content bs ino))) e1 ino (fn-bs-unit bs) max)) e2 ino (fn-bs-unit bs) max))))
                 (:instance fn-ptd-all-unit-member
                            (u (fn-bs-unit (car (fn-lgu-host-final bs ks0 (mv-nth 3 (fn-ptd-run (fn-ptd-init ks0 (len (fn-bs-durable-content bs ino))) e1 ino (fn-bs-unit bs) max)) ino max))))
                            (pairs (fn-lgu-host-run (car (fn-lgu-host-final bs ks0 (mv-nth 3 (fn-ptd-run (fn-ptd-init ks0 (len (fn-bs-durable-content bs ino))) e1 ino (fn-bs-unit bs) max)) ino max)) (cdr (fn-lgu-host-final bs ks0 (mv-nth 3 (fn-ptd-run (fn-ptd-init ks0 (len (fn-bs-durable-content bs ino))) e1 ino (fn-bs-unit bs) max)) ino max)) (mv-nth 3 (fn-ptd-run (mv-nth 0 (fn-ptd-run (fn-ptd-init ks0 (len (fn-bs-durable-content bs ino))) e1 ino (fn-bs-unit bs) max)) e2 ino (fn-bs-unit bs) max)) ino max))
                            (p pair))
                 (:instance fn-ptd-unit-of-host-final
                            (ks ks0)
                            (ops (mv-nth 3 (fn-ptd-run (fn-ptd-init ks0 (len (fn-bs-durable-content bs ino))) e1 ino (fn-bs-unit bs) max))))
                 (:instance fn-lgu-acknowledged-records-are-recovered-at-every-cut
                            (ks ks0)
                            (ops (append (mv-nth 3 (fn-ptd-run (fn-ptd-init ks0 (len (fn-bs-durable-content bs ino))) e1 ino (fn-bs-unit bs) max)) (mv-nth 3 (fn-ptd-run (mv-nth 0 (fn-ptd-run (fn-ptd-init ks0 (len (fn-bs-durable-content bs ino))) e1 ino (fn-bs-unit bs) max)) e2 ino (fn-bs-unit bs) max)))))
                 (:instance fn-ptd-recovered-slice
                            (a0 (fn-lgk-acked ks0))
                            (c0 (fn-lgk-committed ks0))
                            (a1 (fn-lgk-acked (cdr (fn-lgu-host-final bs ks0 (mv-nth 3 (fn-ptd-run (fn-ptd-init ks0 (len (fn-bs-durable-content bs ino))) e1 ino (fn-bs-unit bs) max)) ino max))))
                            (c1 (fn-lgk-committed (cdr (fn-lgu-host-final bs ks0 (mv-nth 3 (fn-ptd-run (fn-ptd-init ks0 (len (fn-bs-durable-content bs ino))) e1 ino (fn-bs-unit bs) max)) ino max))))
                            (ap (fn-lgk-acked (cdr pair)))
                            (cp (fn-lgk-committed (cdr pair)))
                            (rec (fn-lgk-committed
                                  (fn-lgk-recover (fn-bs-durable-content image ino)
                                                  genesis (fn-bs-unit bs) max next-txid)))))))))

; KEYSTONE (P4: AckEligible => DurableCommitEvidence => recovered).  From the
; open (KS0 the kernel of what it read, R-related to BS, the driver at the
; segment's extent), inputs E1 then E2: every record the driver answered
; :posted during E1 is recovered, in answer order right after the open's
; acknowledged records, from every admissible crash image of every cut of the
; host run of E2's operations (each operation's intermediate stores
; included); the open's records stay recovered first.  In-flight actions at a
; crash are covered by the continuations E2 that complete them with their
; at-issue outcomes.  Scope: one segment, no rotation, a batch of one.
(defthm fn-ptd-posted-records-are-recovered-at-every-later-cut
  (let* ((unit (fn-bs-unit bs))
         (r1 (fn-ptd-run (fn-ptd-init ks0 (len (fn-bs-durable-content bs ino))) e1 ino unit max))
         (r2 (fn-ptd-run (mv-nth 0 r1) e2 ino unit max))
         (f1 (fn-lgu-host-final bs ks0 (mv-nth 3 r1) ino max))
         (p (fn-ptd-posted (mv-nth 2 r1)))
         (a0 (fn-lgk-acked ks0))
         (recovered (fn-lgk-committed (fn-lgk-recover (fn-bs-durable-content image ino)
                                                      genesis unit max next-txid))))
    (implies (and (fn-lgk-relp bs ks0 ino genesis max)
                  (fn-ptd-open-kernelp ks0)
                  (member-equal pair (fn-lgu-host-run (car f1) (cdr f1) (mv-nth 3 r2) ino max))
                  (fn-bs-crash-imagep (car pair) image))
             (and (<= (+ a0 (len p)) (len recovered))
                  (equal (take a0 recovered) (take a0 (fn-lgk-committed ks0)))
                  (equal (take (len p) (nthcdr a0 recovered)) p))))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use fn-ptd-posted-records-are-recovered-at-every-later-cut-nested)))

