; Not a book: the next layers of books/commit-proof-theory.lisp, being admitted
; form by form in a session over it (see the lane's continue file). Move each
; group into the book once it is admitted.
(defthm fn2-cpt-lm-step-acknowledge
 (implies (and (fn2-lm-state-valid s) (fn2-lm-event-allowedp event s)
               (equal (fn2-lm-event-tag event) :acknowledge))
          (member-equal (fn2-lm-event-argument event)
                        (fn2-lm-state-acknowledged (fn2-lm-step event s))))
 :hints (("Goal" :in-theory (disable fn2-lm-step fn2-lm-event-allowedp fn2-lm-state-valid
                                     fn2-lm-event-tag fn2-lm-event-argument fn2-lm-state-acknowledged
                                     update-fn2-lm-state-acknowledged))))

(defthm fn2-cpt-emit-ok
 (implies (and (fn2-cpt-hs-okp s) (true-listp (nth 7 s)))
          (and (fn2-cpt-hs-okp (mv-nth 1 (fn2-history-emit event s)))
               (true-listp (nth 7 (mv-nth 1 (fn2-history-emit event s))))))
 :hints (("Goal" :in-theory (e/d (fn2-history-emit) (fn2-lm-event-allowedp fn2-lm-step)))))
(defthm fn2-cpt-emit-acked
 (subsetp-equal (fn2-cpt-hs-acked s) (fn2-cpt-hs-acked (mv-nth 1 (fn2-history-emit event s))))
 :hints (("Goal" :in-theory (e/d (fn2-history-emit fn2-cpt-hs-acked)
                                 (fn2-lm-event-allowedp fn2-lm-step fn2-lm-state-acknowledged)))))
(in-theory (disable fn2-history-emit))

(defthm fn2-cpt-hs-okp-update-nth
 (implies (and (natp i) (not (equal i 6)) (not (equal i 7)))
          (equal (fn2-cpt-hs-okp (update-nth i v s)) (fn2-cpt-hs-okp s))))
(defthm fn2-cpt-hs-acked-update-nth
 (implies (and (natp i) (not (equal i 6)))
          (equal (fn2-cpt-hs-acked (update-nth i v s)) (fn2-cpt-hs-acked s))))
(defthm fn2-cpt-nth-cons-const
 (implies (and (syntaxp (quotep n)) (posp n)) (equal (nth n (cons a l)) (nth (- n 1) l))))
(defthm fn2-cpt-nth-cdr-const
 (implies (and (syntaxp (quotep n)) (natp n)) (equal (nth n (cdr s)) (nth (+ 1 n) s))))
(defthm fn2-cpt-hs-okp-cons-cdr
 (equal (fn2-cpt-hs-okp (cons v (cdr s))) (fn2-cpt-hs-okp s)))
(defthm fn2-cpt-hs-acked-cons-cdr
 (equal (fn2-cpt-hs-acked (cons v (cdr s))) (fn2-cpt-hs-acked s)))
(defthm fn2-cpt-hs-okp-consp
 (implies (fn2-cpt-hs-okp s) (consp s))
 :rule-classes :forward-chaining)
(in-theory (disable fn2-cpt-hs-okp fn2-cpt-hs-acked))

;; Every HISTORY state, row and operation reader is an nth; with update-nth
;; closed, the frame of each update is the built-in nth-update-nth.
(defun fn2-cpt-nth-rules (readers i)
 (declare (xargs :mode :program))
 (if (endp readers) nil
  (cons `(defthm ,(packn (list (car readers) '-cpt-nth))
           (equal (,(car readers) x) (nth ,i x))
           :hints (("Goal" :in-theory (enable ,(car readers)))))
        (fn2-cpt-nth-rules (cdr readers) (+ 1 i)))))
(defmacro fn2-cpt-readers-nth (&rest readers)
 `(progn ,@(fn2-cpt-nth-rules readers 0) (in-theory (disable ,@readers))))
(fn2-cpt-readers-nth fn2-history-state-batches fn2-history-state-operations fn2-history-state-fence
 fn2-history-state-refused fn2-history-state-members fn2-history-state-identities)
(fn2-cpt-readers-nth fn2-history-row-batch fn2-history-row-logs fn2-history-row-issued
 fn2-history-row-done fn2-history-row-uncertain fn2-history-row-fence-issued fn2-history-row-durable
 fn2-history-row-published fn2-history-row-acknowledged fn2-history-row-mode fn2-history-row-preflushed)
(fn2-cpt-readers-nth fn2-history-operation-batch-number fn2-history-operation-role
 fn2-history-operation-identity fn2-history-operation-length fn2-history-operation-terminal
 fn2-history-operation-fua)
(defthm fn2-history-state-requests-cpt-nth (equal (fn2-history-state-requests x) (nth 8 x))
 :hints (("Goal" :in-theory (enable fn2-history-state-requests))))
(in-theory (disable fn2-history-state-requests))

(defmacro fn2-cpt-history-preserves (fn &rest formals)
 `(progn
   (defthm ,(packn (list fn '-cpt-ok))
     (implies (and (fn2-cpt-hs-okp s) (true-listp (nth 7 s)))
              (and (fn2-cpt-hs-okp (mv-nth 1 (,fn ,@formals)))
                   (true-listp (nth 7 (mv-nth 1 (,fn ,@formals))))))
     :hints (("Goal" :in-theory (enable ,fn))))
   (defthm ,(packn (list fn '-cpt-acked))
     (subsetp-equal (fn2-cpt-hs-acked s) (fn2-cpt-hs-acked (mv-nth 1 (,fn ,@formals))))
     :hints (("Goal" :in-theory (enable ,fn))))
   (in-theory (disable ,fn))))

(fn2-cpt-history-preserves fn2-history-request event s)
(fn2-cpt-history-preserves fn2-history-batch event s)
(fn2-cpt-history-preserves fn2-history-write event s)
(fn2-cpt-history-preserves fn2-history-write-result event s)
(fn2-cpt-history-preserves fn2-history-fence event s)
(fn2-cpt-history-preserves fn2-history-fence-result event s)
(fn2-cpt-history-preserves fn2-history-visible tag n s)
(fn2-cpt-history-preserves fn2-history-step event s)

; The acknowledgement an accepted (:ack N) event makes.
(defthm fn2-cpt-visible-ack
 (implies (and (equal (mv-nth 0 (fn2-history-visible :ack n s)) :ok))
          (member-equal n (fn2-cpt-hs-acked (mv-nth 1 (fn2-history-visible :ack n s)))))
 :hints (("Goal" :in-theory (enable fn2-history-visible fn2-history-emit fn2-cpt-hs-acked))))
(defthm fn2-cpt-step-ack
 (implies (equal (mv-nth 0 (fn2-history-step (list :ack n) s)) :ok)
          (member-equal n (fn2-cpt-hs-acked (mv-nth 1 (fn2-history-step (list :ack n) s)))))
 :hints (("Goal" :in-theory (enable fn2-history-step))))

(defun fn2-cpt-translate-state (events s)
 (declare (xargs :verify-guards nil))
 (if (consp events)
     (mv-let (code next) (fn2-history-step (car events) s)
      (if (eq code :ok) (fn2-cpt-translate-state (cdr events) next) s))
   s))
(defthm fn2-cpt-translate-loop-state
 (implies (equal (mv-nth 0 (fn2-history-translate-loop events s)) :ok)
          (equal (mv-nth 1 (fn2-history-translate-loop events s))
                 (reverse (nth 7 (fn2-cpt-translate-state events s)))))
 :hints (("Goal" :in-theory (enable fn2-history-translate-loop))))
(defthm fn2-cpt-translate-state-ok
 (implies (and (fn2-cpt-hs-okp s) (true-listp (nth 7 s)))
          (and (fn2-cpt-hs-okp (fn2-cpt-translate-state events s))
               (true-listp (nth 7 (fn2-cpt-translate-state events s))))))
(defthm fn2-cpt-translate-state-acked
 (implies (and (equal (mv-nth 0 (fn2-history-translate-loop events s)) :ok)
               (member-equal x (fn2-cpt-hs-acked s)))
          (member-equal x (fn2-cpt-hs-acked (fn2-cpt-translate-state events s))))
 :hints (("Goal" :in-theory (enable fn2-history-translate-loop))))
(defthm fn2-cpt-translate-state-ack-event
 (implies (and (equal (mv-nth 0 (fn2-history-translate-loop events s)) :ok)
               (member-equal (list :ack n) events))
          (member-equal n (fn2-cpt-hs-acked (fn2-cpt-translate-state events s))))
 :hints (("Goal" :in-theory (enable fn2-history-translate-loop))))

(defthm fn2-cpt-hs-okp-trace-state
 (implies (and (fn2-cpt-hs-okp s) (true-listp (nth 7 s)))
          (equal (fn2-lm-trace-state (reverse (nth 7 s)))
                 (nth 6 s)))
 :hints (("Goal" :in-theory (enable fn2-cpt-hs-okp))))

; An (:ack N) event in a translation that succeeds leaves N acknowledged,
; fenced and completed in the log model's final state.
(defthm fn2-cpt-translate-ack
 (implies (and (equal (mv-nth 0 (fn2-history-translate events)) :ok)
               (member-equal (list :ack n) events))
          (let ((s (fn2-lm-trace-state (mv-nth 1 (fn2-history-translate events)))))
           (and (member-equal n (fn2-lm-state-acknowledged s))
                (member-equal n (fn2-lm-state-fenced s))
                (member-equal n (fn2-lm-state-completed s)))))
 :hints (("Goal" :in-theory (e/d (fn2-history-translate fn2-cpt-hs-okp fn2-cpt-hs-acked fn2-cpt-lm-orderedp)
                                 (fn2-cpt-translate-state-ack-event fn2-cpt-lm-trace-state-ordered))
                 :use ((:instance fn2-cpt-translate-state-ack-event
                                  (s (list nil nil nil nil nil nil (fn2-lm-initial) nil nil)))
                       (:instance fn2-cpt-translate-state-ok
                                  (s (list nil nil nil nil nil nil (fn2-lm-initial) nil nil)))
                       (:instance fn2-cpt-lm-trace-state-ordered
                                  (trace (mv-nth 1 (fn2-history-translate events))))))))

; ---------------------------------------------------------------------------
; The run's initial machines: both rows of the core the run creates, after
; its two starts, carry no replies. The core is the one with-local-stobj
; creates, so the fact is a ground evaluation per (mode, members).
(defun fn2-cpt-init (mode members fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* ((profile (fn2-b-test-profile *fn2-profile-tiny* mode))
      (fn2-core (fn2-core-init profile fn2-core))
      ((mv ec fn2-core)
       (stobj-let ((fn2-extents (fn2-core-extents fn2-core))) (code fn2-extents)
        (fn2-alloc-begin-epoch 1 fn2-extents) (mv code fn2-core)))
      (a (fn2-machine-global-id *fn2-commit-kind* 0 profile))
      (b (fn2-machine-global-id *fn2-commit-kind* 1 profile))
      ((mv ca ea & fn2-core) (fn2-b-start a members 1 mode b fn2-core))
      ((mv cb eb & fn2-core) (fn2-b-start b members (+ 1 (nfix members)) mode a fn2-core)))
  (mv ec ca ea cb eb fn2-core)))
(defun fn2-cpt-init-view (mode members)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
  (mv-let (ec ca ea cb eb fn2-core) (fn2-cpt-init mode members fn2-core)
   (declare (ignore ec ca ea cb eb))
   (let ((profile (fn2-b-test-profile *fn2-profile-tiny* mode)))
    (mv (fn2-b-visibility (list (fn2-machine-global-id *fn2-commit-kind* 0 profile)
                                (fn2-machine-global-id *fn2-commit-kind* 1 profile)) fn2-core)
        fn2-core)))))
(defun fn2-cpt-no-replies-p (rows)
 (declare (xargs :guard t))
 (or (atom rows)
     (and (not (posp (fn2-b-visible-acks (car rows)))) (fn2-cpt-no-replies-p (cdr rows)))))
(defthm fn2-cpt-no-replies-acked
 (implies (fn2-cpt-no-replies-p rows) (fn2-cpt-acked-rows-p rows events)))

(defthm fn2-cpt-init-view-no-replies
 (implies (and (member-equal mode '(0 1)) (posp members) (<= members 16))
          (fn2-cpt-no-replies-p (fn2-cpt-init-view mode members)))
 :hints (("Goal" :in-theory (disable fn2-cpt-init-view fn2-cpt-no-replies-p)
                 :cases ((equal members 1) (equal members 2) (equal members 3) (equal members 4)
                         (equal members 5) (equal members 6) (equal members 7) (equal members 8)
                         (equal members 9) (equal members 10) (equal members 11) (equal members 12)
                         (equal members 13) (equal members 14) (equal members 15) (equal members 16)))))

(defthm fn2-cpt-execute-acked
 (implies (fn2-cpt-no-replies-p
           (fn2-b-visibility (list (fn2-machine-global-id *fn2-commit-kind* 0 (fn2-b-test-profile *fn2-profile-tiny* mode))
                                   (fn2-machine-global-id *fn2-commit-kind* 1 (fn2-b-test-profile *fn2-profile-tiny* mode)))
                             (mv-nth 5 (fn2-cpt-init mode members fn2-core))))
          (let ((result (mv-nth 0 (fn2-commit-proof-execute commands model-profile mode members seed nil
                                                            fn2-core fn2-sim fn2-own))))
           (fn2-cpt-acked-keys-p (strip-cars (fn2-commit-proof-replies result))
                                 (fn2-commit-proof-events result))))
 :hints (("Goal" :in-theory (union-theories (fn2-cpt-only fn2-commit-proof-execute fn2-commit-proof-replies
                                                          fn2-commit-proof-events)
                                            '(fn2-cpt-init))
                 :do-not-induct t)))

(defthm fn2-cpt-execute-bad-args
 (implies (not (and (fn2-cm-profilep model-profile) (member-equal mode '(0 1))
                    (posp members) (<= members 16) (unsigned-byte-p 32 seed)))
          (equal (fn2-commit-proof-replies
                  (mv-nth 0 (fn2-commit-proof-execute commands model-profile mode members seed faults
                                                      fn2-core fn2-sim fn2-own)))
                 nil))
 :hints (("Goal" :in-theory (union-theories (fn2-cpt-only fn2-commit-proof-execute)
                                            '(fn2-commit-proof-replies)))))

(defthm fn2-cpt-run-acked
 (let ((result (fn2-commit-proof-run commands profile mode members seed)))
  (fn2-cpt-acked-keys-p (strip-cars (fn2-commit-proof-replies result)) (fn2-commit-proof-events result)))
 :hints (("Goal" :in-theory (e/d (fn2-commit-proof-run fn2-commit-proof-run-faults)
                                 (fn2-commit-proof-execute fn2-cpt-init fn2-cpt-init-view-no-replies
                                  fn2-commit-proof-replies fn2-commit-proof-events))
                 :expand ((fn2-cpt-init-view mode members))
                 :use ((:instance fn2-cpt-init-view-no-replies)
                       (:instance fn2-cpt-execute-acked (model-profile profile)
                                  (fn2-core (create-fn2-core)) (fn2-sim (create-fn2-sim))
                                  (fn2-own (create-fn2-own)))
                       (:instance fn2-cpt-execute-bad-args (model-profile profile) (faults nil)
                                  (fn2-core (create-fn2-core)) (fn2-sim (create-fn2-sim))
                                  (fn2-own (create-fn2-own)))))))

; The physical projection removes only :refuse events.
(defthm fn2-cpt-member-physical
 (implies (and (member-equal x events) (not (eq (fn2-lm-event-tag x) :refuse)))
          (member-equal x (fn2-commit-physical-events events))))
(defthm fn2-cpt-acked-keys-physical
 (implies (fn2-cpt-acked-keys-p keys events)
          (fn2-cpt-acked-keys-p keys (fn2-commit-physical-events events))))

(defthm fn2-cpt-acked-keys-translate
 (implies (and (fn2-cpt-acked-keys-p keys events)
               (equal (mv-nth 0 (fn2-history-translate events)) :ok))
          (let ((s (fn2-lm-trace-state (mv-nth 1 (fn2-history-translate events)))))
           (and (subsetp-equal keys (fn2-lm-state-acknowledged s))
                (subsetp-equal keys (fn2-lm-state-fenced s))
                (subsetp-equal keys (fn2-lm-state-completed s)))))
 :hints (("Goal" :induct (len keys) :in-theory (disable fn2-history-translate fn2-lm-trace-state))))

; ---------------------------------------------------------------------------
; The reduction: of the seven conjuncts of fn2-commit-ack-evidencep, the
; three set inclusions are theorems. What remains owed is the translation
; succeeding (the run's projected events are a HISTORY trace), the reply
; counts, the recovered prefix and the recovered length.
(defun fn2-cpt-ack-owed-p (result)
 (declare (xargs :verify-guards nil))
 (let ((accepted (strip-cars (fn2-commit-proof-replies result))))
  (or (not accepted)
      (mv-let (code trace) (fn2-history-translate (fn2-commit-physical-events (fn2-commit-proof-events result)))
       (let ((s (fn2-lm-trace-state trace)))
        (and (eq code :ok)
             (fn2-commit-reply-countsp (fn2-commit-proof-replies result) (fn2-lm-state-submitted s))
             (fn2-lm-prefixp (fn2-commit-proof-recovered result) (fn2-lm-state-submitted s))
             (fn2-lm-acknowledged-in-historyp accepted (fn2-commit-proof-recovered result))))))))

(defthm fn2-commit-ack-implies-durable-reduction
 (let ((result (fn2-commit-proof-run commands profile mode members seed)))
  (implies (fn2-cpt-ack-owed-p result) (fn2-commit-ack-evidencep result)))
 :hints (("Goal" :in-theory (e/d (fn2-commit-ack-evidencep fn2-cpt-ack-owed-p)
                                 (fn2-commit-proof-run fn2-history-translate fn2-lm-trace-state
                                  fn2-commit-physical-events fn2-cpt-run-acked fn2-cpt-acked-keys-p))
                 :use ((:instance fn2-cpt-run-acked)
                       (:instance fn2-cpt-acked-keys-translate
                                  (keys (strip-cars (fn2-commit-proof-replies
                                                     (fn2-commit-proof-run commands profile mode members seed))))
                                  (events (fn2-commit-physical-events
                                           (fn2-commit-proof-events
                                            (fn2-commit-proof-run commands profile mode members seed)))))))))
