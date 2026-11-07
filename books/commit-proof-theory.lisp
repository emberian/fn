; FN2-COMMIT-ACK-IMPLIES-DURABLE, proved in layers. This book holds the parts
; of the conclusion that follow from HISTORY, the log model and the replay's
; own bookkeeping; the protocol-conformance obligation (the translated events
; are accepted) and recovery completeness are stated separately.
(in-package "ACL2")
(include-book "commit-proof")
(fn2-book-layer :b)

; ---------------------------------------------------------------------------
; Log model: acknowledged is within fenced, fenced within completed, in every
; state reachable from the initial one, valid or not.
(defun fn2-cpt-lm-orderedp (s)
 (declare (xargs :guard t))
 (and (ec-call (subsetp-equal (fn2-lm-state-acknowledged s) (fn2-lm-state-fenced s)))
      (ec-call (subsetp-equal (fn2-lm-state-fenced s) (fn2-lm-state-completed s)))))

(local (defthm fn2-cpt-subsetp-cons
 (implies (subsetp-equal a b) (subsetp-equal a (cons x b)))))
(local (defthm fn2-cpt-subsetp-refl (subsetp-equal a a)))
(local (defthm fn2-cpt-member-subsetp
 (implies (and (member-equal x a) (subsetp-equal a b)) (member-equal x b))))
(local (defthm fn2-cpt-subsetp-trans
 (implies (and (subsetp-equal a b) (subsetp-equal b c)) (subsetp-equal a c))))

(defthm fn2-cpt-all-through-member
 (implies (and (posp n) (fn2-lm-all-through-p n ids)) (member-equal n ids))
 :hints (("Goal" :expand ((fn2-lm-all-through-p n ids)))))

(defthm fn2-cpt-lm-reader-nth
 (and (equal (fn2-lm-state-completed s) (nth 1 s))
      (equal (fn2-lm-state-fenced s) (nth 2 s))
      (equal (fn2-lm-state-acknowledged s) (nth 3 s)))
 :rule-classes nil)

(defthm fn2-cpt-lm-step-ordered
 (implies (fn2-cpt-lm-orderedp s) (fn2-cpt-lm-orderedp (fn2-lm-step event s)))
 :hints (("Goal" :in-theory (enable fn2-lm-step fn2-lm-event-allowedp fn2-lm-knownp))))

(defthm fn2-cpt-lm-ordered-update-valid
 (implies (fn2-cpt-lm-orderedp s) (fn2-cpt-lm-orderedp (update-nth 10 v s)))
 :hints (("Goal" :in-theory (disable fn2-lm-state-acknowledged fn2-lm-state-fenced fn2-lm-state-completed)
                 :use ((:instance fn2-cpt-lm-reader-nth)
                       (:instance fn2-cpt-lm-reader-nth (s (update-nth 10 v s)))))))

(defthm fn2-cpt-lm-run-ordered
 (implies (fn2-cpt-lm-orderedp s) (fn2-cpt-lm-orderedp (fn2-lm-run trace s)))
 :hints (("Goal" :in-theory (disable fn2-cpt-lm-orderedp))))
(in-theory (disable fn2-cpt-lm-orderedp))

(defthm fn2-cpt-lm-trace-state-ordered
 (fn2-cpt-lm-orderedp (fn2-lm-trace-state trace))
 :hints (("Goal" :in-theory (disable fn2-cpt-lm-orderedp fn2-lm-run)
                 :use ((:instance fn2-cpt-lm-run-ordered (s (fn2-lm-initial)))))))

; ---------------------------------------------------------------------------
; Open only FN (and KEEP); every other function its body calls stays closed.
(defmacro fn2-cpt-only (fn &rest keep)
 `(set-difference-theories (current-theory :here)
   (set-difference-eq (all-fnnames (body ',fn nil world)) '(,fn mv-nth nfix posp len ,@keep))))

; Every batch with a positive reply count has an (:ack batch) event.
(defun fn2-cpt-acked-rows-p (rows events)
 (declare (xargs :guard t))
 (if (atom rows) t
  (and (or (not (posp (fn2-b-visible-acks (car rows))))
           (ec-call (member-equal (list :ack (fn2-b-visible-batch (car rows))) events)))
       (fn2-cpt-acked-rows-p (cdr rows) events))))
(defun fn2-cpt-acked-keys-p (keys events)
 (declare (xargs :guard t))
 (if (atom keys) t
  (and (ec-call (member-equal (list :ack (car keys)) events))
       (fn2-cpt-acked-keys-p (cdr keys) events))))

(defthm fn2-cpt-acked-keys-member
 (implies (and (fn2-cpt-acked-keys-p keys events) (member-equal k keys))
          (member-equal (list :ack k) events)))
(defthm fn2-cpt-acked-rows-mono
 (implies (and (fn2-cpt-acked-rows-p rows events) (subsetp-equal events more))
          (fn2-cpt-acked-rows-p rows more)))
(defthm fn2-cpt-acked-keys-mono
 (implies (and (fn2-cpt-acked-keys-p keys events) (subsetp-equal events more))
          (fn2-cpt-acked-keys-p keys more)))

(defthm fn2-cpt-visible-for-batch
 (implies (fn2-b-visible-for batch rows)
          (equal (fn2-b-visible-batch (fn2-b-visible-for batch rows)) batch)))
(defthm fn2-cpt-visible-for-nil-acks
 (equal (fn2-b-visible-acks nil) nil))
(defthm fn2-cpt-visible-for-acked
 (implies (and (fn2-cpt-acked-rows-p rows events)
               (posp (fn2-b-visible-acks (fn2-b-visible-for batch rows))))
          (member-equal (list :ack batch) events))
 :hints (("Goal" :induct (fn2-b-visible-for batch rows)
                 :in-theory (disable fn2-b-visible-acks fn2-b-visible-batch))))

(defthm fn2-cpt-project-visible-grows
 (subsetp-equal events (fn2-b-project-visible old new events))
 :hints (("Goal" :in-theory (fn2-cpt-only fn2-b-project-visible))))
(defthm fn2-cpt-member-project-visible
 (implies (member-equal x events) (member-equal x (fn2-b-project-visible old new events)))
 :hints (("Goal" :in-theory (fn2-cpt-only fn2-b-project-visible))))
(defthm fn2-cpt-project-visible-acked
 (implies (fn2-cpt-acked-rows-p old events)
          (fn2-cpt-acked-rows-p new (fn2-b-project-visible old new events)))
 :hints (("Goal" :induct (fn2-b-project-visible old new events)
                 :in-theory (fn2-cpt-only fn2-b-project-visible))))

(defthm fn2-cpt-project-issues-grows
 (subsetp-equal events (mv-nth 3 (fn2-b-project-issues descriptors seen manifests events bytes fn2-core)))
 :hints (("Goal" :in-theory (fn2-cpt-only fn2-b-project-issues))))

(defthm fn2-cpt-acked-keys-put-assoc
 (implies (and (fn2-cpt-acked-keys-p (strip-cars replies) events) (member-equal (list :ack k) events))
          (fn2-cpt-acked-keys-p (strip-cars (put-assoc-equal k v replies)) events)))
(defthm fn2-cpt-acked-rows-member
 (implies (and (fn2-cpt-acked-rows-p rows events) (member-equal row rows)
               (posp (fn2-b-visible-acks row)))
          (member-equal (list :ack (fn2-b-visible-batch row)) events))
 :hints (("Goal" :in-theory (disable fn2-b-visible-acks fn2-b-visible-batch))))
(defthm fn2-cpt-observe-replies-acked
 (implies (and (fn2-cpt-acked-keys-p (strip-cars replies) events)
               (fn2-cpt-acked-rows-p views events))
          (fn2-cpt-acked-keys-p (strip-cars (fn2-commit-proof-observe-replies views replies)) events))
 :hints (("Goal" :in-theory (fn2-cpt-only fn2-commit-proof-observe-replies))))

(defthm fn2-cpt-member-revappend
 (iff (member-equal a (revappend x y)) (or (member-equal a x) (member-equal a y)))
 :hints (("Goal" :induct (revappend x y) :in-theory (disable fn2-cpt-member-subsetp))))
(defthm fn2-cpt-member-append
 (iff (member-equal a (append x y)) (or (member-equal a x) (member-equal a y))))
(defthm fn2-cpt-subsetp-revappend-x
 (implies (subsetp-equal c x) (subsetp-equal c (revappend x y))))
(defthm fn2-cpt-subsetp-revappend-y
 (implies (subsetp-equal c y) (subsetp-equal c (revappend x y))))
(defthm fn2-cpt-subsetp-append-x
 (implies (subsetp-equal c x) (subsetp-equal c (append x y))))
(defthm fn2-cpt-subsetp-append-y
 (implies (subsetp-equal c y) (subsetp-equal c (append x y))))
(defthm fn2-cpt-subsetp-reverse (subsetp-equal x (reverse x))
 :hints (("Goal" :in-theory (disable fn2-cpt-subsetp-revappend-x)
                 :use ((:instance fn2-cpt-subsetp-revappend-x (c x) (y nil))))))
(defthm fn2-cpt-member-project-issues
 (implies (member-equal x events)
          (member-equal x (mv-nth 3 (fn2-b-project-issues descriptors seen manifests events bytes fn2-core))))
 :hints (("Goal" :in-theory (fn2-cpt-only fn2-b-project-issues))))
(in-theory (disable fn2-b-project-issues fn2-b-project-visible fn2-commit-proof-observe-replies))
;; ---- base: everything above is proved ----
;; The replay's events and replies, without the flags that never feed them.
(defun fn2-cpt-replay-ev (commands turn ids profile replies seen manifests events
                          fn2-core fn2-sim fn2-own)
 (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil))
 (if (atom commands)
     (mv replies (reverse events) fn2-core fn2-sim fn2-own)
  (b* ((before (fn2-b-visibility ids fn2-core))
       ((mv & extra fn2-core fn2-sim fn2-own)
        (fn2-commit-proof-step (car commands) turn ids profile fn2-core fn2-sim fn2-own))
       (after (fn2-b-visibility ids fn2-core))
       (events (fn2-b-project-visible before after (append (reverse extra) events)))
       ((mv code seen manifests events &)
        (fn2-b-project-issues (fn2-b-outbox fn2-core) seen manifests events 0 fn2-core)))
   (fn2-cpt-replay-ev (cdr commands) (+ 1 (nfix turn)) ids profile
    (fn2-commit-proof-observe-replies after replies) seen manifests
    (if (eq code :ok) events (cons (list :projection-error code) events))
    fn2-core fn2-sim fn2-own))))

(defthm fn2-cpt-replay-ev-equal
 (b* (((mv & & & & replies2 & events2 & & &)
       (fn2-commit-proof-replay commands turn ids profile admitted fresh refused stable saw
                                replies seen manifests events fn2-core fn2-sim fn2-own))
      ((mv replies3 events3 & & &)
       (fn2-cpt-replay-ev commands turn ids profile replies seen manifests events
                          fn2-core fn2-sim fn2-own)))
  (and (equal replies2 replies3) (equal events2 events3)))
 :hints (("Goal" :in-theory (union-theories (fn2-cpt-only fn2-commit-proof-replay)
                                            '(fn2-cpt-replay-ev)))))

;; Both coverage predicates survive every way the replay grows EVENTS.
(defthm fn2-cpt-acked-rows-append
 (implies (fn2-cpt-acked-rows-p rows events) (fn2-cpt-acked-rows-p rows (append extra events))))
(defthm fn2-cpt-acked-keys-append
 (implies (fn2-cpt-acked-keys-p keys events) (fn2-cpt-acked-keys-p keys (append extra events))))
(defthm fn2-cpt-acked-rows-cons
 (implies (fn2-cpt-acked-rows-p rows events) (fn2-cpt-acked-rows-p rows (cons x events))))
(defthm fn2-cpt-acked-keys-cons
 (implies (fn2-cpt-acked-keys-p keys events) (fn2-cpt-acked-keys-p keys (cons x events))))
(defthm fn2-cpt-acked-keys-visible
 (implies (fn2-cpt-acked-keys-p keys events)
          (fn2-cpt-acked-keys-p keys (fn2-b-project-visible old new events))))
(defthm fn2-cpt-acked-rows-issues
 (implies (fn2-cpt-acked-rows-p rows events)
          (fn2-cpt-acked-rows-p rows (mv-nth 3 (fn2-b-project-issues d seen manifests events bytes fn2-core)))))
(defthm fn2-cpt-acked-keys-issues
 (implies (fn2-cpt-acked-keys-p keys events)
          (fn2-cpt-acked-keys-p keys (mv-nth 3 (fn2-b-project-issues d seen manifests events bytes fn2-core)))))

;; One iteration keeps the invariant: rows with replies have :ack events.
(defthm fn2-cpt-replay-step-acked
 (implies (and (fn2-cpt-acked-rows-p before events)
               (fn2-cpt-acked-keys-p (strip-cars replies) events))
          (let* ((ev1 (fn2-b-project-visible before after (append extra events)))
                 (ev2 (mv-nth 3 (fn2-b-project-issues d seen manifests ev1 bytes fn2-core)))
                 (ev3 (if flag ev2 (cons x ev2))))
           (and (fn2-cpt-acked-rows-p after ev3)
                (fn2-cpt-acked-keys-p (strip-cars (fn2-commit-proof-observe-replies after replies)) ev3))))
 :hints (("Goal" :in-theory (disable fn2-cpt-acked-rows-p fn2-cpt-acked-keys-p))))

(defthm fn2-cpt-replay-ev-acked
 (implies (and (fn2-cpt-acked-rows-p (fn2-b-visibility ids fn2-core) events)
               (fn2-cpt-acked-keys-p (strip-cars replies) events))
          (b* (((mv replies2 events2 & & &)
                (fn2-cpt-replay-ev commands turn ids profile replies seen manifests events
                                   fn2-core fn2-sim fn2-own)))
           (fn2-cpt-acked-keys-p (strip-cars replies2) events2)))
 :hints (("Goal" :induct (fn2-cpt-replay-ev commands turn ids profile replies seen manifests events
                                            fn2-core fn2-sim fn2-own)
                 :in-theory (e/d (fn2-cpt-replay-ev)
                                 (fn2-cpt-acked-rows-p fn2-cpt-acked-keys-p fn2-commit-proof-step
                                  fn2-b-visibility fn2-commit-terminal-refusals fn2-b-outbox)))))

(defthm fn2-cpt-replay-acked
 (implies (and (fn2-cpt-acked-rows-p (fn2-b-visibility ids fn2-core) events)
               (fn2-cpt-acked-keys-p (strip-cars replies) events))
          (b* (((mv & & & & replies2 & events2 & & &)
                (fn2-commit-proof-replay commands turn ids profile admitted fresh refused stable saw
                                         replies seen manifests events fn2-core fn2-sim fn2-own)))
           (fn2-cpt-acked-keys-p (strip-cars replies2) events2)))
 :hints (("Goal" :in-theory (disable fn2-commit-proof-replay fn2-cpt-replay-ev fn2-cpt-acked-keys-p))))

(defthm fn2-cpt-member-reverse
 (implies (not (stringp x)) (iff (member-equal a (reverse x)) (member-equal a x))))
(defthm fn2-cpt-subsetp-reverse-of
 (implies (and (subsetp-equal c x) (not (stringp x))) (subsetp-equal c (reverse x))))

; Death and recovery with no injected fault keep every projected event.
(defthm fn2-cpt-crash-recover-grows
 (subsetp-equal events (mv-nth 4 (fn2-b-crash-recover profile model nil manifests events read-fault reads
                                                      fn2-core fn2-sim fn2-own)))
 :hints (("Goal" :in-theory (e/d (fn2-b-crash-recover fn2-b-rec-inject)
                                 (fn2-sim-crash fn2-b-death-difference fn2-init-executor fn2-b-rec-truth
                                  fn2-b-rec-run fn2-b-rec-history fn2-b-rec-assume)))))

; ---------------------------------------------------------------------------
; HISTORY: the log-model state a translation carries is the log model run on
; the trace it emitted, its acknowledged set only grows, and an accepted
; (:ack B) event leaves B acknowledged.
(defun fn2-cpt-hs-okp (s)
 (declare (xargs :verify-guards nil))
 (equal (fn2-history-state-log-state s)
        (fn2-lm-run (reverse (fn2-history-state-trace s)) (fn2-lm-initial))))
(defun fn2-cpt-hs-acked (s)
 (declare (xargs :verify-guards nil))
 (fn2-lm-state-acknowledged (fn2-history-state-log-state s)))

(defthm fn2-cpt-hs-reader-nth
 (and (equal (fn2-history-state-log-state s) (nth 6 s))
      (equal (fn2-history-state-trace s) (nth 7 s))))
(in-theory (disable fn2-history-state-log-state fn2-history-state-trace))

(defthm fn2-cpt-revappend-append-gen
 (equal (revappend x (append y z)) (append (revappend x y) z)))
(defthm fn2-cpt-revappend-as-append
 (implies (syntaxp (not (equal y ''nil)))
          (equal (revappend x y) (append (revappend x nil) y)))
 :hints (("Goal" :in-theory (disable fn2-cpt-revappend-append-gen)
                 :use ((:instance fn2-cpt-revappend-append-gen (y nil) (z y))))))
(defthm fn2-cpt-lm-run-append
 (implies (true-listp a) (equal (fn2-lm-run (append a b) s) (fn2-lm-run b (fn2-lm-run a s))))
 :hints (("Goal" :in-theory (disable fn2-lm-step))))
(defthm fn2-cpt-true-listp-revappend
 (equal (true-listp (revappend x y)) (true-listp y)))
(defthm fn2-cpt-lm-step-acked
 (subsetp-equal (fn2-lm-state-acknowledged s) (fn2-lm-state-acknowledged (fn2-lm-step event s)))
 :hints (("Goal" :in-theory (enable fn2-lm-step))))
(defthm fn2-cpt-lm-step-acknowledge
 (implies (and (fn2-lm-state-valid s) (fn2-lm-event-allowedp event s)
               (equal (fn2-lm-event-tag event) :acknowledge))
          (member-equal (fn2-lm-event-argument event)
                        (fn2-lm-state-acknowledged (fn2-lm-step event s))))
 :hints (("Goal" :in-theory (enable fn2-lm-step))))

(defthm fn2-cpt-emit-ok
 (implies (and (fn2-cpt-hs-okp s) (true-listp (fn2-history-state-trace s)))
          (and (fn2-cpt-hs-okp (mv-nth 1 (fn2-history-emit event s)))
               (true-listp (fn2-history-state-trace (mv-nth 1 (fn2-history-emit event s))))))
 :hints (("Goal" :in-theory (enable fn2-history-emit))))
(defthm fn2-cpt-emit-acked
 (subsetp-equal (fn2-cpt-hs-acked s) (fn2-cpt-hs-acked (mv-nth 1 (fn2-history-emit event s))))
 :hints (("Goal" :in-theory (enable fn2-history-emit))))
(in-theory (disable fn2-history-emit))

(defthm fn2-cpt-hs-okp-update-nth
 (implies (and (natp i) (not (equal i 6)) (not (equal i 7)))
          (equal (fn2-cpt-hs-okp (update-nth i v s)) (fn2-cpt-hs-okp s))))
(defthm fn2-cpt-hs-acked-update-nth
 (implies (and (natp i) (not (equal i 6)))
          (equal (fn2-cpt-hs-acked (update-nth i v s)) (fn2-cpt-hs-acked s))))
(in-theory (disable fn2-cpt-hs-okp fn2-cpt-hs-acked))

(defmacro fn2-cpt-history-preserves (fn &rest formals)
 `(progn
   (defthm ,(packn (list fn '-cpt-ok))
     (implies (and (fn2-cpt-hs-okp s) (true-listp (fn2-history-state-trace s)))
              (and (fn2-cpt-hs-okp (mv-nth 1 (,fn ,@formals)))
                   (true-listp (fn2-history-state-trace (mv-nth 1 (,fn ,@formals))))))
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
                 (reverse (fn2-history-state-trace (fn2-cpt-translate-state events s)))))
 :hints (("Goal" :in-theory (enable fn2-history-translate-loop))))
(defthm fn2-cpt-translate-state-ok
 (implies (and (fn2-cpt-hs-okp s) (true-listp (fn2-history-state-trace s)))
          (and (fn2-cpt-hs-okp (fn2-cpt-translate-state events s))
               (true-listp (fn2-history-state-trace (fn2-cpt-translate-state events s))))))
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
 (implies (and (fn2-cpt-hs-okp s) (true-listp (fn2-history-state-trace s)))
          (equal (fn2-lm-trace-state (reverse (fn2-history-state-trace s)))
                 (fn2-history-state-log-state s)))
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
