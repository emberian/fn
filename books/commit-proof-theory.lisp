; FN2-COMMIT-ACK-IMPLIES-DURABLE in layers: the parts of its conclusion that
; follow from the log model and the replay's own bookkeeping. The keystone
; itself stays owed; books/commit-proof-theory-next.lsp carries the next
; layers (the replay invariant, HISTORY's translation invariant, the initial
; machines and the reduction), not yet admitted.
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
(defthm fn2-cpt-subsetp-cons-right
 (implies (subsetp-equal a b) (subsetp-equal a (cons x b))))
(defthm fn2-cpt-subsetp-self (subsetp-equal a a))
(defthm fn2-cpt-member-of-subsetp
 (implies (and (member-equal x a) (subsetp-equal a b)) (member-equal x b)))
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

(defthm fn2-cpt-acked-keys-revappend
 (implies (fn2-cpt-acked-keys-p keys x) (fn2-cpt-acked-keys-p keys (revappend x y))))

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
 :hints (("Goal" :in-theory (disable fn2-commit-proof-replay fn2-cpt-replay-ev fn2-cpt-acked-keys-p
                                     fn2-cpt-acked-rows-p fn2-cpt-replay-ev-acked)
                 :use ((:instance fn2-cpt-replay-ev-acked)))))

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
(defthmd fn2-cpt-lm-ack-nth (equal (fn2-lm-state-acknowledged s) (nth 3 s)))
(defthm fn2-cpt-lm-step-acked
 (subsetp-equal (fn2-lm-state-acknowledged s) (fn2-lm-state-acknowledged (fn2-lm-step event s)))
 :hints (("Goal" :in-theory (e/d (fn2-lm-step fn2-cpt-lm-ack-nth) (fn2-lm-state-acknowledged)))))
(defthm fn2-cpt-lm-step-acknowledge-shape
 (implies (and (fn2-lm-state-valid s) (fn2-lm-event-allowedp event s)
               (equal (fn2-lm-event-tag event) :acknowledge))
          (equal (fn2-lm-step event s)
                 (update-fn2-lm-state-acknowledged
                  (cons (fn2-lm-event-argument event) (fn2-lm-state-acknowledged s)) s)))
 :hints (("Goal" :in-theory (e/d (fn2-lm-step)
                                 (fn2-lm-event-allowedp fn2-lm-state-valid fn2-lm-state-acknowledged
                                  update-fn2-lm-state-acknowledged update-fn2-lm-state-valid
                                  update-fn2-lm-state-submitted update-fn2-lm-state-completed
                                  update-fn2-lm-state-fenced update-fn2-lm-state-crashed
                                  update-fn2-lm-state-witnesses update-fn2-lm-state-survivors
                                  update-fn2-lm-state-corrupt update-fn2-lm-state-bad-tail
                                  update-fn2-lm-state-rollback))
                 :do-not '(generalize eliminate-destructors))))
(defthm fn2-cpt-lm-acknowledged-update
 (equal (fn2-lm-state-acknowledged (update-fn2-lm-state-acknowledged v s)) v)
 :hints (("Goal" :in-theory (enable fn2-cpt-lm-ack-nth))))
