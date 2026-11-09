; The sticky stop is a recovery boundary over every environment (ROOTSWAP-ASTRA
; Q1 item 1). A stopped core may hold partially updated volatile state (a
; publish that stopped after marking transactions published), so it never
; resumes serving: recovery starts a fresh core from the device.
;
; FN2-ENV-STEP-REFUSES-WHEN-STOPPED: from a core whose stop bit is set, the
; device's take, the host's admission, a loan write and every action outside
; the vocabulary log nothing and leave the core exactly as it was; a turn
; only zeroes its per-turn work counters (no transition runs). The other
; actions are the completions of operations the device already holds and the
; clock, signal and :epoch posts: FN2-ENV-STEP-FRAME-WHEN-STOPPED says that
; any action whatever logs at most a :result entry and changes no child but
; the ops table (results recorded, never harvested), the control (the stop
; bit stays set, FN2-ENV-STEP-STOP-STICKY) and the extents (:epoch).
; FN2-ENV-STEPS-WHEN-STOPPED lifts it to every action list: the device log
; gains no take, the core stays stopped, and every other child (commit rows,
; machines, pool, scheduler, ...) is the stopped core's.
; FN2-ENV-STEPS-TAKES-FROZEN-AFTER-STOP: for every run whose prefix stopped
; the core, the suffix adds no take to the device log.
;
; What the statement does not say: operations the device took before the
; stop may still land (a write reaches the medium, a send reaches its peer);
; they stay the device's until completion or teardown.
(in-package "ACL2")
(include-book "commit-durable-all")

;; ---------------------------------------------------------------------------
;; The host entries and the admission refuse on the stop bit (by definition).
(defthm fn2-host-ops-when-stopped-by-definition
  (implies (equal (fn2-exec-stop c) 1)
           (and (equal (fn2-host-outbox-peek k c) (mv :stopped 0 0))
                (equal (fn2-host-action slot c) (mv :stopped 0 0 0 0 0 0 0 0 0 0 0 0 0 0))
                (equal (fn2-host-outbox-ack n c) (mv :stopped c))
                (equal (fn2-host-op-finish slot gen c) (mv :stopped c))
                (equal (fn2-commit-admit-keyed members mode okind oslot ogen c) (mv :stopped 0 0 0 c))))
  :hints (("Goal" :in-theory '(fn2-host-outbox-peek fn2-host-action fn2-host-outbox-ack fn2-host-op-finish
                               fn2-commit-admit-keyed fn2-core-stopped-p-is-exec-stop))))

;; ---------------------------------------------------------------------------
;; The turn on a stopped core: the loop ends before its first transition.
(defthm fn2-exec-stop-of-set-turn-work
  (and (equal (fn2-exec-stop (fn2-exec-set-turn-bytes v c)) (fn2-exec-stop c))
       (equal (fn2-exec-stop (fn2-exec-set-turn-steps v c)) (fn2-exec-stop c)))
  :hints (("Goal" :in-theory (enable fn2-exec-stop fn2-exec-set-turn-bytes fn2-exec-set-turn-steps
                                     fn2-control-stop update-fn2-control-turn-bytes
                                     update-fn2-control-turn-steps))))

(defthm fn2-turn-when-stopped
  (implies (equal (fn2-exec-stop c) 1)
           (equal (fn2-turn c)
                  (mv :stop 0 0 0 (fn2-exec-set-turn-steps 0 (fn2-exec-set-turn-bytes 0 c)))))
  :hints (("Goal" :in-theory '(fn2-turn fn2-concrete-turn fn2-concrete-loop-stop-p fn2-turn-status
                               fn2-exec-stop-of-set-turn-work (:e equal))
           :expand ((:free (fuel h k a nobs nvisits nactions core)
                     (fn2-concrete-loop fuel h k a nobs nvisits nactions core))))))

(defthm fn2-exec-stop-of-env-begin-epoch
  (equal (fn2-exec-stop (fn2-env-begin-epoch epoch c)) (fn2-exec-stop c))
  :hints (("Goal" :in-theory (enable fn2-exec-stop fn2-env-begin-epoch))))

;; ---------------------------------------------------------------------------
;; THE STATEMENT, over the step function the run and recovery interpret.
(defun fn2-env-stopped-refusal-p (action)
  (declare (xargs :guard t))
  (not (member-eq (fn2-env-tag action) '(:post-result :accept-result :clock :signal :epoch))))
(defun-nx fn2-env-stopped-after (action c)
  (if (eq (fn2-env-tag action) :turn)
      (fn2-exec-set-turn-steps 0 (fn2-exec-set-turn-bytes 0 c))
    c))

(defthm fn2-env-step-refuses-when-stopped
  (implies (and (equal (fn2-exec-stop c) 1) (fn2-env-stopped-refusal-p action))
           (equal (fn2-env-step action recoveryp image rlog c)
                  (mv nil (fn2-env-stopped-after action c))))
  :hints (("Goal" :in-theory '(fn2-env-step fn2-env-take fn2-env-loan-write fn2-env-admit
                               fn2-env-stopped-refusal-p fn2-env-stopped-after
                               fn2-host-ops-when-stopped-by-definition fn2-turn-when-stopped
                               (:e mv-nth) (:e equal) (:e member-eq) mv-nth car-cons cdr-cons zp
                               member-eq member-equal))))

;; Every child but the ops table, the control and the extents.
(defun fn2-env-stopped-frame-terms (children)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom children) nil
    (let ((field (and (consp (car children)) (caar children))))
      (if (member-eq field '(fn2-core-ops fn2-core-control fn2-core-extents))
          (fn2-env-stopped-frame-terms (cdr children))
        (cons `(equal (,field c) (,field c0))
              (fn2-env-stopped-frame-terms (cdr children)))))))
(make-event
 `(defun-nx fn2-env-stopped-frame-p (c0 c)
    (and ,@(fn2-env-stopped-frame-terms *fn2-core-children*))))
(defthm fn2-env-stopped-frame-p-reflexive
  (fn2-env-stopped-frame-p c c))
(defthm fn2-env-stopped-frame-p-of-update-ops
  (equal (fn2-env-stopped-frame-p c0 (update-fn2-core-ops ops c)) (fn2-env-stopped-frame-p c0 c))
  :hints (("Goal" :in-theory (enable fn2-env-stopped-frame-p))))
(defthm fn2-env-stopped-frame-p-of-set-turn-work
  (and (equal (fn2-env-stopped-frame-p c0 (fn2-exec-set-turn-bytes v c)) (fn2-env-stopped-frame-p c0 c))
       (equal (fn2-env-stopped-frame-p c0 (fn2-exec-set-turn-steps v c)) (fn2-env-stopped-frame-p c0 c)))
  :hints (("Goal" :in-theory (enable fn2-env-stopped-frame-p fn2-exec-set-turn-bytes fn2-exec-set-turn-steps))))
(defthm fn2-env-stopped-frame-p-of-env-begin-epoch
  (equal (fn2-env-stopped-frame-p c0 (fn2-env-begin-epoch epoch c)) (fn2-env-stopped-frame-p c0 c))
  :hints (("Goal" :in-theory (enable fn2-env-stopped-frame-p fn2-env-begin-epoch))))
(defthm fn2-env-stopped-frame-p-of-host-posts
  (and (equal (fn2-env-stopped-frame-p c0 (fn2-host-post-result cell slot gen evkind outcome reason count aux0 aux1 c))
              (fn2-env-stopped-frame-p c0 c))
       (equal (fn2-env-stopped-frame-p c0 (fn2-host-post-accept-result slot gen outcome reason cap-index cap-nonce
                                                                       family port w0 w1 w2 w3 c))
              (fn2-env-stopped-frame-p c0 c))
       (equal (fn2-env-stopped-frame-p c0 (fn2-host-post-clock mono real flags c)) (fn2-env-stopped-frame-p c0 c))
       (equal (fn2-env-stopped-frame-p c0 (fn2-host-post-signal bits c)) (fn2-env-stopped-frame-p c0 c)))
  :hints (("Goal" :in-theory '(fn2-host-post-result fn2-host-post-accept-result fn2-host-post-clock
                               fn2-host-post-signal fn2-env-stopped-frame-p-of-update-ops))))
(defthm fn2-exec-stop-of-host-posts
  (and (equal (fn2-exec-stop (fn2-host-post-result cell slot gen evkind outcome reason count aux0 aux1 c))
              (fn2-exec-stop c))
       (equal (fn2-exec-stop (fn2-host-post-accept-result slot gen outcome reason cap-index cap-nonce
                                                          family port w0 w1 w2 w3 c))
              (fn2-exec-stop c))
       (equal (fn2-exec-stop (fn2-host-post-clock mono real flags c)) (fn2-exec-stop c))
       (equal (fn2-exec-stop (fn2-host-post-signal bits c)) (fn2-exec-stop c)))
  :hints (("Goal" :in-theory (enable fn2-exec-stop fn2-host-post-result fn2-host-post-accept-result
                                     fn2-host-post-clock fn2-host-post-signal))))

;; A device-log entry a stopped core may make: none, or a completion's result.
(defun fn2-env-stopped-entry-p (entry)
  (declare (xargs :guard t))
  (or (null entry) (and (consp entry) (eq (car entry) :result))))

(in-theory (disable fn2-env-stopped-frame-p fn2-env-stopped-after fn2-env-stopped-entry-p))
(defthm fn2-env-step-frame-when-stopped
  (implies (equal (fn2-exec-stop c) 1)
           (mv-let (entry after) (fn2-env-step action recoveryp image rlog c)
             (and (fn2-env-stopped-entry-p entry)
                  (equal (fn2-exec-stop after) 1)
                  (equal (fn2-env-stopped-frame-p c0 after) (fn2-env-stopped-frame-p c0 c)))))
  :hints (("Goal" :cases ((fn2-env-stopped-refusal-p action)))
          ("Subgoal 2" :in-theory '(fn2-env-step fn2-env-post fn2-env-stopped-refusal-p fn2-env-stopped-entry-p
                                    fn2-env-stopped-frame-p-of-host-posts fn2-env-stopped-frame-p-of-env-begin-epoch
                                    fn2-exec-stop-of-host-posts fn2-exec-stop-of-env-begin-epoch
                                    (:e mv-nth) (:e equal) (:e member-eq) mv-nth car-cons cdr-cons zp
                                    member-eq member-equal))
          ("Subgoal 1" :in-theory '(fn2-env-step-refuses-when-stopped fn2-env-stopped-after fn2-env-stopped-entry-p
                                    fn2-exec-stop-of-set-turn-work fn2-env-stopped-frame-p-of-set-turn-work
                                    mv-nth car-cons cdr-cons (:e zp)))))

(defthm fn2-env-step-stop-sticky
  (implies (equal (fn2-exec-stop c) 1)
           (equal (fn2-exec-stop (mv-nth 1 (fn2-env-step action recoveryp image rlog c))) 1))
  :hints (("Goal" :use ((:instance fn2-env-step-frame-when-stopped (c0 c)))
           :in-theory '(mv-nth))))

;; ---------------------------------------------------------------------------
;; Every action list from a stopped core: the device log gains no take, the
;; core stays stopped, and every child but ops, control and extents is the
;; stopped core's.
(defun fn2-env-takes (log)
  (declare (xargs :guard t))
  (cond ((atom log) nil)
        ((and (consp (car log)) (eq (car (car log)) :take)) (cons (car log) (fn2-env-takes (cdr log))))
        (t (fn2-env-takes (cdr log)))))
(local
 (defthm fn2-env-takes-of-stopped-entry
   (implies (fn2-env-stopped-entry-p entry)
            (equal (fn2-env-takes (if entry (cons entry rlog) rlog)) (fn2-env-takes rlog)))
   :hints (("Goal" :in-theory '(fn2-env-stopped-entry-p fn2-env-takes car-cons cdr-cons (:e eq) (:e consp))))))

(local
 (defthm fn2-sb-mv-nth-of-cons
   (and (equal (mv-nth 0 (cons a x)) a)
        (equal (mv-nth 1 (cons a (cons b x))) b)
        (equal (mv-nth 2 (cons a (cons b (cons d x)))) d))))
(local
 (defthm fn2-env-steps-when-stopped-gen
   (implies (and (equal (fn2-exec-stop c) 1) (fn2-env-stopped-frame-p c0 c))
            (and (equal (fn2-env-takes (mv-nth 0 (fn2-env-steps actions ids rlog acked c))) (fn2-env-takes rlog))
                 (equal (fn2-exec-stop (mv-nth 2 (fn2-env-steps actions ids rlog acked c))) 1)
                 (fn2-env-stopped-frame-p c0 (mv-nth 2 (fn2-env-steps actions ids rlog acked c)))))
   :hints (("Goal" :induct (fn2-env-steps actions ids rlog acked c)
            :in-theory '(fn2-env-steps car-cons cdr-cons (:e zp) atom fn2-env-takes-of-stopped-entry
                         fn2-sb-mv-nth-of-cons
                         fn2-env-step-frame-when-stopped fn2-env-step-stop-sticky)))))

(defthm fn2-env-steps-when-stopped
  (implies (equal (fn2-exec-stop c) 1)
           (and (equal (fn2-env-takes (mv-nth 0 (fn2-env-steps actions ids rlog acked c))) (fn2-env-takes rlog))
                (equal (fn2-exec-stop (mv-nth 2 (fn2-env-steps actions ids rlog acked c))) 1)
                (fn2-env-stopped-frame-p c (mv-nth 2 (fn2-env-steps actions ids rlog acked c)))))
  :hints (("Goal" :use ((:instance fn2-env-steps-when-stopped-gen (c0 c)))
           :in-theory '(fn2-env-stopped-frame-p-reflexive))))

;; A run whose prefix stopped the core: the suffix, whatever it is, adds no
;; take to the device log.
(local
 (defthm fn2-env-steps-of-append
   (equal (fn2-env-steps (append pre post) ids rlog acked c)
          (mv-let (rlog acked c) (fn2-env-steps pre ids rlog acked c)
            (fn2-env-steps post ids rlog acked c)))
   :hints (("Goal" :induct (fn2-env-steps pre ids rlog acked c)
            :in-theory '(fn2-env-steps binary-append mv-nth car-cons cdr-cons atom (:e zp))))))

(defthm fn2-env-steps-takes-frozen-after-stop
  (implies (equal (fn2-exec-stop (mv-nth 2 (fn2-env-steps pre ids rlog acked c))) 1)
           (equal (fn2-env-takes (mv-nth 0 (fn2-env-steps (append pre post) ids rlog acked c)))
                  (fn2-env-takes (mv-nth 0 (fn2-env-steps pre ids rlog acked c)))))
  :hints (("Goal" :in-theory '(fn2-env-steps-of-append fn2-env-steps-when-stopped))))
