; Test-only evidence and the bounded-completion environment; no served book.
(in-package "ACL2")

(defun fn2-echo-stat (key stats)
  (declare (xargs :verify-guards nil))
  (nfix (cdr (assoc-equal key stats))))
(defun fn2-echo-count (key stats)
  (declare (xargs :verify-guards nil))
  (if key (put-assoc-equal key (+ 1 (fn2-echo-stat key stats)) stats) stats))
(defun fn2-echo-merge-stats (a b)
  (declare (xargs :verify-guards nil))
  (if (atom a) b
    (fn2-echo-merge-stats
     (cdr a) (put-assoc-equal (caar a)
                  (if (member-eq (caar a) '(:max-age :max-bound))
                      (max (nfix (cdar a)) (fn2-echo-stat (caar a) b))
                    (+ (nfix (cdar a)) (fn2-echo-stat (caar a) b))) b))))
(in-theory (disable fn2-echo-stat fn2-echo-count fn2-echo-merge-stats))

(defconst *fn2-echo-drop-causes*
  '(:process-death :reset :half-open-deadline :nonreading-deadline
    :client-disconnect :admission-refused :unattributed))
(defun fn2-echo-histogram (keys stats)
  (declare (xargs :verify-guards nil))
  (if (atom keys) nil
    (cons (cons (car keys) (fn2-echo-stat (car keys) stats))
          (fn2-echo-histogram (cdr keys) stats))))
(in-theory (disable fn2-echo-histogram))

; ROUND2 C.3: S turns per runnable continuation, allowing every row ahead
; of it in the anonymous FIFO. H > 3 drains our <=3 observations/turn;
; V=min(K,Aturn) allows even every calendar visit to emit a descriptor.
; Each receive quantum needs receive/send/reset (3 runs), terminal receive,
; terminal send and borrow release (3 adapter services). Add admission and
; final client read. Full input is supplied at accept, client output drained
; each turn. D=O: round-robin adapter service, one slot per turn.
; B(n) = 2*S + 2 + ceil(n/Q)*(3*S + 3*D + 1).
(defun fn2-echo-live-bound (bytes profile)
  (declare (xargs :verify-guards nil))
  (let* ((m (+ (fn2-profile-c profile) (fn2-profile-accept-credits profile) 1))
         (v (max 1 (min (fn2-profile-k profile) (fn2-profile-aturn profile))))
         (s (+ 1 (ceiling (* (fn2-profile-calendar-length profile) m) v)))
         (q (max 1 (min *fn2-sim-network-capacity* (min *fn2-echo-run-bytes*
                             (cdar (fn2-profile-pool-classes profile))))))
         (d (fn2-profile-o profile)))
    (+ (* 2 s) 2 (* (ceiling (nfix bytes) q) (+ (* 3 s) (* 3 d) 1)))))
(in-theory (disable fn2-echo-live-bound))

(defun fn2-echo-live-flight (left index fn2-sim)
  (declare (xargs :stobjs fn2-sim :verify-guards nil :measure (nfix left)
                  :hints (("Goal" :use ((:instance fn2-test-countdown (x left))
                                        (:instance fn2-test-count-op (x left))) :in-theory nil))))
  (if (zp left) (mv nil 0)
    (if (< 0 (fn2-sim-active index fn2-sim)) (mv t index)
      (fn2-echo-live-flight (- left 1) (mod (+ 1 index) (fn2-sim-rows fn2-sim)) fn2-sim))))
(in-theory (disable fn2-echo-live-flight))

; Poll asynchronous completions every turn, including while work is runnable.
; No random delays/retries: a would-block violates this environment and fails.
; Accepts without a supplied client complete :busy, rather than waiting forever.
(defun fn2-echo-live-advance (allow next fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil))
  (b* (((mv found slot) (fn2-echo-live-flight (fn2-sim-rows fn2-sim) next fn2-sim))
       ((unless found) (mv :pass next fn2-core fn2-sim fn2-own))
       (accept (and (= (fn2-sim-active slot fn2-sim) 1)
                    (= (fn2-sim-kind slot fn2-sim) *fn2-action-accept*)))
       ((mv & fn2-core fn2-sim fn2-own)
        (cond ((and accept allow)
               (fn2-sim-echo-accept slot *fn2-fault-none* (fn2-u32 (fn2-sim-now fn2-sim)) t fn2-core fn2-sim fn2-own))
              (accept
               (fn2-sim-complete-result slot (fn2-sim-gen slot fn2-sim) *fn2-action-accept*
                 *fn2-event-accept-result* 0 :busy 0 0 *fn2-fault-none* 0 (fn2-sim-now fn2-sim) nil
                 fn2-core fn2-sim fn2-own))
              (t (fn2-sim-complete slot *fn2-fault-none* 0 fn2-core fn2-sim fn2-own))))
       (verdict (if (= (fn2-sim-active slot fn2-sim) 1)
                    (list :fail :liveness-adapter-would-block slot) :pass))
       (fn2-sim (fn2-sim-clock (+ 1 (fn2-sim-now fn2-sim)) *fn2-fault-none* fn2-sim))
       (fn2-core (fn2-sim-post-clock (fn2-sim-now fn2-sim) (fn2-sim-real fn2-sim) fn2-core)))
    (mv verdict (mod (+ 1 slot) (fn2-sim-rows fn2-sim)) fn2-core fn2-sim fn2-own)))
(in-theory (disable fn2-echo-live-advance))

 ; Physical effects are counted by the adapter, at their actual landing.
(defun fn2-echo-observed-advance (allow stats fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil))
  (mv-let (completed fn2-core fn2-sim fn2-own)
    (fn2-sim-advance-with-clients nil allow fn2-core fn2-sim fn2-own)
    (declare (ignore completed))
    (mv stats fn2-core fn2-sim fn2-own)))
(in-theory (disable fn2-echo-observed-advance))

(defun fn2-echo-storage-counts (ids names fn2-sim)
  (declare (xargs :stobjs fn2-sim :verify-guards nil))
  (if (atom ids) nil
    (cons (list (nth (car ids) names) :applied (fn2-sim-hitsi (car ids) fn2-sim))
          (fn2-echo-storage-counts (cdr ids) names fn2-sim))))
(in-theory (disable fn2-echo-storage-counts))
