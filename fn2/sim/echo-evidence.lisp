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
    :client-disconnect :unattributed))
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
         (q (max 1 (min 4096 (min (fn2-profile-run-bytes profile)
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
               (fn2-sim-echo-accept slot 26 (fn2-u32 (fn2-sim-now fn2-sim)) t fn2-core fn2-sim fn2-own))
              (accept
               (fn2-sim-complete-result slot (fn2-sim-gen slot fn2-sim) *fn2-action-accept*
                 *fn2-event-accept-result* 0 :busy 0 0 26 0 (fn2-sim-now fn2-sim) nil
                 fn2-core fn2-sim fn2-own))
              (t (fn2-sim-complete slot 26 0 fn2-core fn2-sim fn2-own))))
       (verdict (if (= (fn2-sim-active slot fn2-sim) 1)
                    (list :fail :liveness-adapter-would-block slot) :pass))
       (fn2-sim (fn2-sim-clock (+ 1 (fn2-sim-now fn2-sim)) 26 fn2-sim))
       (fn2-core (fn2-sim-post-clock (fn2-sim-now fn2-sim) (fn2-sim-real fn2-sim) fn2-core)))
    (mv verdict (mod (+ 1 slot) (fn2-sim-rows fn2-sim)) fn2-core fn2-sim fn2-own)))
(in-theory (disable fn2-echo-live-advance))

; Read-only preview of the advance's second PRNG draw, using the same PRNG.
; This neither consumes a draw nor changes the safety schedule.
(defun fn2-echo-advance-word (fn2-sim)
  (declare (xargs :stobjs fn2-sim :verify-guards nil))
  (mv-let (ignored a b c d)
    (fn2-prng-next (fn2-sim-s0 fn2-sim) (fn2-sim-s1 fn2-sim)
                  (fn2-sim-s2 fn2-sim) (fn2-sim-s3 fn2-sim))
    (declare (ignore ignored))
    (mv-let (word a b c d) (fn2-prng-next a b c d)
      (declare (ignore a b c d)) word)))
(in-theory (disable fn2-echo-advance-word))

; Which storage fault branches can have an effect at THIS physical boundary?
; Exclude wakes, saved terminal/release cells, cancelled work and sticky dead
; devices. Tear needs a pending unit; repeated device death is not a new effect.
(defun fn2-echo-storage-eligible (slot word fn2-sim)
  (declare (xargs :stobjs fn2-sim :verify-guards nil))
  (let* ((kind (fn2-sim-kind slot fn2-sim))
         (physical (and (= (fn2-sim-active slot fn2-sim) 1)
                        (= (fn2-sim-cancelled slot fn2-sim) 0)))
         (offset (fn2-sim-storage-offset slot fn2-sim))
         (len (fn2-sim-range-len slot fn2-sim)))
    (stobj-let ((fn2-sim-storage (fn2-sim-disk fn2-sim)))
      (eligible)
      (let* ((n (fn2-sim-storage-rows fn2-sim-storage))
             (alive (= (fn2-storage-dead fn2-sim-storage) 0))
             (readp (and physical alive (< 0 len) (= kind *fn2-action-read*)))
             (writep (and physical alive (< 0 len) (= kind *fn2-action-write*)))
             (fencep (and physical alive (= kind *fn2-action-fence*)
                          (fn2-storage-fence-roomp slot fn2-sim-storage))))
        (append (if (< 0 n) '(7) nil)
                (if (and (<= 512 n)
                         (fn2-storage-unit-pendingp (mod word (floor n 512)) fn2-sim-storage)) '(11) nil)
                (if alive '(13) nil)
                (if (member-equal kind (list *fn2-action-read* *fn2-action-write* *fn2-action-fence*)) '(14) nil)
                (if readp '(6) nil)
                (if (and readp (< offset n) (not (= offset (fn2-sim-redirect offset n kind 8)))) '(8) nil)
                (if (and writep (< offset n) (not (= offset (fn2-sim-redirect offset n kind 9)))) '(9) nil)
                (if writep '(12) nil)
                (if (and physical (= kind *fn2-action-write*) (< 0 len)) '(24) nil)
                (if fencep '(23) nil)
                (if (and fencep (eq (fn2-sim-profile-name fn2-sim) :broad)) '(10) nil)))
      eligible)))
(in-theory (disable fn2-echo-storage-eligible))

; The advance records its actual selected fault at the old ring head. Count
; an eligible branch only when its terminal result also witnesses the effect.
(defun fn2-echo-observed-advance (allow stats fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil))
  (b* (((mv found slot) (fn2-sim-next-flight fn2-sim))
       (ring (fn2-sim-ring-head fn2-sim))
       (eligible (if (and found (not (fn2-sim-wake-first-p found slot fn2-sim)))
                     (fn2-echo-storage-eligible slot (fn2-echo-advance-word fn2-sim) fn2-sim) nil))
       ((mv & fn2-core fn2-sim fn2-own) (fn2-sim-echo-advance allow fn2-core fn2-sim fn2-own))
       (fault (fn2-sim-ring-faulti ring fn2-sim))
       (count (fn2-sim-terminal-count slot fn2-sim))
       (reason (fn2-sim-terminal-reason slot fn2-sim))
       (applied (and (member-equal fault eligible)
                     (cond ((member-equal fault '(8 9)) (< 0 count))
                           ((equal fault 6) (= reason *fn2-reason-io*))
                           ((equal fault 12) (= reason *fn2-reason-no-space*))
                           ((equal fault 24) (= (fn2-sim-terminal-outcome slot fn2-sim) *fn2-outcome-short*))
                           (t t)))))
    (mv (if applied (fn2-echo-count fault stats) stats) fn2-core fn2-sim fn2-own)))
(in-theory (disable fn2-echo-observed-advance))

(defun fn2-echo-storage-counts (ids names stats fn2-sim)
  (declare (xargs :stobjs fn2-sim :verify-guards nil))
  (if (atom ids) nil
    (cons (list (nth (car ids) names) :selected (fn2-sim-hitsi (car ids) fn2-sim)
                :applied (fn2-echo-stat (car ids) stats))
          (fn2-echo-storage-counts (cdr ids) names stats fn2-sim))))
(in-theory (disable fn2-echo-storage-counts))
