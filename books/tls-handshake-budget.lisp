; fn: the TLS handshake budget over any traffic (lane tls-handshake-budget,
; 2026-09-29; row W2a of COMPLETE-BEFORE-6.6.0; PKT-639; PRF-986).
;
; The decision the host calls, its limits, state and one-step bound are
; books/tls-handshake-decision.lisp (read its header first).  This book
; proves the bound over ANY sequence of the host's events:
;   KEYSTONE fn-hsb-admits-per-tick-are-bounded: over any sequence of
;     events (any sources, any order, any number) from any state, the
;     handshakes admitted in one tick are at most L (the largest L the
;     events were decided under, so a live change is covered).
;   KEYSTONE fn-hsb-source-admits-are-bounded: from any state, over any
;     sequence of events whose times are nondecreasing and within [T0, T1],
;     one untrusted source is admitted at most N + N x (T1 - T0) / 60,000
;     handshakes.
;
; Host callers: host/owner-host.lisp fn-owner-handshake-admit,
; fn-owner-handshake-done, fn-owner-handshake-leave (called by
; host/native/mux.lisp fnn-mux-begin, fnn-mux-request-handshake,
; fnn-mux-start-waiting-handshake, fnn-mux-finish).

(in-package "ACL2")
(include-book "tls-handshake-decision")

; -----------------------------------------------------------------------------
; The events the host's calls make, and the bound over any sequence of them.
;   (:admit HL TRUSTEDP ADDRESS NOW QUEUEDP)   fn-owner-handshake-admit
;   (:done ID)                                 fn-owner-handshake-done
;   (:leave)                                   fn-owner-handshake-leave

(defun fn-hsb-event (s e)
  (declare (xargs :guard t))
  (cond ((and (consp e) (equal (car e) :admit))
         (fn-hsb-state (fn-hsb-admit s (fn-hsb-at 1 e) (fn-hsb-at 2 e) (fn-hsb-at 3 e)
                                     (fn-hsb-at 4 e) (fn-hsb-at 5 e))))
        ((and (consp e) (equal (car e) :done)) (fn-hsb-done s (fn-hsb-at 1 e)))
        ((and (consp e) (equal (car e) :leave)) (fn-hsb-leave s))
        (t s)))

(defun fn-hsb-admittedp (s e)
  (declare (xargs :guard t))
  (and (consp e) (equal (car e) :admit)
       (equal (fn-hsb-verdict (fn-hsb-admit s (fn-hsb-at 1 e) (fn-hsb-at 2 e) (fn-hsb-at 3 e)
                                            (fn-hsb-at 4 e) (fn-hsb-at 5 e)))
              :admit)))

; The handshakes admitted in tick K over the events ES from S.
(defun fn-hsb-admits-in-tick (k s es)
  (declare (xargs :guard t))
  (if (consp es)
      (+ (if (and (fn-hsb-admittedp s (car es))
                  (equal (fn-hsb-tick (fn-hsb-event s (car es))) (nfix k)))
             1 0)
         (fn-hsb-admits-in-tick k (fn-hsb-event s (car es)) (cdr es)))
    0))

; Every admission event decided under an in-flight limit at most LMAX.
(defun fn-hsb-events-under (lmax es)
  (declare (xargs :guard t))
  (if (consp es)
      (and (or (not (and (consp (car es)) (equal (car (car es)) :admit)))
               (<= (fn-hsb-lim-in-flight (fn-hsb-at 1 (car es))) (nfix lmax)))
           (fn-hsb-events-under lmax (cdr es)))
    t))

(defthm fn-hsb-event-tick-monotone
  (<= (fn-hsb-tick s) (fn-hsb-tick (fn-hsb-event s e)))
  :rule-classes :linear)

(defthm fn-hsb-event-started-in-tick
  (implies (and (consp e) (equal (car e) :admit)
                (equal (fn-hsb-tick (fn-hsb-event s e)) (fn-hsb-tick s)))
           (equal (fn-hsb-started (fn-hsb-event s e))
                  (+ (fn-hsb-started s) (if (fn-hsb-admittedp s e) 1 0)))))

(defthm fn-hsb-event-started-in-a-new-tick
  (implies (< (fn-hsb-tick s) (fn-hsb-tick (fn-hsb-event s e)))
           (equal (fn-hsb-started (fn-hsb-event s e))
                  (if (fn-hsb-admittedp s e) 1 0))))

(defthm fn-hsb-event-started-unchanged-otherwise
  (implies (not (and (consp e) (equal (car e) :admit)))
           (and (equal (fn-hsb-started (fn-hsb-event s e)) (fn-hsb-started s))
                (equal (fn-hsb-tick (fn-hsb-event s e)) (fn-hsb-tick s))
                (not (fn-hsb-admittedp s e)))))

(defthm fn-hsb-admitted-under-the-limit
  (implies (fn-hsb-admittedp s e)
           (< (if (equal (fn-hsb-tick (fn-hsb-event s e)) (fn-hsb-tick s))
                  (fn-hsb-started s)
                0)
              (fn-hsb-lim-in-flight (fn-hsb-at 1 e))))
  :hints (("Goal" :use ((:instance fn-hsb-admit-admits-under-the-limits
                                   (hl (fn-hsb-at 1 e)) (trustedp (fn-hsb-at 2 e))
                                   (address (fn-hsb-at 3 e)) (now (fn-hsb-at 4 e))
                                   (queuedp (fn-hsb-at 5 e)))))))

(in-theory (disable fn-hsb-event fn-hsb-admittedp))

;; The room left in tick K from S: what S already started in it (0 before
;; K; the whole limit once K is past, when nothing more is admitted in it).
(defun fn-hsb-used (k s lmax)
  (declare (xargs :guard t))
  (cond ((equal (fn-hsb-tick s) (nfix k)) (min (fn-hsb-started s) (nfix lmax)))
        ((< (fn-hsb-tick s) (nfix k)) 0)
        (t (nfix lmax))))

(defun fn-hsb-event-under (lmax e)
  (declare (xargs :guard t))
  (or (not (and (consp e) (equal (car e) :admit)))
      (<= (fn-hsb-lim-in-flight (fn-hsb-at 1 e)) (nfix lmax))))

(local
 (defthm fn-hsb-event-step
   (implies (fn-hsb-event-under lmax e)
            (<= (+ (if (and (fn-hsb-admittedp s e)
                            (equal (fn-hsb-tick (fn-hsb-event s e)) (nfix k)))
                       1 0)
                   (fn-hsb-used k s lmax))
                (fn-hsb-used k (fn-hsb-event s e) lmax)))
   :hints (("Goal" :use ((:instance fn-hsb-admitted-under-the-limit)
                         (:instance fn-hsb-event-started-in-tick)
                         (:instance fn-hsb-event-started-in-a-new-tick)
                         (:instance fn-hsb-event-started-unchanged-otherwise)
                         (:instance fn-hsb-event-tick-monotone))))
   :rule-classes nil))

(local
 (defthm fn-hsb-used-bounded
   (<= (fn-hsb-used k s lmax) (nfix lmax))
   :rule-classes :linear))

(defthm fn-hsb-events-under-opens
  (equal (fn-hsb-events-under lmax es)
         (if (consp es)
             (and (fn-hsb-event-under lmax (car es))
                  (fn-hsb-events-under lmax (cdr es)))
           t))
  :rule-classes :definition)

(local
 (defthm fn-hsb-admits-in-tick-general
   (implies (fn-hsb-events-under lmax es)
            (<= (+ (fn-hsb-admits-in-tick k s es) (fn-hsb-used k s lmax))
                (nfix lmax)))
   :hints (("Goal" :induct (fn-hsb-admits-in-tick k s es)
                   :in-theory (disable fn-hsb-used fn-hsb-event-under))
           ("Subgoal *1/1" :use ((:instance fn-hsb-event-step (e (car es))))))
   :rule-classes nil))

; KEYSTONE: the handshakes admitted in any one tick, over any sequence of
; events from any state, are at most L (the largest in-flight limit the
; admissions were decided under).
(defthm fn-hsb-admits-per-tick-are-bounded
  (implies (fn-hsb-events-under lmax es)
           (<= (fn-hsb-admits-in-tick k s es) (nfix lmax)))
  :hints (("Goal" :use fn-hsb-admits-in-tick-general
                  :in-theory (disable fn-hsb-admits-in-tick fn-hsb-events-under)))
  :rule-classes :linear)

; -----------------------------------------------------------------------------
; The table's size over any traffic (GPT-6's 2026-09-29 call: the
; accounting structure is bounded, and the bound resets no source's
; accounting: books/tls-handshake-decision.lisp fn-hsb-table-fullp).

; The state after the events ES from S.
(defun fn-hsb-run (s es)
  (declare (xargs :guard t))
  (if (consp es) (fn-hsb-run (fn-hsb-event s (car es)) (cdr es)) s))

(local
 (defthm fn-hsb-event-buckets-len
   (implies (fn-hsb-event-under lmax e)
            (<= (len (fn-hsb-buckets (fn-hsb-event s e)))
                (max (len (fn-hsb-buckets s)) (* 64 (nfix lmax)))))
   :hints (("Goal" :in-theory (e/d (fn-hsb-event fn-hsb-lim-sources)
                                   (fn-hsb-admit-buckets-len))
            :use ((:instance fn-hsb-admit-buckets-len
                             (hl (fn-hsb-at 1 e)) (trustedp (fn-hsb-at 2 e))
                             (address (fn-hsb-at 3 e)) (now (fn-hsb-at 4 e))
                             (queuedp (fn-hsb-at 5 e))))))
   :rule-classes :linear))

; KEYSTONE: over any sequence of events from any state, the table holds at
; most the larger of the rows it started with and 64 x L (the largest
; in-flight limit the admissions were decided under, so a live change of L
; is covered); the initial state has none.
(defthm fn-hsb-buckets-are-bounded
  (implies (fn-hsb-events-under lmax es)
           (<= (len (fn-hsb-buckets (fn-hsb-run s es)))
               (max (len (fn-hsb-buckets s)) (* 64 (nfix lmax)))))
  :hints (("Goal" :induct (fn-hsb-run s es)
                  :in-theory (disable fn-hsb-event-under)))
  :rule-classes :linear)

; -----------------------------------------------------------------------------
; The per-source bound.  Over events whose times are nondecreasing within
; [T0, T1], decided at one rate N, a source is admitted at most
; N + N x (T1 - T0) / 60,000 handshakes (the bucket's burst and its
; refill), whatever else is offered, from ANY state: a bucket never holds
; more than N x 60,000.  The invariant: 60,000 x (the source's admissions
; from now on) <= (its bucket's level now) + N x (T1 - now).

; The source's bucket level at NOW in the rows.
(defun fn-hsb-eff (rows key rate now)
  (declare (xargs :guard t))
  (fn-hsb-level (fn-hsb-lookup key rows) rate now))

(local (in-theory (enable fn-hsb-lookup fn-hsb-prune fn-hsb-put fn-hsb-drop)))

(local
 (defthm fn-hsb-lookup-of-drop
   (equal (fn-hsb-lookup key (fn-hsb-drop k2 rows))
          (if (equal key k2) nil (fn-hsb-lookup key rows)))))

(local
 (defthm fn-hsb-lookup-of-put
   (equal (fn-hsb-lookup key (fn-hsb-put k2 lv st rows))
          (if (equal key k2) (cons lv st) (fn-hsb-lookup key rows)))))

(local (include-book "arithmetic-5/top" :dir :system))

(local
 (defthm fn-hsb-times-monotone
   (implies (and (natp n) (natp a) (natp b) (<= a b))
            (<= (* n a) (* n b)))
   :hints (("Goal" :nonlinearp t))
   :rule-classes :linear))

(local
 (defthm fn-hsb-level-at-most-cap
   (<= (fn-hsb-level row rate now) (fn-hsb-cap rate))
   :hints (("Goal" :in-theory (enable fn-hsb-level)))
   :rule-classes :linear))

(local
 (defthm fn-hsb-level-natp
   (natp (fn-hsb-level row rate now))
   :hints (("Goal" :in-theory (enable fn-hsb-level fn-hsb-cap)))
   :rule-classes :type-prescription))

(local
 (defthm fn-hsb-eff-at-most-cap
   (<= (fn-hsb-eff rows key rate now) (fn-hsb-cap rate))
   :rule-classes :linear))

(local
 (defthm fn-hsb-eff-natp
   (natp (fn-hsb-eff rows key rate now))
   :rule-classes :type-prescription))

; Refill: from TT to NOW >= TT any row's level rises by at most N x (NOW - TT).
(local
 (defun fn-hsb-dt (stamp now)
   (if (< (nfix stamp) (nfix now)) (- (nfix now) (nfix stamp)) 0)))

(local
 (defthm fn-hsb-dt-grows
   (implies (and (natp tt) (natp now) (<= tt now))
            (and (natp (fn-hsb-dt st now))
                 (natp (fn-hsb-dt st tt))
                 (<= (fn-hsb-dt st now) (+ (fn-hsb-dt st tt) (- now tt)))))
   :rule-classes nil))

(local
 (defthm fn-hsb-level-by-dt
   (equal (fn-hsb-level row rate now)
          (if (consp row)
              (min (fn-hsb-cap rate)
                   (+ (nfix (car row)) (* (nfix rate) (fn-hsb-dt (cdr row) now))))
            (fn-hsb-cap rate)))
   :hints (("Goal" :in-theory (enable fn-hsb-level)))))

(local
 (defthm fn-hsb-dt-self
   (implies (<= (nfix now) (nfix st)) (equal (fn-hsb-dt st now) 0))
   :hints (("Goal" :in-theory (enable fn-hsb-dt)))))

(local (in-theory (disable fn-hsb-dt)))

(local
 (defthm fn-hsb-level-refill
   (implies (and (natp tt) (natp now) (<= tt now) (natp rate))
            (<= (fn-hsb-level row rate now)
                (+ (fn-hsb-level row rate tt) (* rate (- now tt)))))
   :hints (("Goal" :in-theory (disable fn-hsb-cap)
                   :use ((:instance fn-hsb-dt-grows (st (cdr row)))
                         (:instance fn-hsb-times-monotone (n rate)
                                    (a (fn-hsb-dt (cdr row) now))
                                    (b (+ (fn-hsb-dt (cdr row) tt) (- now tt))))
                         (:instance fn-hsb-times-monotone (n rate) (a tt) (b now)))))
   :rule-classes nil))

(local
 (defthm fn-hsb-eff-refill
   (implies (and (natp tt) (natp now) (<= tt now) (natp rate))
            (<= (fn-hsb-eff rows key rate now)
                (+ (fn-hsb-eff rows key rate tt) (* rate (- now tt)))))
   :hints (("Goal" :use ((:instance fn-hsb-level-refill (row (fn-hsb-lookup key rows))))))
   :rule-classes nil))

; Pruning never raises a level: a dropped row was full.
(local
 (defthm fn-hsb-eff-of-prune
   (<= (fn-hsb-eff (fn-hsb-prune rows rate now) key rate now)
       (fn-hsb-eff rows key rate now))
   :hints (("Goal" :induct (fn-hsb-prune rows rate now)
                   :in-theory (e/d (fn-hsb-fullp) (fn-hsb-level fn-hsb-level-by-dt fn-hsb-cap))))
   :rule-classes :linear))

(local
 (defthm fn-hsb-level-of-fresh
   (implies (and (natp lv) (natp now) (<= lv (fn-hsb-cap rate)))
            (equal (fn-hsb-level (cons lv now) rate now) lv))))

(local
 (defthm fn-hsb-eff-of-put
   (implies (and (natp lv) (natp now) (<= lv (fn-hsb-cap rate)))
            (equal (fn-hsb-eff (fn-hsb-put k2 lv now rows) key rate now)
                   (if (equal key k2) lv (fn-hsb-eff rows key rate now))))
   :hints (("Goal" :in-theory (disable fn-hsb-put fn-hsb-cap)))))

(in-theory (disable fn-hsb-eff))

; What an admission does to the buckets.
(defthm fn-hsb-buckets-of-admit
  (equal (fn-hsb-buckets (fn-hsb-state (fn-hsb-admit s hl trustedp address now queuedp)))
         (if (and (equal (fn-hsb-verdict (fn-hsb-admit s hl trustedp address now queuedp)) :admit)
                  (not trustedp))
             (fn-hsb-put (fn-hsb-source-key address)
                         (- (fn-hsb-eff (fn-hsb-buckets s) (fn-hsb-source-key address)
                                        (fn-hsb-lim-rate hl) now)
                            *fn-hsb-window-ms*)
                         (nfix now)
                         (fn-hsb-prune (fn-hsb-buckets s) (fn-hsb-lim-rate hl) now))
           (fn-hsb-buckets s)))
  :hints (("Goal" :in-theory (e/d (fn-hsb-admit fn-hsb-eff) (fn-hsb-level fn-hsb-level-by-dt fn-hsb-lookup fn-hsb-put fn-hsb-prune fn-hsb-cap fn-hsb-lim-sources fn-hsb-lim-queue fn-hsb-table-fullp fn-hsb-len-of-put fn-hsb-len-of-drop fn-hsb-len-of-prune fn-hsb-len-of-drop-when-has fn-hsb-has fn-hsb-drop)))))

(defthm fn-hsb-admit-needs-a-handshake-of-level
  (implies (and (equal (fn-hsb-verdict (fn-hsb-admit s hl trustedp address now queuedp)) :admit)
                (not trustedp))
           (<= *fn-hsb-window-ms*
               (fn-hsb-eff (fn-hsb-buckets s) (fn-hsb-source-key address) (fn-hsb-lim-rate hl) now)))
  :hints (("Goal" :in-theory (e/d (fn-hsb-admit fn-hsb-eff) (fn-hsb-level fn-hsb-level-by-dt fn-hsb-lookup fn-hsb-put fn-hsb-prune fn-hsb-cap fn-hsb-lim-sources fn-hsb-lim-queue fn-hsb-table-fullp fn-hsb-len-of-put fn-hsb-len-of-drop fn-hsb-len-of-prune fn-hsb-len-of-drop-when-has fn-hsb-has fn-hsb-drop))))
  :rule-classes :linear)

(defthm fn-hsb-buckets-of-done-leave
  (and (equal (fn-hsb-buckets (fn-hsb-done s id)) (fn-hsb-buckets s))
       (equal (fn-hsb-buckets (fn-hsb-leave s)) (fn-hsb-buckets s))))

(in-theory (disable fn-hsb-admit fn-hsb-state fn-hsb-verdict fn-hsb-detail))

; The handshakes admitted from untrusted source KEY over the events ES.
(defun fn-hsb-source-admits (key s es)
  (declare (xargs :guard t))
  (if (consp es)
      (+ (if (and (fn-hsb-admittedp s (car es))
                  (not (fn-hsb-at 2 (car es)))
                  (equal (fn-hsb-source-key (fn-hsb-at 3 (car es))) key))
             1 0)
         (fn-hsb-source-admits key (fn-hsb-event s (car es)) (cdr es)))
    0))

; Every admission event decided at rate N, at a time within [PREV, T1] and
; no earlier than the one before it.
(defun fn-hsb-events-timed (es prev t1 n)
  (declare (xargs :guard t))
  (if (consp es)
      (if (and (consp (car es)) (equal (car (car es)) :admit))
          (and (natp (fn-hsb-at 4 (car es)))
               (<= (nfix prev) (fn-hsb-at 4 (car es)))
               (<= (fn-hsb-at 4 (car es)) (nfix t1))
               (equal (fn-hsb-lim-rate (fn-hsb-at 1 (car es))) n)
               (fn-hsb-events-timed (cdr es) (fn-hsb-at 4 (car es)) t1 n))
        (fn-hsb-events-timed (cdr es) prev t1 n))
    t))

; One admission event, for source KEY: its admission is paid from the level.
(local
 (defthm fn-hsb-event-source-step
   (implies (and (consp e) (equal (car e) :admit)
                 (equal (fn-hsb-at 4 e) now) (natp now)
                 (equal (fn-hsb-lim-rate (fn-hsb-at 1 e)) n))
            (<= (+ (if (and (fn-hsb-admittedp s e)
                            (not (fn-hsb-at 2 e))
                            (equal (fn-hsb-source-key (fn-hsb-at 3 e)) key))
                       *fn-hsb-window-ms* 0)
                   (fn-hsb-eff (fn-hsb-buckets (fn-hsb-event s e)) key n now))
                (fn-hsb-eff (fn-hsb-buckets s) key n now)))
   :hints (("Goal" :in-theory (e/d (fn-hsb-event fn-hsb-admittedp)
                                   (fn-hsb-put fn-hsb-prune fn-hsb-lookup fn-hsb-level fn-hsb-cap))
                   :use ((:instance fn-hsb-admit-needs-a-handshake-of-level
                                    (hl (fn-hsb-at 1 e)) (trustedp (fn-hsb-at 2 e))
                                    (address (fn-hsb-at 3 e)) (now (fn-hsb-at 4 e))
                                    (queuedp (fn-hsb-at 5 e)))
                         (:instance fn-hsb-eff-at-most-cap (rows (fn-hsb-buckets s))
                                    (key (fn-hsb-source-key (fn-hsb-at 3 e))) (rate n)))))
   :rule-classes nil))

(local
 (defthm fn-hsb-event-other-step
   (implies (not (and (consp e) (equal (car e) :admit)))
            (and (equal (fn-hsb-buckets (fn-hsb-event s e)) (fn-hsb-buckets s))
                 (not (fn-hsb-admittedp s e))))
   :hints (("Goal" :in-theory (enable fn-hsb-event fn-hsb-admittedp)))))

(local
 (defthm fn-hsb-source-admit-case
   (implies (and (natp tt) (consp e) (equal (car e) :admit)
                 (natp now) (equal (fn-hsb-at 4 e) now) (<= tt now)
                 (equal (fn-hsb-lim-rate (fn-hsb-at 1 e)) n) (natp n)
                 (<= (* *fn-hsb-window-ms* c)
                     (+ (fn-hsb-eff (fn-hsb-buckets (fn-hsb-event s e)) key n now)
                        (* n (- t1 now)))))
            (<= (* *fn-hsb-window-ms*
                   (+ (if (and (fn-hsb-admittedp s e)
                               (not (fn-hsb-at 2 e))
                               (equal (fn-hsb-source-key (fn-hsb-at 3 e)) key))
                          1 0)
                      c))
                (+ (fn-hsb-eff (fn-hsb-buckets s) key n tt) (* n (- t1 tt)))))
   :hints (("Goal" :in-theory (disable fn-hsb-event fn-hsb-admittedp)
                   :use ((:instance fn-hsb-event-source-step)
                         (:instance fn-hsb-eff-refill (rows (fn-hsb-buckets s)) (rate n)))))
   :rule-classes nil))

(local
 (defun fn-hsb-source-induct (s es tt)
   (declare (xargs :verify-guards nil))
   (if (consp es)
       (if (and (consp (car es)) (equal (car (car es)) :admit))
           (fn-hsb-source-induct (fn-hsb-event s (car es)) (cdr es) (fn-hsb-at 4 (car es)))
         (fn-hsb-source-induct (fn-hsb-event s (car es)) (cdr es) tt))
     (list s tt))))

(local
 (defthm fn-hsb-source-admits-general
   (implies (and (natp tt) (fn-hsb-events-timed es tt t1 n) (natp t1) (<= tt t1) (natp n))
            (<= (* *fn-hsb-window-ms* (fn-hsb-source-admits key s es))
                (+ (fn-hsb-eff (fn-hsb-buckets s) key n tt) (* n (- t1 tt)))))
   :hints (("Goal" :induct (fn-hsb-source-induct s es tt)
                   :in-theory (disable fn-hsb-event fn-hsb-admittedp))
           ("Subgoal *1/1" :use ((:instance fn-hsb-source-admit-case (e (car es))
                                            (now (fn-hsb-at 4 (car es)))
                                            (c (fn-hsb-source-admits key (fn-hsb-event s (car es))
                                                                     (cdr es))))))
           ("Subgoal *1/2" :use ((:instance fn-hsb-event-other-step (e (car es)))))
           ("Subgoal *1/3" :use ((:instance fn-hsb-times-monotone (n n) (a tt) (b t1)))))
   :rule-classes nil))

(local
 (defthm fn-hsb-events-timed-of-nfix
   (equal (fn-hsb-events-timed es (nfix t0) (nfix t1) n)
          (fn-hsb-events-timed es t0 t1 n))))

; KEYSTONE: from ANY state, over any events whose times are nondecreasing
; within [T0, T1], decided at rate N, one untrusted source is admitted at
; most N + N x (T1 - T0) / 60,000 handshakes (stated in token-milliseconds;
; the times are the recorded clock's naturals, as fn-hsb-events-timed reads
; them).
(defthm fn-hsb-source-admits-are-bounded
  (implies (and (fn-hsb-events-timed es t0 t1 n) (<= (nfix t0) (nfix t1)) (natp n))
           (<= (* *fn-hsb-window-ms* (fn-hsb-source-admits key s es))
               (+ (* n *fn-hsb-window-ms*) (* n (- (nfix t1) (nfix t0))))))
  :hints (("Goal" :in-theory (disable fn-hsb-source-admits fn-hsb-events-timed)
                  :use ((:instance fn-hsb-source-admits-general (tt (nfix t0)) (t1 (nfix t1)))
                        (:instance fn-hsb-events-timed-of-nfix)
                        (:instance fn-hsb-eff-at-most-cap (rows (fn-hsb-buckets s)) (rate n)
                                   (now (nfix t0)))))
          ("Goal'" :in-theory (enable fn-hsb-cap))))
