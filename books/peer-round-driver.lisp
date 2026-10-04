; Resumable pull/catch-up driver. Protocol/session/cursor decisions remain
; the existing session machines'. This book chooses which retained round
; gets one I/O quantum and the order of its already-authored effects/events.
(in-package "ACL2")
(include-book "feed-wire-input")
(include-book "scheduler-peers")

; Keys are ACL2's pair (kind peer), never a host-derived identity.
(defun fn-prd-key (kind peer)
  (declare (xargs :guard t))
  (list kind peer))

; The remaining sweep is captured, so one trickling round cannot repeatedly
; select itself before healthy pull/catch-up rounds in that same sweep.
(defun fn-prd-select (active remaining)
  (declare (xargs :guard (true-listp active)))
  (if (consp remaining)
      (if (member-equal (car remaining) active)
          (list (car remaining) (cdr remaining))
        (fn-prd-select active (cdr remaining)))
    (list nil nil)))

(defun fn-prd-sweep (active remaining)
  (declare (xargs :guard (true-listp active)))
  (if (consp remaining)
      (if (member-equal (car remaining) active)
          (cons (car remaining) (fn-prd-sweep active (cdr remaining)))
        (fn-prd-sweep active (cdr remaining)))
    nil))

; KEYSTONE PRF-1260: every retained admitted key in a stable sweep is visited,
; in order, without being skipped by driver selection. This
; assumes each physical I/O attempt returns; it is not a resolver/time bound.
(defthm fn-prd-sweep-visits-all-admitted-rounds
  (implies (and (true-listp remaining) (subsetp-equal remaining active))
           (equal (fn-prd-sweep active remaining) remaining)))

; A pending partial write/handshake/local continuation precedes later effects.
; Wait readiness never feeds a lost event or closes the protocol state.
; ROUND-DEADLINE bounds the whole round (S054/S067, the interim approved
; bound): an unfinished round past it is lost, whatever it waits on, so a
; peer that trickles or a local verdict that never completes cannot hold its
; flight. The session machines answer the loss by failing the round with its
; cursor at the last journaled position; nothing past that is acknowledged.
(defun fn-prd-action (done effects events io now deadline round-deadline)
  (declare (xargs :guard t))
  (cond ((and (not done) (natp round-deadline) (<= round-deadline (nfix now)))
         (list :lost :round-deadline))
        (io (if (and (natp deadline) (<= deadline (nfix now)))
                (list :lost :timeout)
              (list :io io)))
        ((consp effects) (list :effect (car effects)))
        ((consp events) (list :event (car events)))
        (done (list :finish))
        (t (list :read))))

; The round's wall budget, decided here: local policy, a scheduling bound and
; not a data cap. A round that runs out resumes from its journaled cursor at
; the next due time, so any batch that fits makes progress.
(defun fn-prd-round-seconds ()
  (declare (xargs :guard t))
  600)

(defun fn-prd-round-deadline (now)
  (declare (xargs :guard t))
  (+ (nfix now) (* 1000 (fn-prd-round-seconds))))

; KEYSTONE (a round is bounded in time). Past its deadline an unfinished round
; has exactly one action: it is lost. No read, write, effect or event of it
; runs, so its flight ends within one driver selection of the deadline.
(defthm fn-prd-round-past-deadline-is-lost
  (implies (and (not done) (natp round-deadline) (<= round-deadline (nfix now)))
           (equal (fn-prd-action done effects events io now deadline round-deadline)
                  '(:lost :round-deadline))))

; Before its deadline the round's action is the per-I/O driver's, unchanged.
(defthm fn-prd-round-before-deadline-is-unchanged
  (implies (or done (not (natp round-deadline)) (< (nfix now) round-deadline))
           (equal (fn-prd-action done effects events io now deadline round-deadline)
                  (fn-prd-action done effects events io now deadline nil))))

(defun fn-prd-deadline (now seconds)
  (declare (xargs :guard t))
  (+ (nfix now) (* 1000 (nfix seconds))))

(defun fn-prd-resume-at (now ms)
  (declare (xargs :guard t))
  (+ (nfix now) (nfix ms)))

(defun fn-prd-read-limit (session-limit)
  (declare (xargs :guard t))
  (if (posp session-limit)
      (min session-limit *fn-feed-wire-input-max-chunk-octets*)
    *fn-feed-wire-input-max-chunk-octets*))

(defun fn-prd-write-end (offset total)
  (declare (xargs :guard t))
  (min (nfix total) (+ (nfix offset) *fn-feed-wire-input-max-chunk-octets*)))

; The most driver actions one selected round takes before the sweep moves on,
; while they progress (a wait ends its selection at once). A scheduling
; quantum, not a data cap: an unfinished round resumes at its next selection.
(defun fn-prd-flight-quantum ()
  (declare (xargs :guard t))
  256)

(defun fn-prd-idle-ms ()
  (declare (xargs :guard t))
  10)

; S145 for the pull worker (tests/test_native_feed_idle.py on d5b0b9100: 2,466
; owner transit holds in 13 s, the worker re-reading both plan tables every
; 10 ms with no round admitted).  The pause after a sweep in which no round
; progressed: while a round is admitted, the I/O poll fn-prd-idle-ms; with
; none, until the earliest free scheduled row of the pull and catch-up tables
; is due, at least fn-prd-idle-ms and at most fn-prd-idle-max-ms.  The host
; sleeps it on the owner's commit signal (host/native/pull-service.lisp
; fnn-pull-idle-wait), so a commit, a configuration change and the stop end it
; early.  A scheduling bound, not a data cap.
(defun fn-prd-idle-max-ms ()
  (declare (xargs :guard t))
  1000)

; A row (PEER NEXT INTERVAL BUSY) that will start a round once NEXT passes.
(defun fn-prd-row-schedulablep (row)
  (declare (xargs :guard t))
  (and (consp row)
       (posp (fn-sched-pull-interval (cdr row)))
       (not (fn-sched-pull-busy (cdr row)))))

(defun fn-prd-row-wait (row now)
  (declare (xargs :guard t))
  (nfix (- (fn-sched-pull-next (if (consp row) (cdr row) nil)) (nfix now))))

; The least wait past NOW until a schedulable row of TBL is due (BEST so far),
; nil when none is.  Tail recursive: the tables hold the operator's peers.
(defun fn-prd-next-due-wait (tbl now best)
  (declare (xargs :guard t))
  (if (consp tbl)
      (fn-prd-next-due-wait
       (cdr tbl) now
       (if (fn-prd-row-schedulablep (car tbl))
           (if (natp best)
               (min (fn-prd-row-wait (car tbl) now) best)
             (fn-prd-row-wait (car tbl) now))
         best))
    best))

; KEYSTONE SUBJECT (host/native/pull-service.lisp fnn-pull-worker).
(defun fn-prd-pause-ms (active tbl now)
  (declare (xargs :guard t))
  (if (consp active)
      (fn-prd-idle-ms)
    (let ((wait (fn-prd-next-due-wait tbl now nil)))
      (if (natp wait)
          (max (fn-prd-idle-ms) (min (fn-prd-idle-max-ms) wait))
        (fn-prd-idle-max-ms)))))

(local
 (defthm fn-prd-next-due-wait-below-best
   (implies (natp best)
            (and (natp (fn-prd-next-due-wait tbl now best))
                 (<= (fn-prd-next-due-wait tbl now best) best)))
   :hints (("Goal" :induct (fn-prd-next-due-wait tbl now best)))))

(local
 (defthm fn-prd-next-due-wait-below-each-row
   (implies (and (member-equal row tbl) (fn-prd-row-schedulablep row))
            (and (natp (fn-prd-next-due-wait tbl now best))
                 (<= (fn-prd-next-due-wait tbl now best) (fn-prd-row-wait row now))))
   :hints (("Goal" :induct (fn-prd-next-due-wait tbl now best)
            :in-theory (disable fn-prd-row-schedulablep fn-prd-row-wait)))))

; KEYSTONE (an idle pull worker is not a busy poll, and never a stall): every
; pause is at least the I/O poll and at most a second ...
(defthm fn-prd-pause-is-bounded
  (and (<= (fn-prd-idle-ms) (fn-prd-pause-ms active tbl now))
       (<= (fn-prd-pause-ms active tbl now) (fn-prd-idle-max-ms)))
  :rule-classes nil)

; ... a worker with a round admitted keeps the I/O poll ...
(defthm fn-prd-pause-polls-while-a-round-runs
  (implies (consp active)
           (equal (fn-prd-pause-ms active tbl now) (fn-prd-idle-ms))))

; ... and an idle worker never sleeps past the time a schedulable row is due.
(defthm fn-prd-pause-never-sleeps-past-a-due-round
  (implies (and (member-equal row tbl) (fn-prd-row-schedulablep row))
           (<= (fn-prd-pause-ms active tbl now)
               (max (fn-prd-idle-ms) (fn-prd-row-wait row now))))
  :hints (("Goal" :in-theory (disable fn-prd-row-schedulablep fn-prd-row-wait
                                      fn-prd-next-due-wait
                                      fn-prd-next-due-wait-below-each-row)
           :use ((:instance fn-prd-next-due-wait-below-each-row (best nil))))))

; These are concrete observations of named transport failure classes.
; A core/store/unknown condition is never silently turned into round loss.
(defun fn-prd-loss-class-ok (stage class)
  (declare (xargs :guard t))
  (if (equal stage :local)
      (equal class "fnn-store-error")
    (if (member-equal class '("fnn-os-error" "fnn-peer-dial-error"
                             "fnn-tls-unavailable" "fnn-tls-config-error"
                             "fnn-tls-handshake-error" "fnn-tls-verify-error"
                             "fnn-tls-io-error")) t nil)))

; Push links retain one output and the ACL2 framer's suffix. This action
; selection orders physical work without copying the feed reply machine.
; DEADLINE is the link's one retained wait: a connect, handshake or output
; progress window while PHASE or OUTPUTP holds, and otherwise the wait for
; the peer's next reply (the greeting, or the answer to a command that has
; left; the host arms it with fn-prd-round-deadline and clears it at the
; next complete reply).  Retained input is drained first: a reply already
; read is never discarded by its own deadline.  Past the deadline the link
; is lost, so a peer that never answers (a hung server, a path gone
; half-open after the write) cannot hold its link and its in-flight entry
; until a restart (read-peer 2026-10-04).
(defun fn-prd-feed-action (phase outputp drainp offerp now deadline)
  (declare (xargs :guard t))
  (let ((expired (and (natp deadline) (<= deadline (nfix now)))))
    (cond ((or phase outputp)
           (if expired :timeout (cond (phase phase) (t :write))))
          (drainp :reply)
          (expired :timeout)
          (offerp :offer)
          (t :read))))

; Preserve the feed's existing per-quantum deadline while smaller physical
; write attempts yield to other peers. Successful prefixes never reset it.
(defun fn-prd-write-quantum-end (offset total quantum)
  (declare (xargs :guard t))
  (min (nfix total) (+ (nfix offset) (nfix quantum))))
