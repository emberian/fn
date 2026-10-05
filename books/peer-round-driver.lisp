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

; ---------------------------------------------------------------------------
; SCEN-FEED-PACE (lane feed-pace, 2026-10-05): the push worker's pace.
;
; scenarios-2 measured an outbound feed to a streaming peer that answers at
; once at 2.4 articles a second (tests/test_native_peering.py, the
; 1,100-article case: 462 s at batch 6).  The worker ran ONE
; fn-prd-feed-action per link per round and slept a fixed 1/20 s after every
; round that did anything, about eight rounds an article.  Now the worker
; (host/native/feed-service.lisp fnn-feed-worker-loop) pumps each link until
; its next action waits on the kernel or its quantum is spent, and asks this
; how long to wait, and on what.  Each link reports (ACTION BLOCKED AWAITING):
;   ACTION    fn-prd-feed-action's answer for the link after its pump, or
;             :dial for a link with no connection;
;   BLOCKED   the readiness its last physical attempt reported: :input or
;             :output (a read or a write that would block, a handshake's
;             WANT, a connect still in progress), nil when it progressed;
;   AWAITING  the peer owes the link an answer: a reply to a command that has
;             left, the greeting, a handshake (the link's deadline is armed).
; A scheduling decision only: every offer, reply and loss stays the feed
; port's, and the 600 s reply deadline stays fn-prd-feed-action's.

; The most actions one link takes in a round while they progress.  Fairness,
; not a data cap: an unfinished link continues at once in the next round,
; after every other link has had its turn.
(defun fn-prd-feed-quantum ()
  (declare (xargs :guard t))
  32)

; The I/O poll: the first wait of a quiet worker, the floor of every wait,
; and how often a worker waiting on its sockets looks at the commit count.
(defun fn-prd-feed-poll-ms ()
  (declare (xargs :guard t))
  50)

; S145 (lane served-live): quiet rounds at the poll before the wait doubles.
(defun fn-prd-feed-busy-rounds ()
  (declare (xargs :guard t))
  20)

(defun fn-prd-feed-link-action (link)
  (declare (xargs :guard t))
  (if (consp link) (car link) nil))

(defun fn-prd-feed-link-blocked (link)
  (declare (xargs :guard t))
  (if (and (consp link) (consp (cdr link))) (cadr link) nil))

(defun fn-prd-feed-link-awaiting (link)
  (declare (xargs :guard t))
  (if (and (consp link) (consp (cdr link)) (consp (cddr link))) (caddr link) nil))

; What one link waits on: :now (it can act without waiting: an offer to ask
; for, a reply already read, a write the kernel has not refused), :input or
; :output (its socket's readiness), or :commit (nothing is owed to it and
; nothing is in progress: it waits for an article, a retry coming due or a
; redial, which a commit or the clock brings).  A read that found nothing on
; a link the peer owes nothing is :commit, not :input: an idle connection is
; not a busy poll (S145).
(defun fn-prd-feed-link-wait (link)
  (declare (xargs :guard t))
  (let ((action (fn-prd-feed-link-action link))
        (blocked (fn-prd-feed-link-blocked link)))
    (cond ((member-equal action '(:offer :reply :connected :timeout)) :now)
          ((member-equal action '(:write :connect :tls :read))
           (cond ((not (member-equal blocked '(:input :output))) :now)
                 ((or (fn-prd-feed-link-awaiting link) (not (equal action :read)))
                  blocked)
                 (t :commit)))
          (t :commit))))

(defun fn-prd-feed-wait-rank (wait)
  (declare (xargs :guard t))
  (cond ((equal wait :now) 2)
        ((member-equal wait '(:input :output)) 1)
        (t 0)))

; The most urgent wait of LINKS (BEST so far): 2 :now, 1 a socket, 0 the
; commit signal.  Tail recursive: LINKS are the operator's peers.
(defun fn-prd-feed-round-rank (links best)
  (declare (xargs :guard t))
  (if (consp links)
      (fn-prd-feed-round-rank
       (cdr links) (max (nfix best) (fn-prd-feed-wait-rank (fn-prd-feed-link-wait (car links)))))
    (nfix best)))

; The least positive wait past NOW until one of DIALS (the next-dial times of
; the links with no connection) comes due, or BEST; nil when none is ahead.
(defun fn-prd-feed-dial-wait (dials now best)
  (declare (xargs :guard t))
  (if (consp dials)
      (fn-prd-feed-dial-wait
       (cdr dials) now
       (let ((wait (- (nfix (car dials)) (nfix now))))
         (if (and (posp wait) (or (not (natp best)) (< wait best))) wait best)))
    best))

; A quiet worker's wait: the poll for its first busy rounds, then doubling
; (100, 200, 400, 800 ms) to fn-prd-idle-max-ms.  This was the host's
; fnn-feed-idle-seconds; it is decided here now.
(defun fn-prd-feed-quiet-ms (idle)
  (declare (xargs :guard t))
  (let ((past (- (nfix idle) (fn-prd-feed-busy-rounds))))
    (cond ((< past 0) (fn-prd-feed-poll-ms))
          ((equal past 0) 100)
          ((equal past 1) 200)
          ((equal past 2) 400)
          ((equal past 3) 800)
          (t (fn-prd-idle-max-ms)))))

(local
 (defthm fn-prd-feed-quiet-ms-is-bounded
   (and (<= (fn-prd-feed-poll-ms) (fn-prd-feed-quiet-ms idle))
        (<= (fn-prd-feed-quiet-ms idle) (fn-prd-idle-max-ms)))
   :rule-classes :linear))

; KEYSTONE SUBJECT (host/native/feed-service.lisp fnn-feed-worker-loop).
; The round's wait: (:now 0) when any link can act; else (:poll MS), waiting
; on the sockets ACL2 named (fn-prd-feed-link-wait) and the commit count, or
; (:signal MS), waiting on the owner's commit signal alone.  IDLE counts the
; rounds since one progressed.  MS never passes a redial.
(defun fn-prd-feed-pause (links idle dials now)
  (declare (xargs :guard t))
  (let ((rank (fn-prd-feed-round-rank links 0)))
    (if (equal rank 2)
        (list :now 0)
      (let ((ms (fn-prd-feed-quiet-ms idle))
            (due (fn-prd-feed-dial-wait dials now nil)))
        (list (if (equal rank 1) :poll :signal)
              (if (natp due) (min ms (max (fn-prd-feed-poll-ms) due)) ms))))))

(local
 (defthm fn-prd-feed-round-rank-at-least-best
   (<= (nfix best) (fn-prd-feed-round-rank links best))
   :rule-classes :linear))

(local
 (defthm fn-prd-feed-round-rank-at-least-each-link
   (implies (member-equal link links)
            (<= (fn-prd-feed-wait-rank (fn-prd-feed-link-wait link))
                (fn-prd-feed-round-rank links best)))
   :hints (("Goal" :induct (fn-prd-feed-round-rank links best)
            :in-theory (disable fn-prd-feed-link-wait fn-prd-feed-wait-rank)))))

(local
 (defthm fn-prd-feed-round-rank-at-most-two
   (implies (<= (nfix best) 2)
            (and (natp (fn-prd-feed-round-rank links best))
                 (<= (fn-prd-feed-round-rank links best) 2)))
   :hints (("Goal" :induct (fn-prd-feed-round-rank links best)))))

(local
 (defthm fn-prd-feed-dial-wait-below-best
   (implies (natp best)
            (and (natp (fn-prd-feed-dial-wait dials now best))
                 (<= (fn-prd-feed-dial-wait dials now best) best)))
   :hints (("Goal" :induct (fn-prd-feed-dial-wait dials now best)))))

(local
 (defthm fn-prd-feed-dial-wait-below-each-dial
   (implies (and (member-equal dial dials) (< (nfix now) (nfix dial)))
            (and (natp (fn-prd-feed-dial-wait dials now best))
                 (<= (fn-prd-feed-dial-wait dials now best) (- (nfix dial) (nfix now)))))
   :hints (("Goal" :induct (fn-prd-feed-dial-wait dials now best)))))

; KEYSTONE (SCEN-FEED-PACE): the feed never sleeps while an article can
; leave.  A link that may have a deliverable article (its action is :offer:
; it is ready and the feed port has not been asked since something changed),
; that holds a reply already read, or whose command is retained for a socket
; the kernel has not refused (:write, last attempt not blocked) makes the
; round's wait (:now 0).
(defthm fn-prd-feed-never-sleeps-while-an-article-can-leave
  (implies (and (member-equal link links)
                (or (member-equal (fn-prd-feed-link-action link) '(:offer :reply))
                    (and (equal (fn-prd-feed-link-action link) :write)
                         (not (member-equal (fn-prd-feed-link-blocked link)
                                            '(:input :output))))))
           (equal (fn-prd-feed-pause links idle dials now) '(:now 0)))
  :hints (("Goal" :in-theory (disable fn-prd-feed-round-rank-at-least-each-link
                                      fn-prd-feed-round-rank-at-most-two
                                      fn-prd-feed-round-rank fn-prd-feed-dial-wait
                                      fn-prd-feed-quiet-ms)
           :use ((:instance fn-prd-feed-round-rank-at-least-each-link (best 0))
                 (:instance fn-prd-feed-round-rank-at-most-two (best 0))))))

; KEYSTONE (a waiting worker neither spins nor stalls): every wait that is
; not (:now 0) is on the sockets or the commit signal, for at least the poll
; and at most fn-prd-idle-max-ms ...
(defthm fn-prd-feed-pause-is-bounded
  (let ((pause (fn-prd-feed-pause links idle dials now)))
    (or (equal pause '(:now 0))
        (and (member-equal (car pause) '(:poll :signal))
             (<= (fn-prd-feed-poll-ms) (cadr pause))
             (<= (cadr pause) (fn-prd-idle-max-ms)))))
  :rule-classes nil)

; ... a link waiting on its socket is never left to the commit signal alone
; (its reply would wait for the timer) ...
(defthm fn-prd-feed-pause-polls-a-waiting-socket
  (implies (and (member-equal link links)
                (member-equal (fn-prd-feed-link-wait link) '(:input :output)))
           (not (equal (car (fn-prd-feed-pause links idle dials now)) :signal)))
  :hints (("Goal" :in-theory (disable fn-prd-feed-round-rank-at-least-each-link
                                      fn-prd-feed-round-rank-at-most-two
                                      fn-prd-feed-round-rank fn-prd-feed-link-wait
                                      fn-prd-feed-dial-wait fn-prd-feed-quiet-ms)
           :use ((:instance fn-prd-feed-round-rank-at-least-each-link (best 0))
                 (:instance fn-prd-feed-round-rank-at-most-two (best 0))))))

; ... and never sleeps past a redial that is ahead.
(defthm fn-prd-feed-pause-never-sleeps-past-a-redial
  (implies (and (member-equal dial dials) (< (nfix now) (nfix dial)))
           (<= (cadr (fn-prd-feed-pause links idle dials now))
               (max (fn-prd-feed-poll-ms) (- (nfix dial) (nfix now)))))
  :hints (("Goal" :in-theory (disable fn-prd-feed-dial-wait-below-each-dial
                                      fn-prd-feed-dial-wait)
           :use ((:instance fn-prd-feed-dial-wait-below-each-dial (best nil))))))
