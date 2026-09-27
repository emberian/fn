; fn: the decision journal -- the readings that store nothing, recorded so
; that replay reproduces the decisions made from them (lane time-model-2,
; 2026-09-27, slice 2 of planning/design-time-model-2026-09-27.md section
; 3.7; PRF-314).
;
; Ember's rule: the fold is a pure function of the log; a clock reading is
; an event the host appends, never a call made inside an owner step.  A
; decision that reaches durable state rides the record log.  A decision
; that stores NOTHING -- the disk's mode, a POST refused try-later at its
; command or after its article, a mutating control request answered busy,
; the posters told uncertain at the stall, the owner's own clock reading
; for a served read -- is made from the scheduler's value of
; books/owner-time-model.lisp, and every event that value takes is one
; journal entry (fn-otm-recorded-time-is-monotone: each advances JSEQ by
; one).  The host renders the entry here (fn-otm-disk-step) and offers it to
; the service-log writer thread, which appends it to STORE/journal/
; decisions.fnj: never on the owner, never waiting on the disk the journal
; may be measuring, bounded by ACL2's sink (books/log-sink.lisp; a line it
; drops is counted, and shows here as a gap in JSEQ).
;
; What this book proves (KEYSTONE fn-otm-journal-determines-the-decisions):
; for any run of the host's calls -- disk events, notes, and the gate's
; picks, observations and commit events interleaved in any order -- the
; journal the run writes, read back by fn-otm-journal-read and replayed by
; fn-otm-replay from the same start, AGREES (every recomputed word equals
; the journaled one, no gap) and ends at the run's disk and clock; and every
; decision the host asks of the value (admission, mode, wait, reply lines,
; health's lines) reads only that disk and clock
; (fn-otm-decisions-read-only-the-journal-state).  So the journal and the
; record log together determine every decision: the record log the durable
; state (lane proto-determinism's audit), the journal the rest.
;
; What the process loses if it dies with entries unflushed: those entries,
; and with them the ability to replay the decisions after the last flushed
; one -- nothing durable.  Each of those decisions stored nothing (a
; disk event keeps the pipeline, fn-otm-disk-event-keeps-the-pipeline; a
; shed stores nothing, fn-own-outcome's :refused), so no record, no
; acknowledgement and no reply that promised durability depends on an
; unwritten entry.  The next run starts a new journal segment (a start
; entry, sequence 0) from fn-otm-init.
(in-package "ACL2")
(include-book "owner-time-model")
(local (include-book "arithmetic-5/top" :dir :system))

; -----------------------------------------------------------------------------
; The line codec: an entry is a list of naturals, written as their decimal
; digits separated by one space and ended by LF.  A file is the entries'
; lines in order.

(defun fn-otm-dec-octets (n)
  ; the decimal digits of a positive N, most significant first; nil for 0
  (declare (xargs :guard t :measure (nfix n)))
  (if (posp n)
      (append (fn-otm-dec-octets (floor n 10)) (list (+ 48 (mod n 10))))
    nil))

(defun fn-otm-nat-octets (n)
  (declare (xargs :guard t))
  (if (posp n) (fn-otm-dec-octets n) (list 48)))

(defun fn-otm-jline (ns)
  (declare (xargs :guard t))
  (if (consp ns)
      (append (fn-otm-nat-octets (car ns))
              (if (consp (cdr ns)) (cons 32 (fn-otm-jline (cdr ns))) (list 10)))
    nil))

(defun fn-otm-jlines (entries)
  (declare (xargs :guard t))
  (if (consp entries)
      (append (fn-otm-jline (car entries)) (fn-otm-jlines (cdr entries)))
    nil))

(defun fn-otm-revonto (x acc)
  (declare (xargs :guard t))
  (if (consp x) (fn-otm-revonto (cdr x) (cons (car x) acc)) acc))

; The reader: one pass over the octets.  ACC the number being read (nil:
; no digit since the last separator), FIELDS the entry's numbers so far,
; reversed, ENTRIES the entries so far, reversed.  Answers (mv STATUS
; ENTRIES): :whole, :torn (the last line has no LF: a line the writer had
; not finished when the process died, dropped) or :malformed (an octet
; that is not a digit, a space or an LF, or an empty field).
(defun fn-otm-jparse (xs acc fields entries)
  (declare (xargs :guard t :measure (len xs)))
  (if (consp xs)
      (let ((o (car xs)))
        (cond ((and (natp o) (<= 48 o) (<= o 57))
               (fn-otm-jparse (cdr xs) (+ (* 10 (nfix acc)) (- o 48)) fields entries))
              ((and (equal o 32) acc)
               (fn-otm-jparse (cdr xs) nil (cons acc fields) entries))
              ((and (equal o 10) acc)
               (fn-otm-jparse (cdr xs) nil nil (cons (fn-otm-revonto fields (list acc)) entries)))
              (t (mv :malformed (fn-otm-revonto entries nil)))))
    (mv (if (or acc fields) :torn :whole) (fn-otm-revonto entries nil))))

(defun fn-otm-journal-read (octets)
  (declare (xargs :guard t))
  (mv-let (status entries) (fn-otm-jparse octets nil nil nil)
    (declare (ignore status))
    entries))

(defun fn-otm-nat-lists-p (entries)
  (declare (xargs :guard t))
  (if (consp entries)
      (and (nat-listp (car entries)) (consp (car entries))
           (fn-otm-nat-lists-p (cdr entries)))
    (null entries)))

;; The codec's round trip.
(local
 (defun fn-otm-digits-value (xs acc)
   (if (consp xs)
       (fn-otm-digits-value (cdr xs) (+ (* 10 (nfix acc)) (- (car xs) 48)))
     acc)))

(local
 (defun fn-otm-digit-octets-p (xs)
   (if (consp xs)
       (and (natp (car xs)) (<= 48 (car xs)) (<= (car xs) 57)
            (fn-otm-digit-octets-p (cdr xs)))
     t)))

(local
 (defthm fn-otm-jparse-of-digits
   (implies (and (fn-otm-digit-octets-p xs) (consp xs))
            (equal (fn-otm-jparse (append xs rest) acc fields entries)
                   (fn-otm-jparse rest (fn-otm-digits-value xs acc) fields entries)))))

(local
 (defthm fn-otm-digit-octets-p-of-append
   (equal (fn-otm-digit-octets-p (append a b))
          (and (fn-otm-digit-octets-p a) (fn-otm-digit-octets-p b)))))

(local
 (defthm fn-otm-digits-value-of-append
   (equal (fn-otm-digits-value (append a b) acc)
          (fn-otm-digits-value b (fn-otm-digits-value a acc)))))

(local
 (defthm fn-otm-dec-octets-digits
   (fn-otm-digit-octets-p (fn-otm-dec-octets n))))

(local
 (defthm fn-otm-dec-octets-value
   (equal (fn-otm-digits-value (fn-otm-dec-octets n) 0) (nfix n))))

(local
 (defthm fn-otm-digits-value-of-nil
   (implies (consp xs)
            (equal (fn-otm-digits-value xs nil) (fn-otm-digits-value xs 0)))
   :hints (("Goal" :expand ((fn-otm-digits-value xs nil) (fn-otm-digits-value xs 0))))))

(local
 (defthm fn-otm-dec-octets-consp
   (implies (posp n) (consp (fn-otm-dec-octets n)))))

(local
 (defthm fn-otm-nat-octets-facts
   (and (fn-otm-digit-octets-p (fn-otm-nat-octets n))
        (consp (fn-otm-nat-octets n))
        (equal (fn-otm-digits-value (fn-otm-nat-octets n) nil) (nfix n)))
   :hints (("Goal" :in-theory (disable fn-otm-dec-octets fn-otm-digits-value)))))

(local (in-theory (disable fn-otm-nat-octets)))

(local
 (defthm fn-otm-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(local
 (defun fn-otm-jline-ind (ns fields)
   (if (consp ns)
       (if (consp (cdr ns)) (fn-otm-jline-ind (cdr ns) (cons (car ns) fields)) fields)
     fields)))

(local
 (defthm fn-otm-jparse-of-jline
   (implies (and (nat-listp ns) (consp ns))
            (equal (fn-otm-jparse (append (fn-otm-jline ns) rest) nil fields entries)
                   (fn-otm-jparse rest nil nil (cons (fn-otm-revonto fields ns) entries))))
   :hints (("Goal" :induct (fn-otm-jline-ind ns fields)))))

(local
 (defun fn-otm-jlines-ind (es entries)
   (if (consp es) (fn-otm-jlines-ind (cdr es) (cons (car es) entries)) entries)))

(local
 (defthm fn-otm-jparse-of-jlines
   (implies (fn-otm-nat-lists-p es)
            (equal (fn-otm-jparse (fn-otm-jlines es) nil nil entries)
                   (mv :whole (fn-otm-revonto entries es))))
   :hints (("Goal" :induct (fn-otm-jlines-ind es entries)
            :in-theory (disable fn-otm-jparse-of-jline))
           ("Subgoal *1/1" :use ((:instance fn-otm-jparse-of-jline
                                            (ns (car es)) (rest (fn-otm-jlines (cdr es)))
                                            (fields nil)))))))

;; The journal file reads back as the entries written, in order.
(defthm fn-otm-journal-read-of-jlines
  (implies (fn-otm-nat-lists-p es)
           (and (equal (fn-otm-journal-read (fn-otm-jlines es)) es)
                (equal (mv-nth 0 (fn-otm-jparse (fn-otm-jlines es) nil nil nil)) :whole))))

; -----------------------------------------------------------------------------
; The entries.  (SEQ OP READING A B C WORD), all naturals:
;   SEQ   the value's JSEQ after the event (0 for a start entry)
;   OP    0 start, 1 :clock, 2 :served, 3 :issue, 4 :return, 5 a note
;   A B C :issue's limits (D H C); :served's wall ms and has-wall (1/0);
;         a note's two counts; else 0
;   WORD  the event's word, by the code below (0 for a start or a note)

(defun fn-otm-op-of-kind (kind)
  (declare (xargs :guard t))
  (cond ((eq kind :clock) 1) ((eq kind :served) 2) ((eq kind :issue) 3)
        ((eq kind :return) 4) (t 0)))

(defun fn-otm-kind-of-op (op)
  (declare (xargs :guard t))
  (cond ((eql op 1) :clock) ((eql op 2) :served) ((eql op 3) :issue)
        ((eql op 4) :return) (t nil)))

(defun fn-otm-word-code (w)
  (declare (xargs :guard t))
  (case w
    (:issued 1) (:returned 2) (:recovered 3) (:recovered-from-stall 4)
    (:became-slow 5) (:became-stalled 6) (:none 7) (:clock-regressed 8)
    (:fault 9) (otherwise 0)))

(defun fn-otm-event-args (kind arg)
  (declare (xargs :guard t))
  (cond ((eq kind :issue) (fn-otm-limits arg))
        ((eq kind :served)
         (list (nfix (if (consp arg) (car arg) 0))
               (if (and (consp arg) (consp (cdr arg)) (cadr arg)) 1 0)
               0))
        (t (list 0 0 0))))

(defun fn-otm-journal-entry (s2 kind reading arg word)
  (declare (xargs :guard t))
  (let ((a (fn-otm-event-args kind arg)))
    (list (fn-otm-jseq s2) (fn-otm-op-of-kind kind) (nfix reading)
          (nfix (car a)) (nfix (cadr a)) (nfix (caddr a)) (fn-otm-word-code word))))

; THE HOST'S CALL for every disk event (host/native/owner.lisp
; fnn-owner-disk-event): (WORD S' JOURNAL-LINE LOG-LINE).
(defun fn-otm-disk-step (s kind reading arg)
  (declare (xargs :guard t))
  (mv-let (w s2) (fn-otm-disk-event s kind reading arg)
    (list w s2
          (fn-otm-jline (fn-otm-journal-entry s2 kind reading arg w))
          (fn-otm-log-line s2 w))))

(defthm fn-otm-disk-step-unfolds
  (let ((r (fn-otm-disk-step s kind reading arg)))
    (and (equal (car r) (mv-nth 0 (fn-otm-disk-event s kind reading arg)))
         (equal (cadr r) (mv-nth 1 (fn-otm-disk-event s kind reading arg))))))

; A note: a decision the host made from the value that changes nothing in
; it but is journaled with its counts (the stall's release: A members told
; uncertain, B queued POSTs refused try-later).
(defun fn-otm-note (s a b)
  (declare (xargs :guard t))
  (let ((s2 (fn-otm-make (fn-otm-ocp s) (fn-otm-disk s)
                         (list (fn-otm-now s) (fn-otm-regressions s) (+ 1 (fn-otm-jseq s))))))
    (mv s2 (list (fn-otm-jseq s2) 5 (fn-otm-now s) (nfix a) (nfix b) 0 0))))

; THE HOST'S CALL for a note: (S' JOURNAL-LINE).
(defun fn-otm-note-step (s a b)
  (declare (xargs :guard t))
  (mv-let (s2 e) (fn-otm-note s a b) (list s2 (fn-otm-jline e))))

; THE HOST'S CALL at a run's start (the gate made from fn-otm-init): the
; start entry, with the first monotonic READING and the WALL reading.
(defun fn-otm-start-line (reading wall)
  (declare (xargs :guard t))
  (fn-otm-jline (list 0 0 (nfix reading) (nfix wall) 0 0 0)))

; -----------------------------------------------------------------------------
; Replay.  From S, apply each entry's event to the value and compare the
; recomputed word with the journaled one.  Answers (mv VERDICT S'):
; :agrees, or (:gap SEQ) (an entry missing before SEQ: dropped by the sink,
; or the file cut), (:diverged SEQ) (the recomputed word differs), or
; (:malformed SEQ).  A start entry resets S to fn-otm-init.

(defun fn-otm-replay (s entries)
  (declare (xargs :guard t :measure (len entries)))
  (if (consp entries)
      (let ((e (car entries)))
        (if (not (and (nat-listp e) (equal (len e) 7)))
            (mv (list :malformed (if (consp e) (car e) nil)) s)
          (let ((seq (nth 0 e)) (op (nth 1 e)) (reading (nth 2 e))
                (a (nth 3 e)) (b (nth 4 e)) (c (nth 5 e)) (code (nth 6 e)))
            (cond ((equal op 0)
                   (if (equal seq 0)
                       (fn-otm-replay (fn-otm-init) (cdr entries))
                     (mv (list :malformed seq) s)))
                  ((not (equal seq (+ 1 (fn-otm-jseq s))))
                   (mv (list :gap seq) s))
                  ((fn-otm-kind-of-op op)
                   (mv-let (w s2)
                     (fn-otm-disk-event s (fn-otm-kind-of-op op) reading (list a b c))
                     (if (equal (fn-otm-word-code w) code)
                         (fn-otm-replay s2 (cdr entries))
                       (mv (list :diverged seq) s))))
                  ((equal op 5)
                   (mv-let (s2 e2) (fn-otm-note s a b)
                     (declare (ignore e2))
                     (fn-otm-replay s2 (cdr entries))))
                  (t (mv (list :malformed seq) s))))))
    (mv :agrees s)))

; A run of the host's calls on the gate's value, each step one of
;   (:event KIND READING ARG)  fn-otm-disk-step        (one entry)
;   (:note A B)                fn-otm-note-step        (one entry)
;   (:next W)                  fn-otm-next             (the gate's pick)
;   (:observe CLASS HOLD WAIT) fn-otm-observe          (a quantum's release)
;   (:commit EVENT)            fn-otm-commit-event     (the committer)
; Answers (mv ENTRIES S').
(defun fn-otm-run (s steps)
  (declare (xargs :guard t :measure (len steps)))
  (if (consp steps)
      (let ((st (car steps)))
        (cond ((and (true-listp st) (eq (car st) :event))
               (mv-let (w s2) (fn-otm-disk-event s (nth 1 st) (nth 2 st) (nth 3 st))
                 (mv-let (es s3) (fn-otm-run s2 (cdr steps))
                   (mv (cons (fn-otm-journal-entry s2 (nth 1 st) (nth 2 st) (nth 3 st) w) es)
                       s3))))
              ((and (true-listp st) (eq (car st) :note))
               (mv-let (s2 e) (fn-otm-note s (nth 1 st) (nth 2 st))
                 (mv-let (es s3) (fn-otm-run s2 (cdr steps))
                   (mv (cons e es) s3))))
              ((and (true-listp st) (eq (car st) :next))
               (mv-let (c s2) (fn-otm-next s (nth 1 st))
                 (declare (ignore c))
                 (fn-otm-run s2 (cdr steps))))
              ((and (true-listp st) (eq (car st) :observe))
               (fn-otm-run (fn-otm-observe s (nth 1 st) (nth 2 st) (nth 3 st)) (cdr steps)))
              ((and (true-listp st) (eq (car st) :commit))
               (mv-let (a s2) (fn-otm-commit-event s (nth 1 st))
                 (declare (ignore a))
                 (fn-otm-run s2 (cdr steps))))
              (t (fn-otm-run s (cdr steps)))))
    (mv nil s)))

; The host appends only events of the four kinds.
(defun fn-otm-run-okp (steps)
  (declare (xargs :guard t))
  (if (consp steps)
      (and (if (and (true-listp (car steps)) (eq (car (car steps)) :event))
               (member-eq (nth 1 (car steps)) '(:clock :served :issue :return))
             t)
           (fn-otm-run-okp (cdr steps)))
    t))

;; ---------------------------------------------------------------------------
;; The event is a function of the disk and the clock alone, and of the
;; journaled arguments.

(defun fn-otm-same-dc (a b)
  (declare (xargs :guard t))
  (and (equal (fn-otm-disk a) (fn-otm-disk b)) (equal (fn-otm-clock a) (fn-otm-clock b))))

(local (in-theory (disable fn-otm-disk-tick fn-otm-disk-issue fn-otm-disk-return)))

(local
 (defthm fn-otm-limits-idempotent
   (equal (fn-otm-limits (fn-otm-limits arg)) (fn-otm-limits arg))
   :hints (("Goal" :in-theory (enable fn-otm-limits fn-otm-deadline-of-limit
                                      fn-otm-stall-of-limit fn-otm-cadence-of-limit)))))

(local
 (defthm fn-otm-limits-of-list3
   (implies (and (true-listp l) (equal (len l) 3))
            (equal (list (nfix (car l)) (nfix (cadr l)) (nfix (caddr l)))
                   (if (nat-listp l) l (list (nfix (car l)) (nfix (cadr l)) (nfix (caddr l))))))))

(local
 (defthm fn-otm-limits-shape
   (and (true-listp (fn-otm-limits arg))
        (equal (len (fn-otm-limits arg)) 3)
        (nat-listp (fn-otm-limits arg)))
   :hints (("Goal" :in-theory (enable fn-otm-limits fn-otm-deadline-of-limit
                                      fn-otm-stall-of-limit fn-otm-cadence-of-limit)))))

(local
 (defthm fn-otm-disk-issue-of-limits
   (equal (fn-otm-disk-issue d now (fn-otm-limits arg)) (fn-otm-disk-issue d now arg))
   :hints (("Goal" :in-theory (e/d (fn-otm-disk-issue) (fn-otm-limits))))))

;; The event at the journal's normalized reading and arguments is the
;; host's own call.
(local
 (defthm fn-otm-disk-event-of-nfix-reading
   (equal (fn-otm-disk-event s kind (nfix reading) arg)
          (fn-otm-disk-event s kind reading arg))
   :hints (("Goal" :in-theory (e/d (fn-otm-disk-event fn-otm-dc-event) (fn-otm-limits))))))

(local
 (defthm fn-otm-disk-event-of-journal-args
   (implies (member-eq kind '(:clock :served :issue :return))
            (let ((a (fn-otm-event-args kind arg)))
              (equal (fn-otm-disk-event s kind reading
                                        (list (nfix (car a)) (nfix (cadr a)) (nfix (caddr a))))
                     (fn-otm-disk-event s kind reading arg))))
   :hints (("Goal" :in-theory (e/d (fn-otm-disk-event fn-otm-dc-event) (fn-otm-limits))
            :use ((:instance fn-otm-limits-of-list3 (l (fn-otm-limits arg))))))))

;; ... and it is a function of the disk and the clock.
(local
 (defthm fn-otm-disk-event-congruence
   (implies (fn-otm-same-dc r s)
            (and (equal (mv-nth 0 (fn-otm-disk-event r kind reading arg))
                        (mv-nth 0 (fn-otm-disk-event s kind reading arg)))
                 (fn-otm-same-dc (mv-nth 1 (fn-otm-disk-event r kind reading arg))
                                 (mv-nth 1 (fn-otm-disk-event s kind reading arg)))))
   :hints (("Goal" :in-theory (e/d (fn-otm-disk-event fn-otm-same-dc) (fn-otm-dc-event))))))

(local
 (defthm fn-otm-disk-event-replayed
   (implies (and (fn-otm-same-dc r s)
                 (member-eq kind '(:clock :served :issue :return)))
            (let ((a (fn-otm-event-args kind arg)))
              (and (equal (mv-nth 0 (fn-otm-disk-event
                                     r kind (nfix reading)
                                     (list (nfix (car a)) (nfix (cadr a)) (nfix (caddr a)))))
                          (mv-nth 0 (fn-otm-disk-event s kind reading arg)))
                   (fn-otm-same-dc (mv-nth 1 (fn-otm-disk-event
                                              r kind (nfix reading)
                                              (list (nfix (car a)) (nfix (cadr a))
                                                    (nfix (caddr a)))))
                                   (mv-nth 1 (fn-otm-disk-event s kind reading arg))))))
   :hints (("Goal" :in-theory (disable fn-otm-disk-event fn-otm-event-args fn-otm-same-dc
                                       fn-otm-disk-event-congruence
                                       fn-otm-disk-event-of-journal-args
                                       fn-otm-disk-event-of-nfix-reading)
            :use ((:instance fn-otm-disk-event-congruence
                             (reading (nfix reading))
                             (arg (list (nfix (car (fn-otm-event-args kind arg)))
                                        (nfix (cadr (fn-otm-event-args kind arg)))
                                        (nfix (caddr (fn-otm-event-args kind arg))))))
                  (:instance fn-otm-disk-event-of-nfix-reading
                             (arg (list (nfix (car (fn-otm-event-args kind arg)))
                                        (nfix (cadr (fn-otm-event-args kind arg)))
                                        (nfix (caddr (fn-otm-event-args kind arg))))))
                  (:instance fn-otm-disk-event-of-journal-args))))))

(local
 (defthm fn-otm-note-replayed
   (implies (fn-otm-same-dc r s)
            (fn-otm-same-dc (mv-nth 0 (fn-otm-note r a b)) (mv-nth 0 (fn-otm-note s a b))))
   :hints (("Goal" :in-theory (enable fn-otm-now fn-otm-regressions fn-otm-jseq)))))

(local
 (defthm fn-otm-same-dc-jseq
   (implies (fn-otm-same-dc r s) (equal (fn-otm-jseq r) (fn-otm-jseq s)))
   :hints (("Goal" :in-theory (enable fn-otm-jseq)))))

(local
 (defthm fn-otm-same-dc-of-gate-steps
   (and (implies (fn-otm-same-dc r s) (fn-otm-same-dc r (mv-nth 1 (fn-otm-next s w))))
        (implies (fn-otm-same-dc r s) (fn-otm-same-dc r (fn-otm-observe s c h x)))
        (implies (fn-otm-same-dc r s)
                 (fn-otm-same-dc r (mv-nth 1 (fn-otm-commit-event s e)))))
   :hints (("Goal" :in-theory (enable fn-otm-next-is-ocp-next fn-otm-observe-keeps-the-disk
                                      fn-otm-commit-event-is-ocp-commit-event)))))

(local
 (defthm fn-otm-same-dc-reflexive
   (fn-otm-same-dc s s)))

(local
 (defthm fn-otm-journal-entry-shape
   (let ((e (fn-otm-journal-entry s2 kind reading arg w)))
     (and (nat-listp e) (consp e) (equal (len e) 7)))))

(local
 (defthm fn-otm-note-entry-shape
   (let ((e (mv-nth 1 (fn-otm-note s a b))))
     (and (nat-listp e) (consp e) (equal (len e) 7)))))

(local
 (defthm fn-otm-run-entries-shape
   (fn-otm-nat-lists-p (mv-nth 0 (fn-otm-run s steps)))
   :hints (("Goal" :in-theory (disable fn-otm-journal-entry fn-otm-note)))))

(local
 (defthm fn-otm-note-seq
   (equal (car (mv-nth 1 (fn-otm-note s a b))) (+ 1 (fn-otm-jseq s)))
   :hints (("Goal" :in-theory (enable fn-otm-jseq)))))

(local (in-theory (disable fn-otm-same-dc fn-otm-disk-event fn-otm-note fn-otm-next
                           fn-otm-observe fn-otm-commit-event)))

(local
 (defun fn-otm-ev-state (s kind reading arg)
   (mv-let (w s2) (fn-otm-disk-event s kind reading arg) (declare (ignore w)) s2)))

(local
 (defun fn-otm-replay-args (kind arg)
   (let ((a (fn-otm-event-args kind arg)))
     (list (nfix (car a)) (nfix (cadr a)) (nfix (caddr a))))))

(local
 (defun fn-otm-note-state (s a b)
   (mv-let (s2 e) (fn-otm-note s a b) (declare (ignore e)) s2)))

(local
 (defthm fn-otm-note-state-of-nfix
   (equal (fn-otm-note-state s (nfix a) (nfix b)) (fn-otm-note-state s a b))
   :hints (("Goal" :in-theory (enable fn-otm-note)))))

(local
 (defthm fn-otm-disk-event-replayed2
   (implies (and (fn-otm-same-dc r s) (member-eq kind '(:clock :served :issue :return)))
            (and (equal (mv-nth 0 (fn-otm-disk-event r kind (nfix reading)
                                                     (fn-otm-replay-args kind arg)))
                        (mv-nth 0 (fn-otm-disk-event s kind reading arg)))
                 (fn-otm-same-dc (fn-otm-ev-state r kind (nfix reading)
                                                  (fn-otm-replay-args kind arg))
                                 (mv-nth 1 (fn-otm-disk-event s kind reading arg)))))
   :hints (("Goal" :in-theory (e/d (fn-otm-ev-state fn-otm-replay-args)
                                   (fn-otm-disk-event fn-otm-event-args fn-otm-same-dc
                                    fn-otm-disk-event-replayed))
            :use ((:instance fn-otm-disk-event-replayed))))))

(local (in-theory (disable fn-otm-disk-event-replayed fn-otm-disk-event-of-journal-args
                           fn-otm-disk-event-of-nfix-reading fn-otm-disk-event-congruence)))

;; One well-formed event entry whose word agrees steps the replay.
(local
 (defthm fn-otm-replay-step
   (implies (and (nat-listp e) (equal (len e) 7)
                 (not (equal (nth 1 e) 0))
                 (equal (nth 0 e) (+ 1 (fn-otm-jseq r)))
                 (fn-otm-kind-of-op (nth 1 e))
                 (equal (fn-otm-word-code
                         (mv-nth 0 (fn-otm-disk-event r (fn-otm-kind-of-op (nth 1 e)) (nth 2 e)
                                                      (list (nth 3 e) (nth 4 e) (nth 5 e)))))
                        (nth 6 e)))
            (equal (fn-otm-replay r (cons e rest))
                   (fn-otm-replay (fn-otm-ev-state r (fn-otm-kind-of-op (nth 1 e)) (nth 2 e)
                                                   (list (nth 3 e) (nth 4 e) (nth 5 e)))
                                  rest)))
   :hints (("Goal" :expand ((fn-otm-replay r (cons e rest)))
            :in-theory (e/d (fn-otm-ev-state)
                            (fn-otm-disk-event fn-otm-word-code fn-otm-kind-of-op))))))

(local
 (defthm fn-otm-journal-entry-nths
   (let ((e (fn-otm-journal-entry s2 kind reading arg w)))
     (and (equal (nth 0 e) (fn-otm-jseq s2))
          (equal (nth 1 e) (fn-otm-op-of-kind kind))
          (equal (nth 2 e) (nfix reading))
          (equal (list (nth 3 e) (nth 4 e) (nth 5 e)) (fn-otm-replay-args kind arg))
          (equal (nth 6 e) (fn-otm-word-code w))
          (nat-listp e) (equal (len e) 7)))
   :hints (("Goal" :in-theory (e/d (fn-otm-journal-entry fn-otm-replay-args)
                                   (fn-otm-event-args fn-otm-word-code))))))

(local
 (defthm fn-otm-kind-op-round-trip
   (implies (member-eq kind '(:clock :served :issue :return))
            (and (equal (fn-otm-kind-of-op (fn-otm-op-of-kind kind)) kind)
                 (not (equal (fn-otm-op-of-kind kind) 0))))))

(local
 (defthm fn-otm-jseq-of-event
   (equal (fn-otm-jseq (mv-nth 1 (fn-otm-disk-event s kind reading arg)))
          (+ 1 (fn-otm-jseq s)))
   :hints (("Goal" :use ((:instance fn-otm-recorded-time-is-monotone))))))

;; One event entry replays as the host's event from any value with the same
;; disk and clock.
(local
 (defthm fn-otm-replay-of-event-entry
   (implies (and (fn-otm-same-dc r s) (member-eq kind '(:clock :served :issue :return)))
            (equal (fn-otm-replay
                    r (cons (fn-otm-journal-entry (mv-nth 1 (fn-otm-disk-event s kind reading arg))
                                                  kind reading arg
                                                  (car (fn-otm-disk-event s kind reading arg)))
                            rest))
                   (fn-otm-replay (fn-otm-ev-state r kind (nfix reading)
                                                   (fn-otm-replay-args kind arg))
                                  rest)))
   :hints (("Goal" :in-theory (e/d (fn-otm-same-dc-jseq)
                                   (fn-otm-replay-step fn-otm-disk-event-replayed2
                                    fn-otm-disk-event fn-otm-word-code
                                    fn-otm-event-args fn-otm-journal-entry fn-otm-replay
                                    fn-otm-replay-args fn-otm-op-of-kind fn-otm-kind-of-op
                                    fn-otm-ev-state))
            :use ((:instance fn-otm-replay-step
                             (e (fn-otm-journal-entry
                                 (mv-nth 1 (fn-otm-disk-event s kind reading arg))
                                 kind reading arg
                                 (car (fn-otm-disk-event s kind reading arg)))))
                  (:instance fn-otm-disk-event-replayed2))))))

(local
 (defthm fn-otm-replay-of-note-entry
   (implies (fn-otm-same-dc r s)
            (equal (fn-otm-replay r (cons (mv-nth 1 (fn-otm-note s a b)) rest))
                   (fn-otm-replay (fn-otm-note-state r a b) rest)))
   :hints (("Goal" :expand ((fn-otm-replay r (cons (mv-nth 1 (fn-otm-note s a b)) rest)))
            :in-theory (enable fn-otm-note fn-otm-note-state fn-otm-same-dc fn-otm-jseq)))))

(local
 (defthm fn-otm-ev-state-same-dc
   (implies (and (fn-otm-same-dc r s) (member-eq kind '(:clock :served :issue :return)))
            (fn-otm-same-dc (fn-otm-ev-state r kind (nfix reading) (fn-otm-replay-args kind arg))
                            (mv-nth 1 (fn-otm-disk-event s kind reading arg))))
   :hints (("Goal" :use ((:instance fn-otm-disk-event-replayed2))))))

(local
 (defthm fn-otm-note-state-same-dc
   (implies (fn-otm-same-dc r s)
            (fn-otm-same-dc (fn-otm-note-state r a b) (car (fn-otm-note s a b))))
   :hints (("Goal" :in-theory (e/d (fn-otm-note-state) (fn-otm-note-replayed))
            :use ((:instance fn-otm-note-replayed))))))

(local
 (defun-nx fn-otm-rr-ind (s r steps)
   (declare (xargs :measure (len steps)))
   (if (consp steps)
       (let ((st (car steps)))
         (cond ((and (true-listp st) (eq (car st) :event))
                (fn-otm-rr-ind (mv-nth 1 (fn-otm-disk-event s (nth 1 st) (nth 2 st) (nth 3 st)))
                               (fn-otm-ev-state r (nth 1 st) (nfix (nth 2 st))
                                                (fn-otm-replay-args (nth 1 st) (nth 3 st)))
                               (cdr steps)))
               ((and (true-listp st) (eq (car st) :note))
                (fn-otm-rr-ind (mv-nth 0 (fn-otm-note s (nth 1 st) (nth 2 st)))
                               (fn-otm-note-state r (nth 1 st) (nth 2 st))
                               (cdr steps)))
               ((and (true-listp st) (eq (car st) :next))
                (fn-otm-rr-ind (mv-nth 1 (fn-otm-next s (nth 1 st))) r (cdr steps)))
               ((and (true-listp st) (eq (car st) :observe))
                (fn-otm-rr-ind (fn-otm-observe s (nth 1 st) (nth 2 st) (nth 3 st)) r (cdr steps)))
               ((and (true-listp st) (eq (car st) :commit))
                (fn-otm-rr-ind (mv-nth 1 (fn-otm-commit-event s (nth 1 st))) r (cdr steps)))
               (t (fn-otm-rr-ind s r (cdr steps)))))
     (list s r))))

(local
 (defthm fn-otm-replay-of-nil
   (equal (fn-otm-replay r nil) (mv :agrees r))
   :hints (("Goal" :expand ((fn-otm-replay r nil))))))

(local (in-theory (disable fn-otm-ev-state fn-otm-replay-args fn-otm-note-state
                           fn-otm-journal-entry)))

(local
 (defthm fn-otm-same-dc-transitive
   (implies (and (fn-otm-same-dc a b) (fn-otm-same-dc b c)) (fn-otm-same-dc a c))
   :hints (("Goal" :in-theory (enable fn-otm-same-dc)))))

(local
 (defthm fn-otm-replay-of-run
   (implies (and (fn-otm-run-okp steps) (fn-otm-same-dc r s))
            (let ((run (fn-otm-run s steps)))
              (and (equal (mv-nth 0 (fn-otm-replay r (mv-nth 0 run))) :agrees)
                   (fn-otm-same-dc (mv-nth 1 (fn-otm-replay r (mv-nth 0 run)))
                                   (mv-nth 1 run)))))
   :hints (("Goal" :induct (fn-otm-rr-ind s r steps)
            :in-theory (e/d (fn-otm-run fn-otm-run-okp) (fn-otm-replay nfix))))))

;; KEYSTONE (PRF-314, slice 2: replay determinism).  The subjects are the
;; host's calls: fn-otm-disk-step and fn-otm-note-step (whose journal lines
;; are fn-otm-jline of the entries fn-otm-run collects), and fn-otm-next,
;; fn-otm-observe and fn-otm-commit-event interleaved (host/native/owner.lisp
;; fnn-owner-disk-event, fnn-owner-journal-note, fnn-owner-gate-pick,
;; fnn-owner-gate-release, fnn-owner-commit-event).  For any run of them in
;; any order, the journal it writes reads back whole and replays from the
;; run's start to AGREEMENT, ending at the run's disk and clock.
(defthm fn-otm-journal-determines-the-decisions
  (implies (fn-otm-run-okp steps)
           (let* ((run (fn-otm-run s steps))
                  (file (fn-otm-jlines (mv-nth 0 run)))
                  (replay (fn-otm-replay s (fn-otm-journal-read file))))
             (and (equal (mv-nth 0 (fn-otm-jparse file nil nil nil)) :whole)
                  (equal (mv-nth 0 replay) :agrees)
                  (equal (fn-otm-disk (mv-nth 1 replay)) (fn-otm-disk (mv-nth 1 run)))
                  (equal (fn-otm-clock (mv-nth 1 replay)) (fn-otm-clock (mv-nth 1 run))))))
  :hints (("Goal" :use ((:instance fn-otm-replay-of-run (r s))
                        (:instance fn-otm-run-entries-shape)
                        (:instance fn-otm-journal-read-of-jlines
                                   (es (mv-nth 0 (fn-otm-run s steps)))))
           :in-theory (e/d (fn-otm-same-dc)
                           (fn-otm-run fn-otm-replay fn-otm-jparse fn-otm-jlines
                            fn-otm-journal-read fn-otm-run-okp fn-otm-replay-of-run
                            fn-otm-run-entries-shape fn-otm-journal-read-of-jlines)))))

;; ... and every decision the host asks of the value reads only that disk
;; and clock, so the replay reproduces each of them at its entry.
(defthm fn-otm-decisions-read-only-the-journal-state
  (implies (and (equal (fn-otm-disk a) (fn-otm-disk b))
                (equal (fn-otm-clock a) (fn-otm-clock b)))
           (and (equal (fn-otm-admit-post a) (fn-otm-admit-post b))
                (equal (fn-otm-mode a) (fn-otm-mode b))
                (equal (fn-otm-wait-ms a) (fn-otm-wait-ms b))
                (equal (fn-otm-shed-reply a) (fn-otm-shed-reply b))
                (equal (fn-otm-post-command-reply a) (fn-otm-post-command-reply b))
                (equal (fn-otm-disk-lines a) (fn-otm-disk-lines b))
                (equal (fn-otm-log-line a w) (fn-otm-log-line b w))))
  :hints (("Goal" :in-theory (enable fn-otm-admit-post fn-otm-mode fn-otm-wait-ms
                                     fn-otm-shed-reply fn-otm-post-command-reply
                                     fn-otm-disk-lines fn-otm-log-line fn-otm-now
                                     fn-otm-regressions))))

(in-theory (disable fn-otm-disk-step fn-otm-note-step fn-otm-start-line fn-otm-replay
                    fn-otm-journal-read fn-otm-run))
