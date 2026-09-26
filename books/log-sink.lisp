; fn: what the owner does when its service log cannot take a line (PKT-508,
; PRF-187).
;
; The owner's log lines (books/owner-log.lisp) are written by the thread that
; decided them, under the owner mutex.  A sink that stops draining (stderr on
; a pipe nobody reads, a stalled journald, a slow disk) used to block that
; write, and with it the owner mutex, so the whole node stopped answering,
; the control socket included.  The served path now never waits on the log:
; host/native/io.lisp `fnn-log-line' offers the line to this sink and returns;
; one writer thread (`fnn-log-writer-loop') drains the queue outside every
; owner lock and reports each line it took back here.
;
; The decision (`fn-log-sink-offer'): a line is queued when the queue is empty
; or when the queued octets with it stay within the bound; otherwise it is
; dropped and counted.  No line is too long to log: an empty queue takes any
; line (D27, no ceiling on a datum), so the bound limits the backlog a wedged
; sink leaves in memory, never what one line may say.  A drop is never
; silent: `operator CONFIG health' prints the counts after the eight states
; (books/native-health.lisp `fn-nh-log-sink-line'), and the health scale is
; unchanged (a lost log line is not a state of the Store).
;
; Why dropping and not blocking: the log is an operator's record, never
; evidence of durable acceptance (AGENTS.md: durable acceptance comes only
; from persisted state), so losing a line under a wedged sink loses no
; decision, while waiting on it stops every decision.  Why a bounded queue
; before the drop rather than a non-blocking write: a descriptor's O_NONBLOCK
; is shared by every process holding the same open file description (a
; terminal the shell also reads), and a short non-blocking write splits a
; line; the writer thread writes whole lines with blocking writes and only it
; can wait.
;
; The sink is (PENDING-OCTETS PENDING-LINES DROPPED WRITTEN OFFERED).  The
; maintained relation `fn-log-sink-okp' is established by `fn-log-sink-init'
; (host: `fnn-log-writer-start') and preserved by both transitions
; (`fn-log-sink-offer' from `fnn-log-line', `fn-log-sink-take' from
; `fnn-log-writer-loop'): every line offered is written, pending or dropped,
; and the pending octets are within the bound unless one line is pending.
;
; Prefix `fn-log-sink-' (docs/prefixes.md).
(in-package "ACL2")

; The backlog a wedged sink may leave queued: 1 MiB of log octets, about
; ten thousand of the owner's outcome lines.  A work and allocation bound of
; the log writer (D27), not a bound on a datum: see `fn-log-sink-offer'.
(defconst *fn-log-sink-pending-bound* 1048576)

(defun fn-log-sink-pending-bound ()
  (declare (xargs :guard t))
  *fn-log-sink-pending-bound*)

; How long a stopping owner waits for the writer to drain before it exits
; without it (the lines still queued are lost with the process, which a
; wedged sink would lose anyway).
(defconst *fn-log-sink-close-wait-seconds* 10)

(defun fn-log-sink-close-wait-seconds ()
  (declare (xargs :guard t))
  *fn-log-sink-close-wait-seconds*)

(defun fn-log-sink-field (i s)
  (declare (xargs :guard (natp i)))
  (cond ((atom s) 0)
        ((zp i) (nfix (car s)))
        (t (fn-log-sink-field (1- i) (cdr s)))))

(defun fn-log-sink-pending-octets (s) (declare (xargs :guard t)) (fn-log-sink-field 0 s))
(defun fn-log-sink-pending-lines (s) (declare (xargs :guard t)) (fn-log-sink-field 1 s))
(defun fn-log-sink-dropped (s) (declare (xargs :guard t)) (fn-log-sink-field 2 s))
(defun fn-log-sink-written (s) (declare (xargs :guard t)) (fn-log-sink-field 3 s))
(defun fn-log-sink-offered (s) (declare (xargs :guard t)) (fn-log-sink-field 4 s))

(defun fn-log-sink-init ()
  (declare (xargs :guard t))
  (list 0 0 0 0 0))

; One line of LEN octets (its LF included) offered while the owner decides:
; (DECISION SINK'), DECISION :queue or :drop.  There is no third answer: the
; offer never waits.
(defun fn-log-sink-offer (s len bound)
  (declare (xargs :guard t))
  (let ((po (fn-log-sink-pending-octets s))
        (pl (fn-log-sink-pending-lines s))
        (d (fn-log-sink-dropped s))
        (w (fn-log-sink-written s))
        (o (fn-log-sink-offered s))
        (len (nfix len))
        (bound (nfix bound)))
    (if (or (zp pl) (<= (+ po len) bound))
        (list :queue (list (+ po len) (+ 1 pl) d w (+ 1 o)))
      (list :drop (list po pl (+ 1 d) w (+ 1 o))))))

; The writer took the oldest pending line, of LEN octets, and its write
; ended with OUTCOME: :written, or anything else (a failed write), which
; counts the line dropped.  With nothing pending the sink is unchanged.
(defun fn-log-sink-take (s len outcome)
  (declare (xargs :guard t))
  (let ((po (fn-log-sink-pending-octets s))
        (pl (fn-log-sink-pending-lines s))
        (d (fn-log-sink-dropped s))
        (w (fn-log-sink-written s))
        (o (fn-log-sink-offered s)))
    (if (zp pl)
        (list po pl d w o)
      (list (if (equal pl 1) 0 (nfix (- po (nfix len))))
            (1- pl)
            (if (equal outcome :written) d (+ 1 d))
            (if (equal outcome :written) (+ 1 w) w)
            o))))

; The maintained relation.
(defun fn-log-sink-okp (s bound)
  (declare (xargs :guard t))
  (let ((po (fn-log-sink-pending-octets s))
        (pl (fn-log-sink-pending-lines s)))
    (and (true-listp s)
         (equal (len s) 5)
         (nat-listp s)
         (equal (fn-log-sink-offered s)
                (+ (fn-log-sink-written s) pl (fn-log-sink-dropped s)))
         (implies (zp pl) (equal po 0))
         (or (<= po (nfix bound)) (equal pl 1)))))

; -----------------------------------------------------------------------------
; Theorems

(defthm fn-log-sink-init-okp
  (fn-log-sink-okp (fn-log-sink-init) bound))

; KEYSTONE (the relation is maintained).  Every offer and every take keeps
; each offered line accounted for (written, pending or dropped) and the
; pending octets within the bound or one line; so a sink that never drains
; holds at most max(bound, one line) octets, however long the owner runs.
(defthm fn-log-sink-offer-preserves-okp
  (implies (fn-log-sink-okp s bound)
           (fn-log-sink-okp (cadr (fn-log-sink-offer s len bound)) bound)))

(defthm fn-log-sink-take-preserves-okp
  (implies (fn-log-sink-okp s bound)
           (fn-log-sink-okp (fn-log-sink-take s len outcome) bound)))

; KEYSTONE (the served path never waits, and drops only past the bound).
; The offer's decision is :queue or :drop, and it is :drop exactly when a
; line is already pending and this one would take the pending octets past
; the bound: a line offered to an empty queue is always queued.
(defthm fn-log-sink-offer-drops-only-past-the-bound
  (and (member-equal (car (fn-log-sink-offer s len bound)) '(:queue :drop))
       (iff (equal (car (fn-log-sink-offer s len bound)) :drop)
            (and (posp (fn-log-sink-pending-lines s))
                 (< (nfix bound)
                    (+ (fn-log-sink-pending-octets s) (nfix len)))))))

; What a drop changes: the dropped count by one and nothing pending.
(defthm fn-log-sink-drop-counts
  (implies (equal (car (fn-log-sink-offer s len bound)) :drop)
           (let ((s2 (cadr (fn-log-sink-offer s len bound))))
             (and (equal (fn-log-sink-dropped s2) (+ 1 (fn-log-sink-dropped s)))
                  (equal (fn-log-sink-pending-lines s2) (fn-log-sink-pending-lines s))
                  (equal (fn-log-sink-pending-octets s2) (fn-log-sink-pending-octets s))))))

(in-theory (disable fn-log-sink-offer fn-log-sink-take fn-log-sink-okp))
