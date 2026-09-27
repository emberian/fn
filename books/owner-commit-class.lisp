; fn: the owner's commit class -- when the batch of queued submissions is
; committed (lane commit-onto-log, 2026-09-27; PKT-688 (4), decided by the
; coordinator: "the POST's durable commit becomes its own scheduled class").
;
; On a format-9 store a served POST's read step queues its submission and
; returns; a COMMIT quantum (host/native/owner.lisp fnn-owner-commit-queued)
; takes every queued submission up to the operator's bounds, runs each one's
; sequential life under the owner mutex, appends their records as one log
; batch, fences the segment once and only then releases the members' replies.
; The batch is everything queued when the commit quantum is admitted, so the
; admission rule decides the batch: this book's `fn-ocm-next' wraps
; books/owner-scheduler.lisp's `fn-osch-next' (the four classes' cyclic pick,
; PRF-248) and admits the commit class
;
;   - when no thread of the four classes waits (nothing else is ready: the
;     batch is everything that arrived; at one poster it is that poster), or
;   - when the commit class has been passed over BOUND times in a row while
;     it waited (so a stream of other quanta delays a batch by at most BOUND
;     quanta).
;
; A commit pick does not move the four classes' cursor, and every other pick
; is exactly `fn-osch-next''s: PRF-248's control bound holds over the
; non-commit quanta unchanged (`fn-ocm-next-otherwise-is-osch-next'), and the
; commit class itself waits at most BOUND quanta of the others
; (`fn-ocm-commit-waits-at-most-the-bound').
(in-package "ACL2")
(include-book "owner-scheduler")

; The commit class's bound: at most this many quanta of the other classes
; run while a commit waits.
(defconst *fn-ocm-bound* 4)

; The five classes the gate admits and their slots: the four of
; *fn-osch-order* at their slots, and :commit at slot 4.
(defun fn-ocm-classp (x)
  (declare (xargs :guard t))
  (or (eq x :commit) (fn-osch-classp x)))
(defun fn-ocm-class-index (c)
  (declare (xargs :guard t))
  (if (eq c :commit) 4 (fn-osch-class-index c)))

; The state: (SCHED SKIPPED), SCHED the four classes' scheduler state, SKIPPED
; the picks that passed over a waiting commit since its last admission.
(defun fn-ocm-init ()
  (declare (xargs :guard t))
  (list (fn-osch-init) 0))
(defun fn-ocm-sched (s)
  (declare (xargs :guard t))
  (if (consp s) (car s) nil))
(defun fn-ocm-skipped (s)
  (declare (xargs :guard t))
  (if (and (consp s) (consp (cdr s))) (nfix (cadr s)) 0))

; The pick.  W the four classes' waiting counts, COMMIT whether the commit
; class waits.  Answers (mv CLASS S'), CLASS one of the four, :commit or nil.
(defun fn-ocm-next (s w commit)
  (declare (xargs :guard t))
  (if (and commit
           (or (fn-osch-idlep w) (<= *fn-ocm-bound* (fn-ocm-skipped s))))
      (mv :commit (list (fn-ocm-sched s) 0))
    (mv-let (class sched) (fn-osch-next (fn-ocm-sched s) w)
      (mv class (list sched (if (and commit class)
                                (+ 1 (fn-ocm-skipped s))
                              (fn-ocm-skipped s)))))))

; The hold and wait fold: a commit quantum is not one of the four classes'
; rows (it is counted by the log's own lines); the others fold as before.
(defun fn-ocm-observe (s class hold-ms wait-ms)
  (declare (xargs :guard t))
  (if (eq class :commit)
      s
    (list (fn-osch-observe (fn-ocm-sched s) class hold-ms wait-ms)
          (fn-ocm-skipped s))))

(defun fn-ocm-health-lines (s)
  (declare (xargs :guard t))
  (fn-osch-health-lines (fn-ocm-sched s)))

; =============================================================================
; Theorems

; Every pick that is not the commit class's is the four classes' own pick
; from the same scheduler state, and it leaves the same scheduler state.
(defthm fn-ocm-next-otherwise-is-osch-next
  (implies (not (equal (mv-nth 0 (fn-ocm-next s w commit)) :commit))
           (and (equal (mv-nth 0 (fn-ocm-next s w commit))
                       (mv-nth 0 (fn-osch-next (fn-ocm-sched s) w)))
                (equal (fn-ocm-sched (mv-nth 1 (fn-ocm-next s w commit)))
                       (mv-nth 1 (fn-osch-next (fn-ocm-sched s) w)))))
  :hints (("Goal" :in-theory (disable fn-osch-next fn-osch-idlep))))

; A commit pick leaves the four classes' state untouched.
(defthm fn-ocm-commit-pick-keeps-the-sched
  (implies (equal (mv-nth 0 (fn-ocm-next s w commit)) :commit)
           (and (equal (fn-ocm-sched (mv-nth 1 (fn-ocm-next s w commit)))
                       (fn-ocm-sched s))
                (equal (fn-ocm-skipped (mv-nth 1 (fn-ocm-next s w commit))) 0)))
  :hints (("Goal" :in-theory (disable fn-osch-next fn-osch-idlep))))

; The commit class is admitted only when nothing else waits or it has been
; passed over BOUND times.
(defthm fn-ocm-commit-only-when-idle-or-due
  (implies (equal (mv-nth 0 (fn-ocm-next s w commit)) :commit)
           (and commit
                (or (fn-osch-idlep w)
                    (<= *fn-ocm-bound* (fn-ocm-skipped s)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-osch-next fn-osch-idlep))))

; KEYSTONE.  The subject is `fn-ocm-next', which host/native/owner.lisp
; fnn-owner-gate-pick calls at every release of the owner and every arrival
; at an idle one.  WS the successive waiting observations; while the commit
; class waits at every pick, the number of quanta of the other classes that
; run before a commit pick is at most BOUND less the passes already made.
(defun fn-ocm-commit-delay (s ws)
  (declare (xargs :guard t :measure (len ws)))
  (if (consp ws)
      (mv-let (class s2) (fn-ocm-next s (car ws) t)
        (cond ((equal class :commit) 0)
              ((null class) (fn-ocm-commit-delay s2 (cdr ws)))
              (t (+ 1 (fn-ocm-commit-delay s2 (cdr ws))))))
    0))

(defthm fn-ocm-commit-waits-at-most-the-bound
  (<= (fn-ocm-commit-delay s ws)
      (nfix (- *fn-ocm-bound* (fn-ocm-skipped s))))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-ocm-commit-delay s ws)
           :in-theory (disable fn-osch-next fn-osch-idlep))))
