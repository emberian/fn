; S9 bounded drain scan, an unactivated source contract.
; The caller must acquire and fund an immutable snapshot lease before START,
; retain it until release, and supply a mutation coordinate changed by every
; mutation that can invalidate a zero.  No host entry calls this yet.
(in-package "ACL2")
(include-book "owner-feed")

; Logical pending-work folds; these never run as scheduling subjects.
(defun fn-orc-queue-pending-model (queue)
  (declare (xargs :guard t))
  (if (consp queue)
      (+ (if (equal (fn-feed-entry-state (car queue))
                    '(:dropped :retry-bound)) 0 1)
         (fn-orc-queue-pending-model (cdr queue)))
    0))

(defun fn-orc-table-pending-model (table)
  (declare (xargs :guard t))
  (if (consp table)
      (+ (fn-orc-queue-pending-model
          (fn-feed-queue (fn-own-feed-entry-feed (car table))))
         (fn-orc-table-pending-model (cdr table)))
    0))

; Cursor = (snapshot table-tail queue-tail pending snapshot-coordinate).
; A transition inspects at most one feed entry or one queue entry.  A table
; load and a queue inspection occupy separate scheduling steps, including
; empty queues.  No LEN, table lookup, or report rendering executes here.
(defun fn-orc-start (table coordinate)
  (declare (xargs :guard (natp coordinate)))
  (list table table nil 0 coordinate))

(defun fn-orc-donep (cursor)
  (declare (xargs :guard (true-listp cursor)))
  (and (atom (nth 1 cursor)) (atom (nth 2 cursor))))

(defun fn-orc-next (cursor)
  (declare (xargs :guard (true-listp cursor)))
  (let ((table (nth 1 cursor))
        (queue (nth 2 cursor))
        (pending (nfix (nth 3 cursor))))
    (cond
     ((consp queue)
      (list (nth 0 cursor) table (cdr queue)
            (+ pending (if (equal (fn-feed-entry-state (car queue))
                                  '(:dropped :retry-bound))
                           0 1))
            (nth 4 cursor)))
     ((consp table)
      (list (nth 0 cursor) (cdr table)
            (fn-feed-queue (fn-own-feed-entry-feed (car table)))
            pending (nth 4 cursor)))
     (t cursor))))

; Zero can be reported only after the whole snapshot was inspected and
; only at its mutation coordinate.  An incomplete or stale zero refuses.
(defun fn-orc-zero-currentp (cursor coordinate)
  (declare (xargs :guard (and (true-listp cursor)
                             (natp (nth 4 cursor))
                             (natp coordinate))))
  (and (fn-orc-donep cursor)
       (equal (nth 4 cursor) coordinate)
       (equal (nfix (nth 3 cursor)) 0)))

; The logical tally is deliberately not an executable scheduling subject.
(defun fn-orc-remaining (cursor)
  (declare (xargs :guard (true-listp cursor)))
  (+ (nfix (nth 3 cursor))
     (fn-orc-queue-pending-model (nth 2 cursor))
     (fn-orc-table-pending-model (nth 1 cursor))))

(verify-guards fn-orc-queue-pending-model)
(verify-guards fn-orc-table-pending-model)
(verify-guards fn-orc-start)
(verify-guards fn-orc-donep)
(verify-guards fn-orc-next)
(verify-guards fn-orc-zero-currentp)
(verify-guards fn-orc-remaining)

(defthm fn-orc-start-tally-is-the-snapshot-by-definition
  (equal (fn-orc-remaining (fn-orc-start table coordinate))
         (fn-orc-table-pending-model table)))

(defthm fn-orc-next-keeps-the-snapshot-coordinate
  (equal (nth 4 (fn-orc-next cursor)) (nth 4 cursor)))

(defthm fn-orc-zero-current-requires-complete-current-scan-by-definition
  (implies (fn-orc-zero-currentp cursor coordinate)
           (and (fn-orc-donep cursor)
                (equal (nth 4 cursor) coordinate)
                (equal (nfix (nth 3 cursor)) 0))))

; Conservation across each bounded transition connects the executable
; cursor to the full-table logical pending-work fold.  Together with START,
; a completed current zero accounts for every entry of the captured table.
(defthm fn-orc-next-preserves-snapshot-pending-tally
  (equal (fn-orc-remaining (fn-orc-next cursor))
         (fn-orc-remaining cursor))
  :hints (("Goal" :in-theory (enable fn-orc-next fn-orc-remaining
                                     fn-orc-table-pending-model))))

(defthm fn-orc-complete-zero-has-no-remaining-pending
  (implies (fn-orc-zero-currentp cursor coordinate)
           (equal (fn-orc-remaining cursor) 0))
  :hints (("Goal" :in-theory (enable fn-orc-zero-currentp
                                     fn-orc-remaining fn-orc-queue-pending-model
                                     fn-orc-table-pending-model
                                     fn-orc-queue-pending-model))))

(in-theory (disable fn-orc-start fn-orc-next fn-orc-zero-currentp
                    fn-orc-remaining))
