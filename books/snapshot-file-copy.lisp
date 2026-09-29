; Snapshot file-copy cursor (S7, PRF-1069).  Source names one held immutable
; file incarnation, not a pathname reopened between steps.  LIMIT is its
; captured prefix length; later appends are outside that prefix.  QUANTUM
; bounds each allocation/I/O step, never the total stored file.  The host
; calls PLAN before allocating and ADVANCE after observing the pread count.
(in-package "ACL2")

(defun fn-osc-statep (s)
  (declare (xargs :guard t))
  (and (true-listp s) (equal (len s) 3)
       (natp (nth 1 s)) (natp (nth 2 s))
       (<= (nth 2 s) (nth 1 s))))

(defun fn-osc-begin (source limit)
  (declare (xargs :guard (natp limit)))
  (list source limit 0))

(defun fn-osc-plan (s quantum)
  (declare (xargs :guard t))
  (cond ((not (fn-osc-statep s)) (list :refused :cursor))
        ((not (posp quantum)) (list :refused :quantum))
        ((equal (nth 2 s) (nth 1 s)) (list :done (car s) (nth 1 s)))
        (t (list :read (car s) (nth 2 s)
                 (min quantum (- (nth 1 s) (nth 2 s)))))))

(defun fn-osc-advance (s quantum observed)
  (declare (xargs :guard t))
  (let ((plan (fn-osc-plan s quantum)))
    (cond ((not (equal (car plan) :read)) (list :refused :not-reading s))
          ((not (equal observed (nth 3 plan))) (list :refused :short-read s))
          (t (list :continue (list (car s) (nth 1 s)
                                  (+ (nth 2 s) (nth 3 plan))))))))

; KEYSTONE PRF-1069.  A successful step preserves the held incarnation and
; total prefix length, advances by exactly the observed full read, and
; cannot skip/truncate past the prefix or exceed the per-step quantum.
(defthm fn-osc-successful-step-is-the-exact-bounded-prefix
  (implies (and (fn-osc-statep s) (posp quantum)
                (< (nth 2 s) (nth 1 s))
                (equal observed (nth 3 (fn-osc-plan s quantum))))
           (let ((next (cadr (fn-osc-advance s quantum observed))))
             (and (equal (car (fn-osc-advance s quantum observed)) :continue)
                  (fn-osc-statep next)
                  (equal (car next) (car s))
                  (equal (nth 1 next) (nth 1 s))
                  (equal (nth 2 next) (+ (nth 2 s) observed))
                  (< (nth 2 s) (nth 2 next))
                  (<= observed quantum)
                  (<= (nth 2 next) (nth 1 s)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-osc-statep fn-osc-plan fn-osc-advance))))

; A short read never advances the cursor to a fabricated completion.
(defthm fn-osc-short-read-keeps-the-cursor
  (implies (and (equal (car (fn-osc-plan s quantum)) :read)
                (not (equal observed (nth 3 (fn-osc-plan s quantum)))))
           (equal (fn-osc-advance s quantum observed)
                  (list :refused :short-read s)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-osc-advance))))

(defthm fn-osc-done-is-the-entire-captured-prefix
  (implies (and (fn-osc-statep s) (posp quantum))
           (iff (equal (car (fn-osc-plan s quantum)) :done)
                (equal (nth 2 s) (nth 1 s))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-osc-statep fn-osc-plan))))
