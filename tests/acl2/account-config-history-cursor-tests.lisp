(in-package "ACL2")
(include-book "../../books/account-config-history-cursor")

(defun fn-acht-run (n s)
 (declare (xargs :guard (natp n)))
 (if (zp n) s (fn-acht-run (1- n) (fn-cp-nth 1 (fn-ach-tick s)))))

; Reachable complete chronological append, including an empty predecessor.
(assert-event
 (let* ((s (fn-ach-begin '(old-c0 old-c1) 'typed-c2))
        (out (fn-acht-run 6 s)))
  (and (fn-ach-reachablep s)
       (equal (fn-ach-denotation s) '(old-c0 old-c1 typed-c2))
       (fn-ach-reachablep out)
       (equal (fn-cp-nth 1 out) :ready)
       (equal (fn-cp-nth 4 out) '(old-c0 old-c1 typed-c2)))))

(assert-event
 (let* ((s (fn-ach-begin nil 'typed-c0)) (out (fn-acht-run 2 s)))
  (and (fn-ach-reachablep s) (equal (fn-ach-denotation s) '(typed-c0))
       (equal (fn-cp-nth 1 out) :ready)
       (equal (fn-cp-nth 4 out) '(typed-c0)))))

(assert-event
 (let* ((s (fn-ach-begin '(c0) 'c1)) (next (fn-cp-nth 1 (fn-ach-tick s))))
  (and (fn-ach-reachablep s) (fn-ach-reachablep next)
       (equal (fn-ach-denotation next) (fn-ach-denotation s))
       (not (equal (fn-cp-nth 1 s) :ready))
       (< (fn-ach-rank next) (fn-ach-rank s)))))

(assert-event
 (let ((s (fn-ach-state :restore nil nil '(c0 c1) 'c1)))
  (and (equal (fn-cp-nth 0 (fn-ach-tick s)) :ready)
       (equal (fn-cp-nth 4 (fn-cp-nth 1 (fn-ach-tick s)))
              (fn-ach-denotation s)))))

; Hypothesis removals are corrupted-state/model data, not issued leases.
(assert-event
 (let ((history '(c0 . bad-tail)))
  (and (not (true-listp history))
       (not (and (fn-ach-reachablep (fn-ach-begin history 'c1))
                 (equal (fn-ach-denotation (fn-ach-begin history 'c1))
                        (append history '(c1))))))))

(assert-event
 (let ((s (fn-ach-state :ready '(unconsumed) nil '(c1) 'c1)))
  (and (not (fn-ach-reachablep s))
       (not (and (fn-ach-reachablep (fn-cp-nth 1 (fn-ach-tick s)))
                 (equal (fn-ach-denotation (fn-cp-nth 1 (fn-ach-tick s)))
                        (fn-ach-denotation s)))))))

(assert-event
 (let ((s (fn-ach-begin '(c0) 'c1)))
  (and (not (equal (fn-cp-nth 0 (fn-ach-tick s)) :ready))
       (not (equal (fn-cp-nth 4 (fn-cp-nth 1 (fn-ach-tick s)))
                   (fn-ach-denotation s))))))

(assert-event
 (let ((s (fn-ach-state :invalid nil nil nil 'c1)))
  (and (not (fn-ach-reachablep s)) (not (equal (fn-cp-nth 1 s) :ready))
       (not (< (fn-ach-rank (fn-cp-nth 1 (fn-ach-tick s))) (fn-ach-rank s))))))

(assert-event
 (let ((s (fn-ach-state :ready nil nil '(c0 c1) 'c1)))
  (and (fn-ach-reachablep s) (equal (fn-cp-nth 1 s) :ready)
       (not (< (fn-ach-rank (fn-cp-nth 1 (fn-ach-tick s))) (fn-ach-rank s))))))
