; Chronological C-history append prepared one borrowed/rebuilt cell per tick.
; This cursor grants neither source authority nor allocation allowance.
(in-package "ACL2")
(include-book "consumer-position-fields")

(defun fn-ach-state (phase remaining reversed output record)
 (declare (xargs :guard t))
 (list :account-config-history phase remaining reversed output record))

(defun fn-ach-begin (history record)
 (declare (xargs :guard t))
 (fn-ach-state :copy history nil nil record))

(defun fn-ach-tick (s)
 (declare (xargs :guard t))
 (let ((phase (fn-cp-nth 1 s)) (remaining (fn-cp-nth 2 s))
       (reversed (fn-cp-nth 3 s)) (output (fn-cp-nth 4 s))
       (record (fn-cp-nth 5 s)))
  (case phase
   (:copy
    (if (consp remaining)
        (list :yield (fn-ach-state phase (cdr remaining)
                                  (cons (car remaining) reversed) nil record))
      (list :yield (fn-ach-state :restore nil reversed (list record) record))))
   (:restore
    (if (consp reversed)
        (list :yield (fn-ach-state phase nil (cdr reversed)
                                  (cons (car reversed) output) record))
      (list :ready (fn-ach-state :ready nil nil output record))))
   (:ready (list :ready s))
   (otherwise '(:refused :configuration-history-phase)))))

; Ghost observation, never called by the served cursor.
(defun fn-ach-denotation (s)
 (declare (xargs :guard t :verify-guards nil))
 (case (fn-cp-nth 1 s)
  (:copy (append (revappend (fn-cp-nth 3 s) (fn-cp-nth 2 s))
                 (list (fn-cp-nth 5 s))))
  (:restore (revappend (fn-cp-nth 3 s) (fn-cp-nth 4 s)))
  (:ready (fn-cp-nth 4 s))
  (otherwise nil)))

(defun fn-ach-reachablep (s)
 (declare (xargs :guard t))
 (and (true-listp s) (equal (len s) 6)
      (eq (fn-cp-nth 0 s) :account-config-history)
      (true-listp (fn-cp-nth 2 s))
      (true-listp (fn-cp-nth 3 s))
      (true-listp (fn-cp-nth 4 s))
      (case (fn-cp-nth 1 s)
       (:copy (null (fn-cp-nth 4 s)))
       (:restore (null (fn-cp-nth 2 s)))
       (:ready (and (null (fn-cp-nth 2 s)) (null (fn-cp-nth 3 s))))
       (otherwise nil))))

(local (defthm fn-ach-revappend-append
 (equal (append (revappend xs ys) zs) (revappend xs (append ys zs)))
 :hints (("Goal" :induct (revappend xs ys)))))

(defthm fn-ach-begin-establishes-exact-append
 (implies (true-listp history)
          (and (fn-ach-reachablep (fn-ach-begin history record))
               (equal (fn-ach-denotation (fn-ach-begin history record))
                      (append history (list record)))))
 :hints (("Goal" :in-theory (enable fn-ach-begin fn-ach-state fn-ach-reachablep
                                     fn-ach-denotation fn-cp-nth))))

(defthm fn-ach-tick-preserves-complete-append
 (implies (fn-ach-reachablep s)
          (and (fn-ach-reachablep (fn-cp-nth 1 (fn-ach-tick s)))
               (equal (fn-ach-denotation (fn-cp-nth 1 (fn-ach-tick s)))
                      (fn-ach-denotation s))))
 :hints (("Goal" :in-theory (enable fn-ach-tick fn-ach-state fn-ach-reachablep
                                     fn-ach-denotation fn-cp-nth))))

(defthm fn-ach-ready-is-actual-complete-output
 (implies (equal (fn-cp-nth 0 (fn-ach-tick s)) :ready)
          (equal (fn-cp-nth 4 (fn-cp-nth 1 (fn-ach-tick s)))
                 (fn-ach-denotation s)))
 :hints (("Goal" :in-theory (enable fn-ach-tick fn-ach-state fn-ach-reachablep
                                     fn-ach-denotation fn-cp-nth))))

(defun fn-ach-rank (s)
 (declare (xargs :guard t))
 (case (fn-cp-nth 1 s)
  (:copy (+ (* 2 (len (fn-cp-nth 2 s))) (len (fn-cp-nth 3 s)) 2))
  (:restore (+ (len (fn-cp-nth 3 s)) 1))
  (otherwise 0)))

(defthm fn-ach-tick-makes-progress
 (implies (and (fn-ach-reachablep s) (not (equal (fn-cp-nth 1 s) :ready)))
          (< (fn-ach-rank (fn-cp-nth 1 (fn-ach-tick s))) (fn-ach-rank s)))
 :hints (("Goal" :in-theory (enable fn-ach-tick fn-ach-state fn-ach-reachablep
                                     fn-ach-rank fn-cp-nth))))

(in-theory (disable fn-ach-state fn-ach-begin fn-ach-tick fn-ach-denotation
                    fn-ach-reachablep fn-ach-rank))
