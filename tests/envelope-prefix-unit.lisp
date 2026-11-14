(in-package "ACL2")
(include-book "../sim/envelope-prefix")
(include-book "../books/owed-conn")
(include-book "evidence/native-envelope-trace")

(defconst *fn2-envelope-prefix-test-profile*
  (put-assoc-equal :trace nil *fn2-conn-wire-profile*))

; Split immediately after Take, before Ack: TAKEN is essential state, not
; an optional replay statistic. Dropping it makes the very next event illegal.
(defun fn2-envelope-resume-test-run (drop-taken fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (let ((fn2-core (fn2-init-executor *fn2-envelope-prefix-test-profile* :echo nil fn2-core)))
    (mv-let (first taken caps fn2-core)
      (fn2-envelope-prefix (take 3 *fn2-native-trace*) 0 t nil nil fn2-core)
      (let ((antecedent (and (true-listp (take 3 *fn2-native-trace*))
                             (natp 0) (eq first :pass) (consp taken))))
        (mv-let (last taken caps fn2-core)
          (fn2-envelope-prefix (nthcdr 3 *fn2-native-trace*) 3 t
            (if drop-taken nil taken) caps fn2-core)
          (declare (ignore taken))
          (mv (list antecedent last caps) fn2-core))))))
(defun fn2-envelope-resume-test (drop-taken)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (answer fn2-core) (fn2-envelope-resume-test-run drop-taken fn2-core) answer)))

(assert-event
 (let ((whole (fn2-envelope-replay *fn2-native-trace* *fn2-envelope-prefix-test-profile* t))
       (resumed (fn2-envelope-resume-test nil))
       (mutant (fn2-envelope-resume-test t)))
   (and (eq (car whole) :pass)
        (equal resumed (cons t whole))
        (equal (take 2 mutant) '(t (:ack-untaken 3))))))
