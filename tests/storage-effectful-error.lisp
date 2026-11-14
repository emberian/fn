; Source probe: physical prefixes and real commit uncertainty are separate
; controls of the same simulator fault. This is not a whole-host ACK theorem.
(in-package "ACL2")
(include-book "../books/commit-proof")
(include-book "storage-effectful-physical")

; The same effectful error then traverses the actual issued commit writes,
; completion normalization, harvester and generated commit decision. Two
; earlier accepted batches must still recover after the later uncertainty.
(defun fn2-see-commit (fault)
 (declare (xargs :verify-guards nil))
 (let* ((p (fn2-cm-profile :crash-only t t nil 0 0))
        (r (fn2-commit-proof-run
            (append (make-list 600 :initial-element (list :auto *fn2-fault-none*))
                    '((:start 0 2 5 0) (:start 1 2 7 0))
                    (make-list 600 :initial-element (list :auto fault))) p 0 2 1))
        (replies (fn2-commit-proof-replies r)))
  (and (fn2-commit-proof-admitted r) (fn2-commit-proof-saw-uncertain r)
       (fn2-commit-proof-stable r) (fn2-commit-ack-evidencep r)
       (equal (len replies) 2)
       (equal (cdr (assoc-equal 1 replies)) 2)
       (equal (cdr (assoc-equal 2 replies)) 2)
       (equal (len (fn2-commit-proof-recovered r)) 2))))

(assert-event (and (fn2-see-commit *fn2-fault-no-space*)
                   (fn2-see-commit *fn2-fault-write-io*)))

; A successfully performed fence is held before its terminal, then the actual
; clock/mailbox/commit timeout path runs. The matching control posts that same
; saved return normally. Both use real commit writes after two accepted batches.
(defun fn2-see-held-commit (hold)
 (declare (xargs :verify-guards nil))
 (let* ((p (fn2-cm-profile :crash-only t t nil 0 0))
        (r (fn2-commit-proof-run
            (append (make-list 600 :initial-element (list :auto *fn2-fault-none*))
                    '((:start 0 2 5 0))
                    (make-list 600 :initial-element
                      (if hold '(:auto-lost-fence) '(:auto-staged-fence)))) p 0 2 1))
        (replies (fn2-commit-proof-replies r)))
  (and (fn2-commit-proof-admitted r) (fn2-commit-proof-stable r)
       (fn2-commit-ack-evidencep r)
       (equal (fn2-commit-proof-saw-uncertain r) hold)
       (equal (len replies) (if hold 2 3))
       (equal (cdr (assoc-equal 1 replies)) 2)
       (equal (cdr (assoc-equal 2 replies)) 2)
       (if hold (not (assoc-equal 3 replies))
         (equal (cdr (assoc-equal 3 replies)) 2))
       ; The held third batch may not reply, but its physically persisted
       ; seal is real: recovery must find it along with the prior batches.
       (equal (len (fn2-commit-proof-recovered r)) 3))))

(assert-event (and (fn2-see-held-commit nil) (fn2-see-held-commit t)))
