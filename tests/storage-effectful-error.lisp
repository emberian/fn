; Source probe: physical prefixes and real commit uncertainty are separate
; controls of the same simulator fault. This is not a whole-host ACK theorem.
(in-package "ACL2")
(include-book "../books/commit-proof")
(include-book "storage-effectful-physical")

; The same effectful error then traverses the actual issued commit writes,
; completion normalization, harvester and generated commit decision. Two
; earlier accepted batches must still recover after the later uncertainty.
(defun fn2-see-commit ()
 (declare (xargs :verify-guards nil))
 (let* ((p (fn2-cm-profile :crash-only t t nil 0 0))
        (r (fn2-commit-proof-run
            (append (make-list 600 :initial-element '(:auto 26))
                    '((:start 0 2 5 0) (:start 1 2 7 0))
                    (make-list 600 :initial-element '(:auto 12))) p 0 2 1))
        (replies (fn2-commit-proof-replies r)))
  (and (fn2-commit-proof-admitted r) (fn2-commit-proof-saw-uncertain r)
       (fn2-commit-proof-stable r) (fn2-commit-ack-evidencep r)
       (equal (len replies) 2)
       (equal (cdr (assoc-equal 1 replies)) 2)
       (equal (cdr (assoc-equal 2 replies)) 2)
       (equal (len (fn2-commit-proof-recovered r)) 2))))

(assert-event (fn2-see-commit))
