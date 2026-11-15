; The production runtime map is disjoint from the five trailing jobs.
(in-package "ACL2")
(include-book "../books/machines-b")
(defun fn2-csm-controls (s count sources rows)
 (declare (xargs :guard (and (natp s) (natp count) (natp sources) (natp rows)) :measure (nfix (- (nfix count) (nfix s)))))
 (if (>= (nfix s) (nfix count)) nil
  (cons (fn2-b-ctl-runtime-row s count sources rows) (fn2-csm-controls (+ 1 s) count sources rows))))
(assert-event
 (let* ((p *fn2-profile-tiny*) (c (fn2-b-ctl-rows p)) (f (fn2-b-format-floor p)) (sources (fn2-b-cns-source-rows p))
        (first (fn2-b-ctl-slot 0 p)) (last (fn2-b-ctl-runtime-row (- c 1) c sources f)))
  (and (posp c) (equal (car (fn2-csm-controls 0 c sources f)) first)
       (equal last (- (fn2-b-cns-source-row 0 sources f) 1))
       (< last (fn2-b-semantic-retention-row f))
       ; Removing the reserved-job offset aliases the last control row
       ; with the ordinary block-read verifier at F-2.
       (equal (+ (- f c) -1 (- c 1)) (- f 2))
       (not (equal last (- f 2))))))
