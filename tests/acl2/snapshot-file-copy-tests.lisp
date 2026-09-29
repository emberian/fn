(in-package "ACL2")
(include-book "../../books/snapshot-file-copy")
(include-book "must-fail-checked")
; A nonempty prefix crosses several quanta and its final partial read is
; required, not truncated at the full-quantum boundary.
(defconst *fn-osc0* (fn-osc-begin 41 10))
(assert-event
 (let* ((s *fn-osc0*) (q 4) (got 4)
        (next (cadr (fn-osc-advance s q got))))
   (and (fn-osc-statep s) (posp q) (< (nth 2 s) (nth 1 s))
        (equal got (nth 3 (fn-osc-plan s q)))
        (equal (fn-osc-plan s q) '(:read 41 0 4))
        (equal (fn-osc-advance s q got) '(:continue (41 10 4)))
        (fn-osc-statep next) (equal (car next) (car s))
        (equal (nth 1 next) (nth 1 s))
        (equal (nth 2 next) (+ (nth 2 s) got))
        (< (nth 2 s) (nth 2 next)) (<= got q)
        (<= (nth 2 next) (nth 1 s)))))
(defconst *fn-osc8* '(41 10 8))
(assert-event (equal (fn-osc-plan *fn-osc8* 4) '(:read 41 8 2)))
(assert-event (equal (fn-osc-advance *fn-osc8* 4 2) '(:continue (41 10 10))))
(assert-event
 (let ((s '(41 10 10)) (q 4))
   (and (fn-osc-statep s) (posp q)
        (equal (car (fn-osc-plan s q)) :done)
        (equal (nth 2 s) (nth 1 s)))))
; Hypothesis-removal: every retained successful-step hypothesis holds;
; omitting the full-read equality leaves a refusal, never an advanced prefix.
(assert-event
 (let ((s *fn-osc8*) (q 4) (got 1))
   (and (fn-osc-statep s) (posp q) (< (nth 2 s) (nth 1 s))
        (not (equal got (nth 3 (fn-osc-plan s q))))
        (equal (fn-osc-advance s q got) '(:refused :short-read (41 10 8)))
        (not (equal (car (fn-osc-advance s q got)) :continue)))))
(must-fail-checked
 (defthm fn-osc-completes-without-the-full-read
   (implies (and (fn-osc-statep s) (posp q) (< (nth 2 s) (nth 1 s)))
            (equal (car (fn-osc-advance s q got)) :continue))))
; Malformed-state / invalid quantum witnesses are not reachable cursor steps.
(assert-event (equal (fn-osc-plan '(41 10 11) 4) '(:refused :cursor)))
(assert-event (equal (fn-osc-plan *fn-osc0* 0) '(:refused :quantum)))
