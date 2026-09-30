(in-package "ACL2")
(include-book "../../books/consumer-remote-scan-model")

(defun fn-crpst-row (sequence groups)
 (declare (xargs :guard t))
 (fn-held-plain (fn-record-make sequence 1 1 "<remote@fn.test>" '(65) groups
                                "remote-pin" "remote-content" "remote-release" 1 841000000) 0))

(defun fn-crpst-plan (frontier)
 (declare (xargs :guard t))
 (list :scan-request nil (fn-cp-state '(104) '(110) frontier 2 nil)
       (append (fn-cp-entry '(105) '(97) '(105) 1 1 1 0) (list '((97) (98)) '(1)))
       '((97) (98)) '(scope) 0))

(defun fn-crpst-run (fuel answer key rows)
 (declare (xargs :guard (natp fuel) :verify-guards nil :measure (nfix fuel)))
 (if (or (zp fuel) (not (eq (fn-cp-nth 0 answer) :yield))) answer
  (let* ((s (fn-cp-nth 1 answer))
         (next (fn-crps-tick s key (nth (nfix (fn-cp-nth 5 s)) rows))))
   (if (and (fn-crpsm-invariant s)
             (or (not (eq (fn-cp-nth 0 next) :yield)) (fn-crpsm-invariant (fn-cp-nth 1 next))))
       (fn-crpst-run (1- fuel) next key rows) '(:broken)))))

;@positive fn-crps-begin-establishes-no-skipped-match
;@positive fn-crps-tick-preserves-no-skipped-match
;@positive fn-crps-poll-selects-one-actual-matching-event
; Filtered row, nonarticle event, crosspost once, exact retained continuation.
(assert-event
 (let* ((x (fn-crpst-row 2 '("a" "b")))
        (rows (list (fn-crpst-row 0 '("c")) '(:consumer-event) x))
        (start (fn-crps-begin (fn-crpst-plan 3) '(key) 3))
        (partial (fn-crpst-run 2 start '(key) rows))
        (out (fn-crpst-run 40 partial '(key) rows)))
  (and (fn-held-p x) (eq (fn-cp-nth 0 start) :yield) (fn-crpsm-invariant (fn-cp-nth 1 start))
       (eq (fn-cp-nth 0 partial) :yield) (fn-crpsm-invariant (fn-cp-nth 1 partial))
       (eq (fn-cp-nth 0 out) :poll) (equal (fn-cp-nth 2 out) x)
       (equal (fn-cp-nth 9 (fn-cp-nth 1 out)) 3) (equal (fn-cp-nth 3 out) 3)
       (not (fn-cp-nth 4 out)))))

; Empty filtered page advances exact window; policy0 refuses instead of default16.
(assert-event
 (let* ((rows (list (fn-crpst-row 0 '("c")) (fn-crpst-row 1 '("a"))))
        (out (fn-crpst-run 40 (fn-crps-begin (fn-crpst-plan 2) '(key) 1) '(key) rows)))
  (and (eq (fn-cp-nth 0 out) :poll) (null (fn-cp-nth 2 out))
       (equal (fn-cp-nth 9 (fn-cp-nth 1 out)) 1) (fn-cp-nth 4 out)
       (equal (fn-crps-begin (fn-crpst-plan 2) '(key) 0) '(:refused :scan-policy)))))

; Missing retained row is an explicit gap; no continuation crosses it.
(assert-event
 (let ((s (fn-cp-nth 1 (fn-crps-begin (fn-crpst-plan 2) '(key) 2))))
  (and (equal (fn-crps-tick s '(key) nil) '(:unavailable :history 0))
       (equal (fn-crps-tick s '(changed) (fn-crpst-row 0 '("a"))) '(:refused :consumer-source-changed)))))

;@hypothesis-removal fn-crps-tick-preserves-no-skipped-match carried-invariant
; Corrupted state: accepted yield but copied query suffix invented a member.
(assert-event
 (let* ((row (fn-crpst-row 0 '("c")))
        (s (fn-crps-state '(key) nil nil '((97)) 0 1 1 :match row '("c") '((100) (100))))
        (next (fn-crps-tick s '(key) nil)))
  (and (not (fn-crpsm-invariant s)) (eq (fn-cp-nth 0 next) :yield)
       (not (fn-crpsm-invariant (fn-cp-nth 1 next))))))


;@hypothesis-removal fn-crps-begin-establishes-no-skipped-match yield
(assert-event
 (let ((out (fn-crps-begin (fn-crpst-plan 2) '(key) 0)))
  (and (not (eq (fn-cp-nth 0 out) :yield))
       (not (fn-crpsm-invariant (fn-cp-nth 1 out))))))

;@hypothesis-removal fn-crps-tick-preserves-no-skipped-match yield
(assert-event
 (let* ((s (fn-cp-nth 1 (fn-crps-begin (fn-crpst-plan 2) '(key) 2)))
        (out (fn-crps-tick s '(changed) nil)))
  (and (fn-crpsm-invariant s) (not (eq (fn-cp-nth 0 out) :yield))
       (not (fn-crpsm-invariant (fn-cp-nth 1 out))))))

;@hypothesis-removal fn-crps-poll-selects-one-actual-matching-event carried-invariant
(assert-event
 (let* ((row (fn-crpst-row 0 '("c")))
        (s (fn-crps-state '(key) nil nil '((97)) 0 1 1 :match row '("c") '((99))))
        (out (fn-crps-tick s '(key) nil)))
  (and (not (fn-crpsm-invariant s)) (eq (fn-cp-nth 0 out) :poll) (fn-cp-nth 2 out)
       (not (fn-crpsm-intersects (fn-cp-nth 4 s) (fn-record-groups row))))))

;@positive fn-crps-tick-advances-a-matched-row-only-after-full-exclusion
(assert-event
 (let* ((row (fn-crpst-row 0 '("c")))
        (s (fn-crps-state '(key) nil nil '((97)) 0 1 1 :match row nil '((97))))
        (out (fn-crps-tick s '(key) nil)))
  (and (fn-crpsm-invariant s) (eq (fn-cp-nth 8 s) :match) (eq (fn-cp-nth 0 out) :yield)
       (equal (fn-cp-nth 5 (fn-cp-nth 1 out)) (1+ (nfix (fn-cp-nth 5 s))))
       (not (fn-crpsm-intersects (fn-cp-nth 4 s) (fn-record-groups row))))))

;@hypothesis-removal fn-crps-tick-advances-a-matched-row-only-after-full-exclusion carried-invariant
; Corrupted state: dropped the matching article suffix before inspection.
(assert-event
 (let* ((row (fn-crpst-row 0 '("a")))
        (s (fn-crps-state '(key) nil nil '((97)) 0 1 1 :match row nil '((97))))
        (out (fn-crps-tick s '(key) nil)))
  (and (not (fn-crpsm-invariant s)) (eq (fn-cp-nth 8 s) :match) (eq (fn-cp-nth 0 out) :yield)
       (equal (fn-cp-nth 5 (fn-cp-nth 1 out)) (1+ (nfix (fn-cp-nth 5 s))))
       (fn-crpsm-intersects (fn-cp-nth 4 s) (fn-record-groups row)))))

;@hypothesis-removal fn-crps-poll-selects-one-actual-matching-event poll
(assert-event
 (let* ((s (fn-cp-nth 1 (fn-crps-begin (fn-crpst-plan 2) '(key) 2)))
        (out (fn-crps-tick s '(key) nil)))
  (and (fn-crpsm-invariant s) (not (eq (fn-cp-nth 0 out) :poll))
       (fn-cp-nth 2 out) (not (equal (fn-cp-nth 2 out) (fn-cp-nth 9 s))))))

;@hypothesis-removal fn-crps-poll-selects-one-actual-matching-event selected-event
(assert-event
 (let* ((s (fn-cp-nth 1 (fn-crps-begin (fn-crpst-plan 0) '(key) 2)))
        (out (fn-crps-tick s '(key) nil)))
  (and (fn-crpsm-invariant s) (eq (fn-cp-nth 0 out) :poll) (not (fn-cp-nth 2 out))
       (not (fn-crpsm-intersects (fn-cp-nth 4 s)
                (fn-record-groups (fn-crps-row-article (fn-cp-nth 2 out))))))))

;@hypothesis-removal fn-crps-tick-advances-a-matched-row-only-after-full-exclusion match-phase
; Corrupted unused slot9 in a :read cursor has no matching-row meaning.
(assert-event
 (let* ((row (fn-crpst-row 0 '("a")))
        (s (fn-crps-state '(key) nil nil '((97)) 0 1 1 :read row nil nil))
        (out (fn-crps-tick s '(key) '(:nonarticle))))
  (and (fn-crpsm-invariant s) (not (eq (fn-cp-nth 8 s) :match))
       (eq (fn-cp-nth 0 out) :yield)
       (equal (fn-cp-nth 5 (fn-cp-nth 1 out)) (1+ (nfix (fn-cp-nth 5 s))))
       (fn-crpsm-intersects (fn-cp-nth 4 s) (fn-record-groups row)))))

;@hypothesis-removal fn-crps-tick-advances-a-matched-row-only-after-full-exclusion progress
(assert-event
 (let* ((row (fn-crpst-row 0 '("b")))
        (s (fn-crps-state '(key) nil nil '((97) (98)) 0 1 1 :match row '("b") '((97) (98))))
        (out (fn-crps-tick s '(key) nil)))
  (and (fn-crpsm-invariant s) (eq (fn-cp-nth 8 s) :match) (eq (fn-cp-nth 0 out) :yield)
       (not (equal (fn-cp-nth 5 (fn-cp-nth 1 out)) (1+ (nfix (fn-cp-nth 5 s)))))
       (fn-crpsm-intersects (fn-cp-nth 4 s) (fn-record-groups row)))))

;@hypothesis-removal fn-crps-tick-advances-a-matched-row-only-after-full-exclusion yield
; Corrupted CP queryID1 makes cursor slot5 look like a scalar scan position.
; The actual maintained CP producer never installs this malformed ID.
(assert-event
 (let* ((row (fn-crpst-row 0 '("a")))
        (entry (fn-cp-entry '(105) '(97) 1 1 1 1 0))
        (s (fn-crps-state '(key) nil entry '((97)) 0 1 1 :match row '("a") '((97))))
        (out (fn-crps-tick s '(key) nil)))
  (and (fn-crpsm-invariant s) (eq (fn-cp-nth 8 s) :match) (not (eq (fn-cp-nth 0 out) :yield))
       (equal (fn-cp-nth 5 (fn-cp-nth 1 out)) (1+ (nfix (fn-cp-nth 5 s))))
       (fn-crpsm-intersects (fn-cp-nth 4 s) (fn-record-groups row)))))

;@positive fn-crps-poll-selects-one-actual-matching-event
(assert-event
 (let* ((row (fn-crpst-row 0 '("a" "b")))
        (s (fn-crps-state '(key) nil nil '((97) (98)) 0 1 1 :match row '("a" "b") '((97) (98))))
        (out (fn-crps-tick s '(key) nil)))
  (and (fn-crpsm-invariant s) (eq (fn-cp-nth 0 out) :poll) (fn-cp-nth 2 out)
       (equal '(key) (fn-cp-nth 1 s)) (equal (fn-cp-nth 2 out) (fn-cp-nth 9 s))
       (fn-crpsm-intersects (fn-cp-nth 4 s)
          (fn-record-groups (fn-crps-row-article (fn-cp-nth 2 out))))
       (equal (fn-cp-nth 9 (fn-cp-nth 1 out)) (1+ (nfix (fn-cp-nth 5 s)))))))

;@positive fn-crps-tick-preserves-no-skipped-match
(assert-event
 (let* ((row (fn-crpst-row 0 '("b")))
        (s (fn-crps-state '(key) nil nil '((97) (98)) 0 1 1 :match row '("b") '((97) (98))))
        (out (fn-crps-tick s '(key) nil)))
  (and (fn-crpsm-invariant s) (eq (fn-cp-nth 0 out) :yield)
       (fn-crpsm-invariant (fn-cp-nth 1 out)))))
