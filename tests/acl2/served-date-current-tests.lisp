; Literal witnesses for the t42 served-step DATE theorems.
(in-package "ACL2")
(include-book "../../books/served-date-current")

(defconst *date-old* (fn-clock-observation 1000000 843004800000 500 t))
(defconst *date-now* (fn-clock-observation 1061000 843004861000 500 t))
(defconst *date-later* (fn-clock-observation 1062000 843004862000 500 t))
(defconst *date-no-wall* (fn-clock-observation 1061000 0 500 nil))

; Positive: the theorem has no hypotheses. The connection is reachable by
; served-open; the current reading is over a minute after the pinned one.
(assert-event
 (let ((reply (fn-served-result-effects
               (fn-served-step (fn-date-test-conn *date-old* *date-now*)
                               '(68 65 84 69 13 10) fn-arena))))
   (and (fn-served-connp (fn-date-test-conn *date-old* *date-now*))
        (equal reply
               (fn-nntp-result-effects
                (fn-nntp-date-response nil (fn-nntp-env *date-now* nil t))))
        (equal reply
               (fn-served-result-effects
                (fn-served-step (fn-date-test-conn nil *date-now*)
                                '(68 65 84 69 13 10) fn-arena)))
        (not (equal reply
                    (fn-served-result-effects
                     (fn-served-step (fn-date-test-conn *date-old* *date-later*)
                                     '(68 65 84 69 13 10) fn-arena)))))))

; No hypothesis-removal witnesses: the keystone is unconditional, including
; malformed/missing observations. These check both distinct named refusals.
(assert-event
 (and
  (equal (fn-served-result-effects
          (fn-served-step (fn-date-test-conn *date-old* nil)
                          '(68 65 84 69 13 10) fn-arena))
         (fn-nntp-result-effects
          (fn-nntp-single nil (fn-proto-text "DATE" :no-observation))))
  (equal (fn-served-result-effects
          (fn-served-step (fn-date-test-conn *date-old* *date-no-wall*)
                          '(68 65 84 69 13 10) fn-arena))
         (fn-nntp-result-effects
          (fn-nntp-single nil (fn-proto-text "DATE" :no-wall))))
  (not (equal (fn-proto-text "DATE" :no-observation)
              (fn-proto-text "DATE" :no-wall)))))

; MUTATION (old implementation): selecting the pinned environment produces
; the old timestamp and violates the literal theorem conclusion.
(assert-event
 (let ((old-reply (fn-nntp-result-effects
                   (fn-nntp-date-response nil (fn-nntp-env *date-old* nil t))))
       (current-reply (fn-nntp-result-effects
                       (fn-nntp-date-response nil (fn-nntp-env *date-now* nil t)))))
   (and (fn-clock-observationp *date-old*)
        (fn-clock-has-wall *date-old*)
        (fn-clock-observationp *date-now*)
        (fn-clock-has-wall *date-now*)
        (not (equal old-reply current-reply)))))

; NEWGROUPS gets the same current-year selection; NEWNEWS keeps its separate
; historical horizon until the parser-current split is implemented.
(assert-event
 (and (equal (fn-nntp-env-observation
              (fn-post-command-env nil *date-old* *date-now*
               (list :command (fn-nntp-string-octets "NEWGROUPS 260101 000000 GMT"))))
             *date-now*)
      (equal (fn-nntp-env-observation
              (fn-post-command-env nil *date-old* *date-now*
               (list :command (fn-nntp-string-octets "NEWNEWS * 260101 000000 GMT"))))
             *date-old*)))

; Positive, full (empty) antecedent of the post-layer noninterference law.
(assert-event
 (let* ((archive (fn-initial-state nil))
        (ps (fn-post-open-session archive))
        (config (fn-inj-make-config t '(102 110) nil 32768)))
   (equal (fn-nntp-post-step-pinned ps archive nil nil config *date-old* *date-now*
                                   '(:command (68 65 84 69)) fn-arena)
          (fn-nntp-post-step-pinned ps archive nil nil config nil *date-now*
                                   '(:command (68 65 84 69)) fn-arena))))

; Full empty antecedent of the arbitrary-session served-step theorem.
; This is a successful DATE path, not a no-op/gated witness.
(assert-event
 (let* ((conn (fn-date-test-conn *date-old* *date-now*))
        (reply (fn-served-result-effects
                (fn-served-step (fn-date-command-conn conn *date-old*)
                                '(68 65 84 69 13 10) fn-arena))))
   (and (equal reply
               (fn-served-result-effects
                (fn-served-step (fn-date-command-conn conn nil)
                                '(68 65 84 69 13 10) fn-arena)))
        (equal reply (fn-nntp-result-effects
                      (fn-nntp-date-response nil (fn-nntp-env *date-now* nil t)))))))

; Case-insensitive command selection; invalid arguments still win over a
; missing current reading (the normal DATE syntax refusal, not 503).
(assert-event
 (and
  (equal (fn-served-result-effects
          (fn-served-step (fn-date-test-conn *date-old* *date-now*)
                          '(100 65 116 69 13 10) fn-arena))
         (fn-nntp-result-effects
          (fn-nntp-date-response nil (fn-nntp-env *date-now* nil t))))
  (equal (fn-served-result-effects
          (fn-served-step (fn-date-test-conn *date-old* nil)
                          '(68 65 84 69 32 120 13 10) fn-arena))
         (fn-nntp-result-effects
          (fn-nntp-single nil (fn-proto-text "DATE" :syntax))))))
