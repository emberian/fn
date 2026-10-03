; fn: the feed link backoff's test book (docs/proof-style.md sec. 6).
;
; Order: a scenario (the host's fold over ten consecutive failures of one
; link from `peer add''s base of 1000 ms, then a ready and a failure), the
; drop line, then the teeth of each keystone of books/feed-link-backoff.lisp.

(in-package "ACL2")
(include-book "../../books/feed-link-backoff")

; -----------------------------------------------------------------------------
; Scenario: what fnn-feed-drop-link carries across consecutive failures.

(defun flbt-run (base streak count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (let ((r (fn-flb-lost base streak)))
      (cons (car r) (flbt-run base (cadr r) (- count 1))))))

(defun flbt-streak-after (base streak count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      streak
    (flbt-streak-after base (cadr (fn-flb-lost base streak)) (- count 1))))

(assert-event
 (equal (flbt-run 1000 0 11)
        '(1000 2000 4000 8000 16000 32000 64000 128000 256000 300000 300000)))
; The carried streak stops advancing once the ceiling is reached.
(assert-event (equal (flbt-streak-after 1000 0 9) 9))
(assert-event (equal (flbt-streak-after 1000 0 11) 9))
; Ready resets: the next failure waits the base again.
(assert-event (equal (fn-flb-lost 1000 (fn-flb-ready 9)) '(1000 1)))
; A base of zero stays zero and never advances the streak.
(assert-event (equal (flbt-run 0 0 3) '(0 0 0)))
(assert-event (equal (flbt-streak-after 0 0 3) 0))
; A base above the ceiling is clamped to it.
(assert-event (equal (fn-flb-lost 999999 0) '(300000 0)))

; The drop line, as the native test reads it.
(assert-event
 (equal (fn-flb-drop-line '(102 115 110 49) :eof 2000)          ; "fsn1"
        (fn-record-string-octets
         "feed peer=fsn1 link=dropped reason=lost-eof retry-ms=2000")))
(assert-event
 (equal (fn-flb-drop-line '(102 115 110 49) :read 1000)
        (fn-record-string-octets
         "feed peer=fsn1 link=dropped reason=lost-read retry-ms=1000")))

(assert-event
 (equal (fn-flb-drop-line '(102 115 110 49) :credential 1000)
        (fn-record-string-octets
         "feed peer=fsn1 link=dropped reason=credential-refused retry-ms=1000")))

; -----------------------------------------------------------------------------
; Teeth: fn-flb-lost-advances-the-backoff
;
; (let* ((d1 (fn-flb-lost-delay base streak))
;        (d2 (fn-flb-lost-delay base (fn-flb-lost-streak base streak))))
;   (and (<= d1 d2)
;        (implies (and (< 0 d1) (< d1 *fn-flb-max-delay*)) (< d1 d2))))

(defun flbt-d1 (base streak) (fn-flb-lost-delay base streak))
(defun flbt-d2 (base streak)
  (fn-flb-lost-delay base (fn-flb-lost-streak base streak)))

; Reachable positive witness (the host's first two failures after a ready,
; base 1000): the complete antecedent and conclusion.
(assert-event
 (and (equal (flbt-d1 1000 0) 1000) (equal (flbt-d2 1000 0) 2000)
      (< 0 (flbt-d1 1000 0)) (< (flbt-d1 1000 0) *fn-flb-max-delay*)
      (<= (flbt-d1 1000 0) (flbt-d2 1000 0))
      (< (flbt-d1 1000 0) (flbt-d2 1000 0))))

; Hypothesis removal, (< 0 d1): base 0.  The retained hypothesis holds, the
; omitted one fails, and the strict conclusion fails.
(assert-event
 (and (< (flbt-d1 0 0) *fn-flb-max-delay*)
      (not (< 0 (flbt-d1 0 0)))
      (not (< (flbt-d1 0 0) (flbt-d2 0 0)))))

; Hypothesis removal, (< d1 *fn-flb-max-delay*): at the ceiling.  The
; retained hypothesis holds, the omitted one fails, the conclusion fails.
(assert-event
 (and (< 0 (flbt-d1 1000 9))
      (not (< (flbt-d1 1000 9) *fn-flb-max-delay*))
      (not (< (flbt-d1 1000 9) (flbt-d2 1000 9)))))

; -----------------------------------------------------------------------------
; Teeth: fn-flb-lost-doubles-below-the-ceiling
;
; (implies (<= (* 2 d1) *fn-flb-max-delay*) (equal d2 (* 2 d1)))

(assert-event
 (and (<= (* 2 (flbt-d1 1000 3)) *fn-flb-max-delay*)
      (equal (flbt-d1 1000 3) 8000)
      (equal (flbt-d2 1000 3) (* 2 (flbt-d1 1000 3)))))

; Hypothesis removal: 200000 doubles past the ceiling; d2 is the ceiling.
(assert-event
 (and (not (<= (* 2 (flbt-d1 200000 0)) *fn-flb-max-delay*))
      (not (equal (flbt-d2 200000 0) (* 2 (flbt-d1 200000 0))))))

; -----------------------------------------------------------------------------
; Teeth: fn-flb-first-loss-after-ready-waits-the-base (no hypothesis)

(assert-event
 (and (equal (fn-flb-lost-delay 1000 (fn-flb-ready 5)) 1000)
      (not (equal (fn-flb-lost-delay 1000 5) 1000))))
