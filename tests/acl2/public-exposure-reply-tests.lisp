; Witnesses and teeth for books/public-exposure-reply.lisp (PRF-161;
; exposure-reply-size, PKT-481).
;
; The three keystones have no hypotheses, so the rule asks for a reachable
; witness of each conclusion, not must-fails per hypothesis.  Each witness
; here makes the conclusion non-degenerate (a count above zero, a 481 split
; across effects, the failed-login close), and each MUTATION witness,
; labelled, shows the conclusion is false for the tempting wrong twin: the
; recognizer started off a line start, and a scan that restarts at every
; effect.  The served-size witness runs the executable the host calls over
; a 3 MiB reply, the size that stopped the owner before the fix.
(in-package "ACL2")
(include-book "../../books/public-exposure-reply")
(include-book "must-fail-checked")

(defconst *pxr-lim* (fn-exp-lim-make 3 2 2 600 60 2 1 :none))
(defconst *pxr-xs* (fn-exp-register (fn-exp-initial) 5 '(:inet 127 0 0 2) 5000))

(defconst *pxr-481* (fn-exp-line "481 authentication failed"))
(defconst *pxr-281* (fn-exp-line "281 authentication accepted"))

; -----------------------------------------------------------------------------
; KEYSTONE fn-exp-481-scan-counts-the-481-replies
;   (car (fn-exp-481-scan octets 1 0)) = (fn-exp-481-count octets t)

; Witness: two 481 replies around a 281, and a "481 " that is not at a line
; start ("X481 "), which neither side counts.
(defconst *pxr-stream*
  (append *pxr-481* *pxr-281* (fn-record-string-octets "X481 ") '(13 10)
          *pxr-481*))
(assert-event (equal (fn-exp-481-count *pxr-stream* t) 2))
(assert-event (equal (car (fn-exp-481-scan *pxr-stream* 1 0))
                     (fn-exp-481-count *pxr-stream* t)))
; A reply cut short after "481" is not a 481 reply on either side.
(assert-event (equal (car (fn-exp-481-scan '(52 56 49) 1 0)) 0))
(assert-event (equal (fn-exp-481-count '(52 56 49) t) 0))

; MUTATION: the recognizer started off a line start misses the first reply.
(must-fail-checked
 (assert-event (equal (car (fn-exp-481-scan *pxr-stream* 0 0))
                      (fn-exp-481-count *pxr-stream* t))))

; -----------------------------------------------------------------------------
; KEYSTONE fn-exp-effects-scan-is-the-reply-scan
;   the scan over EFFECTS is the recognizer over (fn-served-reply-octets
;   effects), and its ANSWERED is whether that reply is non-empty.

; Witness: "481 " split over three :reply effects, with an effect that is not
; a reply between them; the reply stream holds one 481 reply.
(defconst *pxr-split*
  (list (list :reply '(13 10 52))
        (list :close)
        (list :reply '(56 49))
        (list :reply (append '(32) (fn-record-string-octets "failed") '(13 10)))))
(defconst *pxr-split-octets* (fn-served-reply-octets *pxr-split*))
(assert-event (equal (fn-exp-481-count *pxr-split-octets* t) 1))
(assert-event
 (let ((r (fn-exp-effects-scan *pxr-split* 1 0 nil))
       (s (fn-exp-481-scan *pxr-split-octets* 1 0)))
   (and (equal (car r) 1)
        (equal (car r) (car s))
        (equal (cadr r) (cdr s))
        (equal (cddr r) t))))
; ANSWERED is NIL exactly when no reply octet is sent.
(assert-event
 (equal (cddr (fn-exp-effects-scan (list (list :close) (list :reply nil)) 1 0 nil))
        nil))

; MUTATION: a scan that restarts the recognizer at each effect counts a
; "481 " that follows "X" on the wire as a reply of its own.
(defun pxr-restart-scan (effects acc)
  (declare (xargs :guard (natp acc)))
  (if (consp effects)
      (pxr-restart-scan (cdr effects)
                        (car (fn-exp-481-scan (fn-exp-effect-reply (car effects))
                                              1 acc)))
    acc))
(defconst *pxr-mid-line*
  (list (list :reply '(88)) (list :reply '(52 56 49 32 13 10))))
(assert-event (equal (car (fn-exp-effects-scan *pxr-mid-line* 1 0 nil)) 0))
(must-fail-checked
 (assert-event (equal (pxr-restart-scan *pxr-mid-line* 0)
                      (fn-exp-481-count (fn-served-reply-octets *pxr-mid-line*) t))))

; -----------------------------------------------------------------------------
; KEYSTONE fn-exp-observe-effects-is-the-observation-of-the-reply (and
; fn-exp-observe-effects-unfolds): the host's call decides what
; fn-exp-observe decides on the reply octets.

; Witness: the second failed login in the minute, split over effects, closes
; with the 400, exactly as fn-exp-observe decides over the concatenation.
(defconst *pxr-f1*
  (fn-exp-observe-effects *pxr-xs* *pxr-lim* 5 5100 *pxr-split* 30 nil nil))
(assert-event (equal (car *pxr-f1*) :continue))
(defconst *pxr-f2*
  (fn-exp-observe-effects (cdr *pxr-f1*) *pxr-lim* 5 5200 *pxr-split* 30 nil nil))
(assert-event (equal (car *pxr-f2*) (list :close (fn-exp-line *fn-exp-auth-close-line*))))
(assert-event
 (equal *pxr-f2*
        (fn-exp-observe (cdr *pxr-f1*) *pxr-lim* 5 5200 *pxr-split-octets* 30 nil nil)))
(assert-event
 (let ((r (fn-exp-effects-scan *pxr-split* 1 0 nil)))
   (equal (fn-exp-observe-facts (cdr *pxr-f1*) *pxr-lim* 5 5200
                                (if (cddr r) t nil) (car r) 30 nil nil)
          *pxr-f2*)))

; The served size: the executable the host calls, over one step whose reply
; is 3 MiB (an ARTICLE of a 3 MiB article).  Before PKT-481's fix this step
; exhausted the control stack in fn-exp-481-count.  The step answered, so
; the connection's progress stamp moves to NOW and it counts as answered.
(assert-event
 (let ((r (fn-exp-observe-effects
           *pxr-xs* *pxr-lim* 5 7000
           (list (list :reply (make-list 3145728 :initial-element 65))
                 (list :reply '(13 10 46 13 10)))
           40 nil nil)))
   (and (equal (car r) :continue)
        (equal (fn-exp-entry-last (fn-exp-find 5 (fn-exp-conns (cdr r)))) 7000)
        (equal (fn-exp-entry-answered (fn-exp-find 5 (fn-exp-conns (cdr r)))) t)
        (equal (fn-exp-fails (cdr r)) nil))))

; -----------------------------------------------------------------------------
; KEYSTONE fn-exp-idle-keeps-after-progress (lane served-catalog-live; Codex
; r67 F3; Astra c07): the transport accepting output refreshes the idle
; deadline.
;   H  (< (nfix later) (+ (nfix now) (* 1000 (fn-exp-lim-idle lim))))
; The connection (id 5, registered at 5000, limits idle 600 s / first 60 s)
; steps an OVER range whose effects are one cursor: the step sends no octet,
; so the observation records no progress and no answer.

(defconst *pxr-cursor-effects* (list (list :over-cursor (list "fn.test" 1 100000 3 nil t nil))))
(defconst *pxr-after-over*
  (cdr (fn-exp-observe-effects *pxr-xs* *pxr-lim* 5 6000 *pxr-cursor-effects* 12 nil nil)))

; The defect, as it was: the cursor step is not an answer; a reply that is
; still being written 60 s after open is closed by the FIRST-command limit.
(assert-event (not (fn-exp-entry-answered (fn-exp-find 5 (fn-exp-conns *pxr-after-over*)))))
(assert-event (equal (car (fn-exp-idle *pxr-after-over* *pxr-lim* 5 65000)) :close))

; POSITIVE: the hypothesis and the conclusion.  The socket taking a window
; of the reply at 64000 is progress: the check at 65000 keeps, and so does every check until the idle
; limit has passed since the quantum.
(defconst *pxr-progressed* (fn-exp-progress *pxr-after-over* 5 64000))
(assert-event (< 65000 (+ 64000 (* 1000 (fn-exp-lim-idle *pxr-lim*)))))
(assert-event (equal (car (fn-exp-idle *pxr-progressed* *pxr-lim* 5 65000)) :keep))
(assert-event (equal (car (fn-exp-idle *pxr-progressed* *pxr-lim* 5 663999)) :keep))
(assert-event (fn-exp-entry-answered (fn-exp-find 5 (fn-exp-conns *pxr-progressed*))))

; HYPOTHESIS REMOVAL: at exactly the idle limit after the quantum the
; hypothesis fails and so does the conclusion (silence is still closed).
(assert-event (not (< 664000 (+ 64000 (* 1000 (fn-exp-lim-idle *pxr-lim*))))))
(assert-event (equal (car (fn-exp-idle *pxr-progressed* *pxr-lim* 5 664000)) :close))

; FRAME (fn-exp-progress-frame): another connection's entry, and an unknown
; id, are untouched.
(defconst *pxr-two* (fn-exp-register *pxr-after-over* 6 '(:inet 127 0 0 3) 7000))
(assert-event (equal (fn-exp-find 6 (fn-exp-conns (fn-exp-progress *pxr-two* 5 64000)))
                     (fn-exp-find 6 (fn-exp-conns *pxr-two*))))
(assert-event (equal (fn-exp-progress *pxr-two* 99 64000) *pxr-two*))
; MUTATION (labelled): progress credited to the wrong connection does not
; keep this one.
(assert-event (equal (car (fn-exp-idle (fn-exp-progress *pxr-two* 6 64000) *pxr-lim* 5 65000))
                     :close))
