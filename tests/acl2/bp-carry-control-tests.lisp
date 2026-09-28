; Teeth for books/bp-carry-control.lisp (PKT-869, lane operations).
(in-package "ACL2")
(include-book "../../books/bp-carry-control")
(include-book "must-fail-checked")

(defconst *bpcc-paused* (list nil (list "w1") nil))
(defconst *bpcc-dropped* (list nil nil (list (cons "w2" "sender retired"))))
(defconst *bpcc-plan* '(:request attempt outcome key adu "dtn://peer/" nil))

; KEYSTONE fn-bpcc-gate-refuses-a-held-work: its antecedent (a hold) and
; conclusion (refused by name), for a paused and a dropped work.
(assert-event (equal (fn-bpcc-work-state *bpcc-paused* "w1") :paused))
(assert-event (equal (fn-bpcc-request-gate *bpcc-paused* "w1" *bpcc-plan*)
                     '(:refused :carry-paused)))
(assert-event (equal (fn-bpcc-work-state *bpcc-dropped* "w2") :dropped))
(assert-event (equal (fn-bpcc-request-gate *bpcc-dropped* "w2" *bpcc-plan*)
                     '(:refused :carry-dropped)))
; "*" holds every work.
(assert-event (equal (fn-bpcc-request-gate (list t nil nil) "w9" *bpcc-plan*)
                     '(:refused :carry-paused)))
; Hypothesis removal: no hold, and the request plan passes unchanged.
(assert-event (null (fn-bpcc-work-state (fn-bpcc-initial) "w1")))
(assert-event (equal (fn-bpcc-request-gate (fn-bpcc-initial) "w1" *bpcc-plan*) *bpcc-plan*))
(assert-event (equal (fn-bpcc-request-gate *bpcc-paused* "w3" *bpcc-plan*) *bpcc-plan*))
(must-fail-checked
 (defthm bpcc-gate-refuses-without-a-hold
   (equal (car (fn-bpcc-request-gate c work-id plan)) :refused)
   :rule-classes nil))

; fn-bpcc-drop-is-final: a resume of "*" and a pause of the work leave the
; drop; a resume ends a pause.
(assert-event (equal (fn-bpcc-work-state
                      (fn-bpcc-apply *bpcc-dropped* '(:carry "resume" "*" "-")) "w2")
                     :dropped))
(assert-event (equal (fn-bpcc-work-state
                      (fn-bpcc-apply *bpcc-dropped* '(:carry "pause" "w2" "-")) "w2")
                     :dropped))
(assert-event (null (fn-bpcc-work-state
                     (fn-bpcc-apply *bpcc-paused* '(:carry "resume" "w1" "-")) "w1")))
(assert-event (equal (fn-bpcc-dropped-reason
                      (fn-bpcc-apply (fn-bpcc-initial) '(:carry "drop" "w4" "no route")) "w4")
                     "no route"))

; The refusals by name over an image with no works.
(assert-event (equal (fn-bpcc-refusal nil (fn-bpcc-initial) '(:carry "pause" "w1" "-")) :unknown-work))
(assert-event (null (fn-bpcc-refusal nil (fn-bpcc-initial) '(:carry "pause" "*" "-"))))
(assert-event (equal (fn-bpcc-refusal nil (list t nil nil) '(:carry "pause" "*" "-")) :already-paused))
(assert-event (equal (fn-bpcc-refusal nil (fn-bpcc-initial) '(:carry "resume" "*" "-")) :not-paused))
(assert-event (equal (fn-bpcc-refusal nil (fn-bpcc-initial) '(:carry "drop" "*" "x")) :unknown-work))
(assert-event (equal (fn-bpcc-refusal nil (fn-bpcc-initial) '(:carry "drop" "w1")) :malformed))
