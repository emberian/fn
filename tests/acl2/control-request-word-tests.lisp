; fn: witnesses and teeth for books/control-request-word.lisp (lane
; online-reclaim-5): an operator request never prints `NONE' beside a fault.
(in-package "ACL2")
(include-book "../../books/control-request-word")
(include-book "must-fail-checked")

; KEYSTONE fn-crqw-request-word-names-the-outcome, positive witnesses.  The
; reply the owner sends when its reclaim handler faulted: status :fault, no
; reason (host/native/control.lisp: reason nil is ACL2's NONE).
(defconst *crqw-t-none* (fn-nctrl-reason-word nil))
(assert-event (equal *crqw-t-none* *fn-nctrl-no-reason-word*))
(assert-event (member-equal :fault *fn-nctrl-statuses*))
(assert-event (equal (fn-crqw-request-word :fault *crqw-t-none*) (list 102 97 117 108 116)))  ; fault
(assert-event (equal (fn-crqw-request-word :uncertain *crqw-t-none*)
                     (fn-nctrl-reason-word :uncertain)))
; A word the owner named is printed as named (`reclaim installed').
(defconst *crqw-t-installed* (fn-nctrl-reason-word :installed))
(assert-event (not (equal *crqw-t-installed* *fn-nctrl-no-reason-word*)))
(assert-event (equal (fn-crqw-request-word :accepted *crqw-t-installed*) *crqw-t-installed*))
(assert-event (equal (fn-crqw-request-word :refused (fn-nctrl-reason-word :deferred-delta))
                     (fn-nctrl-reason-word :deferred-delta)))
; The old line: NONE beside the fault.
(must-fail-checked
 (assert-event (equal (fn-crqw-request-word :fault *crqw-t-none*) *fn-nctrl-no-reason-word*)))

; Hypothesis removal (the only hypothesis: STATUS is a control status): nil is
; no status, and its word is NONE -- the conclusion's first literal fails.
(assert-event (not (member-equal nil *fn-nctrl-statuses*)))
(assert-event (equal (fn-crqw-request-word nil *crqw-t-none*) *fn-nctrl-no-reason-word*))
