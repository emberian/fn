; Exact contact-window witnesses for the native BP contact caller.
(in-package "ACL2")
(include-book "../../books/bp-contact-service")
(include-book "std/testing/must-fail" :dir :system)

(defconst *bpsc-a* (cons :dtn '(47 47 102 110 45 97 47)))
(defconst *bpsc-b* (cons :dtn '(47 47 102 110 45 98 47)))
(defconst *bpsc-window* (fn-bpsc-window *bpsc-b* 10 20))
(defconst *bpsc-mid* (fn-clock-observation 15 0 0 nil))

(assert-event (fn-bpsc-windowp *bpsc-window*))
(assert-event (equal (fn-bpsc-relative-window *bpsc-b* *bpsc-mid* 0 5)
                     (fn-bpsc-window *bpsc-b* 15 20)))
(assert-event (equal (fn-bpsc-contact-decision
                      (fn-bpsc-relative-window *bpsc-b* *bpsc-mid* 0 5)
                      *bpsc-b* *bpsc-mid* (list *bpsc-b*))
                     :open))
(assert-event (equal (fn-bpsc-contact-decision
                      (fn-bpsc-relative-window *bpsc-b* *bpsc-mid* 1 5)
                      *bpsc-b* *bpsc-mid* (list *bpsc-b*))
                     :closed))
(assert-event (not (fn-bpsc-relative-window
                    *bpsc-b* *bpsc-mid* 0 18446744073709551615)))
(assert-event (equal (fn-bpsc-contact-decision
                      *bpsc-window* *bpsc-b* *bpsc-mid* (list *bpsc-b*))
                     :open))
(assert-event (equal (fn-bpsc-contact-event
                      *bpsc-window* *bpsc-b* *bpsc-mid* (list *bpsc-b*))
                     (list :contact *bpsc-b* t)))
(assert-event (equal (fn-bpsc-contact-decision
                      *bpsc-window* *bpsc-a* *bpsc-mid* (list *bpsc-a*))
                     :closed))
(assert-event (equal (fn-bpsc-contact-decision
                      *bpsc-window* *bpsc-b* *bpsc-mid* nil)
                     :closed))
(assert-event (equal (fn-bpsc-contact-decision
                      *bpsc-window* *bpsc-b*
                      (fn-clock-observation 21 0 0 nil) (list *bpsc-b*))
                     :closed))
(assert-event (equal (fn-bpsc-contact-decision
                      (list :window *bpsc-b* 20 10)
                      *bpsc-b* *bpsc-mid* (list *bpsc-b*))
                     :invalid))

; Each premise of the opening theorem has a concrete counterexample if
; removed: wrong peer, no ready peer, outside the window, malformed window.
(must-fail
 (defthm bpsc-open-without-matching-peer
   (equal (fn-bpsc-contact-decision
           *bpsc-window* *bpsc-a* *bpsc-mid* (list *bpsc-a*)) :open)))
(must-fail
 (defthm bpsc-open-without-ready-peer
   (equal (fn-bpsc-contact-decision
           *bpsc-window* *bpsc-b* *bpsc-mid* nil) :open)))
(must-fail
 (defthm bpsc-open-after-end
   (equal (fn-bpsc-contact-decision
           *bpsc-window* *bpsc-b* (fn-clock-observation 21 0 0 nil)
           (list *bpsc-b*)) :open)))
(must-fail
 (defthm bpsc-open-with-malformed-window
   (equal (fn-bpsc-contact-decision
           (list :window *bpsc-b* 20 10) *bpsc-b* *bpsc-mid*
           (list *bpsc-b*)) :open)))
