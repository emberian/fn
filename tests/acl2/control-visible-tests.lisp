; Teeth for books/control-visible.lisp: reachable witnesses for
; fn-ctl-visible-add-is-visible and fn-ctl-visible-extend-is-visible, and
; per hypothesis (the carried list is the definition's) a witness where the
; conclusion fails without it.
(in-package "ACL2")
(include-book "../../books/control-visible")
(include-book "std/testing/must-fail" :dir :system)

(defconst *cvt-p* (make-list 32 :initial-element 17))
(defconst *cvt-p-hex* (fn-record-octets-string (fn-stx-hex-octets *cvt-p*)))
(defconst *cvt-p-verified* (fn-stx-make-verdict :verified *cvt-p* 1))
(defun cvt-art (msgid groups)
  (fn-make-article msgid nil groups nil t nil))
(defconst *cvt-t* (cvt-art "<t@example.invalid>" (list "fn.mod.a")))
(defconst *cvt-c* (cvt-art "<c@example.invalid>" (list "control.cancel")))
(defconst *cvt-o* (cvt-art "<o@example.invalid>" (list "fn.mod.a")))
(defconst *cvt-a* (cvt-art "<a@example.invalid>" (list "fn.misc")))
(defconst *cvt-verdicts*
  (list (cons "<a@example.invalid>" *cvt-p-verified*)
        (cons "<c@example.invalid>" *cvt-p-verified*)))
; The authority record (P holds cancel over fn.mod.*) withdrawing T, and
; the author record withdrawing P's own signed A, both caused by C.
(defconst *cvt-w-t*
  (fn-ctl-withdrawal-make "<t@example.invalid>" "<c@example.invalid>"
                          *cvt-p-hex* (list "fn.mod.*") 1))
(defconst *cvt-w-a*
  (fn-ctl-withdrawal-make "<a@example.invalid>" "<c@example.invalid>"
                          *cvt-p-hex* nil 1))
(defconst *cvt-ws* (list *cvt-w-t* *cvt-w-a*))

; fn-ctl-visible-add-is-visible.  Witnesses (the carried list is the
; definition's in each):
;   the cancel arrives after its targets: C over (O A T) drops T and A;
(assert-event
 (let ((old (list *cvt-o* *cvt-a* *cvt-t*)))
   (and (equal (fn-ctl-visible-articles old *cvt-ws* *cvt-verdicts*) old)
        (equal (fn-ctl-visible-add *cvt-c* old old *cvt-ws* *cvt-verdicts*)
               (list *cvt-c* *cvt-o*))
        (equal (fn-ctl-visible-add *cvt-c* old old *cvt-ws* *cvt-verdicts*)
               (fn-ctl-visible-articles (cons *cvt-c* old) *cvt-ws*
                                        *cvt-verdicts*)))))
;   the target arrives after its cancel (D29's early cancel): T over (C O)
;   is never added;
(assert-event
 (let* ((old (list *cvt-c* *cvt-o*))
        (vis (fn-ctl-visible-articles old *cvt-ws* *cvt-verdicts*)))
   (and (equal vis old)
        (equal (fn-ctl-visible-add *cvt-t* vis old *cvt-ws* *cvt-verdicts*)
               old)
        (equal (fn-ctl-visible-articles (cons *cvt-t* old) *cvt-ws*
                                        *cvt-verdicts*)
               old))))
;   an ordinary article is consed and nothing is walked.
(assert-event
 (let* ((old (list *cvt-c* *cvt-t*))
        (vis (fn-ctl-visible-articles old *cvt-ws* *cvt-verdicts*)))
   (and (equal vis (list *cvt-c*))
        (not (fn-ctl-causes-p *cvt-ws* "<o@example.invalid>"))
        (equal (fn-ctl-visible-add *cvt-o* vis old *cvt-ws* *cvt-verdicts*)
               (list *cvt-o* *cvt-c*)))))
; Teeth, the one hypothesis: a carried list that is not the definition's
; (here the raw archive, which still holds the withdrawn T) is not repaired
; by an ordinary article, so the conclusion fails.
(must-fail
 (assert-event
  (let ((old (list *cvt-c* *cvt-t*)))
    (equal (fn-ctl-visible-add *cvt-o* old old *cvt-ws* *cvt-verdicts*)
           (fn-ctl-visible-articles (cons *cvt-o* old) *cvt-ws*
                                    *cvt-verdicts*)))))

; fn-ctl-visible-extend-is-visible.  Witness: from the empty archive, the
; batch (O C T A) newest first gives the definition's list (O C).
(assert-event
 (let ((delta (list *cvt-o* *cvt-c* *cvt-t* *cvt-a*)))
   (and (equal (fn-ctl-visible-extend delta nil nil *cvt-ws* *cvt-verdicts*)
               (fn-ctl-visible-articles delta *cvt-ws* *cvt-verdicts*))
        (equal (fn-ctl-visible-extend delta nil nil *cvt-ws* *cvt-verdicts*)
               (list *cvt-o* *cvt-c*)))))
; Teeth, the one hypothesis: a carried list holding an article the archive
; does not (O over the empty archive) is not repaired by the batch (C): the
; stray O stays and the conclusion fails.
(must-fail
 (assert-event
  (equal (fn-ctl-visible-extend (list *cvt-c*) (list *cvt-o*) nil *cvt-ws*
                                *cvt-verdicts*)
         (fn-ctl-visible-articles (list *cvt-c*) *cvt-ws* *cvt-verdicts*))))
