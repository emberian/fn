(in-package "ACL2")
(include-book "substrate-profile-entry-tests")
(include-book "../../books/substrate-profile-selection")
(defun fn-stprt-call (cursor)
 (declare (xargs :guard
  (or (fn-stcp-at 4 cursor) (atom (fn-stcp-at 2 cursor))
      (atom (fn-stcp-at 3 cursor))
      (fn-stmt-p (car (fn-stcp-at 2 cursor))))
  :guard-hints (("Goal" :in-theory (disable fn-stpr-select-resume fn-stcp-at fn-stmt-p)))))
 (mv-let (w c e u) (fn-stpr-select-resume cursor) (list w c e u)))
(make-event (list 'defconst '*stprt-projection*
 (list 'quote (fn-stpr-project
  (list :select (list *stpet-statement*) '("fn.test" "fn.other") nil)
  *stcpt-profile* '(:pinned-cfg) 7 '(:pinned-keyring)))))
(make-event (list 'defconst '*stprt-start*
 (list 'quote (fn-stpr-select-start *stprt-projection*))))
(assert-event
 (let ((r (fn-stprt-call *stprt-start*)))
  (and (fn-stmt-p (car (fn-stcp-at 2 *stprt-start*)))
       (equal (car r) :yield) (equal (nth 3 r) 1)
       (equal (fn-stcp-at 1 (nth 1 r)) *stprt-projection*)
       (equal (fn-stcp-at 4 (nth 1 r)) *stpet-start*))))
(assert-event
 (mv-let (w c e u) (fn-stpr-select-resume *stprt-start*)
  (mv-let (wm cm em um) (fn-stpr-select-resume-model *stprt-start*)
   (equal (list w c e u) (list wm cm em um)))))
; A completed carrier emits exact evidence and advances exactly one group;
; pinned source is retained, and no authority/adoption decision is produced.
(make-event (list 'defconst '*stprt-terminal*
 (list 'quote (list :fn-stpr-select *stprt-projection*
                   (list *stpet-statement*) '("fn.test" "fn.other")
                   (nth 1 (fn-stpet-finish *stpet-start* 100))))))
(assert-event
 (let ((r (fn-stprt-call *stprt-terminal*)))
  (and (equal (car r) :done) (equal (nth 3 r) 0)
       (equal (nth 2 r) (list :fn-stpe-envelope *stcpt-profile*
                             "fn.test" *stpet-statement* *stcpt-commit*))
       (equal (fn-stcp-at 3 (nth 1 r)) '("fn.other"))
       (equal (fn-stcp-at 1 (nth 1 r)) *stprt-projection*))))
