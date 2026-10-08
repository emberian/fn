; The history stobj's generated foundation is EQUAL to the hand-written one
; it replaces (lane s-hcf 2026-10-08).
;
; 1. The abstract stobj's recorded interface (foundation, recognizer,
;    creator, and for every export its name, :logic and :exec function, in
;    order) is the list below, captured from dev 617a83910
;    (books/history-columns.lisp over the hand books/history-columns-
;    foundation.lisp, before the hand forms were deleted).  The attachment
;    `(attach-stobj fn-hist fn-hist-paged)' matches export lists
;    positionally, so the order is part of the statement.  :protect t is on
;    append and clear.
; 2. Every obligation the hand book proved keeps its name.

(in-package "ACL2")
(include-book "../../books/history-columns")
(include-book "must-fail-checked")
(include-book "std/testing/assert-bang" :dir :system)

(defconst *drh-hand-fn-hist-interface*
  '(FN-HIST$C
    (FN-HIST-P FN-HIST$AP FN-HIST$CP)
    (CREATE-FN-HIST CREATE-FN-HIST$A CREATE-FN-HIST$C)
    (FN-HIST-COUNT FN-HIST$A-COUNT FN-HIST$C-COUNT)
    (FN-HIST-AT FN-HIST$A-AT FN-HIST$C-AT)
    (FN-HIST-MSGID-RECORDS FN-HIST$A-MSGID-RECORDS FN-HIST$C-MSGID-RECORDS)
    (FN-HIST-APPEND FN-HIST$A-APPEND FN-HIST$C-APPEND)
    (FN-HIST-CLEAR FN-HIST$A-CLEAR FN-HIST$C-CLEAR)))

(assert-event
 (equal (getprop 'fn-hist 'absstobj-info nil 'current-acl2-world (w state))
        *drh-hand-fn-hist-interface*))

(must-fail-checked
 (assert-event
  (equal (getprop 'fn-hist 'absstobj-info nil 'current-acl2-world (w state))
         (list* (car *drh-hand-fn-hist-interface*)
                (cadr *drh-hand-fn-hist-interface*)
                (caddr *drh-hand-fn-hist-interface*)
                (nth 4 *drh-hand-fn-hist-interface*)
                (nth 3 *drh-hand-fn-hist-interface*)
                (nthcdr 5 *drh-hand-fn-hist-interface*))))
 :unchecked "the passing assert above with two exports swapped")

(defconst *drh-hand-obligations*
  '(create-fn-hist{correspondence} create-fn-hist{preserved}
    fn-hist-count{correspondence} fn-hist-at{correspondence} fn-hist-at{guard-thm}
    fn-hist-msgid-records{correspondence} fn-hist-append{correspondence}
    fn-hist-append{preserved} fn-hist-clear{correspondence} fn-hist-clear{preserved}
    fn-hist-fold-establishes-correspondence fn-hist-fold-table-facts
    fn-hist-fold-mids-of-append))

(defun drh-all-theorems (names w)
  (declare (xargs :mode :program))
  (or (endp names)
      (and (getprop (car names) 'theorem nil 'current-acl2-world w)
           (drh-all-theorems (cdr names) w))))

(assert-event (drh-all-theorems *drh-hand-obligations* (w state)))

(must-fail-checked
 (assert-event (drh-all-theorems '(fn-hist-no-such-obligation) (w state)))
 :unchecked "the passing assert above on a name that is not a theorem")
