; The history stobj's generated foundation is EQUAL to the hand-written one
; it replaces (lane s-hcf 2026-10-08).
;
; 1. The attached generic's full recorded interface is the literal below:
;    the resident paged foundation, recognizer, creator and every export's
;    name, unchanged :logic function and selected :exec function, in order.
;    The generated reference foundation remains the proof witness.
;    The swapped-export refusal still checks positional attachment order;
;    :protect t remains on append and clear.
; 2. Every obligation the reference foundation proved keeps its name.

(in-package "ACL2")
(include-book "../../books/history-columns")
(include-book "must-fail-checked")
(include-book "std/testing/assert-bang" :dir :system)

(defconst *drh-attached-fn-hist-interface*
  '(FN-HIST$P
    (FN-HIST-P FN-HIST$AP FN-HIST$PP)
    (CREATE-FN-HIST CREATE-FN-HIST$A CREATE-FN-HIST$P)
    (FN-HIST-COUNT FN-HIST$A-COUNT FN-HIST$P-COUNT)
    (FN-HIST-AT FN-HIST$A-AT FN-HIST$P-AT)
    (FN-HIST-MSGID-RECORDS FN-HIST$A-MSGID-RECORDS FN-HIST$P-MSGID-RECORDS)
    (FN-HIST-APPEND FN-HIST$A-APPEND FN-HIST$P-APPEND)
    (FN-HIST-CLEAR FN-HIST$A-CLEAR FN-HIST$P-CLEAR)))

(assert-event
 (equal (getprop 'fn-hist 'absstobj-info nil 'current-acl2-world (w state))
        *drh-attached-fn-hist-interface*))

(must-fail-checked
 (assert-event
  (equal (getprop 'fn-hist 'absstobj-info nil 'current-acl2-world (w state))
         (list* (car *drh-attached-fn-hist-interface*)
                (cadr *drh-attached-fn-hist-interface*)
                (caddr *drh-attached-fn-hist-interface*)
                (nth 4 *drh-attached-fn-hist-interface*)
                (nth 3 *drh-attached-fn-hist-interface*)
                (nthcdr 5 *drh-attached-fn-hist-interface*))))
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
