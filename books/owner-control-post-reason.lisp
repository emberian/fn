; fn: the operator's post refused at completion names the Store's reason
; (lane operability-2, row S10, 2026-09-29).
;
; An operator's `post' that the injection admits and the Store then refuses
; (a full store, an unaffordable article) answered `refused operator post
; REFUSED' and logged `refused post path=control message-id=...' with no
; reason word, while the NNTP poster got the 441 sentence: the completion's
; word (fn-own-control-outcome-result folds it into the class :refused) was
; dropped on the way to the reply and the line.  Here the word travels:
;
;   fn-ocpr-reason      the reason a refused completion carries: the Store's
;       word itself (a symbol; fn-nctrl-reason-word renders it on the
;       reasoned reply); nothing for any other class.
;   fn-ocpr-log-line    fn-olog-control-post-line with ` reason=WORD' when
;       the completion refused, unchanged otherwise.
;
; Subjects: host/owner-host.lisp fn-owner-control-outcome (the line, and the
; reason kept for the reply) and host/native/owner.lisp's reply site, which
; takes the admission decision's reason when there is one and this one
; otherwise.
(in-package "ACL2")
(include-book "owner-log")

(defun fn-ocpr-reason (result word)
  (declare (xargs :guard t))
  (if (and (equal result :refused) (symbolp word) word)
      word
    nil))

(defun fn-ocpr-log-line (o word)
  (declare (xargs :guard t))
  (let ((line (fn-olog-control-post-line o word))
        (reason (fn-ocpr-reason (fn-own-control-outcome-result o word) word)))
    (if reason
        (append line (fn-olog-text " ")
                (fn-olog-field "reason" (fn-olog-symbol-text reason)))
      line)))

; The reason is the Store's word exactly when the completion refused; no
; other class carries one.
(defthm fn-ocpr-reason-is-the-word-when-refused-by-definition
  (equal (fn-ocpr-reason result word)
         (if (and (equal result :refused) (symbolp word) word) word nil)))

; KEYSTONE.  The line names the reason exactly when the completion refused:
; a refused completion's line is the plain line followed by ` reason=WORD',
; and every other class's line is the plain line.
(defthm fn-ocpr-line-names-the-reason-exactly-when-refused
  (equal (fn-ocpr-log-line o word)
         (if (and (equal (fn-own-control-outcome-result o word) :refused)
                  (symbolp word) word)
             (append (fn-olog-control-post-line o word) (fn-olog-text " ")
                     (fn-olog-field "reason" (fn-olog-symbol-text word)))
           (fn-olog-control-post-line o word))))
