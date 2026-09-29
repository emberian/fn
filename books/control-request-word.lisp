; fn -- the word an operator request prints (lane online-reclaim-5).
;
; `store reclaim' and `store compact' against a running owner print the
; request's verb and the owner's word (host/native/operator-live.lisp
; fnn-operator-live-request).  The word is the reasoned reply's reason
; (books/native-control-reason.lisp fn-nctrl-reason-word), which is `NONE'
; when the owner named none -- and an owner whose request handler faulted
; names none: the operator read `reclaim NONE' next to exit FAULT (4), as if
; nothing had been reclaimed (online-reclaim-4's finding).  The printed word
; is decided here: the owner's word when it named one, else the status's own
; name (fault, uncertain, refused, ...), never `NONE'.

(in-package "ACL2")
(include-book "native-control-reason")

(defun fn-crqw-request-word (status word)
  (declare (xargs :guard t))
  (if (equal word *fn-nctrl-no-reason-word*)
      (fn-nctrl-reason-word status)
    word))

; KEYSTONE.  For every control status the owner can answer, the printed
; word is never `NONE'; it is the owner's word whenever the owner named one,
; and the status's own name (`fault' for a fault) when it named none.
(defthm fn-crqw-request-word-names-the-outcome
  (implies (member-equal status *fn-nctrl-statuses*)
           (and (not (equal (fn-crqw-request-word status word)
                            *fn-nctrl-no-reason-word*))
                (implies (not (equal word *fn-nctrl-no-reason-word*))
                         (equal (fn-crqw-request-word status word) word))
                (implies (equal word *fn-nctrl-no-reason-word*)
                         (equal (fn-crqw-request-word status word)
                                (fn-nctrl-reason-word status)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-nctrl-reason-word-of-a-reason-is-not-none
                                   (reason status)))
                  :in-theory (e/d (fn-crqw-request-word)
                                  (fn-nctrl-reason-word-of-a-reason-is-not-none)))))

(in-theory (disable fn-crqw-request-word))
