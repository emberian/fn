; ACL2-facing boundary for `tls reload' and the served certificate line
; (PRF-212, books/tls-reload.lisp).  Every decision is the book's; these
; wrappers only name it for the image (host/native/tls-reload.lisp).
(in-package "ACL2")
; D61: the image attaches these (attach-stobj) before the generic they implement;
; a certified host file carries the same order in its own world (tools/host_check.py --attach-order).
(include-book "../books/payload-arena")
(include-book "../books/history-columns")
(include-book "../books/tls-reload")
(include-book "../books/tls-key-exchange")
(include-book "../books/definterface")

(include-book "../books/entries-tls-reload-host")

(definterface fn-tlsr-host-facts
  :class ::program)

(definterface fn-tlsr-host-decide
  :class ::program)

(defun fn-tlsr-host-start-decide (facts)
  ; PRF-387 (PKT-606): `run''s decision, fnn-tls-start-context.
  (declare (xargs :mode :program))
  (fn-tlsr-start-decide facts))

(definterface fn-tlsr-host-start-decide
  :class ::program)

(definterface fn-tlsr-host-start-refusal-line
  :class ::program)

(definterface fn-tlsr-host-acceptp
  :class ::program)

(defun fn-tlsr-host-refusal (decision)
  ; The reason keyword of a refusal (the reply's word), else nil.
  (declare (xargs :mode :program))
  (and (consp decision) (equal (car decision) :refuse)
       (consp (cdr decision)) (car (cdr decision))))

(definterface fn-tlsr-host-refusal
  :class ::program)

(definterface fn-tlsr-host-log-line
  :class ::program)

(definterface fn-tlsr-host-reply-line
  :class ::program)

(definterface fn-tlsr-host-request-encode
  :class ::program)

(definterface fn-tlsr-host-request-decode
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

(definterface fn-tlsr-host-reply-encode
  :class ::program)

(definterface fn-tlsr-host-reply-read
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

(definterface fn-tlsr-host-status-client-line
  :class ::program)

; The TLS key-exchange policy (PRF-1327, books/tls-key-exchange.lisp), called
; by host/native/tls-reload.lisp and host/native/operator-live.lisp.  These
; are guard-verified :logic entries (guard t): the book's functions carry the
; decisions, these only name them for the image.

(definterface fn-tlsk-host-plan :class :common-lisp-compliant :kinds ((octets fn-cbor-octet-listp)))

(defun fn-tlsk-host-plan-policy (plan)
  ; The policy of an accepted plan, else nil.
  (declare (xargs :guard t))
  (and (consp plan) (equal (car plan) :policy)
       (consp (cdr plan)) (cadr plan)))

(definterface fn-tlsk-host-plan-policy :class :common-lisp-compliant)

(defun fn-tlsk-host-plan-refusal (plan)
  ; The reason word of a refused plan, else nil.
  (declare (xargs :guard t))
  (and (consp plan) (equal (car plan) :refused)
       (consp (cdr plan)) (cadr plan)))

(definterface fn-tlsk-host-plan-refusal :class :common-lisp-compliant)

(definterface fn-tlsk-host-decide :class :common-lisp-compliant)

(definterface fn-tlsk-host-servep :class :common-lisp-compliant)

(definterface fn-tlsk-host-serve-groups :class :common-lisp-compliant)

(definterface fn-tlsk-host-serve-mode :class :common-lisp-compliant)

(defun fn-tlsk-host-hybrid-list ()
  (declare (xargs :guard t))
  *fn-tlsk-hybrid-list*)

(definterface fn-tlsk-host-hybrid-list :class :common-lisp-compliant)

(definterface fn-tlsk-host-refusal-line :class :common-lisp-compliant)

(definterface fn-tlsk-host-session-line :class :common-lisp-compliant)

(definterface fn-tlsk-host-tally-bump :class :common-lisp-compliant)

(defun fn-tlsk-host-zero-tally ()
  (declare (xargs :guard t))
  *fn-tlsk-zero-tally*)

(definterface fn-tlsk-host-zero-tally :class :common-lisp-compliant)

(definterface fn-tlsk-host-kx-line :class :common-lisp-compliant)

(definterface fn-tlsk-host-status-lines :class :common-lisp-compliant)

(definterface fn-tlsk-host-health-client-line :class :common-lisp-compliant)

; D59's refusal scope: the library a start runs on (fn-tlsk-library-decide).

(definterface fn-tlsk-host-library-decide :class :common-lisp-compliant)

(definterface fn-tlsk-host-library-line :class :common-lisp-compliant)
