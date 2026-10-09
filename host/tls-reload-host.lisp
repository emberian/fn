; ACL2-facing boundary for `tls reload' and the served certificate line
; (PRF-212, books/tls-reload.lisp).  Every decision is the book's; these
; wrappers only name it for the image (host/native/tls-reload.lisp).
(in-package "ACL2")
; D61: the image attaches these (attach-stobj) before the generic they implement;
; a certified host file carries the same order in its own world (tools/host_check.py --attach-order).
(include-book "../books/payload-arena-attach")
(include-book "../books/history-paged-attach")
(include-book "../books/tls-reload")
(include-book "../books/tls-key-exchange")
(include-book "../books/definterface")

(defun fn-tlsr-host-facts (chain key match not-before not-after san now)
  (declare (xargs :mode :program))
  (fn-tlsr-facts chain key match not-before not-after san now))

(definterface fn-tlsr-host-facts
  :class ::program)

(defun fn-tlsr-host-decide (facts served)
  (declare (xargs :mode :program))
  (fn-tlsr-decide facts served))

(definterface fn-tlsr-host-decide
  :class ::program)

(defun fn-tlsr-host-start-decide (facts)
  ; PRF-387 (PKT-606): `run''s decision, fnn-tls-start-context.
  (declare (xargs :mode :program))
  (fn-tlsr-start-decide facts))

(definterface fn-tlsr-host-start-decide
  :class ::program)

(defun fn-tlsr-host-start-refusal-line (decision)
  (declare (xargs :mode :program))
  (fn-tlsr-start-refusal-line decision))

(definterface fn-tlsr-host-start-refusal-line
  :class ::program)

(defun fn-tlsr-host-acceptp (decision)
  (declare (xargs :mode :program))
  (fn-tlsr-acceptp decision))

(definterface fn-tlsr-host-acceptp
  :class ::program)

(defun fn-tlsr-host-refusal (decision)
  ; The reason keyword of a refusal (the reply's word), else nil.
  (declare (xargs :mode :program))
  (and (consp decision) (equal (car decision) :refuse)
       (consp (cdr decision)) (car (cdr decision))))

(definterface fn-tlsr-host-refusal
  :class ::program)

(defun fn-tlsr-host-log-line (decision facts)
  (declare (xargs :mode :program))
  (fn-tlsr-log-line decision facts))

(definterface fn-tlsr-host-log-line
  :class ::program)

(defun fn-tlsr-host-reply-line (served)
  (declare (xargs :mode :program))
  (fn-tlsr-reply-line served))

(definterface fn-tlsr-host-reply-line
  :class ::program)

(defun fn-tlsr-host-request-encode (verb)
  (declare (xargs :mode :program))
  (fn-tlsr-request-encode verb))

(definterface fn-tlsr-host-request-encode
  :class ::program)

(defun fn-tlsr-host-request-decode (octets)
  (declare (xargs :mode :program
                  :guard (fn-cbor-octet-listp octets)))
  (fn-tlsr-request-decode octets))

(definterface fn-tlsr-host-request-decode
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

(defun fn-tlsr-host-reply-encode (status reason line)
  (declare (xargs :mode :program))
  (fn-tlsr-reply-encode status reason line))

(definterface fn-tlsr-host-reply-encode
  :class ::program)

(defun fn-tlsr-host-reply-read (octets)
  (declare (xargs :mode :program
                  :guard (fn-cbor-octet-listp octets)))
  (fn-tlsr-reply-read octets))

(definterface fn-tlsr-host-reply-read
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

(defun fn-tlsr-host-status-client-line (read)
  (declare (xargs :mode :program))
  (fn-tlsr-status-client-line read))

(definterface fn-tlsr-host-status-client-line
  :class ::program)

; The TLS key-exchange policy (PRF-1327, books/tls-key-exchange.lisp), called
; by host/native/tls-reload.lisp and host/native/operator-live.lisp.  These
; are guard-verified :logic entries (guard t): the book's functions carry the
; decisions, these only name them for the image.
(defun fn-tlsk-host-plan (octets)
  (declare (xargs :guard (fn-cbor-octet-listp octets)))
  (fn-tlsk-config-plan octets))

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

(defun fn-tlsk-host-decide (policy offered)
  (declare (xargs :guard t))
  (fn-tlsk-decide policy offered))

(definterface fn-tlsk-host-decide :class :common-lisp-compliant)

(defun fn-tlsk-host-servep (decision)
  (declare (xargs :guard t))
  (fn-tlsk-servep decision))

(definterface fn-tlsk-host-servep :class :common-lisp-compliant)

(defun fn-tlsk-host-serve-groups (decision)
  (declare (xargs :guard t))
  (fn-tlsk-serve-groups decision))

(definterface fn-tlsk-host-serve-groups :class :common-lisp-compliant)

(defun fn-tlsk-host-serve-mode (decision)
  (declare (xargs :guard t))
  (fn-tlsk-serve-mode decision))

(definterface fn-tlsk-host-serve-mode :class :common-lisp-compliant)

(defun fn-tlsk-host-hybrid-list ()
  (declare (xargs :guard t))
  *fn-tlsk-hybrid-list*)

(definterface fn-tlsk-host-hybrid-list :class :common-lisp-compliant)

(defun fn-tlsk-host-refusal-line (decision)
  (declare (xargs :guard t))
  (fn-tlsk-refusal-line decision))

(definterface fn-tlsk-host-refusal-line :class :common-lisp-compliant)

(defun fn-tlsk-host-session-line (name)
  (declare (xargs :guard t))
  (fn-tlsk-session-line name))

(definterface fn-tlsk-host-session-line :class :common-lisp-compliant)

(defun fn-tlsk-host-tally-bump (tally name)
  (declare (xargs :guard t))
  (fn-tlsk-tally-bump tally name))

(definterface fn-tlsk-host-tally-bump :class :common-lisp-compliant)

(defun fn-tlsk-host-zero-tally ()
  (declare (xargs :guard t))
  *fn-tlsk-zero-tally*)

(definterface fn-tlsk-host-zero-tally :class :common-lisp-compliant)

(defun fn-tlsk-host-kx-line (policy mode tally)
  (declare (xargs :guard t))
  (fn-tlsk-kx-line policy mode tally))

(definterface fn-tlsk-host-kx-line :class :common-lisp-compliant)

(defun fn-tlsk-host-status-lines (served-line kx-line)
  (declare (xargs :guard t))
  (fn-tlsk-status-lines served-line kx-line))

(definterface fn-tlsk-host-status-lines :class :common-lisp-compliant)

(defun fn-tlsk-host-health-client-line (read)
  (declare (xargs :guard t))
  (fn-tlsk-health-client-line read))

(definterface fn-tlsk-host-health-client-line :class :common-lisp-compliant)

; D59's refusal scope: the library a start runs on (fn-tlsk-library-decide).
(defun fn-tlsk-host-library-decide (missing served policy)
  (declare (xargs :guard t))
  (fn-tlsk-library-decide missing served policy))

(definterface fn-tlsk-host-library-decide :class :common-lisp-compliant)

(defun fn-tlsk-host-library-line (decision)
  (declare (xargs :guard t))
  (fn-tlsk-library-line decision))

(definterface fn-tlsk-host-library-line :class :common-lisp-compliant)
