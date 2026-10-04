; ACL2-facing boundary for `tls reload' and the served certificate line
; (PRF-212, books/tls-reload.lisp).  Every decision is the book's; these
; wrappers only name it for the image (host/native/tls-reload.lisp).
(in-package "ACL2")
(include-book "../books/tls-reload")
(include-book "../books/tls-key-exchange")

(defun fn-tlsr-host-facts (chain key match not-before not-after san now)
  (declare (xargs :mode :program))
  (fn-tlsr-facts chain key match not-before not-after san now))

(defun fn-tlsr-host-decide (facts served)
  (declare (xargs :mode :program))
  (fn-tlsr-decide facts served))

(defun fn-tlsr-host-start-decide (facts)
  ; PRF-387 (PKT-606): `run''s decision, fnn-tls-start-context.
  (declare (xargs :mode :program))
  (fn-tlsr-start-decide facts))

(defun fn-tlsr-host-start-refusal-line (decision)
  (declare (xargs :mode :program))
  (fn-tlsr-start-refusal-line decision))

(defun fn-tlsr-host-acceptp (decision)
  (declare (xargs :mode :program))
  (fn-tlsr-acceptp decision))

(defun fn-tlsr-host-refusal (decision)
  ; The reason keyword of a refusal (the reply's word), else nil.
  (declare (xargs :mode :program))
  (and (consp decision) (equal (car decision) :refuse)
       (consp (cdr decision)) (car (cdr decision))))

(defun fn-tlsr-host-log-line (decision facts)
  (declare (xargs :mode :program))
  (fn-tlsr-log-line decision facts))

(defun fn-tlsr-host-reply-line (served)
  (declare (xargs :mode :program))
  (fn-tlsr-reply-line served))

(defun fn-tlsr-host-request-encode (verb)
  (declare (xargs :mode :program))
  (fn-tlsr-request-encode verb))

(defun fn-tlsr-host-request-decode (octets)
  (declare (xargs :mode :program
                  :guard (fn-cbor-octet-listp octets)))
  (fn-tlsr-request-decode octets))

(defun fn-tlsr-host-reply-encode (status reason line)
  (declare (xargs :mode :program))
  (fn-tlsr-reply-encode status reason line))

(defun fn-tlsr-host-reply-read (octets)
  (declare (xargs :mode :program
                  :guard (fn-cbor-octet-listp octets)))
  (fn-tlsr-reply-read octets))

(defun fn-tlsr-host-status-client-line (read)
  (declare (xargs :mode :program))
  (fn-tlsr-status-client-line read))

; The TLS key-exchange policy (PRF-1327, books/tls-key-exchange.lisp), called
; by host/native/tls-reload.lisp and host/native/operator-live.lisp.  These
; are guard-verified :logic entries (guard t): the book's functions carry the
; decisions, these only name them for the image.
(defun fn-tlsk-host-plan (octets)
  (declare (xargs :guard (fn-cbor-octet-listp octets)))
  (fn-tlsk-config-plan octets))

(defun fn-tlsk-host-plan-policy (plan)
  ; The policy of an accepted plan, else nil.
  (declare (xargs :guard t))
  (and (consp plan) (equal (car plan) :policy)
       (consp (cdr plan)) (cadr plan)))

(defun fn-tlsk-host-plan-refusal (plan)
  ; The reason word of a refused plan, else nil.
  (declare (xargs :guard t))
  (and (consp plan) (equal (car plan) :refused)
       (consp (cdr plan)) (cadr plan)))

(defun fn-tlsk-host-decide (policy offered)
  (declare (xargs :guard t))
  (fn-tlsk-decide policy offered))

(defun fn-tlsk-host-servep (decision)
  (declare (xargs :guard t))
  (fn-tlsk-servep decision))

(defun fn-tlsk-host-serve-groups (decision)
  (declare (xargs :guard t))
  (fn-tlsk-serve-groups decision))

(defun fn-tlsk-host-serve-mode (decision)
  (declare (xargs :guard t))
  (fn-tlsk-serve-mode decision))

(defun fn-tlsk-host-hybrid-list ()
  (declare (xargs :guard t))
  *fn-tlsk-hybrid-list*)

(defun fn-tlsk-host-refusal-line (decision)
  (declare (xargs :guard t))
  (fn-tlsk-refusal-line decision))

(defun fn-tlsk-host-session-line (name)
  (declare (xargs :guard t))
  (fn-tlsk-session-line name))

(defun fn-tlsk-host-tally-bump (tally name)
  (declare (xargs :guard t))
  (fn-tlsk-tally-bump tally name))

(defun fn-tlsk-host-zero-tally ()
  (declare (xargs :guard t))
  *fn-tlsk-zero-tally*)

(defun fn-tlsk-host-kx-line (policy mode tally)
  (declare (xargs :guard t))
  (fn-tlsk-kx-line policy mode tally))

(defun fn-tlsk-host-status-lines (served-line kx-line)
  (declare (xargs :guard t))
  (fn-tlsk-status-lines served-line kx-line))

(defun fn-tlsk-host-health-client-line (read)
  (declare (xargs :guard t))
  (fn-tlsk-health-client-line read))
