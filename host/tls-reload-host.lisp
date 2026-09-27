; ACL2-facing boundary for `tls reload' and the served certificate line
; (PRF-212, books/tls-reload.lisp).  Every decision is the book's; these
; wrappers only name it for the image (host/native/tls-reload.lisp).
(in-package "ACL2")
(include-book "../books/tls-reload")

(defun fn-tlsr-host-facts (chain key match not-before not-after san now)
  (declare (xargs :mode :program))
  (fn-tlsr-facts chain key match not-before not-after san now))

(defun fn-tlsr-host-decide (facts served)
  (declare (xargs :mode :program))
  (fn-tlsr-decide facts served))

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
