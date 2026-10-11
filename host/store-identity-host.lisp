; ACL2-facing boundary for `fn identity CONTROL' (Mini M4,
; books/store-identity.lisp).  Every byte is the book's: the request the
; client sends, the reply the owner seals from its genesis verdict, its
; consumer state and the running image's revision, the client's read of it,
; the line it prints and its exit code.  These wrappers only name them for the
; image (host/native/store-identity.lisp).  Loaded after host/owner-host.lisp.
(in-package "ACL2")
(include-book "../books/payload-arena-attach")
; D61: the image attaches these (attach-stobj) before the generic they implement;
; a certified host file carries the same order in its own world (tools/host_check.py --attach-order).
(include-book "../books/history-paged-attach")
(include-book "../books/store-identity")
(include-book "../books/live-profile-control")
(include-book "../books/definterface")
(include-book "../books/owner-state-accessors")

(defun fn-stid-host-request ()
  (declare (xargs :mode :program))
  (fn-stid-request))

;; host/store-identity-host.lisp (Mini M4, `fn identity CONTROL')
(definterface fn-stid-host-request :class ::program)

(defun fn-stid-host-request-p (octets)
  (declare (xargs :mode :program :guard (fn-cbor-octet-listp octets)))
  (fn-stid-request-p octets))

(definterface fn-stid-host-request-p :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

; The owner's reply: the open's verdict this process installed
; (fn-store-genesis), the owner's consumer state, and RUNNING, the image's
; recorded source revision as octets.  NIL outside a running owner.
(defun fn-stid-host-reply (running state)
  (declare (xargs :stobjs state :mode :program))
  (if (not (boundp-global 'fn-owner state))
      (value nil)
    (value (fn-stid-reply (and (boundp-global 'fn-store-genesis state)
                               (f-get-global 'fn-store-genesis state))
                          (fn-sn-consumer (fn-owner-store state))
                          running))))

(definterface fn-stid-host-reply :class ::program)

(defun fn-stid-host-cli-plan (argv)
  (declare (xargs :mode :program))
  (fn-stid-cli-plan argv))

(definterface fn-stid-host-cli-plan :class ::program)

(defun fn-stid-host-usage ()
  (declare (xargs :mode :program))
  *fn-stid-usage*)

(definterface fn-stid-host-usage :class ::program)

(defun fn-stid-host-reply-read (octets)
  (declare (xargs :mode :program :guard (fn-cbor-octet-listp octets)))
  (fn-stid-reply-read octets))

(definterface fn-stid-host-reply-read :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

(defun fn-stid-host-line (value)
  (declare (xargs :mode :program))
  (fn-stid-line value))

(definterface fn-stid-host-line :class ::program)

(defun fn-stid-host-exit-code (value)
  (declare (xargs :mode :program))
  (fn-stid-exit-code value))

(definterface fn-stid-host-exit-code :class ::program)
