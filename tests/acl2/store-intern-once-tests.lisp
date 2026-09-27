; Witnesses for books/store-intern-once (the held row's facts and context
; from one parse).  fn-ipo-facts-context-is-facts-and-context has no
; hypothesis.  REACHABLE: a plain article, a cancel control article (the
; control fact names its target) and octets that are not an article (the
; malformed verdict): the one-parse answer is the two readers' answer, and
; the control fact is the one the reader finds.
(in-package "ACL2")
(include-book "../../books/store-intern-once")

(defun sio-octets (s) (declare (xargs :guard (stringp s))) (fn-record-string-octets s))

(defconst *sio-plain*
  (sio-octets (concatenate 'string
                           "From: a@example.invalid" (coerce '(#\Return #\Newline) 'string)
                           "Newsgroups: fn.test" (coerce '(#\Return #\Newline) 'string)
                           "Subject: plain" (coerce '(#\Return #\Newline) 'string)
                           "Message-ID: <sio-1@example.invalid>" (coerce '(#\Return #\Newline) 'string)
                           (coerce '(#\Return #\Newline) 'string)
                           "body" (coerce '(#\Return #\Newline) 'string))))
(defconst *sio-cancel*
  (sio-octets (concatenate 'string
                           "From: a@example.invalid" (coerce '(#\Return #\Newline) 'string)
                           "Newsgroups: fn.test" (coerce '(#\Return #\Newline) 'string)
                           "Subject: cmsg cancel <sio-1@example.invalid>" (coerce '(#\Return #\Newline) 'string)
                           "Control: cancel <sio-1@example.invalid>" (coerce '(#\Return #\Newline) 'string)
                           "Message-ID: <sio-2@example.invalid>" (coerce '(#\Return #\Newline) 'string)
                           (coerce '(#\Return #\Newline) 'string)
                           "cancel" (coerce '(#\Return #\Newline) 'string))))
(defconst *sio-garbage* '(1 2 3 255))

(assert-event
 (and (equal (mv-list 2 (fn-ipo-facts-context *sio-plain* nil 0))
             (list (fn-held-facts-of *sio-plain*) (fn-held-context-of *sio-plain* nil 0)))
      (equal (mv-list 2 (fn-ipo-facts-context *sio-cancel* nil 3))
             (list (fn-held-facts-of *sio-cancel*) (fn-held-context-of *sio-cancel* nil 3)))
      (equal (mv-list 2 (fn-ipo-facts-context *sio-garbage* nil 0))
             (list (fn-held-facts-of *sio-garbage*) (fn-held-context-of *sio-garbage* nil 0)))
      ;; the cancel's control fact names its target; the plain article's none
      (fn-ctl-control-target (fn-hf-control (fn-held-facts-of *sio-cancel*)))
      (null (fn-ctl-control-target (fn-hf-control (fn-held-facts-of *sio-plain*))))
      ;; the garbage is no article: the malformed verdict
      (equal (fn-hc-verdict (fn-held-context-of *sio-garbage* nil 0))
             (fn-stx-make-verdict :unverified :malformed 0))))
