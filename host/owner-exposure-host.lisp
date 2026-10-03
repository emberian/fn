; The owner's public-exposure limits and its after-step observation, as a
; certified host book (moved from host/owner-host.lisp, which includes it, so
; that host/index-reader-request-host names what it calls).
(in-package "ACL2")
(include-book "../books/owner-state-accessors")
(include-book "../books/owner-connection-state")
(include-book "../books/owner-connection-callbacks")
(include-book "../books/public-exposure-reply")

(defun fn-owner-exposure-limits (fn-owner-st state)
  (declare (xargs :stobjs (fn-owner-st state) :mode :program))
  (fn-owner-callback-exposure-limits fn-owner-st state))

;; After a served step (fn-owner-chunk-span-at in host/owner-host.lisp):
;; `fn-owner-exposure-close' holds the 400 the host appends before it closes,
;; or NIL.  The step's EFFECTS go in, not its reply octets:
;; fn-exp-observe-effects is fn-exp-observe of (fn-served-reply-octets
;; effects) (fn-exp-observe-effects-unfolds) and scans the effects in constant
;; stack without building that list (books/public-exposure-reply.lisp; PKT-481).
(defun fn-owner-exposure-observe (id effects consumed fn-owner-st state)
  (declare (xargs :stobjs (fn-owner-st state) :mode :program))
  (let* ((conn (fn-own-find-conn id (fn-own-conns (fn-owner-core fn-owner-st))))
         (subject (and conn (fn-auth-session-subject (fn-own-conn-session conn))))
         (r (fn-exp-observe-effects (fn-owner-exposure-state state)
                                    (fn-owner-exposure-limits fn-owner-st state) id
                                    (fn-owner-exposure-now fn-owner-st)
                                    effects consumed subject
                                    (and (fn-served-submission effects) t)))
         (state (f-put-global 'fn-owner-exposure (cdr r) state))
         (state (f-put-global 'fn-owner-exposure-close
                              (if (consp (car r)) (cadr (car r)) nil) state)))
    state))
