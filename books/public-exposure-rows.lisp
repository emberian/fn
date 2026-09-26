; fn: the configuration rows of a public reader port (PRF-161).
;
; The slot names books/public-exposure.lisp reads and the words
; books/native-admin.lisp admits for `policy set SLOT VALUE', in one small
; book so that the operator's plan does not include the owner.  Each limit
; slot is a `:set-limit' row keyed (SLOT, ""); `anonymous' is a
; `:set-policy' row.  What each means is books/public-exposure.lisp's header.
;
; This book owns the prefix `fn-exp-' with books/public-exposure.lisp
; (docs/prefixes.md).

(in-package "ACL2")
(include-book "config")

(defconst *fn-exp-slot-connections* "exposure-connections")
(defconst *fn-exp-slot-per-address* "exposure-per-address")
(defconst *fn-exp-slot-steps* "exposure-steps-per-second")
(defconst *fn-exp-slot-idle* "exposure-idle-seconds")
(defconst *fn-exp-slot-first* "exposure-first-seconds")
(defconst *fn-exp-slot-auth-failures* "exposure-auth-failures")
(defconst *fn-exp-slot-posts* "exposure-posts-per-minute")
(defconst *fn-exp-policy-slot* "anonymous")

(defconst *fn-exp-limit-slots*
  (list *fn-exp-slot-connections* *fn-exp-slot-per-address* *fn-exp-slot-steps*
        *fn-exp-slot-idle* *fn-exp-slot-first* *fn-exp-slot-auth-failures*
        *fn-exp-slot-posts*))

; -----------------------------------------------------------------------------
; The operator's words: `policy set SLOT VALUE' (books/native-admin.lisp).

(defun fn-exp-limit-slotp (slot)
  (declare (xargs :guard t))
  (and (member-equal slot *fn-exp-limit-slots*) t))

(defun fn-exp-anonymous-wordp (word)
  (declare (xargs :guard t))
  (and (member-equal word '("none" "open")) t))

