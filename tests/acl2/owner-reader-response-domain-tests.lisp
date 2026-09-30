; Literal no-hypothesis domain witnesses for actual response decorations.
; These exercise the pure producer functions, not registered receipt custody.
(in-package "ACL2")
(include-book "../../books/owner-reader-response-domain")
(defconst *rrdt-owner*
 (fn-own-make nil nil nil 0 1 nil nil nil nil nil nil nil nil nil nil))
(defconst *rrdt-effects*
 (list (list :reply (fn-olog-post-refusal-reply :posting-disallowed))
       (list :reply (fn-olog-post-refusal-reply :oversize))))
(assert-event
 (and (fn-own-shapep *rrdt-owner*)
      (equal (len (fn-olog-served-refusal-lines *rrdt-owner* 0 *rrdt-effects*)) 2)
      (true-listp (fn-olog-served-refusal-lines *rrdt-owner* 0 *rrdt-effects*))))
(defconst *rrdt-limits* (fn-exp-lim-make 3 2 2 600 60 2 1 :none))
(defconst *rrdt-exposure*
 (fn-exp-register (fn-exp-initial) 5 '(:inet 127 0 0 2) 5000))
(defconst *rrdt-login-effects*
 (list (list :reply (fn-exp-line "481 authentication failed"))))
(defconst *rrdt-first*
 (fn-exp-observe-effects *rrdt-exposure* *rrdt-limits* 5 5100
                         *rrdt-login-effects* 30 nil nil))
(defconst *rrdt-second*
 (fn-exp-observe-effects (cdr *rrdt-first*) *rrdt-limits* 5 5200
                         *rrdt-login-effects* 30 nil nil))
(assert-event
 (let ((close (if (consp (car *rrdt-second*)) (cadr (car *rrdt-second*)) nil)))
  (and (eq (car *rrdt-first*) :continue)
       (equal (car *rrdt-second*) (list :close (fn-exp-line *fn-exp-auth-close-line*)))
       close (fn-cbor-octet-listp close))))
(assert-event
 (let* ((r (fn-exp-observe-effects *rrdt-exposure* *rrdt-limits* 5 5100
                                  nil 0 nil nil))
        (close (if (consp (car r)) (cadr (car r)) nil)))
  (and (eq (car r) :continue) (null close))))
