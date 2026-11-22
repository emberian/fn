; Scalar decisions shared by the owner grant decoder, protected login and
; scoped transfer consumers. Enum values follow the durable grant layout.
(in-package "ACL2")
(defconst *fn2-authority-right-consume* 0)
(defconst *fn2-authority-right-read* 1)
(defconst *fn2-authority-right-append* 2)
(defconst *fn2-authority-right-peer* 3)
(defconst *fn2-authority-right-peer-feed* 4)
(defconst *fn2-authority-right-peer-accept* 5)
(defconst *fn2-authority-scope-principal* 2)
(defconst *fn2-authority-scope-own-consumers* 0)
(defconst *fn2-authority-scope-stream* 1)

(defun fn2-grant-scope-admissible-p (right scope target)
 (declare (xargs :guard t))
 (cond ((equal right *fn2-authority-right-consume*)
        (and (equal scope *fn2-authority-scope-own-consumers*) (equal target 0)))
       ((equal right *fn2-authority-right-peer*)
        (and (equal scope *fn2-authority-scope-principal*) (equal target 0)))
       ((member-equal right (list *fn2-authority-right-read* *fn2-authority-right-append*
                                  *fn2-authority-right-peer-feed* *fn2-authority-right-peer-accept*))
        (and (equal scope *fn2-authority-scope-stream*) (posp target) (unsigned-byte-p 60 target)))
       (t nil)))

; Consume only a completed published grant check. Login may acquire the
; role, whereas subsequent requests must still present the original grant.
(defun fn2-peer-role-at-decision (code head grant pinned login)
 (declare (xargs :guard t))
 (if (and (eq code :ok) (posp head) (unsigned-byte-p 60 head)
          (posp grant) (unsigned-byte-p 60 grant)
          (or (equal login 1) (and (equal login 0) (equal grant pinned))))
     grant 0))

(defthm fn2-peer-role-at-decision-width
 (unsigned-byte-p 60 (fn2-peer-role-at-decision code head grant pinned login)))
