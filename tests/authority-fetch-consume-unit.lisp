; Finite served-path regression, not a universal authorization theorem.
; The original fetch branch bypassed current consumer admission. The same
; actual wire fixture delivers the complete article in that baseline; this
; book requires refusal after the decision is connected to fetch.
(in-package "ACL2")
(include-book "authority-read-control")

(defun fn2-authority-fetch-setup-p (r consume read)
  (declare (xargs :verify-guards nil))
  (and (equal (fn2-decl-get :fetch r) t)
       (equal (fn2-decl-get :allow-consume r) consume)
       (equal (fn2-decl-get :allow-read r) read)
       (equal (fn2-decl-get :core-domain r) t)
       (equal (fn2-decl-get :device-written r) t)
       (equal (fn2-decl-get :end r) :quiet)
       (equal (car (last r)) 0)))

(defun fn2-authority-fetch-exact-p (r)
  (declare (xargs :verify-guards nil))
  (equal (fn2-decl-get :reply r)
         (list :accepted "" (fn2-as-article "<read@authority.invalid>" "read-control"))))

(defun fn2-authority-fetch-consume-positive ()
  (declare (xargs :verify-guards nil))
  (let ((neither (fn2-authority-fetch-control-run nil nil))
        (read-only (fn2-authority-fetch-control-run nil t))
        (both (fn2-authority-fetch-control-run t t)))
    (and (fn2-authority-fetch-setup-p neither nil nil)
         (fn2-authority-fetch-setup-p read-only nil t)
         (fn2-authority-fetch-setup-p both t t)
         (equal (fn2-decl-get :reply neither) '(:refused "access" nil))
         (equal (fn2-decl-get :reply read-only) '(:refused "access" nil))
         (fn2-authority-fetch-exact-p both))))

; Run on the qualified application before the source fix to check the
; explicit removed-admission witness; require false in the repaired app.
; Do not assert it in the current world or count it as a proved square.
(defun fn2-authority-fetch-consume-bypass-witness ()
  (declare (xargs :verify-guards nil))
  (let ((r (fn2-authority-fetch-control-run nil nil)))
    (and (fn2-authority-fetch-setup-p r nil nil)
         (fn2-authority-fetch-exact-p r))))

(assert-event (fn2-authority-fetch-consume-positive))
(assert-event (not (fn2-authority-fetch-consume-bypass-witness)))
