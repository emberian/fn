; One definition for the actual C engine workspace sizes and profile default.
(in-package "ACL2")
(include-book "profile")
(fn2-book-layer :b)
; The C schema inventory owns actual bind scratch capacity. This B leaf
; owns only the arena/profile geometry and must not shadow that decision.
(defconst *fn2-idc-arena-default* 65536)
(defun fn2-idc-profile-arena (profile)
 (declare (xargs :guard t))
 (if (and (alistp profile) (assoc-equal :identity-arena-bytes profile))
     (fn2-profile-get :identity-arena-bytes profile) *fn2-idc-arena-default*))
