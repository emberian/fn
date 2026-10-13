; Total readers shared by the replay and carried retention indexes.
(in-package "ACL2")
(include-book "retention")

; fn-retain-pin-id-scanp and fn-retain-release-id-scanp with guard t (the
; relation below is a guard, so its body must be guard-verified at t).
(defun fn-rii-pin-hasp (id pins)
  (declare (xargs :guard t))
  (if (consp pins)
      (or (equal id (fn-retain-obligation-id (car pins)))
          (fn-rii-pin-hasp id (cdr pins)))
    nil))

(defun fn-rii-release-hasp (id releases)
  (declare (xargs :guard t))
  (if (consp releases)
      (or (equal id (fn-retain-release-id (car releases)))
          (fn-rii-release-hasp id (cdr releases)))
    nil))

(defun fn-rii-knownp (id retention)
  (declare (xargs :guard t))
  (if (or (fn-rii-pin-hasp id (fn-retain-pins retention))
          (fn-rii-release-hasp id (fn-retain-releases retention)))
      t
    nil))

; These rules are exported because replay uses them after the book split.
(defthm fn-rii-pin-hasp-is-member
   (iff (fn-rii-pin-hasp id pins)
        (member-equal id (fn-retain-obligation-ids pins))))

(defthm fn-rii-release-hasp-is-member
   (iff (fn-rii-release-hasp id releases)
        (member-equal id (fn-retain-release-ids releases))))

(defthm fn-rii-knownp-is-known-idp
  (iff (fn-rii-knownp id retention)
       (fn-retain-known-idp id (fn-retain-pins retention)
                            (fn-retain-releases retention)))
  :hints (("Goal" :in-theory (enable fn-retain-known-idp))))

(in-theory (disable fn-rii-knownp))
