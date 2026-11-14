; Continuation theorem for the actual ENVELOPE validator. This does not
; equate a partial run to a completed protocol execution or prove the raw host.
(in-package "ACL2")
(include-book "check-envelope")

(defthm fn2-envelope-prefix-compose
  (let ((first (fn2-envelope-prefix prefix i bytes-p taken caps fn2-core)))
    (implies (and (true-listp prefix) (natp i) (eq (mv-nth 0 first) :pass))
             (equal (fn2-envelope-prefix (append prefix suffix) i bytes-p taken caps fn2-core)
                    (fn2-envelope-prefix suffix (+ i (len prefix)) bytes-p
                      (mv-nth 1 first) (mv-nth 2 first) (mv-nth 3 first)))))
  :hints (("Goal" :induct (fn2-envelope-prefix prefix i bytes-p taken caps fn2-core)
           :in-theory (enable fn2-envelope-prefix))))

(defthm fn2-envelope-accepted-extension-has-accepted-prefix
  (implies (and (true-listp prefix)
                (eq (mv-nth 0 (fn2-envelope-prefix (append prefix suffix) i bytes-p taken caps fn2-core)) :pass))
           (eq (mv-nth 0 (fn2-envelope-prefix prefix i bytes-p taken caps fn2-core)) :pass))
  :hints (("Goal" :induct (fn2-envelope-prefix prefix i bytes-p taken caps fn2-core)
           :in-theory (enable fn2-envelope-prefix))))
