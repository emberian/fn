; Exact state-global access used by the owner carry writers.
; These effects equations do not establish the carry invariant of a whole
; owner transition. The owner wrappers must establish the value they put
; and preserve it through every subsequent state effect.
(in-package "ACL2")
(include-book "state-globals")

(defun fn-owner-retain-carry (state)
  (declare (xargs :stobjs state :guard t))
  (if (boundp-global 'fn-owner-retain-carry state)
      (f-get-global 'fn-owner-retain-carry state)
    nil))

(defun fn-owner-retain-carry-put (carry state)
  (declare (xargs :stobjs state :guard t))
  (f-put-global 'fn-owner-retain-carry carry state))

(defthm fn-owner-retain-carry-of-put
  (equal (fn-owner-retain-carry (fn-owner-retain-carry-put carry state))
         carry)
  :hints (("Goal" :in-theory (enable fn-owner-retain-carry
                                    fn-owner-retain-carry-put))))

(defthm fn-owner-retain-carry-of-other-global-put
  (implies (not (equal key 'fn-owner-retain-carry))
           (equal (fn-owner-retain-carry (f-put-global key value state))
                  (fn-owner-retain-carry state)))
  :hints (("Goal" :in-theory (enable fn-owner-retain-carry))))

(in-theory (disable fn-owner-retain-carry fn-owner-retain-carry-put))
