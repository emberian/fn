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

; A caller may open put-global before the getter frame can match. The
; actual fn-owner-finish guard reaches this exact normalized update after
; fn-host-hist-sync clears its unrelated reload flag.
(defthm fn-owner-retain-carry-of-other-global-update-by-definition
  (implies (not (equal key 'fn-owner-retain-carry))
           (equal (fn-owner-retain-carry
                   (update-nth 2 (add-pair key value (nth 2 state)) state))
                  (fn-owner-retain-carry state)))
  :hints (("Goal" :in-theory (enable fn-owner-retain-carry))))

; Actual host guard checkpoints have already opened boundp/get-global to
; the global table. Preserve the complete association, hence both binding
; and stored owner value, without reopening the carry writer.
(defthm fn-owner-retain-carry-put-frames-global-association
  (implies (not (equal key 'fn-owner-retain-carry))
           (equal (assoc-equal key (nth 2 (fn-owner-retain-carry-put carry state)))
                  (assoc-equal key (nth 2 state))))
  :hints (("Goal" :in-theory (enable fn-owner-retain-carry-put put-global))))

; The actual caller's later global puts require the returned state's
; shape. Export this rule while the setter stays closed.
(defthm fn-owner-retain-carry-put-preserves-state-p1
  (implies (state-p1 state)
           (state-p1 (fn-owner-retain-carry-put carry state)))
  :hints (("Goal" :in-theory (e/d (fn-owner-retain-carry-put)
                                  (state-p1)))))

(in-theory (disable fn-owner-retain-carry fn-owner-retain-carry-put))
