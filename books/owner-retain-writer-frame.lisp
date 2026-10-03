; Shared installer/auxiliary-write frame for actual owner carrier writers.
; No recovery producer or complete image row is loaded merely to prove a
; local writer. owner-retain-frame supplies the full pilot-backed profile.
(in-package "ACL2")
(include-book "owner-retain-transitions")

; -----------------------------------------------------------------------------
; The frame.

(defthm fn-orh-retain-statep-of-other-global-put
  (implies (and (not (equal key 'fn-owner))
                (not (equal key 'fn-owner-retain-carry)))
           (equal (fn-owner-retain-statep (f-put-global key value state))
                  (fn-owner-retain-statep state)))
  :hints (("Goal" :in-theory '(fn-owner-retain-statep
                               fn-owner-ocfg-of-other-global-put
                               fn-owner-bound-of-other-global-put
                               fn-owner-retain-carry-of-other-global-put))))

(defthm fn-owner-retain-statep-implies-lgoc
  (implies (fn-owner-retain-statep state)
           (fn-lgoc-invariantp (fn-owner-ocfg state)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-owner-retain-statep))))

(defthm fn-orh-retain-statep-of-install-ocfg
  (implies (and (fn-owner-retain-statep state)
                (fn-lgoc-invariantp oc))
           (fn-owner-retain-statep (fn-owner-install-ocfg oc state)))
  :hints (("Goal" :in-theory '(fn-owner-retain-statep
                               fn-owner-bound-of-install-ocfg
                               fn-owner-ocfg-of-install-ocfg
                               fn-owner-retain-carry-of-install-ocfg))))

(defthm fn-orh-retain-statep-of-retain-carry-put
  (implies (and (fn-owner-retain-statep state)
                (fn-prc-carryp carry))
           (fn-owner-retain-statep (fn-owner-retain-carry-put carry state)))
  :hints (("Goal" :in-theory '(fn-owner-retain-statep
                               fn-owner-bound-of-retain-carry-put
                               fn-owner-ocfg-of-retain-carry-put
                               fn-owner-retain-carry-of-put))))

